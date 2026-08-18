(** The mechanism which maps *external* identifiers (i.e., identifiers of
    definitions which we do not extract) to the models we use in the backends.

    This file contains the reader which loads lists of external names from JSON
    files (see the [-external-names] command-line option), and the name matcher
    maps which the rest of the compiler queries, built by merging the lists
    coming from the various sources. The packaged lists of builtin names
    (typically, Core/Std/Alloc) are in {!ExtractBuiltin}. *)

open Config
open NameMatcher (* TODO: include? *)

(* [ExtractBuiltin] transitively re-exports [ExtractName] (hence
   [NameMatcherMap]) and [ExtractBuiltinCore] (hence [mk_memoized]). *)
open ExtractBuiltin

let log = Logging.builtin_log

(** Raised when a list of external names can not be read. *)
exception Read_error of string

(** One list of external names, in the shapes the maps consume: either a file
    read by {!Json}, or the packaged lists of {!ExtractBuiltin}. *)
type t = {
  types : Pure.external_type_info list;
  functions : (pattern * Pure.external_fun_info) list;
  globals : Pure.external_global_info list;
  trait_decls : Pure.external_trait_decl_info list;
  trait_impls : (pattern * Pure.external_trait_impl_info) list;
}

(** Reading a list of external names from a JSON file. The types below are
    *wire* types: {!Json.load} turns them into the [Pure.external_*_info]
    records which the maps consume. *)
module Json = struct
  (** Raised while converting a single entry. *)
  exception Entry_error of string

  (* ---------------------------------------------------------------------- *)
  (* The entries, as they are written in the files                          *)
  (* ---------------------------------------------------------------------- *)

  (** A Rust name together with the name to use in the backend. *)
  type json_field = { rust : string; extract : string }

  (** [body: null] means that the type is opaque, which is *not* the same thing
      as an enumeration with no variant (e.g. [core::convert::Infallible]). *)
  and json_type_body = {
    kind : string;  (** ["struct"] or ["enum"] *)
    constructor : string option; [@default None]
        (** Structures only. Defaults to {!mk_struct_constructor}. *)
    fields : json_field list; [@default []]  (** Structures only. *)
    variants : json_field list; [@default []]
        (** Enumerations only: the [extract] names are *bare*. *)
    prefix_variant_names : bool; [@default true]
        (** Enumerations only: prefix the variant names with the extraction name
            of the type? See {!variant_extract_name}. *)
  }

  and json_type = {
    rust_pattern : string option; [@default None]
    rust_name : string option; [@default None]
    extract_name : string;
    keep_params : bool list option; [@default None]
    mut_regions : int list; [@default []]
    body : json_type_body option; [@default None]
  }

  and json_fun = {
    rust_pattern : string option; [@default None]
    rust_name : string option; [@default None]
    extract_name : string;
    keep_params : bool list option; [@default None]
    keep_trait_clauses : bool list option; [@default None]
    can_fail : bool; [@default true]
    lift : bool; [@default true]
    has_default : bool; [@default false]
  }

  and json_global = {
    rust_pattern : string option; [@default None]
    rust_name : string option; [@default None]
    extract_name : string;
    can_fail : bool; [@default true]
  }

  and json_trait_decl = {
    rust_pattern : string option; [@default None]
    rust_name : string option; [@default None]
    extract_name : string;
    constructor : string option; [@default None]
        (** Defaults to {!mk_struct_constructor}. *)
  }

  (** The [trait_items] bucket is flat, and keyed by the owning trait: every row
      names a row of the [trait_decls] bucket, as that row spells its name. *)
  and json_trait_item = {
    trait : string;
        (** The owning trait, as its [trait_decls] entry writes it. *)
    kind : string;  (** ["parent_clause"], ["method"], ["const"] or ["type"]. *)
    pos : int option; [@default None]
        (** ["parent_clause"] only: the position of the clause. *)
    rust : string option; [@default None]
        (** Every kind but ["parent_clause"], which has no Rust name. *)
    extract : string;
    has_default : bool; [@default false]  (** Methods only. *)
  }

  and json_trait_impl = {
    rust_pattern : string option; [@default None]
    rust_name : string option; [@default None]
    extract_name : string;
    keep_params : bool list option; [@default None]
    keep_trait_clauses : bool list option; [@default None]
  }
  [@@deriving of_yojson { strict = false }]

  (* ---------------------------------------------------------------------- *)
  (* Decoding a bucket                                                      *)
  (* ---------------------------------------------------------------------- *)

  (** [ppx_deriving_yojson] reports the path of the field it could not decode,
      and nothing else (a path ending in, e.g., ["json_type.extract_name"]): we
      keep only the last component, as the bucket and the index of the entry
      already give the context. *)
  let decode_error_msg (msg : string) : string =
    let field =
      match String.rindex_opt msg '.' with
      | Some i -> String.sub msg (i + 1) (String.length msg - i - 1)
      | None -> msg
    in
    "invalid or missing field \"" ^ field ^ "\""

  (** Decode then convert the entries of a bucket, one by one, so that a failure
      can be attributed to a single entry. An absent bucket is empty. [conv]
      signals an ill-formed entry with {!Entry_error}.

      We do not catch [Failure] here: it would also catch the internal errors
      raised from inside a conversion. {!parse_entry_pattern} turns the one we
      do expect into an {!Entry_error}. *)
  let read_bucket (file : string) (fields : (string * Yojson.Safe.t) list)
      (bucket : string) (of_json : Yojson.Safe.t -> ('r, string) result)
      (conv : 'r -> 'a) : 'a list =
    let rows =
      match List.assoc_opt bucket fields with
      | None | Some `Null -> []
      | Some (`List rows) -> rows
      | Some _ ->
          raise
            (Read_error (Printf.sprintf "%s: \"%s\" must be a list" file bucket))
    in
    let decode (i : int) (row : Yojson.Safe.t) : 'a =
      let error (msg : string) =
        raise (Read_error (Printf.sprintf "%s: %s[%d]: %s" file bucket i msg))
      in
      match of_json row with
      | Error msg -> error (decode_error_msg msg)
      | Ok row -> ( try conv row with Entry_error msg -> error msg)
    in
    List.mapi decode rows

  (* ---------------------------------------------------------------------- *)
  (* Converting the entries                                                 *)
  (* ---------------------------------------------------------------------- *)

  (** The name of the Rust definition an entry is about, as written in the file.

      An entry may give both, in which case ["rust_pattern"] wins *)
  let entry_name (rust_pattern : string option) (rust_name : string option) :
      string =
    match (rust_pattern, rust_name) with
    | Some name, _ | None, Some name -> name
    | None, None ->
        raise (Entry_error "missing field \"rust_pattern\" (or \"rust_name\")")

  (** [parse_pattern] raises [Failure] with a message which carries the position
      of the error inside the pattern: we turn it into an {!Entry_error} so that
      {!read_bucket} can locate the entry. *)
  let parse_entry_pattern (pattern : string) : pattern =
    try parse_pattern pattern with Failure msg -> raise (Entry_error msg)

  let entry_pattern (rust_pattern : string option) (rust_name : string option) :
      pattern =
    parse_entry_pattern (entry_name rust_pattern rust_name)

  (** The files store *bare* variant names, so we prefix them with the
      extraction name of their type unless the entry opted out. Same separators
      as the packaged types of [ExtractBuiltin.builtin_types] - note that HOL4
      uses none. *)
  let variant_extract_name ~(prefix : bool) (type_name : string)
      (variant : string) : string =
    if not prefix then variant
    else
      match backend () with
      | FStar | Coq -> type_name ^ "_" ^ variant
      | Lean -> type_name ^ "." ^ variant
      | HOL4 -> type_name ^ variant

  let external_type_of_json (row : json_type) : Pure.external_type_info =
    let rust_name = entry_pattern row.rust_pattern row.rust_name in
    let body_info : Pure.external_type_body_info option =
      match row.body with
      | None -> None
      | Some body -> (
          match body.kind with
          | "struct" ->
              let constructor =
                Option.value body.constructor
                  ~default:(mk_struct_constructor row.extract_name)
              in
              let fields =
                List.map
                  (fun (f : json_field) -> (f.rust, f.extract))
                  body.fields
              in
              Some (Pure.Struct (constructor, fields))
          | "enum" ->
              let variants =
                List.map
                  (fun (v : json_field) : Pure.external_enum_variant_info ->
                    {
                      rust_variant_name = v.rust;
                      extract_variant_name =
                        variant_extract_name ~prefix:body.prefix_variant_names
                          row.extract_name v.extract;
                      fields = None;
                    })
                  body.variants
              in
              Some (Pure.Enum variants)
          | kind ->
              raise
                (Entry_error
                   ("unknown body kind: '" ^ kind
                  ^ "' (expected \"struct\" or \"enum\")")))
    in
    {
      rust_name;
      extract_name = row.extract_name;
      keep_params = row.keep_params;
      mut_regions = row.mut_regions;
      body_info;
    }

  let external_fun_of_json (row : json_fun) : pattern * Pure.external_fun_info =
    ( entry_pattern row.rust_pattern row.rust_name,
      {
        keep_params = row.keep_params;
        keep_trait_clauses = row.keep_trait_clauses;
        extract_name = row.extract_name;
        can_fail = row.can_fail;
        (* [stateful] is never read: see [FunsAnalysis.analyze_fun_decl]. *)
        stateful = false;
        lift = row.lift;
        has_default = row.has_default;
      } )

  let external_global_of_json (row : json_global) : Pure.external_global_info =
    {
      rust_name = entry_pattern row.rust_pattern row.rust_name;
      extract_name = row.extract_name;
      can_fail = row.can_fail;
    }

  let external_trait_impl_of_json (row : json_trait_impl) :
      pattern * Pure.external_trait_impl_info =
    ( entry_pattern row.rust_pattern row.rust_name,
      {
        extract_name = row.extract_name;
        keep_params = row.keep_params;
        keep_trait_clauses = row.keep_trait_clauses;
      } )

  (** A single decoded [trait_items] entry. *)
  type trait_item =
    | ItParentClause of (int * string)
    | ItConst of (string * string)
    | ItType of (string * string)
    | ItMethod of (string * Pure.external_fun_info)

  (** [declared] is the set of the names of the [trait_decls] entries. *)
  let trait_item_of_json (declared : Collections.StringSet.t)
      (row : json_trait_item) : string * trait_item =
    if not (Collections.StringSet.mem row.trait declared) then
      raise
        (Entry_error
           ("unknown trait: '" ^ row.trait
          ^ "' does not appear in the \"trait_decls\" bucket"));
    (* The kind determines which of [rust] and [pos] must be given. *)
    let item =
      match (row.kind, row.rust, row.pos) with
      | "parent_clause", None, Some pos -> ItParentClause (pos, row.extract)
      | "const", Some rust, None -> ItConst (rust, row.extract)
      | "type", Some rust, None -> ItType (rust, row.extract)
      | "method", Some rust, None ->
          ItMethod
            ( rust,
              {
                keep_params = None;
                keep_trait_clauses = None;
                extract_name = row.extract;
                can_fail = true;
                stateful = false;
                lift = true;
                has_default = row.has_default;
              } )
      | "parent_clause", _, _ ->
          raise
            (Entry_error
               "kind \"parent_clause\" requires \"pos\" and does not accept \
                \"rust\"")
      | ("const" | "type" | "method"), _, _ ->
          raise
            (Entry_error
               ("kind \"" ^ row.kind
              ^ "\" requires \"rust\" and does not accept \"pos\""))
      | kind, _, _ ->
          raise
            (Entry_error
               ("unknown trait item kind: '" ^ kind
              ^ "' (expected \"parent_clause\", \"method\", \"const\" or \
                 \"type\")"))
    in
    (row.trait, item)

  (** [items] is the whole, flat [trait_items] bucket: we pick the entries of
      this trait, in the order of the file. *)
  let external_trait_decl_of_json (items : (string * trait_item) list)
      ((row, name, rust_name) : json_trait_decl * string * pattern) :
      Pure.external_trait_decl_info =
    let pick f =
      List.filter_map
        (fun (trait, item) -> if trait = name then f item else None)
        items
    in
    (* The extraction matches the parent clauses by position, so we order them by
       [pos]; the other items are matched by Rust name. *)
    let parent_clauses =
      List.map snd
        (List.stable_sort
           (fun (pos0, _) (pos1, _) -> compare pos0 pos1)
           (pick (function
             | ItParentClause c -> Some c
             | _ -> None)))
    in
    {
      rust_name;
      extract_name = row.extract_name;
      constructor =
        Option.value row.constructor
          ~default:(mk_struct_constructor row.extract_name);
      parent_clauses;
      consts =
        pick (function
          | ItConst c -> Some c
          | _ -> None);
      types =
        pick (function
          | ItType t -> Some t
          | _ -> None);
      methods =
        pick (function
          | ItMethod m -> Some m
          | _ -> None);
    }

  (* ---------------------------------------------------------------------- *)
  (* Loading a file                                                         *)
  (* ---------------------------------------------------------------------- *)

  (** Load a list of external names from a JSON file. Raises {!Read_error}.

      There is deliberately no version to check; the counterpart is that a field
      may never change meaning - a new one, with a backward-compatible default,
      is the only way to change what a file says. ["format_version"] stays
      reserved and, like any other key we do not know, is accepted and ignored.
  *)
  let load (file : string) : t =
    [%ldebug "Loading the list of external names from: " ^ file];
    let json =
      try Yojson.Safe.from_file file with
      (* [Sys_error] already names the file *)
      | Sys_error msg -> raise (Read_error msg)
      | Yojson.Json_error msg -> raise (Read_error (file ^ ": " ^ msg))
    in
    let fields =
      match json with
      | `Assoc fields -> fields
      | _ ->
          raise
            (Read_error (file ^ ": expected a JSON object at the top level"))
    in
    let read bucket of_json conv =
      read_bucket file fields bucket of_json conv
    in
    let types = read "types" json_type_of_yojson external_type_of_json in
    let functions = read "functions" json_fun_of_yojson external_fun_of_json in
    let globals =
      read "globals" json_global_of_yojson external_global_of_json
    in
    let trait_impls =
      read "trait_impls" json_trait_impl_of_yojson external_trait_impl_of_json
    in
    (* The trait declarations must be decoded before the items which refer to
       them. *)
    let decls =
      read "trait_decls" json_trait_decl_of_yojson
        (fun (row : json_trait_decl) ->
          (* The name as written in the file is what [trait_items] refers to. *)
          let name = entry_name row.rust_pattern row.rust_name in
          (row, name, parse_entry_pattern name))
    in
    let declared =
      Collections.StringSet.of_list (List.map (fun (_, name, _) -> name) decls)
    in
    let items =
      read "trait_items" json_trait_item_of_yojson (trait_item_of_json declared)
    in
    let trait_decls = List.map (external_trait_decl_of_json items) decls in
    { types; functions; globals; trait_decls; trait_impls }
end

(* ------------------------------------------------------------------------ *)
(* The sources of external names                                            *)
(* ------------------------------------------------------------------------ *)

(** The lists given through [-external-names], in command-line order, filled in
    by {!load_files}. *)
let loaded_sources : t list ref = ref []

(** The packaged entries, i.e. the ones we ship. Memoized: {!merge_sources} is
    called once per map, and computing the packaged lists parses all their name
    patterns. *)
let builtin_source =
  mk_memoized (fun () : t ->
      {
        types = builtin_types ();
        functions = mk_builtin_funs ();
        globals = builtin_globals ();
        trait_decls = builtin_trait_decls_info ();
        trait_impls = builtin_trait_impls_info ();
      })

(** Load the files given through [-external-names]. This must be called *before*
    any of the maps below is forced: they are memoized, so forcing them first
    would ignore the imported entries. Raises {!Read_error}. *)
let load_files () : unit =
  loaded_sources := List.map Json.load !external_names_files

(** Concatenate one bucket over all the sources, in increasing order of
    precedence: the packaged entries first, then the files given through
    [-external-names], in command-line order - so that the later entries
    override the earlier ones when building the maps. *)
let merge_sources (get : t -> 'a list) : 'a list =
  List.concat_map get (builtin_source () :: !loaded_sources)

(* ------------------------------------------------------------------------ *)
(* The maps                                                                 *)
(* ------------------------------------------------------------------------ *)

(** Build a name matcher map out of a list of entries ordered by increasing
    precedence: an entry which shadows an earlier one replaces it. When
    [warn_override] is given, such an override is reported as a warning, and
    used to name the two entries in it. *)
let name_matcher_map_of_list ?warn_override (ls : (pattern * 'a) list) :
    'a NameMatcherMap.t =
  let config : print_config = { tgt = TkPattern } in
  List.fold_left
    (fun m (pat, info) ->
      [%ldebug "About to add pattern: " ^ pattern_to_string config pat];
      (* [replace] inserts and checks whether we replaced a pattern *)
      let m, old = NameMatcherMap.replace pat info m in
      (match (old, warn_override) with
      | Some old, Some name ->
          log#swarning
            ("Pattern registered twice for an external definition: "
            ^ pattern_to_string config pat
            ^ " (" ^ name old ^ " is overridden by " ^ name info ^ ")\n")
      | _ -> ());
      m)
    NameMatcherMap.empty ls

(* How the entries are named in the override warning above. *)
let global_extract_name (i : Pure.external_global_info) = i.extract_name
let type_extract_name (i : Pure.external_type_info) = i.extract_name
let fun_extract_name (i : Pure.external_fun_info) = i.extract_name
let trait_decl_extract_name (i : Pure.external_trait_decl_info) = i.extract_name
let trait_impl_extract_name (i : Pure.external_trait_impl_info) = i.extract_name

let mk_external_globals_map () : Pure.external_global_info NameMatcherMap.t =
  name_matcher_map_of_list ~warn_override:global_extract_name
    (List.map
       (fun (info : Pure.external_global_info) -> (info.rust_name, info))
       (merge_sources (fun source -> source.globals)))

let external_globals_map = mk_memoized mk_external_globals_map

let mk_external_types_map () =
  name_matcher_map_of_list ~warn_override:type_extract_name
    (List.map
       (fun (info : Pure.external_type_info) -> (info.rust_name, info))
       (merge_sources (fun source -> source.types)))

let external_types_map = mk_memoized mk_external_types_map

(** Map from rust type name to its external info, restricted to the types that
    carry a [keep_params] filter (i.e. types from which Charon's
    [hide_allocator] pass leaves a dangling allocator type parameter, such as
    [alloc::vec::into_iter::IntoIter]).

    Unlike {!external_types_map}, this map is *not* emptied under
    [-core-models-lib]: even when the external type overrides are disabled, we
    still need to drop the dangling allocator type parameter so that the
    extracted types match the [core_models] library, which models them without
    an allocator (e.g. [IntoIter T] rather than [IntoIter T Global]).

    It is also the only map which is not merged with the sources above: it is
    built from the packaged list alone. Its single consumer
    ([SymbolicToPureTypes.translate_type_decl]) only tries this fallback under
    [-core-models-lib], so an imported entry could not reach it anyway - and
    being single-source, a duplicate pattern here is a bug rather than an
    override, which is what [NameMatcherMap.of_list] asserts. *)
let mk_external_types_keep_params_map () =
  NameMatcherMap.of_list
    (List.filter_map
       (fun (info : Pure.external_type_info) ->
         match info.keep_params with
         | Some _ -> Some (info.rust_name, info)
         | None -> None)
       lean_builtin_types)

let external_types_keep_params_map =
  mk_memoized mk_external_types_keep_params_map

(** All the external trait declarations, ordered by increasing precedence. *)
let external_trait_decls : unit -> Pure.external_trait_decl_info list =
  mk_memoized (fun () -> merge_sources (fun source -> source.trait_decls))

let mk_external_trait_decls_map () =
  name_matcher_map_of_list ~warn_override:trait_decl_extract_name
    (List.map
       (fun (info : Pure.external_trait_decl_info) -> (info.rust_name, info))
       (external_trait_decls ()))

let external_trait_decls_map = mk_memoized mk_external_trait_decls_map

let mk_external_trait_impls_map () =
  let m =
    name_matcher_map_of_list ~warn_override:trait_impl_extract_name
      (merge_sources (fun source -> source.trait_impls))
  in
  [%ltrace NameMatcherMap.to_string (fun _ -> "...") m];
  m

let external_trait_impls_map = mk_memoized mk_external_trait_impls_map

(** The external functions coming from the sources, plus the default trait
    methods, which we synthesize from the trait declarations - hence *after*
    they have been merged. *)
let external_funs : unit -> (pattern * Pure.external_fun_info) list =
  let mk () =
    let sep = backend_choice "_" "." in
    let default_methods =
      List.concat_map
        (fun (d : Pure.external_trait_decl_info) ->
          List.filter_map
            (fun ((fpat, f) : string * Pure.external_fun_info) ->
              if f.has_default then
                Some
                  ( d.rust_name @ [ PIdent (fpat, 0, []) ],
                    {
                      f with
                      extract_name =
                        d.extract_name ^ sep ^ f.extract_name ^ sep ^ "default";
                    } )
              else None)
            d.methods)
        (external_trait_decls ())
    in
    merge_sources (fun source -> source.functions) @ default_methods
  in
  mk_memoized mk

let mk_external_funs_map () =
  [%ldebug "Building the external funs map"];
  let m =
    name_matcher_map_of_list ~warn_override:fun_extract_name (external_funs ())
  in
  [%ltrace NameMatcherMap.to_string (fun _ -> "...") m];
  m

let external_funs_map = mk_memoized mk_external_funs_map

type effect_info = { can_fail : bool }

let mk_external_fun_effects () : (pattern * effect_info) list =
  List.map
    (fun ((pattern, info) : _ * Pure.external_fun_info) ->
      (pattern, { can_fail = info.can_fail }))
    (external_funs ())

let mk_external_fun_effects_map () =
  [%ldebug "Building the external funs effects map"];
  (* No override warning: this map is derived from the same list as
     {!external_funs_map}, which already reported them. *)
  name_matcher_map_of_list (if_backend mk_external_fun_effects [])

let external_fun_effects_map = mk_memoized mk_external_fun_effects_map
