(** The mechanism which maps *external* identifiers (i.e., identifiers of
    definitions which we do not extract) to the models we use in the backends.

    This file contains the name matcher maps and the functions which build them.
    The packaged lists of definitions which those maps are built from
    (typically, Core/Std/Alloc) are in {!ExtractBuiltin}. *)

open Config
open NameMatcher (* TODO: include? *)

(* [ExtractBuiltin] transitively re-exports [ExtractName] (hence
   [NameMatcherMap]) and [ExtractBuiltinCore] (hence [mk_memoized]). *)
open ExtractBuiltin

let log = Logging.builtin_log

let mk_external_globals_map () : Pure.external_global_info NameMatcherMap.t =
  NameMatcherMap.of_list
    (List.map
       (fun (info : Pure.external_global_info) -> (info.rust_name, info))
       (builtin_globals ()))

let external_globals_map = mk_memoized mk_external_globals_map

let mk_external_types_map () =
  NameMatcherMap.of_list
    (List.map
       (fun (info : Pure.external_type_info) -> (info.rust_name, info))
       (builtin_types ()))

let external_types_map = mk_memoized mk_external_types_map

(** Map from rust type name to its external info, restricted to the types that
    carry a [keep_params] filter (i.e. types from which Charon's
    [hide_allocator] pass leaves a dangling allocator type parameter, such as
    [alloc::vec::into_iter::IntoIter]).

    Unlike {!external_types_map}, this map is *not* emptied under
    [-core-models-lib]: even when the external type overrides are disabled, we
    still need to drop the dangling allocator type parameter so that the
    extracted types match the [core_models] library, which models them without
    an allocator (e.g. [IntoIter T] rather than [IntoIter T Global]). *)
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

let mk_external_trait_decls_map () =
  NameMatcherMap.of_list
    (List.map
       (fun (info : Pure.external_trait_decl_info) -> (info.rust_name, info))
       (builtin_trait_decls_info ()))

let external_trait_decls_map = mk_memoized mk_external_trait_decls_map

let mk_external_trait_impls_map () =
  let m = NameMatcherMap.of_list (builtin_trait_impls_info ()) in
  [%ltrace NameMatcherMap.to_string (fun _ -> "...") m];
  m

let external_trait_impls_map = mk_memoized mk_external_trait_impls_map

let builtin_funs : unit -> (pattern * Pure.external_fun_info) list =
  (* We need to take into account the default trait methods *)
  let mk () =
    let funs = mk_builtin_funs () in
    let trait_decls = builtin_trait_decls_info () in
    let default_methods =
      List.map
        (fun (d : Pure.external_trait_decl_info) ->
          List.filter_map
            (fun ((fpat, f) : string * Pure.external_fun_info) ->
              if f.has_default then
                let sep =
                  match backend () with
                  | Lean -> "."
                  | _ -> "_"
                in
                let pattern = d.rust_name @ [ PIdent (fpat, 0, []) ] in
                let info =
                  {
                    f with
                    extract_name =
                      d.extract_name ^ sep ^ f.extract_name ^ sep ^ "default";
                  }
                in
                Some (pattern, info)
              else None)
            d.methods)
        trait_decls
    in
    funs @ List.concat default_methods
  in
  mk_memoized mk

let name_matcher_map_of_list (ls : (pattern * 'a) list) : 'a NameMatcherMap.t =
  let config : print_config = { tgt = TkPattern } in
  List.fold_left
    (fun m (pat, info) ->
      [%ldebug "About to add pattern: " ^ pattern_to_string config pat];
      (* [replace] inserts and checks whether we replaced a pattern *)
      let m, old = NameMatcherMap.replace pat info m in
      [%cassert_opt_span] None (old = None)
        ("Pattern registered twice for a builtin definition: "
        ^ pattern_to_string config pat);
      m)
    NameMatcherMap.empty ls

let mk_external_funs_map () =
  [%ldebug "Builting the builtin funs map"];
  let m =
    name_matcher_map_of_list
      (List.map (fun (name, info) -> (name, info)) (builtin_funs ()))
  in
  [%ltrace NameMatcherMap.to_string (fun _ -> "...") m];
  m

let external_funs_map = mk_memoized mk_external_funs_map

type effect_info = { can_fail : bool }

let mk_builtin_fun_effects () : (pattern * effect_info) list =
  let builtin_funs : (pattern * Pure.external_fun_info) list =
    builtin_funs ()
  in
  List.map
    (fun ((pattern, info) : _ * Pure.external_fun_info) ->
      let info = { can_fail = info.can_fail } in
      (pattern, info))
    builtin_funs

let mk_external_fun_effects_map () =
  [%ldebug "Builting the builtin funs effects map"];
  name_matcher_map_of_list (if_backend mk_builtin_fun_effects [])

let external_fun_effects_map = mk_memoized mk_external_fun_effects_map
