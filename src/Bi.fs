#indent "off"

module Bi

open Core
open OpCPS
open HM
open FSharp.Compatibility.OCaml
open Mlib


type rels =
  { le : t list
  ; ge : t list
  }

exception Fail of (t * t * (tvar, rels) Hashtbl.t)
let notVar x = match prune x with
  | Var _ -> false
  | _ -> true


type constraints = inequation list

let rec moreSpecificThan lhs rhs =
  let constraints = ref []
  in
  unifyI constraints lhs rhs &&
  solveInEqs !constraints

and solveInEqs : constraints -> bool = fun cs ->
  // printfn "recursive solve again:";
  // for x in cs do
  //   printfn "%O" x
  // done;
  match normalize (ref []) cs with
  | None -> true
  | Some [LE(a, b)] -> unify (Var a) b
  | Some [GE(a, b)] -> unify (Var a) b
  | Some cs ->
#if DEBUG
  Log.logConstraints cs;
#endif
  let constraint_groups = Hashtbl.create 16 in
  let _ = flip List.iter cs <| function
  | GE(a, b) ->
    begin match Hashtbl.find_opt constraint_groups a with
    | None ->
      Hashtbl.add constraint_groups a {ge = [b]; le = []}
    | Some ({ ge=ge } as rels) ->
      Hashtbl.replace constraint_groups a {rels with ge = b::ge}
    end
  | LE(a, b) ->
    begin match Hashtbl.find_opt constraint_groups a with
    | None ->
      Hashtbl.add constraint_groups a {ge = []; le = [b]}
    | Some ({ le=le } as rels) ->
      Hashtbl.replace constraint_groups a {rels with le = b::le}
    end
  in
  try
    let recurs = Hashtbl.create 8 in
    let _ = flip Hashtbl.iter constraint_groups <|
        fun k _ ->
          ignore <| solveInEqsFor recurs k constraint_groups
    in true
  with Fail (l, r, g) ->
#if DEBUG
    let _ = flip Hashtbl.iter g <| fun k v ->
      printfn "> fail %O = %O" <| Var k <| prune (Var k);
      printfn "when asserting %O(%O) <= %O(%O)" l (prune l) r (prune r);
      printfn "<=  %O" <| List.map prune v.le;
      printfn ">=  %O" <| List.map prune v.ge
    in
#endif
    false

and typemax maxtype = function
| Var _::tl -> typemax maxtype tl
| hd::tl ->
  let [hd';maxtype'] = refresh_ts [hd; maxtype]
  in if moreSpecificThan maxtype' hd'
  then typemax hd tl
  else typemax maxtype tl
| [] -> maxtype

and typemin mintype = function
| Var _::tl -> typemin mintype tl
| hd::tl ->
  let [hd';mintype'] = refresh_ts [hd; mintype]
  in if moreSpecificThan hd' mintype'
  then typemin hd tl
  else typemin mintype tl
| [] -> mintype

and normalize cs = function
  | LE(a, b)::tl ->
    if unifyI cs (Var a) b
    then normalize cs tl
    else None
  | GE(a, b)::tl ->
    if unifyI cs b (Var a)
    then normalize cs tl
    else None
  | [] ->
    if List.for_all
      (function
       | LE(Null, _) | GE(Null, _) -> true
       | _ -> false)
      !cs
    then Some !cs
    else
      let new_cs = ref []
      in normalize new_cs !cs


and solveInEqsFor recurs typevar constraint_groups: t =
#if DEBUG
  printfn "=====starting: %O======" <| Var typevar;
#endif
  if Hashtbl.mem recurs typevar
  then prune @@ Var typevar
  else
  let _ = Hashtbl.add recurs typevar () in
  match Hashtbl.find_opt constraint_groups typevar with
  | None -> prune @@ Var typevar
  | Some {le=le; ge=ge} ->
    let rec solve_inner = function
    | Var i -> solveInEqsFor recurs i constraint_groups
    | a -> transform solve_inner a
    in
    let rec solve_seq = function
    | [] -> []
    | hd::tl -> solve_inner hd::solve_seq tl
    in
    let le, ge = solve_seq le, solve_seq ge in
    let mintype = match List.filter notVar le with
    | [] -> Var typevar
    | hd::tl -> typemin hd tl
    in
    let maxtype = match List.filter notVar ge with
    | [] -> Var typevar
    | hd :: tl -> typemax hd tl
    in
    let me = Var typevar in
#if DEBUG
    printfn ">> for %O:" me;
    printfn "= %O" <| prune me;
    printfn "less than %O:" (prune mintype);
    printfn "less than of %O" (List.map prune le);
    printfn "greater than %O:" (prune maxtype);
    printfn "greater than of %O" (List.map prune ge);
#endif
    if not (moreSpecificThan me mintype)
      then raise <| Fail(me, mintype, constraint_groups)
    else
    if not (moreSpecificThan maxtype me)
      then raise <| Fail(maxtype, me, constraint_groups)
    else
    let _ = flip List.iter le <| fun t ->
      if not (moreSpecificThan me t)
      then raise <| Fail(me, t, constraint_groups)
    in
    let _ = flip List.iter ge <| fun t ->
      if not (moreSpecificThan t me)
      then raise <| Fail(t, me, constraint_groups)
    in
#if DEBUG
  (fun x ->
      printfn "===========solved: %O = %O============" (Var typevar) x;
      x) <|
#endif
    prune me
