module HM
open Core
open OpCPS
open Mlib
open FSharp.Compatibility.OCaml

exception RecursiveType of t * t

let rec unify : t -> t -> bool =
  fun lhs rhs ->
  let lhs = prune lhs in
  let rhs = prune rhs in
  match lhs, rhs with
  | Forall(ns1, p1), Forall(ns2, p2) ->
      begin
          let fresh2 = [for un in ns2 -> un, Var (ptr())]
          (unify p1 <| fresh (Map.ofList fresh2) p2)
      end &&
      begin
          let fresh1 = [for un in ns1 -> un, Var (ptr())]
          (unify p2 <| fresh (Map.ofList fresh1) p1)
      end
  | Var (Null as lhs),
    Var (Null as rhs)
    when lhs == rhs -> true
  | Var i, b
  | b, Var i ->
    if occur_in i b then
        raise <| RecursiveType(Var i, b)
    else
        i.set b; true
  | (Nom _ as lhs), (Nom _ as rhs) -> lhs = rhs
  | (Bou _ as lhs), (Bou _ as rhs) -> lhs = rhs
  | Fun(a1, r1), Fun(a2, r2)
  | App(a1, r1), App(a2, r2) ->
    unify a1 a2 && unify r1 r2
  | Tup xs1, Tup xs2 -> List.for_all2 unify xs1 xs2
  | _ -> false
