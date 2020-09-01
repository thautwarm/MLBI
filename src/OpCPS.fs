#indent "off"
module OpCPS

open FSharp.Compatibility.OCaml
open Core
open Mlib



exception NonConsistentTypes of t * t


let rec transform_post post root =
    let self = transform_post post in
    let t =
        match root with
        | Bou _ | Nom _  | Var Null -> root
        | Var (Contents t) -> self t
        | App(a, b) -> App(self a, self b)
        | Fun(a, b) -> Fun(self a, self b)
        | Forall(uns, t) -> Forall(uns, self t)
    in post t

let transform_ctx self ctx root =
    let self = self ctx in
    match root with
    | Bou _ | Nom _  | Var Null -> root
    | Var (Contents t) -> self t
    | App(a, b) -> App(self a, self b)
    | Fun(a, b) -> Fun(self a, self b)
    | Forall(uns, t) -> Forall(uns, self t)

let check self root =
    match root with
    | Bou _ | Nom _  | Var Null -> true
    | Var (Contents t) -> self t
    | App(a, b) -> self a && self b
    | Fun(a, b) -> self a && self b
    | Forall(_, t) -> self t

let fresh =
    transform_ctx @@ let rec subst fresh term =
    match term with
    | Bou un ->
        begin match Map.tryFind un fresh with
        | Some x -> x
        | _ -> term
        end
    | _ -> transform_ctx subst fresh term
    in subst

let instantiate =
    function
    | Forall(uns, p) ->
        fresh <| Map.ofList [for un in uns -> un, Var <| ptr ()] <| p
    | a -> a


let refresh_ts : t list -> t list = fun xs ->
    let tbl = Hashtbl.create 8 in
    let post = function
        | Var v when Hashtbl.mem tbl v ->
            Hashtbl.find tbl v
        | Var v ->
            let v' = Var <| ptr ()
            in Hashtbl.add tbl v v'; v'
        | a -> a
    in List.map (transform_post post) xs

let refresh_t : t -> t = fun t ->
    match refresh_ts [t] with
    | [t] -> t
    | _ -> failwith "impossible"

let occur_in : tvar -> t -> bool =
    fun i ty ->
    let rec selfCheck = function
        | Var i' when i' == i -> false
        | x -> check selfCheck x
    in not (selfCheck ty)

let rec unifyI cs lhs rhs =
    match prune lhs, prune rhs with
    | Var (Null as lhs),
      Var (Null as rhs)
      when lhs == rhs -> true

    | (Nom _ as lhs), (Nom _ as rhs) -> lhs = rhs
    | (Bou _ as lhs), (Bou _ as rhs) -> lhs = rhs
    | Var v, rhs -> cs := LE(v, rhs)::!cs; true
    | lhs, Var v -> cs := GE(v, lhs)::!cs; true
    | App(f1, a1), App(f2, a2) ->
        unifyI cs f1 f2 && unifyI cs a1 a2
    | Fun(a1, r1), Fun(a2, r2) ->
        unifyI cs a2 a1 && unifyI cs r1 r2
    | lhs, (Forall(_, _) as rhs) ->
        unifyI cs lhs (instantiate rhs)
    | Forall(_, lhs), rhs ->
        unifyI cs lhs rhs
    | _ -> false

let checkUnifyI cs lhs rhs =
    if unifyI cs lhs rhs
    then ()
    else
    raise <| NonConsistentTypes(lhs, rhs)


let need_parens : t -> bool
    = function
      | Forall(_, _)
      | App(_, _)
      | Fun(_, _) -> true
      | _ -> false

