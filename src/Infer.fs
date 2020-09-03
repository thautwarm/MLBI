module Infer
module Surf = AST
open Core
open OpCPS
open HM
open FSharp.Compatibility.OCaml
open Mlib

type symbol = string

type tyEnv = (symbol, t) Map
let cnt = ref 0
let gensym() =
    let i = incret cnt;
    sprintf "x.%d" i

let type_type = Nom "Type"
let T x = App(type_type, x)
let (|T|_|) x =
  match x with
  | App(Nom "Type", x) -> Some x
  | _ -> None

let new_tvar () = Var <| ptr ()

let rec infer_t : tyEnv  -> Surf.ty_expr -> t =
    fun tyEnv ty_expr ->
    match
        match ty_expr with
        | Surf.TNew tn -> gensym () |> Nom |> T
        | Surf.TTup xs -> Tup <| List.map (infer_t tyEnv) xs |> T
        | Surf.TSym a ->
            T <| Nom a
        | Surf.TVar "_" ->
            T <| new_tvar()
        | Surf.TVar a ->
            match Map.tryFind a tyEnv with
            | None -> failwithf "%s not defined" a
            | Some t -> t
        | Surf.TApp(f, b) ->
            let f = infer_t tyEnv f in
            let b = infer_t tyEnv b in
            T <| App(f, b)
        | Surf.TForall(bounds, p) ->
            let unique_ns = List.map un bounds in
            let new_bindings =
                [|for un in unique_ns -> un.name, T <| Bou un|] in
            let p =
                infer_t (Map.letSeq tyEnv new_bindings) p
            in T <| Forall(unique_ns, p)
        | Surf.TArrow(a, b) ->
            let a = infer_t tyEnv a in
            let b = infer_t tyEnv b in
            T <| Fun(a, b)
        with
    | T x -> x
    | typetype ->
        let tvar = new_tvar() in
        let typetype' = T tvar in
        if not <| unify (typetype') typetype
        then failwith "not a type type"
        else prune tvar

let queries = ref []
let ineqs = ref []
let rec infer_term :
    tyEnv
    -> Surf.expr
    -> t =
    fun tyEnv ->
    function
    | Surf.EInt _ -> Nom "int"
    | Surf.ETup xs ->
        Tup <| List.map (infer_term tyEnv) xs
    | Surf.EVar v ->
        let v' = new_tvar()
        checkUnifyI ineqs <| v' <| tyEnv.[v]
        v'
    | Surf.ELam(s, v) ->
        let a = new_tvar()
        let t = infer_term (Map.add s a tyEnv) v
        Fun(a, t)
    | Surf.EApp(f, a) ->
        let a = infer_term tyEnv a
        let f = infer_term tyEnv f
        let a0, r0 = new_tvar(), new_tvar()
        checkUnifyI ineqs <| Fun(a0, r0) <| f
        checkUnifyI ineqs <| a0 <| a
        r0
    | Surf.ELet(t, n, v, body) ->
        let t =
            match t with
            | Some t -> infer_t tyEnv t
            | _ -> new_tvar()
        let tyEnv = Map.add n t tyEnv
        let v = infer_term tyEnv v
        checkUnifyI ineqs t v
        infer_term tyEnv body
    | Surf.EQuery expr ->
        let t = infer_term tyEnv expr
        queries := t :: !queries
        t


