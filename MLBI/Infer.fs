module Infer
open Common
open HM
open HMUnification
open CamlCompat

type tyEnv = (symbol, HM.t) Map
let cnt = ref 0
let gensym() =
    incr cnt;
    sprintf "x.%d" !cnt

let type_type = HM.TNom "Type"
let T x = HM.TApp(type_type, x)
let (|T|_|) x =
  match x with
  | HM.TApp(HM.TNom "Type", x) -> Some x
  | _ -> None


let rec infer_t : tcstate -> tyEnv  -> Surf.ty_expr -> t =
    fun ({new_tvar=new_tvar; unify=unify; prune=prune} as tc) tyEnv ty_expr ->
    match
        match ty_expr with
        | Surf.TNew tn -> gensym () |> TNom |> T
        | Surf.TSym a ->
            T <| TNom a
        | Surf.TVar "_" ->
            T <| new_tvar()
        | Surf.TVar a ->
            match Map.tryFind a tyEnv with
            | None -> failwithf "%s not defined" a
            | Some t -> t
        | Surf.TApp(f, b) ->
            let f = infer_t tc tyEnv f in
            let b = infer_t tc tyEnv b in
            T <| TApp(f, b)
        | Surf.TTup xs ->
            List.map (infer_t tc tyEnv) xs |> TTup |> T
        | Surf.TForall(bounds, p) ->
            let unique_ns = List.map un bounds in
            let new_bindings =
                [|for un in unique_ns -> un.name, T <| TBound un|] in
            let p =
                infer_t tc (Map.letSeq tyEnv new_bindings) p
            in T <| TForall(unique_ns, p)
        | Surf.TArrow(a, b) ->
            let a = infer_t tc tyEnv a in
            let b = infer_t tc tyEnv b in
            T <| TArrow(a, b)
        with
    | T x -> x
    | typetype ->
        let tvar = new_tvar() in
        let typetype' = T tvar in
        if not <| unify (typetype') typetype
        then failwith "not a type type"
        else prune tvar

let queries = darray()
let ineqs = dset()
let rec infer_term :
    tcstate
    -> tyEnv
    -> Surf.expr
    -> t =
    fun ({new_tvar=new_tvar; unify=unify; prune=prune} as tc) tyEnv ->
    function
    | Surf.EVar v ->
        let t = new_tvar()
        DSet.add ineqs (t, tyEnv.[v])
        t
    | Surf.ELam(s, v) ->
        let a = new_tvar()
        let t = infer_term tc (Map.add s a tyEnv) v
        TArrow(a, t)
    | Surf.EApp(f, a) ->
        let a = infer_term tc tyEnv a
        let f = infer_term tc tyEnv f
        let a0, r0 = new_tvar(), new_tvar()
        DSet.add ineqs (TArrow(a0, r0), f)
        DSet.add ineqs (a0, a)
        r0
    | Surf.ELet(t, n, v, body) ->
        let t =
            match t with
            | Some t -> infer_t tc tyEnv t
            | _ -> new_tvar()
        let tyEnv = Map.add n t tyEnv
        let v = infer_term tc tyEnv v
        DSet.add ineqs (t, v)
        infer_term tc tyEnv body
    | Surf.EQuery expr ->
        let t = infer_term tc tyEnv expr
        DArray.push queries t
        t



