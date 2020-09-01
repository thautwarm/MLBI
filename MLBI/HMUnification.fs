module HMUnification

open HM
open CamlCompat
open Common

exception RecursiveType of string

let substitute : (t, t) map -> t -> t
    = fun map ->
    let rec self : t -> t = fun a ->
        match Map.tryFind a map with
        | Some t -> t
        | None -> generic_transform self a
    in self

let fresh :  (un, t) map -> t -> t =
  fun map ->
    let rec self : t -> t =
      function
      | TBound a as t ->
          begin
          match Map.tryFind a map with
          | Some t -> t
          | None -> t
          end
      | t -> generic_transform self t
    in self

type tcstate =
  { unify : t -> t -> bool
  ; unifyInsts : t -> t -> bool
  ; unifyOrder : t -> t -> bool
  ; unifyBI : t -> t -> (t -> t -> unit) -> bool
  ; tenv : t darray
  ; prune : t -> t
  ; new_tvar : unit -> t
  ; prune_with_var_check : (int -> unit) -> t -> t
  }

let mk_tcstate (tenv: t darray)
    =
    let bound_links : (un, int dset) dict = dict() in
    let unlink (b: un) f =
        match Dict.pop bound_links b with
        | None -> ()
        | Some rels ->
        let _ = DSet.foreach rels <| fun rel ->
            let _ = DArray.set tenv rel <| TVar rel
            in f rel
        in
        DSet.clear rels
      in
    let new_tvar() =
        let typeref = DArray.len tenv in
        let tvar = TVar typeref in
        let _ = DArray.push tenv tvar in
        tvar
      in
    let occur_in : int -> t -> bool =
        fun i ty ->
        match ty with
        | TVar i' when i' = i -> false
        | _ ->
            let rec check = function
                | TVar i' when i' = i -> false
                | x -> generic_check check x
            in not (check ty)
      in
    let link : int -> t -> t =
        fun typeref t ->
        match match t with
              | TBound un ->  Some un
              | _ -> None
              with
        | None ->
           let _ = DArray.set tenv typeref t
           in t
        | Some un ->
            let _ = DArray.set tenv typeref t
            let links =
                Dict.getForce bound_links un <|
                fun _ -> DSet.ofList [typeref]
            in
            let _ = if not <| DSet.contains links typeref
                    then DSet.add links typeref
            in t

      in
    let rec prune : t -> t =
        function
        | TVar i as a ->
            begin
                match DArray.ith tenv i with
                | TVar i' when i' = i -> a
                | t -> link i <| prune t
            end
        | a -> generic_transform prune a
      in

    // check if any unsolved type variables
    let rec prune_with_var_check : (int -> 'a) -> t -> t =
        fun f a ->
        match match a with
              | TVar i ->
                begin
                    match DArray.ith tenv i with
                    | TVar i' when i' = i -> a
                    | t -> link i <| prune t
                end
              | _ ->
                generic_trans_ctx prune_with_var_check f a
            with
        | TVar v as a -> ignore(f v); a
        | a -> a
      in
    let instantiate =
        function
        | TForall(ns, t) ->
            let freshmap =
              Map.ofList <|
                List.map (fun x -> TBound x, new_tvar()) ns
            in substitute freshmap t
        | a -> a
      in
    let rec unifyOrder : t -> t -> bool
      = fun lhs rhs ->
        let lhs = prune lhs in
        let rhs = prune rhs in
        if lhs = rhs then true
        else
        // printfn "%O ~ %O" lhs rhs;
        match lhs, rhs with
        | TVar i, b
        | b, TVar i ->
          if occur_in i b then
              raise <| RecursiveType "a ~ a -> b"
          else let _ = link i b in true
        | _, TForall _ ->
          unifyOrder lhs <| instantiate rhs
        | TForall (_, lhs), _ -> unifyOrder lhs rhs
        | TImplicit lhs, rhs
        | lhs, TImplicit rhs ->
          unifyOrder lhs rhs
        | TArrow(a1, r1), TArrow(a2, r2) ->
          unifyOrder a2 a1 &&
          unifyOrder r1 r2
        | TApp(f1, a1), TApp(f2, a2) ->
          unifyOrder f1 f2 &&
          unifyOrder a1 a2
        | TTup xs1, TTup xs2 ->
          List.forall2 unifyOrder xs1 xs2
        | _ -> false
      in
    let rec unifyInsts : t -> t -> bool
      = fun lhs rhs ->
        let lhs = prune lhs in
        let rhs = prune rhs in
        if lhs = rhs then true
        else
        // printfn "%O ~ %O" lhs rhs;
        match lhs, rhs with
        | TForall(_, lhs), _ ->
          unifyInsts lhs rhs
        | TVar i, b
        | b, TVar i ->
          if occur_in i b then
              raise <| RecursiveType "a ~ a -> b"
          else let _ = link i b in true
        | _, TForall(_, _) ->
          unifyInsts lhs <| instantiate rhs

        | TImplicit lhs, rhs
        | lhs, TImplicit rhs ->
          unifyInsts lhs rhs
        | TArrow(a1, r1), TArrow(a2, r2) ->
          unifyInsts a2 a1 &&
          unifyInsts r1 r2
        | TApp(f1, a1), TApp(f2, a2) ->
          unifyInsts f1 f2 &&
          unifyInsts a1 a2
        | TTup xs1, TTup xs2 ->
          List.forall2 unifyInsts xs1 xs2
        | _ -> false
      in
    let rec unify : t -> t -> bool =
      fun lhs rhs ->
      let lhs = prune lhs in
      let rhs = prune rhs in
      if lhs = rhs then true
      else
      match lhs, rhs with
      | TForall(ns1, p1), TForall(ns2, p2) ->
        let n1, n2 = List.length ns1, List.length ns2 in
        if n1 <> n2 then false
        else
        let subst1 =
          Map.ofList <|
          List.map (fun n -> n, new_tvar()) ns1
          in
        let generic = p2 in
        if not <| unify (fresh subst1 p1) generic then false
        else
        let generic = prune generic in
        let allValidBounds = Set.ofList <| List.map (fun x -> TBound x) ns2
        (* forall a. a -> 'v ~ forall b. b -> b
           we firstly solve: 'tvar -> 'v ~ b -> b
           then: 'tvar ~ b ~'v
           then:  as we know 'tvar is from a,
           hence: **b** is mapped to **a** in lhs type,
           we get: lhs = forall a. a -> a
         *)
        in
        let rec getLHSBounds rhsBoundsToLHS =
          function
          | [] -> Some rhsBoundsToLHS
          | (k, v) :: tail ->
            let v = prune v in
            if Set.contains v allValidBounds
               || Map.containsKey v rhsBoundsToLHS
            then None
            else
            let rhsBoundsToLHS =
              Map.add v (TBound k) rhsBoundsToLHS
            in getLHSBounds rhsBoundsToLHS tail
        in
        (match getLHSBounds Map.empty
               <| Map.toList subst1
          with
        | None -> false
        | Some lhsBounds ->
        let backmap1 = ref [] in
        let backmap2 = ref [] in
        let _ = List.foreach ns2 <| fun un ->
            unlink un <| fun i ->
              begin
                backmap1 := (TVar i, TBound un) :: !backmap1;
                backmap2 := (TVar i, Map.find (TBound un) lhsBounds) :: !backmap2;
                ()
              end
          in
        let backmap1, backmap2 =
          Map.ofList !backmap1, Map.ofList !backmap2
          in
        let p1, p2 = prune p1, prune p2 in
        unify (substitute backmap2 p2) p2 &&
        unify (substitute backmap1 p1) p1)
      | TVar i, b
      | b, TVar i ->
        if occur_in i b then
            raise <| RecursiveType "a ~ a -> b"
        else ignore(link i b); true
      | TArrow(a1, r1), TArrow(a2, r2)
      | TApp(a1, r1), TApp(a2, r2) ->
        unify a1 a2 && unify r1 r2
      | TTup xs1, TTup xs2 ->
        List.forall2 unify xs1 xs2
      | _ -> false
      in
    let rec unifyBI : t -> t -> (t -> t -> unit) -> bool
      = fun lhs rhs f ->
        let lhs = prune lhs in
        let rhs = prune rhs in
        if lhs = rhs then true
        else
        // printfn "%O ~ %O" lhs rhs;
        match lhs, rhs with
        | TVar _, _ -> f lhs rhs; true
        | _, TVar _ -> f lhs rhs; true
        | _, TForall _ ->
          unifyBI lhs <| instantiate rhs <| f
        | TForall (_, lhs), _ -> unifyBI lhs rhs f
        | TImplicit lhs, rhs
        | lhs, TImplicit rhs ->
          unifyBI lhs rhs f
        | TArrow(a1, r1), TArrow(a2, r2) ->
          unifyBI a2 a1 f &&
          unifyBI r1 r2 f
        | TApp(f1, a1), TApp(f2, a2) ->
          unifyBI f1 f2 f &&
          unifyBI a1 a2 f
        | TTup xs1, TTup xs2 ->
          List.forall2 (fun a b -> unifyBI a b f) xs1 xs2
        | _ -> false
      in
    { tenv = tenv
    ; unify = unify
    ; unifyInsts = unifyInsts
    ; unifyOrder = unifyOrder
    ; unifyBI = unifyBI
    ; new_tvar = new_tvar
    ; prune = prune
    ; prune_with_var_check = prune_with_var_check
    }


// a ~ (b, c)
// a ~ (a, a)
// b ~ a
// c ~ a
// c ~ a


let isVar = function TVar _ -> true | _ -> false

type InEq = { le : t darray; ge : t darray }

type solverstate =
  { solveInEq : t -> t -> bool
  ; solveInEqs: (t * t) array -> bool
  }
let rec less_than : t -> t -> bool =
    fun lhs rhs ->
    let small_tc = mk_tcstate(darray())
    let subst_table = dict()
    let rec subst =
      function
      | TVar i ->
        match Dict.tryFind subst_table i with
        | Some a -> a
        | None ->
          let a = small_tc.new_tvar()
          in subst_table.[i] <- a; a

      | root -> generic_transform subst root
    in
    let lhs = subst lhs
    let rhs = subst rhs
    let solver = mk_solver_state small_tc small_tc
    solver.solveInEq lhs rhs

and mk_solver_state = fun ({prune=prune; unify=unify; unifyBI=unifyBI; unifyInsts=unifyInsts} as tc) ->
  // helpers
  let check_unify lhs rhs =
      match unify lhs rhs with
      | false -> failwithf "unify %O ~ %O failed" (prune lhs) (prune rhs)
      | _ -> ()
  let pushForce (d: (_, _) dict) i a =
      let xs = Dict.getForce d i <| fun _ -> darray()
      in DArray.push xs a

  let (|FoundNonEmpty|Otherwise|) (y, x) =
    match Dict.tryFind y x with
    | None -> Otherwise
    | Some xs when Seq.isEmpty xs -> Otherwise
    | Some xs -> FoundNonEmpty xs

  // fixpoint normalizer
  let rec normalize xs =
    let xs' = dset() in
    let rec loop =
      function
      | (lhs, rhs)::tl ->
        let it = unifyBI lhs rhs <| fun lhs rhs -> DSet.add xs' (lhs, rhs)
        if it then loop tl else None
      | [] ->
        let xs = [| for (lhs, rhs) in xs' -> prune lhs, prune rhs |]
        if Array.forall
          (function (TVar _, _) | (_, TVar _) -> true | _ -> false)
          xs
        then  Some xs
        else DSet.clear xs'; normalize xs
    in loop xs
  // type order
  let rec typemax (xs : _ darray) =
    let rec recmax maxi i =
      if i = -1 then maxi
      else if isVar xs.[i] then recmax maxi (i - 1)
      else if less_than xs.[maxi] xs.[i] then recmax i (i-1)
      else recmax maxi (i - 1)
    match Seq.tryFindIndex (function TVar _ -> false | _ -> true) xs with
    | Some i -> recmax i <| DArray.len xs - 1
    | None -> 0

  and typemin (xs : _ darray) =
    let rec recmin mi i =
      if i = -1 then mi
      else if isVar xs.[i] then recmin mi (i - 1)
      else if less_than xs.[i] xs.[mi] then recmin i (i-1)
      else recmin mi (i - 1)
    match Seq.tryFindIndex (function TVar _ -> false | _ -> true) xs with
    | Some i -> recmin i <| DArray.len xs - 1
    | None -> 0

  and solveInEq : t -> t -> bool =
    fun lhs rhs ->
      let xs' = dset()
      (tc.unifyBI lhs rhs <| fun lhs rhs -> DSet.add xs' (lhs, rhs))
      && solveInEqs xs'

  and solveInEqs: (t * t) array -> bool = fun xs ->
    match normalize xs with
    | None -> false
    | Some [||] -> true
    | Some [|lhs, rhs|] -> unify lhs rhs
    | Some xs ->
    let rels = dict()
    let wip_vars = dset()
    for (lhs, rhs) in xs do
      match lhs, rhs with
      | TVar i, _ ->
        let {le=le} = Dict.getForce rels i <| fun _ -> { le = darray(); ge = darray() }
        in DArray.push le rhs
      | _, TVar i ->
        let {ge=ge} = Dict.getForce rels i <| fun _ -> { le = darray(); ge = darray() }
        in DArray.push ge lhs
      | _ -> failwith "impossible"
    done
    let rec solveI i =
      if DSet.contains wip_vars i then
        prune <| TVar i
      else
      DSet.add wip_vars i
      match (le_rels, i), (ge_rels, i) with
      | Otherwise, Otherwise -> prune <| TVar i
      | FoundNonEmpty les, Otherwise -> solve_le les i
      | Otherwise, FoundNonEmpty ges -> solve_ge ges i
      | FoundNonEmpty les, FoundNonEmpty ges ->
        ignore (solve_le les i); solve_ge ges i
    and solve_ge ges i =
      let ges = solve_seq ges
      let me = TVar i
      let ti = typemax ges
      solveInEq (ges.[ti]) me
      for k = 0 to ti-1 do
        solveInEq ges.[k] me
      done
      for k = ti+1 to DArray.len ges - 1 do
        solveInEq ges.[k] me
      done
      prune me
    and solve_le les i =
      let les = solve_seq les
      let me = TVar i
      let ti = typemin les
      solveInEq me (les.[ti])
      for k = 0 to ti-1 do
        solveInEq me les.[k]
      done
      for k = ti+1 to DArray.len les - 1 do
        solveInEq me les.[k]
      done
      prune me
    and solve_seq es =
      let es = Seq.map prune es
      let es =
        let rec recurse =
          function
          | TVar j -> prune <| solveI j
          | a -> generic_transform recurse a
        in Seq.map recurse es
      let res = darray()
      for e in es do
        DArray.push res (prune e)
      done
      res


//////
  let xs = Array.ofSeq <| normalize xs
  match xs with
  | [||] -> ()
  | [|lhs, rhs|] -> check_unify lhs rhs
  | _ ->
  let le_rels = dict()
  let ge_rels = dict()
  let rel_vars = dset()
  let wip_vars = dset()
  for (lhs, rhs) in xs do
      match prune lhs, prune rhs with
      | TVar i, _ -> DSet.add rel_vars i; pushForce le_rels i rhs
      | _, TVar i -> DSet.add rel_vars i; pushForce ge_rels i lhs
      | _ -> failwith "impossible"
  done
  let typemax (xs : _ darray) =
    let rec recmax maxi i =
      if i = -1 then maxi
      else if isVar xs.[i] then recmax maxi (i - 1)
      else if less_than xs.[maxi] xs.[i] then recmax i (i-1)
      else recmax maxi (i - 1)
    match Seq.tryFindIndex (function TVar _ -> false | _ -> true) xs with
    | Some i -> recmax i <| DArray.len xs - 1
    | None -> 0
  let typemin (xs : _ darray) =
    let rec recmin mi i =
      if i = -1 then mi
      else if isVar xs.[i] then recmin mi (i - 1)
      else if less_than xs.[i] xs.[mi] then recmin i (i-1)
      else recmin mi (i - 1)
    match Seq.tryFindIndex (function TVar _ -> false | _ -> true) xs with
    | Some i -> recmin i <| DArray.len xs - 1
    | None -> 0
  let (|FoundNonEmpty|Otherwise|) (y, x) =
      match Dict.tryFind y x with
      | None -> Otherwise
      | Some xs when Seq.isEmpty xs -> Otherwise
      | Some xs -> FoundNonEmpty xs


and solveInEqs : tcstate -> (t * t) dset -> unit =
  fun ({prune=prune; unifyBI=unifyBI; unifyInsts=unifyInsts} as tc) xs ->
    let check = function false -> failwith "unify failed" | _ -> ()
    let check2 lhs rhs =
      function
      | false -> failwithf "unify %O ~ %O failed" (prune lhs) (prune rhs)
      | _ -> ()
    let rec recurse xs =
      let xs' = dset() in
      for (lhs, rhs) in xs do
        if unifyBI lhs rhs <| fun lhs rhs -> DSet.add xs' (lhs, rhs)
        then ()
        else failwith "unification error"
      done
      let xs = Seq.map (fun (lhs, rhs) -> prune lhs, prune rhs) xs'
      if Seq.forall
         (function (TVar _, _) | (_, TVar _) -> true | _ -> false)
         xs
      then xs
      else recurse xs
    let xs = recurse xs
    printfn "====<<<<<<<<<<<<<<<<<<"
    for (lhs, rhs) in xs do
      printfn "%O <= %O" (prune lhs) (prune rhs)
    done
    match Seq.length xs with
    | 0 -> ()
    | 1 ->
      match Seq.last xs with
      | (TVar _ as lhs, (_ as rhs)) -> unifyInsts lhs rhs |> check
      | ((_ as lhs), (TVar _ as rhs)) -> unifyInsts lhs rhs |> check
      | _ -> failwith ""
    | _ ->
    let le_rels = dict()
    let ge_rels = dict()
    let rel_vars = dset()
    let wip_vars = dset()
    let pushForce (d: (_, _) dict) i a =
      let xs = Dict.getForce d i <| fun _ ->
        darray()
      DArray.push xs a

    for (lhs, rhs) in xs do
      match prune lhs, prune rhs with
      | TVar i, _ -> DSet.add rel_vars i; pushForce le_rels i rhs
      | _, TVar i -> DSet.add rel_vars i; pushForce ge_rels i lhs
      | _ -> failwith "impossible"
    done

    let isVar = function TVar _ -> true | _ -> false
    let typemax (xs : _ darray) =
        let rec recmax maxi i =
          if i = -1 then maxi
          else if isVar xs.[i] then recmax maxi (i - 1)
          else if less_than xs.[maxi] xs.[i] then recmax i (i-1)
          else recmax maxi (i - 1)
        match Seq.tryFindIndex (function TVar _ -> false | _ -> true) xs with
        | Some i -> recmax i <| DArray.len xs - 1
        | None -> 0
    let typemin (xs : _ darray) =
        let rec recmin mi i =
          if i = -1 then mi
          else if isVar xs.[i] then recmin mi (i - 1)
          else if less_than xs.[i] xs.[mi] then recmin i (i-1)
          else recmin mi (i - 1)
        match Seq.tryFindIndex (function TVar _ -> false | _ -> true) xs with
        | Some i -> recmin i <| DArray.len xs - 1
        | None -> 0
    let (|FoundNonEmpty|Otherwise|) (y, x) =
      match Dict.tryFind y x with
      | None -> Otherwise
      | Some xs when Seq.isEmpty xs -> Otherwise
      | Some xs -> FoundNonEmpty xs

    let solve_inst lhs rhs =
      let xs' = dset()
      if unifyBI lhs rhs <| fun lhs rhs -> DSet.add xs' (lhs, rhs)
      then
        solveInEqs tc xs'
      else check2 lhs rhs false

    let rec solveI i =
      if DSet.contains wip_vars i then
        prune <| TVar i
      else
      DSet.add wip_vars i
      match (le_rels, i), (ge_rels, i) with
      | Otherwise, Otherwise -> prune <| TVar i
      | FoundNonEmpty les, Otherwise -> solve_le les i
      | Otherwise, FoundNonEmpty ges -> solve_ge ges i
      | FoundNonEmpty les, FoundNonEmpty ges ->
        ignore (solve_le les i); solve_ge ges i
    and solve_ge ges i =
      let ges = solve_seq ges
      let me = TVar i
      let ti = typemax ges
      solve_inst (ges.[ti]) me
      for k = 0 to ti-1 do
        solve_inst ges.[k] me
      done
      for k = ti+1 to DArray.len ges - 1 do
        solve_inst ges.[k] me
      done
      prune me
    and solve_le les i =
      let les = solve_seq les
      printfn "========typevar: %d========" i
      for o in les do
        printfn "<= %O" <| prune o
      done
      let me = TVar i
      let ti = typemin les
      printfn "min: %O" <| prune les.[ti]
      solve_inst me (les.[ti])
      for k = 0 to ti-1 do
        solve_inst me les.[k]
      done
      for k = ti+1 to DArray.len les - 1 do
        solve_inst me les.[k]
      done
      prune me
    and solve_seq es =
      let es = Seq.map prune es
      let es =
        let rec recurse =
          function
          | TVar j -> prune <| solveI j
          | a -> generic_transform recurse a
        in Seq.map recurse es
      let res = darray()
      for e in es do
        DArray.push res (prune e)
        // match prune e with
        // |  TVar j when i = j -> ()
        // | e -> DArray.push res e
      done
      res
    for i in rel_vars do
      ignore (solveI i)
    done
