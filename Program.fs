// Learn more about F# at http://fsharp.org

open System
open Infer
open AST
open OpCPS
open Core
open Mlib


let t = TVar
let (^->) a b = TArrow(a, b)
let (^@) a b = TApp(a, b)
let (^.) xs t = TForall(xs, t)



module Predef =
    let t = Nom
    let (^->) a b = Fun(a, b)
    let (^@) a b = App(a, b)
    let (^.) xs t = Forall(xs, t)
    let int = T <| t"int"
    let inc = t"int" ^-> t"int"
    let list = t"list"
    let incs = list  ^@ inc
    let id =
        let a = un("a") in
        [a] ^. (Bou a) ^-> (Bou a)
    let ids = list ^@ id
        (* [forall a. a -> a] *)
    let cons =
        (* forall a. a -> [a] -> [a] *)
        let a = un("a") in
        [a] ^. Bou a ^-> (list ^@ Bou a) ^-> (list ^@ Bou a)
    let concat =
        (* forall a. [a] -> [a] -> [a] *)
        let a = un("a") in
        [a] ^. (list ^@ Bou a) ^-> (list ^@ Bou a) ^-> (list ^@ Bou a)
    let choose =
        let a = un("a") in
        [a] ^. Bou a ^-> Bou a ^-> Bou a

[<EntryPoint>]
let main argv =
    let tyEnv = Map.ofList [
        "int", Predef.int;
        "list", Predef.list;
        "inc", Predef.inc;
        "incs", Predef.incs;
        "id", Predef.id;
        "ids", Predef.ids;
        "++", Predef.concat;
        ":", Predef.cons;
        "choose", Predef.choose
    ]
    let f = ["a"] ^. t"a" ^-> t"a"

    let t1 = infer_term tyEnv @@
                ELet(Some f, "id", ELam("x", EVar("x")), EVar("id"))
    (* inc:ids *)
    let t2 = infer_term tyEnv @@
                EApp ( EApp(EVar(":"),  EVar("inc")) , EVar("ids") )
    (* id:incs *)
    let t3 = infer_term tyEnv @@
                EApp ( EApp(EVar(":"),  EVar("id")) , EVar("incs") )

    (* id:ids *)
    let t4 = infer_term tyEnv @@
                EApp
                  ( EApp(EVar(":"),  EVar("id"))
                  , EVar("ids")
                  )

    (* ids ++ ids ++ incs ++ ids ++ ids *)
    let t5 = infer_term tyEnv
            @@ let xs = [EVar("ids"); EVar("ids"); EVar("incs"); EVar("ids"); EVar("ids")] in
               List.foldBack (fun a b -> EApp(EApp(EVar("++"), a), b)) xs (EVar "ids")

    (* choose id *)
    let t6 = infer_term tyEnv (EApp((EVar "choose"), EVar("id")))

    (* let x = choose id in x inc *)
    let t6 = infer_term tyEnv
            @@ EApp(
                EQuery(EApp((EVar "choose"), EVar("id"))), EVar("inc"))

    printfn "start solving"
    printfn "can solve?: %b" <| Bi.solveInEqs !Infer.ineqs
    for t in [
               t1;
               t2;
               t3;
               t4;
               t5;
               t6
             ] do
        printfn "%O" <| prune t
    done

    printfn "queried expression type:"
    for t in !Infer.queries do
        printfn "%O" <| prune t
    done
    0 // return an integer exit code

