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
    let type_of_inc = t"int" ^-> t"int"
    let list = t"list"
    let type_of_incs = list  ^@ type_of_inc
    let type_of_id =
        let a = un("a") in
        [a] ^. (Bou a) ^-> (Bou a)
    let type_of_ids = list ^@ type_of_id
    let type_of_cons =
        let a = un("a") in
        [a] ^. Bou a ^-> (list ^@ Bou a) ^-> (list ^@ Bou a)
    let type_of_concat =
        let a = un("a") in
        [a] ^. (list ^@ Bou a) ^-> (list ^@ Bou a) ^-> (list ^@ Bou a)


[<EntryPoint>]
let main argv =
    let tyEnv = Map.ofList [
        "int", Predef.int;
        "list", Predef.list;
        "inc", Predef.type_of_inc;
        "incs", Predef.type_of_incs;
        "id", Predef.type_of_id;
        "ids", Predef.type_of_ids;
        "++", Predef.type_of_concat;
        ":", Predef.type_of_cons;
    ]
    let f = ["a"] ^. t"a" ^-> t"a"
    let e1 = ELet(Some f, "id", ELam("x", EVar("x")), EVar("id"))

    let e2 =
        EApp
          ( EApp(EVar(":"),  EVar("inc"))
          , EVar("ids")
          )

    let e3 =
        EApp
          ( EApp(EVar(":"),  EVar("id"))
          , EVar("incs")
          )

    let e4 =
        EApp
          ( EApp(EVar(":"),  EVar("id"))
          , EVar("ids")
          )

    let e5 =
        let xs = [EVar("ids"); EVar("ids"); EVar("incs"); EVar("ids")]
        in
        List.foldBack (fun a b -> EApp(EApp(EVar("++"), a), b)) xs (EVar "ids")
    let t1 = infer_term tyEnv e1
    let t2 = infer_term tyEnv e2
    let t3 = infer_term tyEnv e3
    let t4 = infer_term tyEnv e4
    let t5 = infer_term tyEnv e5
    printfn "start solving"
    printfn "can solve? %b" <| Bi.solveInEqs !Infer.ineqs
    for t in [
               t1;
               t2;
               t3;
               t4;
               t5
             ] do
        printfn "%O" <| prune t
    done
    0 // return an integer exit code

