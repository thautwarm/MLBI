module Log
open Core
open Mlib

let logConstraints cs =
     printfn "==========="
     flip List.iter cs <|
       function
       | LE(a, b) ->
            printfn "%O = %O <= %O" (Var a) (prune <| Var a) (prune b)
       | GE(a, b) ->
            printfn "%O = %O >= %O" (Var a) (prune <| Var a) (prune b)