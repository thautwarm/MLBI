#indent "off"
module rec Core

open Rt
open FSharp.Compatibility.OCaml
open Mlib


type un =
    { runtimeId: string
    ; refId : int
    ; name: string
    }
    with override this.ToString() = Core.show_un this
    end

(* unique name *)
let un s =
    { refId = incret refCnt
    ; runtimeId = currentRuntimeId
    ; name = s
    }

type tvar = t ptr
and t =
| Var of tvar
| App of t * t
| Fun of t * t
| Bou of un
| Nom of string
| Tup of t list
| Forall of un list * t
    with override this.ToString() = Core.show_t this
    end


type inequation =
| LE of tvar * t
| GE of tvar * t
    with override this.ToString() =
        let prune = Core.prune in
        match this with
        | LE(a, b) ->
            sprintf "%O <= %O" <| Var a <| (prune b)
        | GE(a, b) ->
            sprintf "%O >= %O" <| Var a <| (prune b)
    end

let verbose_printing = ref false
let show_un { runtimeId = ri
            ; refId = fi
            ; name = name
            }
    = if !verbose_printing then
        sprintf "%s@(%s-%u)"  name ri fi
      else name

let need_parens : t -> bool
    = function
      | Forall(_, _)
      | App(_, _)
      | Fun(_, _) -> true
      | _ -> false

let transform self root =
    match root with
    | Bou _ | Nom _  | Var Null -> root
    | Var (Contents t) -> self t
    | App(a, b) -> App(self a, self b)
    | Fun(a, b) -> Fun(self a, self b)
    | Forall(uns, t) -> Forall(uns, self t)
    | Tup xs -> Tup <| List.map self xs


let rec fix = fun f x ->
    f (fix f) x

let prune = fix transform

let naming = Hashtbl.create 256
let namingCnt = ref 0

let show_t x =
  let rec show_t =
    fun x ->
    let nest t =
      let s = show_t t in
      if need_parens t then
        "(" ^ s  ^ ")"
      else s
    in
    let (!) = show_t in
    match x with
    | Var a ->
        begin match Hashtbl.find_opt naming a with
        | Some v -> v
        | _ ->
            let v = sprintf "'%d" (incret namingCnt)
            in Hashtbl.add naming a <| v; v
        end
    | Nom s -> s
    | Bou un -> show_un un
    | App(f, a) ->
      !f ^ " " ^ nest a
    | Fun(a, r) ->
      nest a ^ " -> " ^ !r
    | Tup xs -> "(" ^ String.concat ", " (List.map show_t xs) ^ ")"
    | Forall(ns, t)  ->
      "forall " ^ String.concat " " (List.map show_un ns)
      ^ "." ^ !t
  in show_t x