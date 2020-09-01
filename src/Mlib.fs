module Mlib

open FSharp.Compatibility.OCaml
let (@@) f x = f x
let (^) : string -> string -> string = (+)
let flip f x y = f y x

let constant x = fun _ -> x

type 'a ptr() = class
    let mutable _contents :' a option = None
    member _.contents with get() = _contents
    member _.set v = _contents <- Some v
end

let (|Contents|Null|) (x: 'a ptr) =
    match x.contents with
    | Some v -> Contents (v: 'a)
    | None -> Null

let _z = ptr()
let _ = _z.set 2

let _ = match _z with
        | Contents a -> printfn "%d" a
        | Null -> printfn "no"

let incret : int ref -> int =
    fun x ->
    let i = x.contents in
    x.contents <- i + 1;
    i

type ('a, 'b) Either =
    | Either of 'a
    | Otherwise of 'b


let readFile = System.IO.File.ReadAllText

let writeFile f contents =
    let dirname = System.IO.Path.GetDirectoryName(f: string)

    if System.String.IsNullOrEmpty dirname
       || System.String.IsNullOrWhiteSpace dirname
    then ()
    else ignore <| System.IO.Directory.CreateDirectory(dirname)

    System.IO.File.WriteAllText(f, contents)

let joinPath a b = System.IO.Path.Join([|a; b|])

(* get nanoseconds *)
let timeNs () : int64
    = System.DateTime.UtcNow.Ticks

let intern : string -> string
    = System.String.Intern

let (|KV|) (x : System.Collections.Generic.KeyValuePair<'k, 'v>) =
    KV(x.Key, x.Value)

module Map =
    let mem = Map.containsKey
    let letSeq m1 m2 =
        Map.foldBack Map.add (Map.ofSeq m2) m1

module List =
    let assoc_opt = List.try_assoc

module Hashtbl =
    let find_opt = Hashtbl.tryfind

