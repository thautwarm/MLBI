module Rt
open Mlib

let currentRuntimeId =
    sprintf "%O%d"
    <| System.Guid.NewGuid()
    <| timeNs()

let refCnt = ref 0