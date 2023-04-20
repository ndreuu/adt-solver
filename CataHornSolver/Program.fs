open System.IO
open Microsoft.FSharp.Core
open ProofBased.Solver

module Program =

  [<EntryPoint>]
  let main args =
    match args with
    | [| path; dbgPath |] ->

      let d = Path.Join [|dbgPath; "dbg" |]
      if Directory.Exists d then Directory.Delete (d, true)
      Directory.CreateDirectory d |> ignore
      
      run path (Some d) |> printfn "%O"
      0
    | [| path |] ->
      run path None |> printfn "%O"
      0
    | _ -> 
      1
