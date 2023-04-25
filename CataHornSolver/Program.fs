open System.IO
open ProofBased.Solver

module Program =

  [<EntryPoint>]
  let main = function
    | [| path; dbgPath |] ->
      let d = Path.Join [| dbgPath; "dbg" |]
      if Directory.Exists d then Directory.Delete (d, true)
      Directory.CreateDirectory d |> ignore
      
      printfn $"{run path (Some d)}"
      0
    | [| path |] ->
      printfn $"{run path None}"
      0
    | _ -> 
      1
