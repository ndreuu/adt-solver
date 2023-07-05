open System.IO
open System.Text.RegularExpressions
open ProofBased.Solver

module Program =

  [<EntryPoint>]
  let main = function
    | [| path; dbgPath; timeLimit |] ->
      let d = Path.Join [| dbgPath; "dbg" |]
      if Directory.Exists d then Directory.Delete (d, true)
      Directory.CreateDirectory d |> ignore
      let v, st, curDuration = run path (Some d) (Some timeLimit)
      printfn $"{v}"
      printfn $"{curDuration}"
      for s in st do printfn $"{s}"
     
      
      0
    | [| path; dbgPath |] ->
      let d = Path.Join [| dbgPath; "dbg" |]
      if Directory.Exists d then Directory.Delete (d, true)
      Directory.CreateDirectory d |> ignore
      let v, st, curDuration = run path (Some d) None
      printfn $"{v}"
      printfn $"{curDuration}"
      for s in st do printfn $"{s}"
      
      
      // printfn $"{r}"
      // for d in ds do printfn $"{d}"
      0
    | [| path |] ->
      printfn $"{run path None None}"
      0
    | _ -> 
      1
