open System.IO
open System.Text.RegularExpressions
open NUnit.Framework
open ProofBased.Solver

module Program =

  [<EntryPoint>]
  let main _ = 
      let file = Path.Join(TestContext.CurrentContext.TestDirectory, "Tests/Source/racer.horn.smt2")
      let v, st, curDuration = run file None None
      printfn $"{v}"
      printfn $"{curDuration}"
      for s in st do printfn $"{s}"
      0

  // let main = function
  //   | [| path; dbgPath; timeLimit |] ->
  //     let d = Path.Join [| dbgPath; "dbg" |]
  //     if Directory.Exists d then Directory.Delete (d, true)
  //     Directory.CreateDirectory d |> ignore
  //     let v, st, curDuration = run path (Some d) (Some timeLimit)
  //     printfn $"{v}"
  //     printfn $"{curDuration}"
  //     for s in st do printfn $"{s}"
  //     0
  //   | [| path; dbgPath |] ->
  //     let d = Path.Join [| dbgPath; "dbg" |]
  //     if Directory.Exists d then Directory.Delete (d, true)
  //     Directory.CreateDirectory d |> ignore
  //     let v, st, curDuration = run path (Some d) None
  //     printfn $"{v}"
  //     printfn $"{curDuration}"
  //     for s in st do printfn $"{s}"
  //     0
  //   | [| path |] ->
  //     printfn $"{run path None None}"
  //     0
  //   | _ -> 
  //     1
