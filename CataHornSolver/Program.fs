open System.IO
open System.Text.RegularExpressions
open NUnit.Framework
open ProofBased
open ProofBased.Solver

module Program =

  [<EntryPoint>]
  let main _ = 
      // let files = Path.Join(TestContext.CurrentContext.TestDirectory, "Tests/Source/adt_lia")
      // printfn $"{Directory.Exists(files)}"
      //
      // let  d = DirectoryInfo(files);
      // let a = d .GetFiles("*.smt2"); //Getting Text files
      // printfn $"{a}"
      //
      
      let file = Path.Join(TestContext.CurrentContext.TestDirectory, "Tests/Source/racer.horn.smt2")
      printfn $"{File.Exists(file)}"
      let v, st, curDuration = run file None None
      let a = Utils.join "\n" (List.map (fun (n, t) -> $"{n} {t}") st)  
      File.WriteAllText("./out.txt", $"{v}\n{curDuration}\n{a}")
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
