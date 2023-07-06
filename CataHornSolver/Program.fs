open System.IO
open System.Text.RegularExpressions
open NUnit.Framework
open ProofBased
open ProofBased.Solver

module Program =

  [<EntryPoint>]
  // let main _ = 
      // let path = Path.Join(TestContext.CurrentContext.TestDirectory, @"Tests/Source/TIP-no-NAT")
      // let path = @"./Tests/Source/TIP-no-NAT"
      // printfn $"{Directory.Exists(path)}"
      // let dir = DirectoryInfo(path);
      // let files = dir.GetFiles("*.smt2"); 
      // for file in files do
      //   let v, st, curDuration = run file.DirectoryName None None
      //   let content = Utils.join "\n" (List.map (fun (n, t) -> $"{n} {t}") st)  
      //   File.WriteAllText("./out.txt", $"{v}\n{curDuration}\n{content}")
      // 0

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
      0
    | [| path |] ->
      
      // let path = Path.Join(TestContext.CurrentContext.TestDirectory, @"Tests/Source/TIP-no-NAT")
      // let path = @"./Tests/Source/TIP-no-NAT"
      // printfn $"{Directory.Exists(path)}"
      // let dir = DirectoryInfo(path);
      // let files = dir.GetFiles("*.smt2"); 
      // for file in files do
      //   let v, st, curDuration = run file.DirectoryName None None
      //   let content = Utils.join "\n" (List.map (fun (n, t) -> $"{n} {t}") st)  
      //   File.WriteAllText("./out.txt", $"{v}\n{curDuration}\n{content}")
      let testName = Path.GetFileName path
      let result, st, curDurName = run path None None
      let durations = Utils.join "\n" (List.map (fun (n, t) -> $"\t{n} {t}") st)  
      let content = $"{testName} {result}\n\t{curDurName}\n{durations}"
      File.WriteAllText("./out.txt", content")
      printfn $"{content}"
      0
    | _ -> 
      1
