open System
open System.IO
open System.Text.RegularExpressions
open CataHornSolver
open Microsoft.VisualStudio.TestPlatform.CoreUtilities.Helpers
open Microsoft.VisualStudio.TestPlatform.Utilities
open NUnit.Framework
open ProofBased
open ProofBased.Solver
open SMTLIB2


module Program =
  // let mutable FileTimes = false
  let withRedlog = true

  let runWithCVC file fileTimes =
    run (10, 30, 10, 10) file None None z3Process.Instances.learner.CVC (not <| withRedlog) fileTimes

  let runWithCVC' file fileTimes =
    try
      Some (runWithCVC file fileTimes)
    with e ->
      None

  let runWithCVC2 file fileTimes =
    run (2, 30, 10, 10) file None None z3Process.Instances.learner.CVC (not <| withRedlog) fileTimes


  let runWithCVC2' file fileTimes =
    try
      Some (runWithCVC2 file fileTimes)
    with e ->
      None

  let runWithCVCRedlog file fileTimes =
    run (10, 30, 10, 2) file None None z3Process.Instances.learner.CVC withRedlog fileTimes

  let runWithCVCRedlog' file fileTimes =
    try
      Some (runWithCVCRedlog file fileTimes)
    with e ->
      None

  let runWithZ3 file fileTimes =
    run (2, 20, 10, 10) file None None z3Process.Instances.learner.CVC (not <| withRedlog) fileTimes

  let runWithZ3' file fileTimes =
    try
      Some (runWithZ3 file fileTimes)
    with e ->
      None

  let runWithZ3Redlog file fileTimes =
    run (2, 20, 10, 5) file None None z3Process.Instances.learner.CVC withRedlog fileTimes

  let runWithZ3Redlog' file fileTimes =
    try
      Some (runWithZ3Redlog file fileTimes)
    with e ->
      None
  
  let modes =
    let solver = function
      | ArgumentsParser.CVC -> z3Process.Instances.learner.CVC
      | ArgumentsParser.Z3 -> z3Process.Instances.learner.Z3
    function
    | Result.Ok (file, (fTimes, modes)) ->
      Result.Ok
        (List.map (function
          | s, (tLearner, tTeacher, tChecker, Some tRedlog) ->
            match fTimes with
              | Some fTimes ->
                File.WriteAllText ($"{fTimes}-{s}-rd", "");
                lazy run (tLearner, tTeacher, tChecker, tRedlog) file None None (solver s) withRedlog (Some $"{fTimes}-{s}-rd")
              | None ->
                lazy run (tLearner, tTeacher, tChecker, tRedlog) file None None (solver s) withRedlog None
          | s, (tLearner, tTeacher, tChecker, None) ->
            match fTimes with
            | Some fTimes ->
              File.WriteAllText ($"{fTimes}-{s}", "")
              lazy run (tLearner, tTeacher, tChecker, 0) file None None (solver s) (not withRedlog) (Some $"{fTimes}-{s}")
            | None ->  
              lazy run (tLearner, tTeacher, tChecker, 0) file None None (solver s) (not withRedlog) None)
          modes)
    | Error err -> Error err

  let rec choice asyncs =
    asyncs
    |> Async.Choice
    |> Async.RunSynchronously
    |> function
      | Some x -> x
      | None ->
        printfn "unknown"
        Environment.Exit 0
        failwith ""

  let run (fs: Lazy<(string * string) * (string * int64) list * string> list) =
    match fs with
    | [ f ] ->
      f.Force()
    | _ ->
      List.map (fun (f: Lazy<(string * string) * (string * int64) list * string>) ->
        (async { return try Some (f.Force()) with _ -> None }))
        fs
      |> choice
  
  [<EntryPoint>]
  let main = function
    | args ->
      let file =
        match ArgumentsParser.parse args with
          | Result.Ok (file, _) -> file
          | Error err -> failwith err 
      
      match modes (ArgumentsParser.parse args) with
      | Error err ->
        printfn $"{err}"
        1
      | Result.Ok ok ->
        try
          let (status, result), _, _ = run ok
          
          printfn $"{status}"
          
          if status = "unsat" || status = "sat" then
            let path' = Path.GetTempPath () + Guid.NewGuid().ToString () + ".smt2"
            File.WriteAllText (path', Preprocessing.Parametrized.go <| File.ReadAllText file)
            let p = Parser.Parser false
            let cmds = p.ParseFile path'
            
            if List.contains (originalCommand.Command command.GetModel) cmds ||
               List.contains (originalCommand.Command command.GetProof) cmds then
              printfn $"{result}"
              
            let cmds = Preprocessing.chcFF.notFF cmds
            let cmds =
              if status = "unsat" then
                let containsQ = function
                  | originalCommand.Assert (QuantifierApplication (_, Hence (_, Apply (op, _))))
                  | originalCommand.Assert (Hence (_, Apply (op, _)))
                    when Operation.opName op = "q" -> true
                  | _ -> false
                let rec helper (acc, cmds) =
                  match cmds with
                  | x :: _ when containsQ x ->
                    acc, cmds
                  | x :: xs ->
                    helper (x::acc, xs)
                  | [] -> (acc, [])
                let cmds =
                  if
                    List.filter (function
                      | originalCommand.Assert (QuantifierApplication (_, Hence (_, BoolConst false)))
                      | originalCommand.Assert (Hence (_, BoolConst false)) -> true
                      | _ -> false)
                    cmds
                    |> List.length = 1
                  then
                    cmds
                  else
                    List.choose (function
                      | originalCommand.Assert (QuantifierApplication (q, Hence (b, BoolConst false))) ->
                        Some
                          (originalCommand.Assert
                             (QuantifierApplication
                                (q,
                                 Hence (b, smtExpr.Apply (ElementaryOperation ("q", [], BoolSort), [])))))
                      | originalCommand.Assert (Hence (b, BoolConst false)) ->
                        Some (originalCommand.Assert (Hence (b, smtExpr.Apply (ElementaryOperation ("q", [], BoolSort), []))))
                      | otherwise -> Some otherwise)
                      cmds
                match helper ([], cmds) with
                  | _, [] ->
                    cmds
                  | xs, tl ->
                    // printfn $">>>> cmds"
                    List.rev
                      (originalCommand.Assert
                         (Hence (smtExpr.Apply (ElementaryOperation ("q", [], BoolSort), []), BoolConst false)) ::
                      originalCommand.Command (DeclareFun ("q", [], BoolSort)) ::
                      xs) @ tl 
                        

              else cmds

            // let cmds = Preprocessing.ApproximateBooleans.rwrt cmds
            // let cmds = Preprocessing.Selectors.run cmds
            let cmds = cmds |> List.map toString |> join "\n"
            
            match ArgumentsParser.runParser ArgumentsParser.outputContract args with
            | Result.Ok file ->
              File.WriteAllText ($"{file}", $"{status}\n{cmds}\n{result}")
            | _ ->
              // ()
              File.WriteAllText ($".result", $"{status}\n{cmds}\n{result}")
            

      // printfn "9"
        with e ->
          printfn $"{e.Message}\n{e.StackTrace}"
          printfn $"ERR"

        0
    // | args ->
    //   
    //   try
    //     let (status, result), _, _ =
    //       match
    //         List.ofArray
    //         <| Array.filter
    //           (fun arg -> arg = "-cvc" || arg = "-cvc2" || arg = "-cvcRD" || arg = "-z3" || arg = "-z3RD")
    //           args
    //       with
    //       | [ mode ] ->
    //         Map
    //           [ ("-cvc", runWithCVC)
    //             ("-cvc2", runWithCVC2)
    //             ("-cvcRD", runWithCVCRedlog)
    //             ("-z3", runWithZ3)
    //             ("-z3RD", runWithZ3Redlog) ]
    //         |> Map.find mode
    //         <|| (args[0], args[1])
    //       | _ ->
    //         let modes =
    //           match List.ofArray args with
    //           | modes ->
    //             List.choose
    //               (function
    //               | "-cvc" -> Some (async { return runWithCVC' args[0] $"{args[1]}-runWithCVC" })
    //               | "-cvc2" -> Some (async { return runWithCVC2' args[0] $"{args[1]}-runWithCVC2" })
    //               | "-cvcRD" -> Some (async { return runWithCVCRedlog' args[0] $"{args[1]}-runWithCVCRedlog" })
    //               | "-z3" -> Some (async { return runWithZ3' args[0] $"{args[1]}-runWithZ3" })
    //               | "-z3RD" -> Some (async { return runWithZ3Redlog' args[0] $"{args[1]}-runWithZ3Redlog" })
    //               | _ -> None)
    //               modes
    //
    //         choice modes
    //
    //     printfn $"{status}"
    //
    //     if status = "unsat" || status = "sat" then
    //       let path' = Path.GetTempPath () + Guid.NewGuid().ToString () + ".smt2"
    //       File.WriteAllText (path', Preprocessing.Parametrized.go <| File.ReadAllText args[0])
    //       let p = Parser.Parser false
    //       let cmds = p.ParseFile path'
    //       let cmds = Preprocessing.chcFF.notFF cmds
    //       let cmds = Preprocessing.ApproximateBooleans.rwrt cmds
    //       let cmds = Preprocessing.Selectors.run cmds
    //       let cmds = cmds |> List.map toString |> join "\n"
    //       File.WriteAllText (args[2], $"{status}\n{cmds}\n{result}")
    //   // printfn "9"
    //   with e ->
    //     printfn $"{e.Message}"
    //     printfn $"ERR"
    //     
    //   0
