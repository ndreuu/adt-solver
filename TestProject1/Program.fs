open System.Diagnostics
open Antlr4.Runtime
open Microsoft.FSharp.Collections
open SMTLIB2
open System
open System.IO
open System.Threading.Tasks
open SMTLIB2.Parser

module Program =
  type CommandResult =
    { ExitCode: int
      StandardOutput: string
      StandardError: string }

  let executeCommand executable args =
    async {
      let startInfo = ProcessStartInfo()
      startInfo.FileName <- executable

      for a in args do
        startInfo.ArgumentList.Add(a)

      startInfo.RedirectStandardOutput <- true
      startInfo.RedirectStandardError <- true
      startInfo.UseShellExecute <- false
      startInfo.CreateNoWindow <- true
      use p = new Process()
      p.StartInfo <- startInfo
      p.Start() |> ignore

      let outTask =
        Task.WhenAll(
          [| p.StandardOutput.ReadToEndAsync()
             p.StandardError.ReadToEndAsync() |]
        )

      do! p.WaitForExitAsync() |> Async.AwaitTask
      let! out = outTask |> Async.AwaitTask

      return
        { ExitCode = p.ExitCode
          StandardOutput = out.[0]
          StandardError = out.[1] }
    }

  let executeShellCommand command =
    executeCommand "/usr/bin/env" [ "-S"; "bash"; "-c"; command ]

  type Program =
    | Command of originalCommand
    | Definition of definition
    | Text of string

  [<EntryPoint>]
  let main _ =
    let defConstants, decConstants, dataTypes, functions, asserts, skolemAsserts, notSkolemAsserts =
      Approximation.Linearization.linearization "/home/andrew/sys/len.orig.smt2"

    let linContent =
      fun exprs logic out ->
        let push =
          fun y x ->
            List.fold
              (fun acc x ->
                match x with
                | Command x -> x.ToString() :: acc
                | Definition x -> x.ToString() :: acc
                | Text x -> x :: acc)
              x
              y

        []
        |> push exprs
        |> fun xs -> out :: "(check-sat)" :: xs
        |> List.rev
        |> fun xs -> logic :: xs
        |> List.fold (fun acc x -> sprintf "%s%s\n" acc x) ""

    let pwd = "/home/andrew/sys/tst"

    let commandsToProgram =
      List.map (fun x -> Command x)

    let definitionsToProgram =
      List.map (fun x -> Definition x)

    File.WriteAllText(
      sprintf "%s/%s" pwd "lin.smt2",
      linContent
        (commandsToProgram defConstants
         @ definitionsToProgram dataTypes
           @ definitionsToProgram functions
             @ commandsToProgram asserts)
        "(set-logic HORN)"
        ""
    )

    let xAsserts =
      fun xs ->
        xs
        |> List.fold
             (fun acc (xs, x) ->
               (xs
                |> List.fold (fun acc x -> Command x :: acc) []
                |> List.rev
                |> fun xs -> (Command x, xs))
               :: acc)
             []
        |> List.rev

    let skAsserts = xAsserts skolemAsserts

    let nskAsserts = xAsserts notSkolemAsserts

    nskAsserts
    |> List.iter (fun x -> printfn "%s" <| x.ToString())

    let skExamine =
      fun skPath defConstants clause decs ->
        File.WriteAllText(
          skPath,
          linContent
            (commandsToProgram defConstants
             @ definitionsToProgram dataTypes
               @ definitionsToProgram functions @ decs @ [ clause ])
            "(set-logic QF_LIA)"
            "(get-model)"
        )

    let nskExamine =
      fun nskPath clause ->
        File.WriteAllText(
          nskPath,
          linContent
            (commandsToProgram decConstants
             @ definitionsToProgram dataTypes
               @ definitionsToProgram functions @ [ clause ])
            "(set-logic HORN)"
            "(get-model)"
        )

    let varsExmn =
      skExamine <| sprintf "%s/%s" pwd "vars.smt2"

    let constsExmn =
      nskExamine
      <| (sprintf "%s/%s" pwd "constants.smt2")

    let cvc =
      fun file ->
        sprintf "cvc -m %s/%s" pwd file
        |> executeShellCommand
        // "cvc -m /home/andrew/sys/tst/vars.smt2"
        // (sprintf "cvc -m %s/%s" pwd file)
        |> Async.RunSynchronously
    // |> fun r ->
    //      match r.ExitCode with
    //      | 0 when r.StandardOutput = term -> f
    //      | 0 -> f
    //      | _ -> failwith "AAA"


    let cut =
      function
      | _ :: _ :: xs ->
        xs
        |> List.rev
        |> function
          | _ :: _ :: xs -> xs |> List.rev
          | _ -> []
      | _ -> []

    let map =
      fun vModel ->
        let p = Parser(true)

        vModel
        |> List.fold (fun acc x -> acc @ p.ParseLine x) []
        |> List.map (fun x ->
          match x with
          | Prelude.Definition (DefineFun (name, _, _, v)) -> printfn "%s ~ %s\n" <| name <| v.ToString(); (name, v)
          | _ -> failwith "")

    let substitution = fun clause model ->
      let getValue =
        fun x map ->
          map
          |> List.filter (fun (name, v) -> x = name)
          |> function
            | [ (_, v) ] -> v
            | x -> printfn "%s\n" <| x.ToString(); failwith ""

      let rec helper smt =
        match smt with
        | Ident (ident, _) -> getValue ident <| map model
        | Apply (operation, smtExprs) -> Apply(operation, smtExprs |> List.map (fun x -> helper x))
        | And smtExprs -> And(smtExprs |> List.map (fun x -> helper x))
        | Or smtExprs -> Or(smtExprs |> List.map (fun x -> helper x))
        | Not smtExpr -> Not(helper smtExpr)
        | Hence (smtExpr1, smtExpr2) -> Hence(helper smtExpr1, helper smtExpr2)
        | _ -> smt

      Assert (helper clause)


    let rec run =
      fun ((qv, qc: (Program * Program list) list) as q) t cs ->
        match q with
        | ((vClause, decls) :: vqs, (cClause, _) :: cqs) ->
          varsExmn cs vClause decls

          cvc "vars.smt2"
          |> fun r ->
               let output = r.StandardOutput.Split '\n'
               Array.iter (fun x -> printfn "%s\n" <| x.ToString()) output

               match r.ExitCode with
               | 0 when output[0] = "sat" ->
                 let vModel =
                   output
                   |> Array.toList
                   |> cut
                   // |> List.map (fun x -> Text x)

                 // constsExmn cClause vModel
                 let smtClause = match cClause with Command (Assert x) -> x
                 constsExmn <| Command (substitution smtClause vModel)
                 // training constsExmn varsExmn //|> fun t cs ->
                 // run (skAsserts, nskAsserts) t cs
                 ()
               // run (vqs, cqs) t cs
               | 0 when output[0] = "unsat" -> run (vqs, cqs) t cs
               | 0 -> printfn "%s\n" r.StandardOutput
               | _ -> failwith "aaaaaaAA"
        | _ -> printf "done"


    // let rec run0 =
    //   let skExmn =
    //     skExamine <| sprintf "%s/%s" pwd "/vars.smt2"
    //
    //   let nskExmn =
    //     nskExamine
    //     <| (sprintf "%s/%s" pwd "/constants.smt2")
    //
    //   let tmpVars =
    //     executeShellCommand (sprintf "cvc -m %s/%s" pwd "vars.smt2")
    //     |> Async.RunSynchronously
    //     |> fun r ->
    //          let cut =
    //            function
    //            | _ :: _ :: xs ->
    //              xs
    //              |> List.rev
    //              |> function
    //                | _ :: _ :: xs -> xs |> List.rev
    //                | _ -> []
    //            | _ -> []
    //
    //          match r.ExitCode with
    //          | 0 ->
    //            r.StandardOutput.Split '\n'
    //            |> Array.toList
    //            |> cut
    //            |> List.map (fun x -> Text x)
    //          | _ -> failwith "AAA"
    //
    //
    //   executeShellCommand (sprintf "cvc -m %s/%s" pwd "/lin.smt2")
    //   |> Async.RunSynchronously
    //   |> fun r ->
    //        match r.ExitCode with
    //        | 0 when r.StandardOutput = "unsat\n" ->
    //          printfn "YAYAYAY"
    //
    //          // sprintf "%s/%s" pwd "tmp-vars.smt2"
    //          // |> Parser().ParseFile
    //          // |> List.fold (fun _ x -> printfn "%s\n" <| x.ToString()) ()
    //
    //          List.fold2
    //            (fun repeat (skCls, decs) (nskCls, _) ->
    //              if not repeat then
    //                skExmn defConstants skCls decs
    //                nskExmn nskCls tmpVars
    //
    //                // sprintf "%s/%s" pwd "tmp-vars.smt2"
    //                // |> Parser().ParseFile
    //                // |> List.fold (fun _ x -> printfn "%s\n" <| x.ToString()) ()
    //                false
    //              else
    //                repeat)
    //            false
    //            skAsserts
    //            nskAsserts
    //
    //        // run
    //        | _ -> failwith "AAA"

    run (skAsserts, nskAsserts) [] defConstants

    //let p = Parser(true)
    //printf "\n\n----------------------------"
    //p.ParseFile <| "/home/andrew/sys/playground/ans-consts.smt2"
    //|> List.iter (fun x -> printfn "%s\n" <| x.ToString())




    // Approximation.SolverDeprecated.a

    // Invocation sample
    // let r =
    //   executeShellCommand (sprintf "cvc -m %s" "/home/andrew/sys/tst/lin.smt2")
    //   |> Async.RunSynchronously
    //   |> fun r ->
    //        match r.ExitCode with
    //        | 0 -> Some r.StandardOutput
    //        | _ -> None
    //
    // match r with
    // | Some x -> printfn "%s" x
    // | _ -> ()


    // if r.ExitCode = 0 then
    //   printfn "%s" r.StandardOutput
    // else
    //   eprintfn "%s" r.StandardError
    //   Environment.Exit(r.ExitCode)










    // let a = Training.Solver.a
    // Parser().ParseFile "/home/andrew/sys/test.smt2"
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())

    // Training.Linearization.linearization "/home/andrew/sys/len.orig.smt2"
    // Training.read "/home/andrew/sys/bm.vars.smt2"
    // Parser().ParseFile "/home/andrew/sys/bm.vars.smt2"
    // |> List.iter (function | Definition (DefineFun x) -> printfn "%s\n" <| x.ToString() | _ -> ())
    // |> List.iter (fun x -> printfn "%s\n" <| x.ToString())
    0
