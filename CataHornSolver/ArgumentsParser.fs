module CataHornSolver.ArgumentsParser

open Argu
open ProofBased

type CliArguments =
  | File of path: string
  | FileTimes of path: string
  | Learner of SMTSolver: string
  | TimeLimits of learnerTimeLimit: int * teacherTimeLimit: int * checkerTimeLimit: int
  | RedlogTimeLimit of redlogTimeLimit: int
  | OutputContract of path: string
  | Async

  interface IArgParserTemplate with
    member s.Usage =
      match s with
      | File _ -> "path for .smt2 input file"
      | FileTimes _ -> "path for times output file"
      | Learner _ -> "instance of SMT solver for learner"
      | TimeLimits _ -> "time limits for each tool"
      | RedlogTimeLimit _ -> "time limits for redlog"
      | OutputContract _ -> "path for output of model/proof"
      | Async -> "separator for async modes execution"


let file =
  List.choose (function
    | File f -> Some f
    | _ -> None)
  >> function
    | [ file ] -> Ok file
    | _ -> Error "there more then one input file was wrote"

let fileTimes =
  List.choose (function
    | FileTimes f -> Some f
    | _ -> None)
  >> function
    | [ file ] -> Ok <| Some file
    | [] -> Ok None
    | _ -> Error "file time is chose wrong"
    
let outputContract =
  List.choose (function
    | OutputContract f -> Some f
    | _ -> None)
  >> function
    | [ file ] -> Ok file
    | _ -> Error "output file is not specified"

type SMTSolver =
  | CVC
  | Z3

type CoreTimeLimits = int * int * int * int option

type Mode = SMTSolver * CoreTimeLimits

let smtSolver =
  List.choose (function
    | Learner l -> Some l
    | _ -> None)
  >> function
    | [ "cvc" ] -> Ok CVC
    | [ "z3" ] -> Ok Z3
    | _ -> Error "smt solver is chose wrong"

let timeLimits s =
  List.choose
    (function
    | TimeLimits (l, t, c) -> Some (l, t, c)
    | _ -> None)
    s
  |> function
    | [ (l, t, c) ] ->
      List.choose
        (function
        | RedlogTimeLimit tl -> Some tl
        | _ -> None)
        s
      |> function
        | [ r ] -> Ok (l, t, c, Some r)
        | _ -> Ok (l, t, c, None)
    | _ -> Error "time limits is described wrong"

let bind f g s =
  match f s with
  | Ok x ->
    match g s with
    | Ok y -> Ok (x, y)
    | Error err -> Error err
  | Error errX ->
    match g s with
    | Error errY -> Error $"{errX}\n{errY}"
    | _ -> Error errX

let mode s = bind smtSolver timeLimits s
  // match smtSolver s with
  // | Ok solver ->
  //   match timeLimits s with
  //   | Ok tls -> Ok (solver, tls)
  //   | Error err -> Error err
  // | Error errSolver ->
  //   match timeLimits s with
  //   | Error errTls -> Error $"{errSolver}\n{errTls}"
  //   | _ -> Error errSolver

let many =
  let haverErrs rs =
    List.filter
      (function
      | Error _ -> true
      | _ -> false)
      rs
    |> List.length > 0

  List.fold
    (fun (tmp, acc) ->
      function
      | Async -> ([], tmp :: acc)
      | otherwise -> (otherwise :: tmp, acc))
    ([], [])
  >> function
    | (tmp, acc) ->
      let modes' = List.map mode (tmp :: acc)

      if haverErrs modes' then
        Error (
          List.choose
            (function
            | Error err -> Some err
            | _ -> None)
            modes'
          |> Set
          |> Utils.join "\n"
        )
      else
        Ok (
          List.choose
            (function
            | Ok mode -> Some mode
            | _ -> None)
            modes'
        )

let runParser p args =
  let parser = ArgumentParser.Create<CliArguments> ()
  let tokens = (parser.Parse args).GetAllResults ()
  p tokens

let parse args = 
  let parser = ArgumentParser.Create<CliArguments> ()
  let tokens = (parser.Parse args).GetAllResults ()
  bind file (bind fileTimes many) tokens
  
