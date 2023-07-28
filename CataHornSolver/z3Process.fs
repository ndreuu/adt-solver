module CataHornSolver.z3Process

open System
open System.IO
open System.Text.RegularExpressions
open Antlr4.Runtime.Misc
open Process.Process
open ProofBased
open SMTLIB2
open Z3Interpreter

module Instances =
  type instance =
    | Teacher
    | Checker
    | Learner

  type logic =
    | Horn
    | All
    | NIA

    override x.ToString () =
      let l =
        match x with
        | Horn -> "HORN"
        | All -> "ALL"
        | NIA -> "NIA" in

      $"(set-logic {l})\n"

  type option =
    | Proof
    | Model
    | None

  let setOption x =
    function
    | Proof -> $"(set-option :produce-proofs true)\n{x}\n(check-sat)\n(get-proof)"
    | Model -> $"{x}\n(check-sat)\n(get-model)"
    | None -> $"{x}\n(check-sat)"

  let instances =
    [ Teacher,
      (Horn,
       Proof,
       "fp.spacer.global=true fp.xform.inline_eager=false fp.xform.inline_linear=false fp.xform.slice=false fp.datalog.similarity_compressor=false fp.datalog.subsumption=false fp.datalog.unbound_compressor=false fp.xform.tail_simplifier_pve=false")
      Checker, (All, None, "")
      Learner, (NIA, Model, "-T:20") ]
    |> Map

  let content instance cmds =
    let logic, option, _ = instances |> Map.find instance
    $"""{logic}{setOption (join "\n" cmds) option}"""

  let run timeout instance cmds =
    let _, _, flags = instances |> Map.find instance
    let file = Path.GetTempPath () + ".smt2"
    File.WriteAllText (file, content instance cmds)
    let result = execute timeout "./z3" $"{flags} {file}"
    if result.StdOut.Contains "timeout" then
      Option.None
    else Some result.StdOut

    
    // if result.ExitCode = 124 then
      // Option.None
    // elif result.ExitCode = 0 then Some result.StdOut
    // else failwith $"{result.StdErr}"


module Interpreter =
  type result<'a, 'b> =
    | SAT of 'a
    | UNSAT of 'b
    | UNKNOWN

  let names =
    List.choose (function
      | AST.Def (n, _, _, _) -> Some n
      | _ -> None)

  let model consts (content: string) =
    let p = Parser.Parser false
    p.ParseModel (List.ofArray <| content.Split '\n')
    |> snd
    |> List.choose (function
      | definition.DefineFun (n, _, _, _) as d when List.contains n (names consts) ->
        Some (AST.origCommand2program <| Definition d)
      | _ -> None)

  module SoftSolver =
    let softAsserts softs =
      let softNames = List.map (fun n -> $"soft_{n}") (softs)

      List.map2
        (fun n s ->
          AST.Assert (
            AST.Implies (AST.Var s, AST.Or [| AST.Eq (AST.Var n, AST.Int 0); AST.Eq (AST.Var n, AST.Int 1) |])
          ))
        softs
        softNames,
      softNames

    let content constDefs cmds softs =
      let cmds = List.map (AST.program2originalCommand >> toString) cmds |> join "\n"
      let softAsserts, softNames = softAsserts softs
      let softNames' = softNames |> join " "
      let softAsserts' = List.map (AST.program2originalCommand >> toString) (List.sort softAsserts) |> join "\n" 
      let softDecls =
        List.map (fun n -> AST.DeclConst (n, AST.Boolean) |> AST.program2originalCommand |> toString) softNames
        |> join "\n" 
      
      $"{Instances.logic.NIA}(set-option :produce-unsat-cores true)\n{cmds}\n{softDecls}\n{softAsserts'}\n(check-sat-assuming ({softNames'}))\n(get-unsat-core)\n(get-model)"
      
    let run timeout content =
      let _, _, flags = Instances.instances |> Map.find Instances.instance.Learner
      let file = Path.GetTempPath () + ".smt2"
      File.WriteAllText (file, content)
      printfn "HERE"
      let result = execute timeout "./z3" $"{flags} {file}"
      printfn $"EREH\n{result.ExitCode}"
      if result.StdOut.Contains "timeout" then
        Option.None
      else Some result.StdOut
      // elif result.ExitCode = 0 || result.ExitCode = 1 then
      //   Some result.StdOut
      // else failwith $"{result.StdOut} {result.StdErr}"
      //   
    
    let setAssuming (content: string) assumings =
      let assumings' = join " " assumings
      Regex.Replace (content, @"\(check-sat-assuming \(.*\)\)", $"(check-sat-assuming ({assumings'}))")
    
    let solve timeout constDefs cmds softs =
      let content = content constDefs cmds softs
      let rec helper assumings =
        printfn $"helperhelper"
        let out = run timeout <| setAssuming content assumings
        match out with
        | Some out -> 
          let rSat = (Regex @"\bsat\b\n").Matches out
          let rUnknown = (Regex "unknown").Matches out
          let r =
            if rSat.Count = 1 then SAT ()
            elif rUnknown.Count = 1 then failwith "UNKNOWN?"
            else UNSAT ()
          match r with
          | SAT _ ->
            let out = out.Split "\n" |> Array.removeAt 1 |> join "\n"
            Some (SAT (Some <| model constDefs out), (List.map (fun (s: string) -> s.Remove (0, 5)) assumings)) 
          | UNSAT _ -> 
            (Regex @"soft_c_\d+").Matches out
            |> Seq.toList
            |> List.tryHead
            |> function
              | Some x ->
                List.filter (fun a -> a <> x.Value) assumings
                |> helper 
              | None ->
                printfn "!!!!!UNKNOWN"
                Environment.Exit(0)
                failwith ""
        | Option.None -> None
      helper (softAsserts softs |> snd)


  let proof cmds content =
    let queryDecs =
      Regex(@"\(declare-fun query").Matches content
      |> Seq.map (fun (m: Match) -> m.Index |> content.Substring |> Utils.balancedBracket |> Option.get)
      |> Seq.toList

    let mp =
      Regex(@"\(mp").Match content
      |> fun mps -> mps.Index
      |> content.Substring
      |> Utils.balancedBracket
      |> function
        | Some s -> s.Replace ("mp ", "proof mp ")
        | None -> ""

    let p = Parser.Parser false

    for x in
      queryDecs
      @ List.choose
        (function
        | AST.Decl _ as x -> Some (AST.program2originalCommand x |> toString)
        | _ -> None)
        cmds do
      p.ParseLine x |> ignore

    let mp = p.ParseLine mp

    (List.choose
      (function
      | Command (Proof (HyperProof (a, hs, _), x, _)) ->
        Command (Proof (HyperProof (a, hs, BoolConst false), x, BoolConst false))
        |> Some
      | _ -> None)
      mp,
     content)


  let solve timeout instance cmds constDefs softs =
    match instance with
    | Instances.instance.Learner ->
      SoftSolver.solve timeout constDefs cmds softs
    | _ ->
      let _, option, _ = Instances.instances |> Map.find instance

      let input = List.map (AST.program2originalCommand >> toString) cmds
      
      let output =
        Instances.run timeout instance input
      
      match output with
      | Option.None -> Option.None 
      | Some output -> 
        let rUnsat = (Regex "unsat").Matches output
        let rSat = (Regex "sat").Matches output
  
        let r =
          if rUnsat.Count = 1 then UNSAT ()
          elif rSat.Count = 1 then SAT ()
          else UNKNOWN
        
        match option, r with
        | Instances.option.None, UNSAT _ -> Some (UNSAT None, [])
        | Instances.option.Model, UNSAT _ -> Some (UNSAT None, [])
        | Instances.option.Proof, UNSAT _ -> Some (UNSAT (Some <| proof cmds output), [])
        | Instances.option.None, SAT _ -> Some (SAT None, [])
        | Instances.option.Proof, SAT _ -> Some (SAT None, [])
        | Instances.option.Model, SAT _ -> Some (SAT (Some <| model constDefs output), [])
        | _ -> Some (UNKNOWN, [])
  

type snapshot =
  { cmds: AST.Program list
    consts: AST.Program list }

type context =
  { cmds: AST.Program list
    snapshot: snapshot
    softConsts: AST.Name list }

  static member Init () =
    { cmds = []
      snapshot = { cmds = []; consts = [] }
      softConsts = [] }

let tst () =
  let contnet =
    """sat
(
  (define-fun c_2 () Int
    0)
  (define-fun c_0 () Int
    1)
  (define-fun c_3 () Int
    2)
  (define-fun soft_c_1 () Bool
    false)
  (define-fun c_1 () Int
    6)
  (define-fun soft_c_3 () Bool
    false)
  (define-fun Z_194 () Int
    0)
  (define-fun Z_192 () Int
    0)
  (define-fun soft_c_2 () Bool
    true)
  (define-fun soft_c_0 () Bool
    true)
  (define-fun div0 ((x!0 Int) (x!1 Int)) Int
    (ite (and (= x!0 (- 2)) (= x!1 0)) 3
    (ite (and (= x!0 (- 1)) (= x!1 0)) 3
      (- 3))))
  (define-fun mod0 ((x!0 Int) (x!1 Int)) Int
    (ite (and (= x!0 (- 5)) (= x!1 0)) (- 6)
    (ite (and (= x!0 (- 2)) (= x!1 0)) (- 3)
    (ite (and (= x!0 1) (= x!1 0)) (- 3)
      3))))
)"""

  Interpreter.model
    [ AST.Def ("c_0", [], AST.Integer, AST.Int 0)
      AST.Def ("c_1", [], AST.Integer, AST.Int 0)
      AST.Def ("c_2", [], AST.Integer, AST.Int 0)
      AST.Def ("c_3", [], AST.Integer, AST.Int 0) ]
    contnet

  ()
// printfn $"{Utils.balancedBracket contnet}"

// let p = Parser.Parser false
// let xs = p.ParseFile "/home/andrew/Downloads/jjj/dbg/lol/1/a.out"
// for x in xs do printfn $"{x}"

let tstpp () =
  let p = Parser.Parser false

  for x in
    [ "(declare-fun query!0 (Int Int Int) Bool)"
      "(declare-fun Inv (Int Int Int) Bool)"
      "(declare-fun length (Int Int) Bool)" ] do
    p.ParseLine x |> ignore

  let cs =
    p.ParseLine
      """(proof mp ((_ hyper-res 0 0 0 1 0 2) (asserted (forall ((A Int) (B Int) (C Int) )(=> (and (Inv C A B) (length C B) (not (<= 0 A))) (query!0 A B C)))
 ) ((_ hyper-res 0 0 0 1 0 2 0 3) (asserted (forall ((A Int) (B Int) (C Int) (D Int) (E Int) )(=> (and (length E D) (Inv E B C) (length E C) (= A (+ (- 1) B))) (Inv E A D)))
 ) ((_ hyper-res 0 0) (asserted (length 1 0)) (length 1 0)) ((_ hyper-res 0 0 0 1) (asserted (forall ((A Int) (B Int) )(=> (length B A) (Inv B A A)))
 ) ((_ hyper-res 0 0) (asserted (length 1 0)) (length 1 0)) (Inv 1 0 0)) ((_ hyper-res 0 0) (asserted (length 1 0)) (length 1 0)) (Inv 1 (- 1) 0)) ((_ hyper-res 0 0) (asserted (length 1 0)) (length 1 0)) (query!0 (- 1) 0 1)) (asserted (=> (query!0 (- 1) 0 1) false)) false)
"""

  for x in cs do
    printfn $"... {x}"


let chc () =
  executeZ3 "fp.spacer.global=true fp.xform.inline_eager=false fp.xform.inline_linear=false fp.xform.slice=false fp.datalog.similarity_compressor=false fp.datalog.subsumption=false fp.datalog.unbound_compressor=false fp.xform.tail_simplifier_pve=false /home/andrew/Downloads/jjj/dbg/lol/2/smt-input.smt2"
  |> printfn "%O"
  

