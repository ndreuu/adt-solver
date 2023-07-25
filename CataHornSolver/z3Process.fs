module CataHornSolver.z3Process

open System
open System.IO
open System.Text.RegularExpressions
open Antlr4.Runtime.Misc
open Process.Process
open ProofBased
open SMTLIB2
open Z3Interpreter

let runZ3 funDefs constDefs constrDefs funDecls asserts =
  let file = Path.GetTempPath () + ".smt2"

  let content =
    let body =
      (List.map toString funDefs)
      @ (List.map toString constDefs)
      @ (List.map toString constrDefs)
      @ (List.map toString funDecls)
      @ (List.map toString asserts)
      |> join "\n"

    $"""(set-logic HORN)
(set-option :produce-proofs true)
{body}
(check-sat)
(get-proof)
"""

  File.WriteAllText (file, content)

  let result =
    execute
      "./z3"
      $"fp.datalog.subsumption=false fp.spacer.global=true fp.xform.inline_eager=false fp.xform.inline_linear=false fp.xform.slice=false {file}"

  result.StdOut

let z3proof funDefs constDefs constrDefs funDecls asserts =
  let out = runZ3 funDefs constDefs constrDefs funDecls asserts

  let queryDecs =
    Regex(@"\(declare-fun query").Matches out
    |> Seq.map (fun (m: Match) -> m.Index |> out.Substring |> Utils.balancedBracket |> Option.get)
    |> Seq.toList

  let p = Parser.Parser false

  for x in queryDecs @ List.map toString funDecls do
    p.ParseLine x |> ignore

  let mp =
    Regex(@"\(mp").Match out
    |> fun mps -> mps.Index
    |> out.Substring
    |> Utils.balancedBracket
    |> function
      | Some s ->
        s.Replace (
          "mp ",
          "proof mp
                   
                   "
        )
        |> fun s -> s |> p.ParseLine
      | None -> []

  (List.choose
    (function
    | Command (Proof (HyperProof (a, hs, _), x, _)) ->
      Command ((Proof (HyperProof (a, hs, BoolConst false), x, BoolConst false)))
      |> Some
    | _ -> None)
    mp,
   out)

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
       "fp.datalog.subsumption=false fp.spacer.global=true fp.xform.inline_eager=false fp.xform.inline_linear=false fp.xform.slice=false")
      Checker, (All, None, "")
      Learner, (NIA, Model, "fp.spacer.global=true") ]
    |> Map

  let content instance cmds =
    let logic, option, _ = instances |> Map.find instance
    $"""{logic}{setOption (join "\n" cmds) option}"""

  let run instance cmds =
    let _, _, flags = instances |> Map.find instance
    let file = Path.GetTempPath () + ".smt2"
    File.WriteAllText (file, content instance cmds)
    let result = execute "./z3" $"{flags} {file}"

    result.StdOut


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
    let softAsserts constDefs =
      let softNames = List.map (fun n -> $"soft_{n}") (names constDefs)

      List.map2
        (fun n s ->
          AST.Assert (
            AST.Implies (AST.Var s, AST.Or [| AST.Eq (AST.Var n, AST.Int 0); AST.Eq (AST.Var n, AST.Int 1) |])
          ))
        (names constDefs)
        softNames,
      softNames

    let content constDefs cmds =
      let cmds = List.map (AST.program2originalCommand >> toString) cmds |> join "\n"
      let softAsserts, softNames = softAsserts constDefs
      let softNames' = softNames |> join " "
      let softAsserts' = List.map (AST.program2originalCommand >> toString) softAsserts |> join "\n" 
      let softDecls =
        List.map (fun n -> AST.DeclConst (n, AST.Boolean) |> AST.program2originalCommand |> toString) softNames
        |> join "\n" 
      
      $"{Instances.logic.NIA}(set-option :produce-unsat-cores true)\n{cmds}\n{softDecls}\n{softAsserts'}\n(check-sat-assuming ({softNames'}))\n(get-unsat-core)\n(get-model)"
      
    let run content =
      let _, _, flags = Instances.instances |> Map.find Instances.instance.Learner
      let file = Path.GetTempPath () + ".smt2"
      File.WriteAllText (file, content)
      let result = execute "./z3" $"{flags} {file}"
      result.StdOut
    
    let setAssuming (content: string) assumings =
      let assumings' = join " " assumings
      Regex.Replace (content, @"\(check-sat-assuming \(.*\)\)", $"(check-sat-assuming ({assumings'}))")
    
    let solve constDefs cmds =
      let content = content constDefs cmds
      
      let rec helper assumings =
        let out = run <| setAssuming content assumings
        let rSat = (Regex @"\bsat\b\n").Matches out
        let rUnknown = (Regex "unknown").Matches out
        let r =
          if rSat.Count = 1 then SAT ()
          elif rUnknown.Count = 1 then failwith "UNKNOWN?"
          else UNSAT ()
        match r with
        | SAT _ ->
          let out = out.Split "\n" |> Array.removeAt 1 |> join "\n"
          SAT (Some <| model constDefs out) 
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
      helper (softAsserts constDefs |> snd)


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









  let solve instance cmds constDefs =
    match instance with
    | Instances.instance.Learner -> SoftSolver.solve constDefs cmds
    | _ ->
      let _, option, _ = Instances.instances |> Map.find instance

      let content =
        Instances.run instance
        <| List.map (AST.program2originalCommand >> toString) cmds

      let rUnsat = (Regex "unsat").Matches content
      let rSat = (Regex "sat").Matches content

      let r =
        if rUnsat.Count = 1 then UNSAT ()
        elif rSat.Count = 1 then SAT ()
        else UNKNOWN

      // for x in List.map (AST.program2originalCommand >> toString) cmds do
      // printfn $">> {x}"

      // printfn $"contentcontentcontentcontentcontentcontentcontentcontentcontentcontentcontentcontentv\n{content}"

      match option, r with
      | Instances.option.None, UNSAT _ -> UNSAT None
      | Instances.option.Model, UNSAT _ -> UNSAT None
      | Instances.option.Proof, UNSAT _ -> UNSAT (Some <| proof cmds content)
      | Instances.option.None, SAT _ -> SAT None
      | Instances.option.Proof, SAT _ -> SAT None
      | Instances.option.Model, SAT _ -> SAT (Some <| model constDefs content)
      | _ -> UNKNOWN



// let softAsserts =
// List.map (fun n -> AST.Assert (AST.Implies (AST.Var n ))) (names constDefs)




type context =
  { logic: string
    cmds: AST.Program list
    softConsts: AST.Program list }

  static member Init () =
    { logic = "ALL"
      cmds = []
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
