module CataHornSolver.Scheme

open SMTLIB2
open ProofBased.Utils.IntOps
open Z3Interpreter.AST

type AbstractDomain =
  abstract member Definitions: Z3Interpreter.AST.Program list
  abstract member DomainADT: Z3Interpreter.AST.Program list
  abstract member Constants: Z3Interpreter.AST.Program list
  abstract member Approximations: Z3Interpreter.AST.Program list
  abstract member Declarations: Z3Interpreter.AST.Program list
  abstract member Asserts: Z3Interpreter.AST.Program list

let toPrograms = List.map Z3Interpreter.AST.origCommand2program

type OptionAbstr(f, file) =
  let (origCMDsNonBoolApproximated,
       origDecs,
       origAsserts,
       recs,
       adtConstrs,
       defFuns,
       liaTypes,
       defConstants,
       declFuns,
       asserts) =
    f file
  
  // let _ =
  //   Prelude.smtExpr.Apply
  //     (Operation.makeADTOperations
  //        (ADTSort "AbstractDomain")
  //        "None"
  //        ("is-" + "None")
  //        []
  //        |> function x, _, _ -> x, [])
      
  
  interface AbstractDomain with
    member this.Definitions = toPrograms defFuns
    member this.DomainADT =
      [ DeclDataType [("AbstractDomain",  [ ("None", []); ("Some", [ Type.Integer ]) ])] ]
    member this.Approximations =
      [ Def
          ("nil",
           [],
           ADT "AbstractDomain",
           SMTExpr 
            (Prelude.smtExpr.Apply
               (Operation.makeADTOperations (ADTSort "AbstractDomain") "None" ("is-" + "None") [] |> fst3, [])))
      
        Def
          ("cons",
           [  ],
           ADT "AbstractDomain",
           SMTExpr 
            (Prelude.smtExpr.Apply
               (Operation.makeADTOperations (ADTSort "AbstractDomain") "None" ("is-" + "None") [] |> fst3, [])))
      
      ]
      // [ Def
      //     ("nil",
      //      [],
      //      ADT "AbstractDomain",
      //      SMTExpr
      //        (
      //         // Match
      //           Prelude.smtExpr.Apply
      //           (Operation.makeADTOperations
      //             (ADTSort "AbstractDomain")
      //             "None"
      //             ("is-" + "None")
      //             []
      //             |> function x, _, _ -> x, [])
      // // )
      //        )
      //   
      //   Def ("cons", ["head"; "tail"], ADT "AbstractDomain",
      //        Add (Add (Apply ("c_1", []), Mul (Apply ("c_2", []), Var "head")), Mul (Apply ("c_3", []), Var "tail"))) ]

    member this.Asserts = []
    member this.Constants = []
    member this.Declarations = []

type INTAbsrt(f: string -> originalCommand list * (symbol * sort list) list * ((symbol * Type) list * Expr) list * symbol list list * Map<ident,(symbol * int * Type list)> * originalCommand list * originalCommand list * Program list * originalCommand list * originalCommand list, file) =
  let (origCMDsNonBoolApproximated,
       origDecs,
       origAsserts,
       recs,
       adtConstrs,
       defFuns,
       liaTypes,
       defConstants,
       declFuns,
       asserts) =
    f file
  
  let funDecls = List.map Z3Interpreter.AST.origCommand2program declFuns


  let asserts' = List.map Z3Interpreter.AST.origCommand2program asserts

  let apply2app appNames =
    let rec helper =
      function
      | Z3Interpreter.AST.App _
      | Z3Interpreter.AST.Int _
      | Z3Interpreter.AST.Bool _
      | Z3Interpreter.AST.Var _ as expr -> expr
      | Z3Interpreter.AST.Eq (expr1, expr2) -> Z3Interpreter.AST.Eq (helper expr1, helper expr2)
      | Z3Interpreter.AST.Lt (expr1, expr2) -> Z3Interpreter.AST.Lt (helper expr1, helper expr2)
      | Z3Interpreter.AST.Gt (expr1, expr2) -> Z3Interpreter.AST.Gt (helper expr1, helper expr2)
      | Z3Interpreter.AST.Le (expr1, expr2) -> Z3Interpreter.AST.Le (helper expr1, helper expr2)
      | Z3Interpreter.AST.Ge (expr1, expr2) -> Z3Interpreter.AST.Ge (helper expr1, helper expr2)
      | Z3Interpreter.AST.Mod (expr1, expr2) -> Z3Interpreter.AST.Mod (helper expr1, helper expr2)
      | Z3Interpreter.AST.Add (expr1, expr2) -> Z3Interpreter.AST.Add (helper expr1, helper expr2)
      | Z3Interpreter.AST.Subtract (expr1, expr2) -> Z3Interpreter.AST.Subtract (helper expr1, helper expr2)
      | Z3Interpreter.AST.Neg expr -> Z3Interpreter.AST.Neg (helper expr)
      | Z3Interpreter.AST.Mul (expr1, expr2) -> Z3Interpreter.AST.Mul (helper expr1, helper expr2)
      | Z3Interpreter.AST.And exprs -> Z3Interpreter.AST.And (Array.map helper exprs)
      | Z3Interpreter.AST.Or exprs -> Z3Interpreter.AST.Or (Array.map helper exprs)
      | Z3Interpreter.AST.Not expr -> Z3Interpreter.AST.Not (helper expr)
      | Z3Interpreter.AST.Implies (expr1, expr2) -> Z3Interpreter.AST.Implies (helper expr1, helper expr2)
      | Z3Interpreter.AST.Apply (name, exprs) when appNames |> List.contains name -> Z3Interpreter.AST.App (name, List.map helper exprs)
      | Z3Interpreter.AST.Apply (name, exprs) -> Z3Interpreter.AST.Apply (name, List.map helper exprs)
      | Z3Interpreter.AST.ForAll (names, expr) -> Z3Interpreter.AST.ForAll (names, helper expr)
      | Z3Interpreter.AST.Ite (expr1, expr2, expr3) -> Z3Interpreter.AST.Ite (helper expr1, helper expr2, helper expr3)
      | o -> failwith $"{o}"
  
    helper

  let appNames =
    funDecls
    |> List.choose (function
      | Z3Interpreter.AST.Decl (n, _) -> Some n
      | _ -> None)
  
  let asserts'' =
    asserts'
    |> List.choose (function
      | Z3Interpreter.AST.Assert x -> Some (Z3Interpreter.AST.Assert (apply2app appNames x))
      | _ -> None)

  interface AbstractDomain with
    member this.DomainADT = []
    member this.Definitions = toPrograms defFuns
    member this.Approximations = toPrograms liaTypes
    member this.Asserts = asserts''
    member this.Constants = defConstants
    member this.Declarations = funDecls





type Scheme =
  | Int of AbstractDomain
  | Option of AbstractDomain

// let intDomain: AbstractDomain =
//   { new AbstractDomain with
//       member this.Approximate a = [] }


type AbstractDef = AbstractDef of abstraction: originalCommand option * adtApproximation: originalCommand list

module Generate =
  let terms pdng args =
    List.mapi (fun i x -> mult (Expr.makeConst $"c_{(i + pdng + 1)}" IntSort) (Ident (x, IntSort))) args

  let sum pdng ts =
    List.fold add (Expr.makeConst $"c_{pdng}" IntSort) ts

  let pdng_defs cs pdng =
    cs
    |> List.fold
      (fun (pd, acc) (name, _, (args: operation list)) ->
        (args.Length + pd + 1,
         Definition (
           DefineFun (
             name.ToString (),
             List.map (fun arg -> (arg.ToString (), IntSort)) args,
             IntSort,
             sum pd <| terms pd (List.map Prelude.Operation.opName args)
           )
         )
         :: acc))
      (pdng, [])

  let generate commands =
    let pdng, (defs, recs) =
      List.fold
        (fun (pdng, (acc, recs)) x ->
          match x with
          | Command (DeclareDatatype (n, cs)) ->
            let pdng', def = pdng_defs cs pdng
            (pdng', (def @ acc, recs @ [ [ n, cs ] ]))
          | Command (DeclareDatatypes [ n, cs ]) ->
            let pdng', def = pdng_defs cs pdng
            (pdng', (def @ acc, recs @ [ [ n, cs ] ]))
          | Command (DeclareDatatypes ds) as v ->
            List.fold
              (fun (pdng, (acc, recs)) ->
                function
                | _, cs ->
                  let pdng', def = pdng_defs cs pdng
                  (pdng', (def @ acc, recs)))
              (pdng, (acc, recs @ [ ds ]))
              ds
          | _ -> (pdng, (acc, recs)))
        (0, ([], []))
        commands

    defs

type info = { number: int }

type datatype_def' = symbol * (info * (operation * operation * operation list)) list // adt name, [constr, tester, [selector]]

type command' =
  | CheckSat'
  | GetModel'
  | Exit'
  | GetInfo' of string
  | GetProof'
  | SetInfo' of string * string option
  | SetLogic' of string
  | SetOption' of string
  | DeclareDatatype' of datatype_def'
  | DeclareDatatypes' of datatype_def' list
  | DeclareFun' of symbol * bool * sort list * sort
  | DeclareSort' of symbol
  | DeclareConst' of symbol * sort
  | Proof' of hyperProof * asserted * smtExpr

let numerateConstructors' from =
  List.mapi (fun i (c: operation * operation * operation list) -> { number = from + i }, c)

let numerateConstructors =
  fst
  << List.mapFold
    (fun i ->
      function
      | DeclareDatatype (n, cs) -> DeclareDatatype' (n, numerateConstructors' i cs), i + List.length cs
      | DeclareDatatypes adts ->
        let adts', i' =
          List.mapFold (fun i (n, cs) -> (n, numerateConstructors' i cs), i + List.length cs) i adts

        DeclareDatatypes' adts', i'
      | CheckSat -> CheckSat', i
      | GetModel -> GetModel', i
      | Exit -> Exit', i
      | GetInfo x -> GetInfo' x, i
      | GetProof -> GetProof', i
      | SetInfo (x, y) -> SetInfo' (x, y), i
      | SetLogic x -> SetLogic' x, i
      | SetOption x -> SetOption' x, i
      | command.DeclareFun (x, y, z, v) -> DeclareFun' (x, y, z, v), i
      | DeclareSort x -> DeclareSort' x, i
      | DeclareConst (x, y) -> DeclareConst' (x, y), i
      | Proof (x, y, z) -> Proof' (x, y, z), i)
    0

let terms pdng args =
  List.mapi (fun i x -> mult (Expr.makeConst $"c_{(i + pdng + 1)}" IntSort) (Ident (x, IntSort))) args

let sum pdng ts =
  List.fold add (Expr.makeConst $"c_{pdng}" IntSort) ts

module LIAScheme =
  let approximateADT p (n, cs) = 1

// let approximation = function
//   |


// let approximation =
//   fst
//   << List.mapFold
//     (fun i ->
//       function
//       | DeclareDatatype (n, cs) ->
//
//         DeclareDatatype' (n, numerateConstructors' i cs), i + List.length cs
//       | DeclareDatatypes adts ->
//         let adts', i' =
//           List.mapFold (fun i (n, cs) -> (n, numerateConstructors' i cs), i + List.length cs) i adts
//
//         DeclareDatatypes' adts', i'
//       | CheckSat -> CheckSat', i
//       | GetModel -> GetModel', i
//       | Exit -> Exit', i
//       | GetInfo x -> GetInfo' x, i
//       | GetProof -> GetProof', i
//       | SetInfo (x, y) -> SetInfo' (x, y), i
//       | SetLogic x -> SetLogic' x, i
//       | SetOption x -> SetOption' x, i
//       | command.DeclareFun (x, y, z, v) -> DeclareFun' (x, y, z, v), i
//       | DeclareSort x -> DeclareSort' x, i
//       | DeclareConst (x, y) -> DeclareConst' (x, y), i
//       | Proof (x, y, z) -> Proof' (x, y, z), i)
//     0



// module ExpandedScheme =



// let scheme cmds =
// function
// | Int -> AbstractDef (None, [])
// | Optio
