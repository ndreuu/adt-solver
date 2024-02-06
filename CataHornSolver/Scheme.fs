module CataHornSolver.Scheme

open System.Numerics
open ProofBased
open SMTLIB2
open ProofBased.Utils.IntOps
open Z3Interpreter.AST

type IAbstractDomain =
  abstract member Definitions: Z3Interpreter.AST.Program list
  abstract member DomainADT: Z3Interpreter.AST.Program list
  abstract member Constants: Z3Interpreter.AST.Program list
  // abstract member Approximations: Z3Interpreter.AST.Program seq seq
  abstract member Approximations: Z3Interpreter.AST.Program list list
  abstract member Declarations: Z3Interpreter.AST.Program list
  abstract member Asserts: Z3Interpreter.AST.Program list

let toPrograms domain = List.map (origCommand2programWithAbstr domain)

let funDecls declFuns abstrSort = List.map (origCommand2programWithAbstr abstrSort) declFuns
let asserts' asserts abstrSort = List.map (origCommand2programWithAbstr abstrSort) asserts

let apply2app appNames =
  let rec helper =
    function
    | App _
    | Int _
    | Bool _
    | Var _ as expr -> expr
    | Eq (expr1, expr2) -> Eq (helper expr1, helper expr2)
    | Lt (expr1, expr2) -> Lt (helper expr1, helper expr2)
    | Gt (expr1, expr2) -> Gt (helper expr1, helper expr2)
    | Le (expr1, expr2) -> Le (helper expr1, helper expr2)
    | Ge (expr1, expr2) -> Ge (helper expr1, helper expr2)
    | Mod (expr1, expr2) -> Mod (helper expr1, helper expr2)
    | Add (expr1, expr2) -> Add (helper expr1, helper expr2)
    | Subtract (expr1, expr2) -> Subtract (helper expr1, helper expr2)
    | Neg expr -> Neg (helper expr)
    | Mul (expr1, expr2) -> Mul (helper expr1, helper expr2)
    | And exprs -> And (Array.map helper exprs)
    | Or exprs -> Or (Array.map helper exprs)
    | Not expr -> Not (helper expr)
    | Implies (expr1, expr2) -> Implies (helper expr1, helper expr2)
    | Apply (name, exprs) when appNames |> List.contains name -> App (name, List.map helper exprs)
    | Apply (name, exprs) -> Apply (name, List.map helper exprs)
    | Ite (expr1, expr2, expr3) -> Ite (helper expr1, helper expr2, helper expr3)
    | ForAllTyped (names, expr) -> ForAllTyped (names, helper expr)
    | o ->
      printfn $"{o}"
      failwith $"{o}"
  helper

let appNames declFuns abstrSort =
  funDecls declFuns abstrSort
  |> List.choose (function
    | Decl (n, _) -> Some n
    | _ -> None)

let asserts'' asserts declFuns abstrSort =
  asserts' asserts abstrSort
  |> List.choose (function
    | Assert x -> Some (Assert (apply2app (appNames declFuns abstrSort) x))
    | _ -> None)


module Abstract =
  let liaCombination args = function
    | c::cs -> List.fold add c (List.map2 mult cs args)
    | _ -> Number (BigInteger 0)
  
  let abstractOp n vars =
    Operation.makeADTOperations
      (ADTSort "AbstractDomain")
      n  
      ("is-" + n)
      vars |> fst3
  
  let abstractOps =
    List.map
      (fun (n, vars) ->
        n,
        Operation.makeADTOperations
          (ADTSort "AbstractDomain")
          n  
          ("is-" + n)
          vars |> fst3)
  
  let forkBy var constructor =
    match constructor with
    | name, [] -> Prelude.smtExpr.Apply (abstractOp name [], [])
    | name, vars -> Prelude.smtExpr.Apply (abstractOp name vars, [ var ])
    
  let mkAbstractDomainFn constructors intVars abstractVars =
    let rec helper retName intVars = function
      | x :: xs ->
        let intVar = Ident ($"{x}-lolkek", IntSort)
        let intVars' = intVar :: intVars
        intVars',
        Prelude.smtExpr.Match
          (Ident (x, ADTSort "AbstractDomain"),
           List.map (fun (n, _ as c) -> forkBy intVar c, snd <| helper $"{retName}~>{n}-{x}" intVars' xs) constructors
           // [ Prelude.smtExpr.Apply (abstractOp "Some" [ $"i", IntSort ], [ intVar ]), snd <| helper $"{retName}~>some-{x}" intVars' xs
           //   Prelude.smtExpr.Apply (abstractOp "None" [], []), snd <| helper $"{retName}~>none-{x}" intVars xs ]
           )
      | [] ->
        [],
        Prelude.smtExpr.Apply
          (Operation.makeElementaryOperationFromSorts
             retName
             (List.map (fun _ -> IntSort) intVars)
             (ADTSort "AbstractDomain"),
          intVars)
    
    helper "approximating-fn" (List.map (fun n -> Ident (n, IntSort)) intVars) abstractVars
    |> snd
  
  let approximatingFns =
    let rec helper acc = function
      | Prelude.smtExpr.Match (_, ms) ->
        List.fold helper acc (snd <| List.unzip ms) 
      | otherwise ->
        otherwise :: acc
    helper []
  
  let generateIntVars pdng prefix =
    List.unfold (fun i -> if i > 0 then (Some ($"{prefix}", i - 1)) else None)
    >> List.mapi (fun i n -> ($"{n}_{pdng + i}", IntSort))
  
  let generateConstants pdng n = ($"c_{pdng}", IntSort) :: (generateIntVars (pdng + 1) "c" n)
      
  let expandTuple t v = match t with x, y -> (v, x, y) 
      
  let approximatingFnBodies constructors pdng (fns: smtExpr list): int * (ident * smtExpr * sorted_var list) list list =
    // let noneDefinitions =
    //   List.choose (function
    //     | Prelude.Apply (op, _) -> Some (Operation.opName op, Prelude.Apply (abstractOp "None" [], []), [])
    //     | _ -> None)
    //     fns
    //
    let applyConstructor constantPdng (cName, cVars) args vars =
      match cVars with
      | [] ->
        Prelude.Apply (abstractOp cName cVars, []), []
      | _ ->
        Prelude.Apply
          (abstractOp cName cVars,
           [ liaCombination args (List.map Ident <| generateConstants constantPdng (List.length args)) ]), vars
        
    let approximatedDefs pdng f  =
      List.foldBack
        (fun (cName, cVars as constructor) (i, acc) ->
          match f with 
          | Prelude.Apply (op, exprs) ->
            let vars = generateIntVars 0 "x" <| List.length exprs
            let args = List.map Ident vars
            
            (i + (if List.isEmpty cVars then 0 else List.length args + 1),
             (expandTuple (applyConstructor i constructor args vars) <| Operation.opName op) :: acc)
            | _ -> (i, acc))
        constructors
        (pdng, [])
    
    // let constructors = []
    
    let pdng', (defs: (ident * smtExpr * sorted_var list) list list) =
      List.foldBack
        (fun f (pdng, accum) ->
          let pdng', v = approximatedDefs pdng f
          pdng', v :: accum)
        fns
        // constructors
        (pdng, []) 
    
    for d in defs do printfn $"dddd: {d}"
    
    // let pdng', someDefinitions =
    //   List.foldBack
    //     (fun f (i, acc) ->
    //       match f with 
    //       | Prelude.Apply (op, exprs) ->
    //         let vars = generateIntVars 0 "x" <| List.length exprs
    //         let args = List.map Ident vars
    //         (i + List.length args + 1,
    //          (Operation.opName op,
    //           Prelude.Apply
    //             (abstractOp "Some" [ $"i", IntSort ],
    //              [ liaCombination args (List.map Ident <| generateConstants i (List.length args)) ]), 
    //             vars) :: acc)
    //         | _ -> (i, acc))
    //     fns
    //     (pdng, [])
      
        
    pdng', defs
    // List.zip someDefinitions noneDefinitions
  
  let permutations: ((ident * smtExpr * sorted_var list) list) list -> (ident * smtExpr * sorted_var list) list list =
    let insert x = List.map <| List.addLast x 
    let rec helper (acc: _ list list) = function
      | xs::tl -> helper (List.fold (fun acc' x -> acc' @ (insert x acc)) [] xs) tl  
      | [] -> acc
    helper [[]]
    
  let permutationLists: originalCommand list list -> originalCommand list list =
    let insert x xs = List.map (List.addLast x) xs 
    let rec helper acc = function
      | xs::tl ->
        helper (List.fold (fun acc' x -> acc' @ (insert x acc)) [] xs) tl  
      | [] -> acc
    helper [[]]
    
  
  let permutationLists': _ list list list -> _ list list list =
    let insert x (xs: 'a list list) =
      List.map (fun (v: _ list) -> List.addLast x v) xs 
    let rec helper (acc: 'a list list) =
      function
      | xs::tl ->
        helper (List.fold (fun acc' x -> acc' @ (insert x acc)) [] xs) tl  
      | [] -> acc
    helper [[]]
    
  // let permutationLists': _ list list list -> _ list list seq =
  //   let insert x (xs: _ list seq): _ list list seq =
  //       // for x in Seq.head xs do printfn $">> {x}"
  //       // printfn $"{xs.Length}"
  //       Seq.map (fun (v: _ list list) -> (List.addLast x v)) xs 
  //   
  //   let rec helper (acc: _ list list seq) =
  //     function
  //     | [] -> acc
  //     | xs::tl ->
  //       helper (Seq.fold (fun (acc': _ list list seq) x -> Seq.append acc' (insert x acc)) Seq.empty xs) tl  
  //   helper ([[]])
  //
  let rawADTs =
    List.choose (function
      | originalCommand.Command (command.DeclareDatatype (_, xs)) ->
        Some (List.map (fun (c, _, args) ->
          Operation.opName c,
          List.map (fun arg -> Ident (Operation.opName arg, Operation.returnType arg)) args) xs)
      | originalCommand.Command (command.DeclareDatatypes adts) ->
        Some
          (List.concat
           <| List.map
                (fun (_, xs) ->
                List.map
                  (fun (c, _, args) ->
                   Operation.opName c,
                   List.map
                     (fun arg -> Ident (Operation.opName arg, Operation.returnType arg))
                     args)
                  xs)
                adts)
      | _ -> None)
  
  let intArgs = List.choose (function Ident (n, IntSort) -> Some n | _ -> None)
  let adtArgs = List.choose (function Ident (n, ADTSort _) -> Some n | _ -> None)
  let mkDef name vars expr = Definition (DefineFun (name, vars, ADTSort "AbstractDomain", expr))
    
  let apply (expr: smtExpr) (name, body, vars) =
    let rec lolkek map = function
      | smtExpr.Apply (n, exprs) ->
        smtExpr.Apply (n, List.map (lolkek map) exprs)
      | Ident _ as i ->
        match Map.tryFind i map with
        | Some e -> e
        | None -> i
      | otherwise -> otherwise 
      
    let rec helper = function
      | Match (expr, matches) ->
        Match (expr, List.map (fun (pattern, x) -> (pattern, helper x)) matches)
      | smtExpr.Apply (op, exprs) when Operation.opName op = name ->
        let map =
          match exprs, vars with
          | _, [] -> Map.empty
          | _ -> Map <| List.map2 (fun v e -> (v, e)) (List.map Ident vars) exprs
            
        lolkek map body
      | otherwise -> otherwise     
    helper expr
  
  let rec applyMany (expr: smtExpr) (fs: (ident * smtExpr * sorted_var list) list)  =
    List.fold apply expr fs
  
  let constructorApproximations constructors pdng name vars =
    let approximation = mkAbstractDomainFn constructors (intArgs vars) (adtArgs vars)  
    
    printfn $"approximation\n{approximation}"
    
    let pdng', approximatingFnBodies =
      approximatingFns approximation
      |> fun xs ->
        for x in xs do printfn $"{x}"
        xs
      |> approximatingFnBodies constructors pdng
    
    let combinations = permutations <| approximatingFnBodies 
    
    printfn $"combinationscombinationscombinations"
    for c in combinations do printfn $"{c}"
    printfn $"combinationscombinationscombinations"
    
    (pdng', List.map (applyMany approximation) combinations
    |> List.map (mkDef name (List.choose (function
      | Ident (x, ADTSort _) -> Some (x, ADTSort "AbstractDomain")
      | Ident (x, y) -> Some (x, y)
      | _ -> None)
      vars))) 

  let constants cmds =
    let rec helper acc = function
      | smtExpr.Match (_, exprs) -> List.fold helper acc <| List.map snd exprs
      | smtExpr.Apply (_, exprs) -> List.fold helper acc exprs
      | smtExpr.Ident (n, _) when n.Contains "c_" -> n :: acc
      | _ -> acc
      
    let exprs = List.choose (function originalCommand.Definition (DefineFun (_, _, _, expr)) -> Some expr | _ -> None) cmds
    Set (List.fold helper [] exprs)
    |> List.ofSeq
    |> List.map (fun n -> Def (n, [], Integer, Int BigInteger.Zero))
    
 // let rec helper =
      
  let approximationCombinations constructors (cmds: originalCommand list): originalCommand list list =
    let generateApproximations =
      let handleADT pdng rawADT acc =
        List.foldBack
          (fun (name, vars) (pdng, acc) ->
            let pdng', v = constructorApproximations constructors pdng name vars
            (pdng', v :: acc))
          rawADT
          (pdng, acc)
      
      let handleADTs cmds =
        List.foldBack
          (fun rawADT (pdng, acc) ->
            let pdng', v = handleADT pdng rawADT []
            (pdng', v :: acc))
          (rawADTs cmds)
          (0, [])
        
      handleADTs >> snd
    
    generateApproximations cmds
    |> List.map permutationLists
    |> permutationLists'
    |> List.map List.concat 
    



type OptionAbstr(f: sort -> string -> originalCommand list * (symbol * sort list) list * ((symbol * Type) list * Expr) list * symbol list list * Map<ident,(symbol * int * Type list)> * originalCommand list * originalCommand list * Program list * originalCommand list * originalCommand list, file) =
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
    f (ADTSort "AbstractDomain") file
  
  let approximations = Abstract.approximationCombinations [ "Some", [ $"i", IntSort ]; "None", [] ] origCMDsNonBoolApproximated
  // let approximations = Abstract.approximationCombinations [ "Left", [ $"i", IntSort ]; "Right", [ $"i", IntSort ]; ] origCMDsNonBoolApproximated
             // [ Prelude.smtExpr.Apply (abstractOp "Some" [ $"i", IntSort ], [ intVar ]), snd <| helper $"{retName}~>some-{x}" intVars' xs
           //   Prelude.smtExpr.Apply (abstractOp "None" [], []), snd <| helper $"{retName}~>none-{x}" intVars xs ]


  interface IAbstractDomain with
    member this.Definitions =
      toPrograms (ADT "AbstractDomain") defFuns
    member this.DomainADT =
      [ DeclDataType [("AbstractDomain",  [ ("None", []); ("Some", [ Type.Integer ]) ])] ]
      // [ DeclDataType [("AbstractDomain",  [ ("Left", [ Type.Integer ]); ("Right", [ Type.Integer ]) ])] ]
    member this.Approximations =
      (List.map (fun (x) ->
         (List.map origCommand2program x)) approximations)
      // List.map (List.map origCommand2program) <| approximations 
      
      // [ Def
      //     ("nil",
      //      [],
      //      ADT "AbstractDomain",
      //      SMTExpr 
      //       (Prelude.smtExpr.Apply
      //          (Operation.makeADTOperations (ADTSort "AbstractDomain") "None" ("is-" + "None") [] |> fst3, [])) )
      //
      //   Def
      //     ("cons",
      //      [ ("x", Integer); ("y", ADT "AbstractDomain") ],
      //      ADT "AbstractDomain",
      //      SMTExpr 
      //       (Prelude.smtExpr.Match
      //          ((Ident ("y", ADTSort "AbstractDomain")),
      //       [ Prelude.smtExpr.Apply
      //            (Operation.makeADTOperations
      //               (ADTSort "AbstractDomain")
      //               "None"
      //               ("is-" + "None")
      //               [] |> fst3, []),
      //           Prelude.smtExpr.Apply
      //            (Operation.makeADTOperations
      //               (ADTSort "AbstractDomain")
      //               "Some"
      //               ("is-" + "Some")
      //               [ "y", ADTSort "AbstractDomain" ] |> fst3, [ Ident ("x", IntSort) ]);
      //        
      //         Prelude.smtExpr.Apply
      //            (Operation.makeADTOperations
      //               (ADTSort "AbstractDomain")
      //               "Some"  
      //               ("is-" + "Some")
      //               ["y", ADTSort "AbstractDomain"] |> fst3, [ Ident ("y1", IntSort) ]),
      //           Prelude.smtExpr.Apply (Operation.makeADTOperations
      //               (ADTSort "AbstractDomain")
      //               "Some"
      //               ("is-" + "Some")
      //               ["y", ADTSort "AbstractDomain"] |> fst3, [ add (Ident ("c_0", IntSort)) (add (mult (Ident ("c_1", IntSort)) (Ident ("x", IntSort))) (mult (Ident ("c_2", IntSort)) (Ident ("y1", IntSort))))  ] ) 
      //          ]
      //         )
      //       )
      //   )
      // ]
    member this.Asserts = asserts'' asserts declFuns (ADT "AbstractDomain")
    member this.Constants =
      // for c in Abstract.constants <| List.concat approximations do printfn $"cc> {c}"
      Abstract.constants <| List.concat approximations
      
    member this.Declarations = funDecls declFuns (ADT "AbstractDomain")


    
    
let tttt () =
  let p = Parser.Parser false
  let cmds = p.ParseFile "/home/andrew/adt-solver/benchs/tests/pretty-named-tests/adtrem-clam-goal20.smt2"
  for x in Abstract.constants cmds do
    printfn $"{x}"
    
  for x in (Abstract.approximationCombinations  [ "Some", [ $"i", IntSort ]; "None", [] ] cmds) do
    printfn $"-------"
    for y in x do
      printfn $"{y}"
    
  // let aaa = Abstract.permutationLists' [[ ["Ta"; "Ta1"] ; ["Tb"; "Tb1"]]; [ ["Fa"; "Fa1"] ; ["Fb"; "Fb1"]]]
  // for a in aaa do printfn $"{a}"
  // for x in Abstract.rawADTs cmds do
  //   let x = x
  //   
  //   for name, x in x do
  //     printfn $"--------------------------------------------"
  //     for y in Abstract.constructorApproximations name x do
  //       printfn $"AbstractAbstract {y}"
  //     
      
      
      // printfn $"{name} xxx {x}"
      // let aa = (fun x -> Abstract.mkAbstractDomainFn (Abstract.intArgs x) (Abstract.adtArgs x)) x
      // let bb = Abstract.approximatingFns aa 
      // let cc = Abstract.approximatingFnBodies bb
      // printfn $"aaa {aa}"
      // for b in cc do printfn $"bbb {b}"
      //
      
      
      
    // for c in  Abstract.permutations cc do printfn $"< {c}"
  
    
  // let aa  = Abstract.mkAbstractDomainFn [ Ident ("h", IntSort) ] [ "tl" ]
  // let bb =  Abstract.approximatingFns aa 
  // let cc = Abstract.approximatingFnDefs bb
  // for c in bb do printfn $"<> {c}"
  // for c in  Abstract.permutations cc do printfn $"< {c}"

type INTAbsrt(f: sort -> string -> originalCommand list * (symbol * sort list) list * ((symbol * Type) list * Expr) list * symbol list list * Map<ident,(symbol * int * Type list)> * originalCommand list * originalCommand list * Program list * originalCommand list * originalCommand list, file) =
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
    f IntSort file

  interface IAbstractDomain with
    member this.DomainADT = []
    member this.Definitions = toPrograms Integer defFuns 
    member this.Approximations =  [ (toPrograms Integer liaTypes) ]
    member this.Asserts = asserts'' asserts declFuns Integer
    member this.Constants = defConstants
    member this.Declarations = funDecls declFuns Integer

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
        let adts', i' = List.mapFold (fun i (n, cs) -> (n, numerateConstructors' i cs), i + List.length cs) i adts
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




// let scheme cmds =
// function
// | Int -> AbstractDef (None, [])
// | Optio
