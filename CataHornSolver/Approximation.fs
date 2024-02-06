module Approximation

open Microsoft.FSharp.Collections
open SMTLIB2.Parser
open SMTLIB2.Prelude
open Operation
open SMTLIB2
open ProofBased.Utils.IntOps


module Linearization =
  let linearization abstrSort file =
    let p = Parser (false)
    let commands = p.ParseFile file

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
               sum pd <| terms pd (List.map opName args)
             )
           )
           :: acc))
        (pdng, [])

    let padding, dataTypes, recs =
      let pdng, (defs, recs) =
        List.fold
          (fun (pdng, (acc, recs)) x ->
            match x with
            | Command (DeclareDatatype (n, cs)) ->
              let pdng', def = pdng_defs cs pdng
              (pdng', (def @ acc, recs @ [[n, cs]]))
            | Command (DeclareDatatypes [ n, cs ]) ->
              let pdng', def = pdng_defs cs pdng
              (pdng', (def @ acc, recs @ [[n, cs]]))
            | Command (DeclareDatatypes ds) as v ->
              List.fold
                (fun (pdng, (acc, recs)) ->
                  function
                  | _, cs ->
                    let pdng', def = pdng_defs cs pdng
                    (pdng', (def @ acc, recs)))
                (pdng, (acc, recs @ [ ds ]))
                ds
            // failwith $"??? {v}"
            | _ -> (pdng, (acc, recs)))
          (0, ([], []))
          commands

      (pdng, defs |> List.rev, List.map (List.map fst) recs)

    let padding, functions =
      let padding, functions =
        List.fold
          (fun (pdng, acc as r) cmd ->
            match cmd with
            | Command (DeclareFun (name, sorts, _)) ->
              let _, args =
                sorts
                |> List.fold (fun (i, acc) _ -> (i - 1, ($"x_{i}", IntSort) :: acc)) (sorts.Length - 1, [])

              (pdng + args.Length + 1,
               Definition (DefineFun (name, args, IntSort, sum pdng <| terms pdng (List.map fst args)))
               :: acc)
            | _ -> r)
          (padding, [])
          commands

      (padding, functions |> List.rev)

    let asserts =
      let quantiInt = List.map (fun (name, s) -> name, match s with IntSort -> IntSort | _ -> abstrSort)

      let eq_op typ =
        Operation.makeElementaryRelationFromSorts "=" [ typ; typ ]

      let rec helper smt =
        match smt with
        | Apply (UserDefinedOperation _, _) as app -> Apply (eq_op IntSort, [ app; Number 0 ])
        | And smtExprs -> And (smtExprs |> List.map helper)
        | Or smtExprs -> Or (smtExprs |> List.map helper)
        | Not smtExpr -> Not (helper smtExpr)
        | Hence (smtExpr1, smtExpr2) -> Hence (helper smtExpr1, helper smtExpr2)
        | QuantifierApplication (quantifier, smtExpr) ->
          QuantifierApplication (Quantifiers.mapVars quantiInt quantifier, helper smtExpr)
        | _ -> smt

      commands
      |> List.choose (function
        | Assert expr -> Some (Assert (helper expr))
        | _ -> None)

    let asserts' f =
      List.map (function
        | Assert (QuantifierApplication (quantifiers, smtExpr)) ->
          quantifiers |> Quantifiers.getVars |> List.map (Command << DeclareConst), Assert (f smtExpr)
        | Assert expr -> [], Assert (f expr)
        | asrt -> [], asrt)

    let skAsserts = asserts' Not asserts
    let notSkAsserts = asserts' id asserts

    let defConstants =
      List.init padding (fun i -> Definition (DefineFun ($"c_{i}", [], IntSort, Number 0)))

    let decConstants =
      List.init padding (fun i -> Command (DeclareConst ($"c_{i}", IntSort)))

    let defFunctions =
      commands
      |> List.filter (function
        | Definition (DefineFun _) -> true
        | _ -> false)

    (recs, defFunctions, defConstants, decConstants, dataTypes, functions, asserts, skAsserts, notSkAsserts)
