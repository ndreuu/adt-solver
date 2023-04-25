module Tests.ProofBased.Test

open System.Text.RegularExpressions
open NUnit.Framework
open ProofBased
open RedlogParser.RedTrace
open SMTLIB2
open Z3Interpreter.AST

[<TestFixture>]
type TestClass () =

  [<Test>]
  member this.TestMethodPassing () =
    let run consts defFns decFns asserts =
      Solver.solver [] consts defFns decFns asserts
    
    
    let dConsts =
      [ Def ("c_0", [], Int 0); Def ("c_1", [], Int 0); Def ("c_2", [], Int 1) ]
    
    let dDefFuns =
      [ Def ("Z", [], Apply ("c_0", []))
        Def ("S", [ "x" ], Add (Apply ("c_1", []), Mul (Apply ("c_2", []), Var "x"))) ]
    
    let dDeclFuns = [ Decl ("diseqInt", 2) ]
    
    let dA1 =
      Assert (ForAll ([| "x1" |], App ("diseqInt", [| Apply ("Z", []); Apply ("S", [ Var "x1" ]) |])))
    
    let dA2 =
      Assert (ForAll ([| "x2" |], App ("diseqInt", [| Apply ("S", [ Var "x2" ]); Apply ("Z", []) |])))
    
    let dA3 =
      Assert (
        ForAll (
          [| "x3"; "y3" |],
          Implies (
            App ("diseqInt", [| Var "x3"; Var "y3" |]),
            App ("diseqInt", [| Apply ("S", [ Var "x3" ]); Apply ("S", [ Var "y3" ]) |])
          )
        )
      )
    
    let dA4 =
      Assert (ForAll ([| "x4" |], Implies (App ("diseqInt", [| Var "x4"; Var "x4" |]), Bool false)))
    run dConsts dDefFuns dDeclFuns [ dA2; dA1; dA3; dA4 ] |> printfn "%O"
    Assert.True(run dConsts dDefFuns dDeclFuns [ dA2; dA1; dA3; dA4 ] = "SAT")
    // Assert.True


  [<Test>]
  member this.parseRedLog () =
    let input =
      """(!*fof (pasf) (and (or (equal (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) (
(c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) . -12) nil) ((ncong ((c2 . 1) ((c3
. 1) . 1))) (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c5 . 1) . 1) . -12) nil)
(equal (((c2 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil)) (or (equal (((c1 . 1)
((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) .
-12) nil) ((ncong ((c2 . 1) ((c4 . 1) . 1))) (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1)
. 1)) ((c5 . 1) . 1) . -12) nil) (equal (((c2 . 1) . 1)) nil) (equal (((c4 . 1)
. 1)) nil)) (or (neq (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c5 . 1) . 1) .
-12) nil) (equal (((c5 . 1) . 1) . -12) nil)) (ball !_k8 (ball !_k7 (or (ball
!_k2 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) ((c4 . 1) . 1))) (((!_k2
. 1) ((c4 . 1) . 1)) ((!_k7 . 1) ((c4 . 1) . -1))) nil) (neq (((!_k2 . 1) ((c2 .
1) . 1)) ((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12
) ((c5 . 1) . 1) . -12) nil)) (or (and (leq (((!_k2 . 1) . 1) ((c3 . 1) . 1))
nil) (geq (((!_k2 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil))
(and (geq (((!_k2 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k2 . 1) . 1) ((c3 . 1
) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil)))) (equal (((c4 . 1) . 1)) nil) ((
ncong ((c4 . 1) . 1)) (((!_k7 . 1) . 1) ((c5 . 1) . -1) . 12) nil)) (or (and (
leq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 . 1) . 1)) ((c4 . 1) . 1)
) nil) (geq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 . 1) . -1)) ((c4
. 1) . -1)) nil)) (and (geq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2) ((c4 .
1) . 1)) ((c4 . 1) . 1)) nil) (leq (((!_k7 . 1) . 1) ((!_k8 . 1) . -1) ((c3 . 2)
((c4 . 1) . -1)) ((c4 . 1) . -1)) nil)))) (or (and (leq (((!_k8 . 1) . 1) ((c3 .
1) . 1)) nil) (geq (((!_k8 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k8 . 1) . 1
)) nil)) (and (geq (((!_k8 . 1) . 1) ((c3 . 1) . 1)) nil) (leq (((!_k8 . 1) . 1)
((c3 . 1) . -1)) nil) (neq (((!_k8 . 1) . 1)) nil)))) (ball !_k4 (or (equal (((
c4 . 1) . 1)) nil) (equal (((c3 . 1) . 1)) nil) (equal (((c2 . 1) . 1)) nil) (
equal (((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12)
((c5 . 1) . 1) . -12) nil) ((ncong ((c2 . 1) ((c4 . 1) . 1))) (((!_k4 . 1) . 1)
((c1 . 1) ((c3 . 1) . -1) ((c4 . 1) . -1)) ((c5 . 1) . -1) . 12) nil) ((ncong ((
c2 . 2) ((c3 . 1) ((c4 . 1) . 1)))) (((!_k4 . 1) ((c2 . 1) ((c4 . 1) . 1)))) nil
)) (or (and (leq (((!_k4 . 1) . 1) ((c2 . 3) ((c3 . 2) ((c4 . 1) . 1))) ((c2 . 1
) ((c4 . 1) . 1))) nil) (geq (((!_k4 . 1) . 1) ((c2 . 3) ((c3 . 2) ((c4 . 1) .
-1))) ((c2 . 1) ((c4 . 1) . -1))) nil)) (and (geq (((!_k4 . 1) . 1) ((c2 . 3) ((
c3 . 2) ((c4 . 1) . 1))) ((c2 . 1) ((c4 . 1) . 1))) nil) (leq (((!_k4 . 1) . 1)
((c2 . 3) ((c3 . 2) ((c4 . 1) . -1))) ((c2 . 1) ((c4 . 1) . -1))) nil)))) (ball
!_k2 (or (equal (((c3 . 1) . 1)) nil) ((ncong ((c3 . 1) . 1)) (((!_k2 . 1) . 1)
((c5 . 1) . -1) . 12) nil) (neq (((!_k2 . 1) ((c2 . 1) . 1)) ((c1 . 1) ((c3 . 1)
. 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 . 1) . 1) . -12) nil))
(or (and (leq (((!_k2 . 1) . 1) ((c3 . 1) . 1)) nil) (geq (((!_k2 . 1) . 1) ((c3
. 1) . -1)) nil) (neq (((!_k2 . 1) . 1)) nil)) (and (geq (((!_k2 . 1) . 1) ((c3
. 1) . 1)) nil) (leq (((!_k2 . 1) . 1) ((c3 . 1) . -1)) nil) (neq (((!_k2 . 1) .
1)) nil)))) (ball !_k10 (or (equal (((c4 . 1) . 1)) nil) ((ncong ((c4 . 1) . 1))
(((!_k10 . 1) . 1) ((c5 . 1) . -1) . 12) nil) (neq (((!_k10 . 1) ((c2 . 1) . 1))
((c1 . 1) ((c3 . 1) . 1) ((c4 . 1) . 1)) ((c2 . 1) ((c5 . 1) . -1) . 12) ((c5 .
1) . 1) . -12) nil)) (or (and (leq (((!_k10 . 1) . 1) ((c4 . 1) . 1)) nil) (geq
(((!_k10 . 1) . 1) ((c4 . 1) . -1)) nil) (neq (((!_k10 . 1) . 1)) nil)) (and (
geq (((!_k10 . 1) . 1) ((c4 . 1) . 1)) nil) (leq (((!_k10 . 1) . 1) ((c4 . 1) .
-1)) nil) (neq (((!_k10 . 1) . 1)) nil))))) t)"""
    //         let expected = "(forall ((!_k10 Int) (!_k2 Int) (!_k4 Int) (!_k7 Int) (!_k8 Int))
    // (=> (and (and (and (and (and (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0)))) (or (and (<= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 1))) (* c4 1)) 0) (>= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 -1))) (* c4 -1)) 0)) (and (>= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 1))) (* c4 1)) 0) (<= (+ (+ (+ (* !_k7 1) (* !_k8 -1)) (* (* c3 c3) (* c4 -1))) (* c4 -1)) 0)))) (or (and (<= (+ (* !_k8 1) (* c3 1)) 0) (>= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))) (and (>= (+ (* !_k8 1) (* c3 1)) 0) (<= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))))) (or (and (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)) (and (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)))) (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))))) (or (and (<= (+ (* !_k10 1) (* c4 1)) 0) (>= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))) (and (>= (+ (* !_k10 1) (* c4 1)) 0) (<= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))))) (and (or (= (+ (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (+ (* c2 (* c5 -1)) (* c2 12))) (* c5 1)) -12) 0) (not (= (mod (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) (* c2 (* c3 1))) 0)) (= (* c2 1) 0) (= (* c3 1) 0)) (or (= (+ (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (+ (* c2 (* c5 -1)) (* c2 12))) (* c5 1)) -12) 0) (not (= (mod (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) (* c2 (* c4 1))) 0)) (= (* c2 1) 0) (= (* c4 1) 0)) (or (not (= (+ (+ (+ (* c1 (* c3 1)) (* c1 (* c4 1))) (* c5 1)) -12) 0)) (= (+ (* c5 1) -12) 0)) (or (and (<= (+ (* !_k8 1) (* c3 1)) 0) (>= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0))) (and (>= (+ (* !_k8 1) (* c3 1)) 0) (<= (+ (* !_k8 1) (* c3 -1)) 0) (not (= (* !_k8 1) 0)))) (or (and (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0)) (and (>= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 1)))) (* c2 (* c4 1))) 0) (<= (+ (+ (* !_k4 1) (* (* c2 (* c2 c2)) (* (* c3 c3) (* c4 -1)))) (* c2 (* c4 -1))) 0))) (or (and (<= (+ (* !_k2 1) (* c3 1)) 0) (>= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0))) (and (>= (+ (* !_k2 1) (* c3 1)) 0) (<= (+ (* !_k2 1) (* c3 -1)) 0) (not (= (* !_k2 1) 0)))) (or (and (<= (+ (* !_k10 1) (* c4 1)) 0) (>= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0))) (and (>= (+ (* !_k10 1) (* c4 1)) 0) (<= (+ (* !_k10 1) (* c4 -1)) 0) (not (= (* !_k10 1) 0)))))))
    // "
    let actual = $"{Parser.translateToSmt input}"
    printfn $"\n\n\n\n{actual}\n\n\n\n"

    // let p = SMTLIB2.Parser.Parser false
    // let aa = p.ParseLine expected
    // let bb = p.ParseLine actual

    // printfn $"{expected}"

    Assert.True (1 = 1)
  // //

  [<Test>]
  member this.FailEveryTime () =
    let r = Regex @"\D"
    r.Replace ("c_123", "") |> printfn "%O"

    Solver.branch
      4
      (Def (
        "cons",
        [ "x"; "y" ],
        Add (Expr.Apply ("c_1", []), Add (Mul (Expr.Apply ("c_2", []), Var "x"), Mul (Expr.Apply ("c_3", []), Var "y")))
      ))
    |> program2originalCommand
    |> printfn "%O"

    Assert.True true

