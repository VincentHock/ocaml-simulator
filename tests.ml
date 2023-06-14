open Expr;;
open Evaluation ;;
open CS51Utils ;;
open Absbook;;

let empty = vars_of_list [];;
let xy = vars_of_list ["x"; "y"] ;;
let y = vars_of_list ["y"] ;;
let x = vars_of_list ["x"] ;;

let free_vars_tests () =
  unit_test (same_vars (free_vars (Num(3))) empty) "integer" ;
  unit_test (same_vars (free_vars (Var("x"))) x) "variable" ;
  unit_test (same_vars (free_vars (Binop (Plus, Var("x"), Var("y")))) xy) "binop" ;
  unit_test (same_vars (free_vars (Fun("z", Binop(Plus, Binop(Minus, Binop(Plus, Var("x"), Var("y")), Num(3)), Var("z"))))) xy) "function" ;
  unit_test (same_vars (free_vars (Let("x", Num(3), Binop(Plus, Var("x"), Var("y"))))) y) "binding" ;
  unit_test (same_vars (free_vars (Let("x", Binop(Plus, Var("x"), Num(3)), Var("x")))) x) "binding using variables with same name" ;;

let subst_tests () =
  unit_test (subst "x" (Var "y") (Num(3)) = Num(3)) "constant" ;
  unit_test (subst "x" (Var "y") (Var("x")) = Var("y")) "variable sub" ;
  unit_test (subst "y" (Var "z") (Var("x")) = Var("x")) "variable nosub" ;
  unit_test (subst "x" (Var "y") (Binop(Plus, Var("x"), Var("y"))) = Binop(Plus, Var("y"), Var("y"))) "binop sub" ;
  unit_test (subst "x" (Var "y") (Fun("x", Binop(Plus, Var("x"), Var("y")))) = (Fun ("x", Binop(Plus, Var("x"), Var("y"))))) "fun sub" ;;

let eenv = Env.empty () ;;
let xenv = Env.extend eenv "x" (ref (Env.Val (Num 5)));;

let eval_tests evaluator = 
  unit_test (evaluator (Num 5) eenv = Env.Val (Num 5)) "eval constant";
  unit_test (evaluator (Let("x", Num(5), Var("x"))) eenv = Env.Val (Num 5)) "let";
  unit_test (evaluator (App(Fun("x", Binop(Times, Num(2), Var("x"))), Num(5))) eenv = Env.Val (Num 10)) "app";
  unit_test (evaluator (Let("x", Num(5), Conditional(Binop(Equals, Var("x"), Num(0)), Var("x"), Binop(Plus, Var("x"), Var("x"))))) eenv = Env.Val (Num 10)) "conditional";
  unit_test (evaluator (Fun("x", Binop(Plus, Var("x"), Num(1)))) eenv = Env.Val (Fun("x", Binop(Plus, Var("x"), Num(1))))) "function";;

let dyn_lex_tests () = 
  unit_test (eval_l (Letrec("f", Fun("n", Conditional(Binop(Equals, Var("n"), Num(0)), Num(1), Binop(Times, Var("n"), App(Var("f"), Binop(Minus, Var("n"), Num(1)))))), App(Var("f"), Num(4)))) eenv = Env.Val (Num 24)) "letrec dyn" ;
  unit_test (eval_d (Letrec("f", Fun("n", Conditional(Binop(Equals, Var("n"), Num(0)), Num(1), Binop(Times, Var("n"), App(Var("f"), Binop(Minus, Var("n"), Num(1)))))), App(Var("f"), Num(4)))) eenv = Env.Val (Num 24)) "letrec lex" ;;
;;

let tests () =
  free_vars_tests () ;
  subst_tests () ;
  eval_tests eval_s ;
  eval_tests eval_l ;
  eval_tests eval_d ;
  dyn_lex_tests () ;;

let _ = tests () ;;