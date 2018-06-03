(*
  Tests for the lambda calculus parser and reducers.

  EXTEND THIS FILE TO TEST YOUR SOLUTION THOROUGHLY!
*)

open Utils
open Parser
open Reducer


let rec evaluate ~verbose reduce t =
  if verbose then print_string (format_term t) else ();
  match reduce t with
  | None -> 
    if verbose then print_string " =/=>\n\n" else ();
    t
  | Some t' -> 
    if verbose then print_string " ==>\n\n" else ();
    evaluate ~verbose reduce t'


let s1 = "
let tru = (\\t.(\\f.t)) in
let fls = (\\t.(\\f.f)) in
let and = (\\b.(\\c. ((b c) fls))) in
((and tru) tru)
"


let s2 = "
let tru = (\\t.(\\f.t)) in
let fls = (\\t.(\\f.f)) in
let and = (\\b.(\\c. ((b c) fls))) in
((and fls) tru)
"

let c0 = "(\\s. (\\z. z))"

let scc = "(\\n. (\\s. (\\z. (s ((n s) z) ) ) ) ) " 

let scc_c0 = "(" ^ scc ^ c0 ^ ")"


let test1 = "((\\x.x) t)"

let test2 = "(\\x. ((\\y.y) t))"

let test3 = "((\\x. ((\\y.y) t)) b)"

let test4 = "(x ((\\y.y) t))"

let test5 = "(\\x. ((\\y. y) t))"

let testQ1 = "let x = ((\\x. x) t) in ((\\y. y) (\\z. x))"

let test_no_fv = "((\\x.x) (\\y.y))"

let trying = parse("y")

let print_eval_tests str =
  printf "\nEvaluating:\n%s\nin lazy semantics:\n\n" str;
  ignore (evaluate ~verbose:true reduce_lazy (parse str));
  printf "\n\nEvaluating:\n%s\nin strict semantics:\n\n" str;
  ignore (evaluate ~verbose:true reduce_strict (parse str));
  printf "\n\nEvaluating:\n%s\nin normal-order semantics:\n\n" str;
  ignore (evaluate ~verbose:true reduce_normal (parse str))

let rec print_term = function
  | Variable id -> "Variable(" ^ id ^ ")"
  | Abstraction (a,b) -> "Abs(" ^ a ^ ", " ^ print_term b ^ ")"
  | Application (a,b) -> "App(" ^ print_term a ^ ", " ^ print_term b ^ ")"


let print_fv str =
  printf "FV for %s:\n" str ;
  print_string_set (fv (parse str))

let print_fresh_var str =
  printf "Generating fresh var for %s: " str ;
  printf "%s\n" (fresh_var (fv (parse str)))

let rec print_lst = function
  | [] -> printf "\n"
  | hd::rst -> printf "hd "; print_lst rst

let () = 
  printf "\n##### Testing Question 1:\n";
  printf "Parsing string: %s:\n" testQ1;
  printf "%s\n" (print_term (parse testQ1));
  printf "Reformating term to string format:\n";
  printf "%s\n\n" (format_term (parse testQ1));

  printf "Parsing string: %s:\n" s1;
  printf "%s\n" (print_term (parse s1));
  printf "Reformating term to string format:\n";
  printf "%s\n\n" (format_term (parse s1));

  printf "\n##### Testing Question 2:\n";
  print_fv test1;  
  print_fv test3;  
  print_fv test_no_fv;

  printf "\n##### Testing Question 3:\n";
  print_fresh_var test3;
  print_fresh_var "a";
  print_fresh_var "(a b)";
  (*printf "Checking correct out of vars exception:\n";
  printf "%s\n" (fresh_var (string_set_from_list possible_variables));*)

  printf "\n##### Testing Question 4:\n";
  printf "%s\n" (format_term (substitute "x" trying (parse(test1))));
  printf "%s\n" (format_term (substitute "x" (Abstraction ("x",(Application ((Variable "x"),(Variable "y"))))) (Abstraction ("y",(Variable "x")))  ));
  printf "%s\n" (format_term (substitute "x" (Variable "y") (Application ((Variable "x"), (Variable "x"))) ));

  printf "\n##### Testing Evaluation Semantics:\n";
  printf "\nEvaluating:\n%s\nin lazy semantics:\n\n" s1;
  ignore (evaluate ~verbose:true reduce_lazy (parse s1));
  printf "\n\nEvaluating:\n%s\nin strict semantics:\n\n" s2;
  ignore (evaluate ~verbose:true reduce_strict (parse s2));
  printf "\n\nEvaluating:\n%s\nin normal-order semantics:\n\n" s2;
  ignore (evaluate ~verbose:true reduce_normal (parse s2));


  print_eval_tests test2;
  print_eval_tests test3;

  print_eval_tests scc_c0;
  print_eval_tests test4;
  print_eval_tests test1;
  print_eval_tests test5;
  print_eval_tests testQ1;
