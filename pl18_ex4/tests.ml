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


let test_and_1 = "
let tru = (\\t.(\\f.t)) in
let fls = (\\t.(\\f.f)) in
let and = (\\b.(\\c. ((b c) fls))) in
((and tru) tru)
"

let test_and_2 = "
let tru = (\\t.(\\f.t)) in
let fls = (\\t.(\\f.f)) in
let and = (\\b.(\\c. ((b c) fls))) in
((and fls) ((and tru) tru))
"

let env = "
let tru = (\\t. (\\f. t)) in
let fls = (\\t. (\\f. f)) in
let test = (\\l. (\\m. (\\n. ((l m) n)))) in
let and = (\\b. (\\c.  ((b c) fls))) in

let pair = (\\f. (\\s. (\\b.  ((b f) s)))) in
let fst = (\\p. (p tru)) in
let snd = (\\p. (p fls)) in

let c0 = (\\s. (\\z. z)) in
let c1 = (\\s. (\\z. (s z))) in
let c2 = (\\s. (\\z. (s (s z)))) in
let c3 = (\\s. (\\z. (s (s (s z))))) in
let c4 = (\\s. (\\z. (s (s (s (s z)))))) in
let c5 = (\\s. (\\z. (s (s (s (s (s z))))))) in
let c6 = (\\s. (\\z. (s (s (s (s (s (s z)))))))) in
let c7 = (\\s. (\\z. (s (s (s (s (s (s (s z))))))))) in
let c8 = (\\s. (\\z. (s (s (s (s (s (s (s (s z)))))))))) in
let c9 = (\\s. (\\z. (s (s (s (s (s (s (s (s (s z))))))))))) in
let c10 = (\\s. (\\z. (s (s (s (s (s (s (s (s (s (s z)))))))))))) in

let scc = (\\n. (\\s. (\\z. (s ((n s) z))))) in
let plus = (\\m. (\\n. (\\s. (\\z. ((m s) ((n s) z)))))) in
let times = (\\m. (\\n. (\\s. (m (n s))))) in
let power = (\\m. (\\n. (n m))) in
let iszero = (\\m. ((m (\\x. fls)) tru)) in
let prd = (let zz = ((pair c0) c0) in
           let ss = (\\p. ((pair (snd p)) ((plus c1) (snd p)))) in
           (\\m. (fst ((m ss) zz)))) in
let leq = (\\m. (\\n. (iszero ((n prd) m)))) in
let equal = (\\m. (\\n. ((and ((leq m) n)) ((leq n) m)))) in

let Y = (\\f. ((\\x. (f (x x))) (\\x. (f (x x))))) in
let Z = (\\f. ((\\x. (f (\\y. ((x x) y)))) (\\x. (f (\\y. ((x x) y)))))) in
"

let test_fact_l = env ^ "
let fact_l = (Y (\\f. (\\n. (((test (iszero n)) c1) (((times n) (f (prd n)))))))) in
((equal (fact_l c2)) c2)
"

let test_fact_s = env ^ "
let fact_s = (Z (\\f. (\\n. ((((test (iszero n)) (\\x. c1)) (\\x. (((times n) (f (prd n)))))) (\\x.x))))) in
((equal (fact_s c2)) c2)
"
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

let s3 = "
let tru = (\\t.(\\f.t)) in
let fls = (\\t.(\\f.f)) in
let and = (\\b.(\\c. ((b c) fls))) in
 and fls tru
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
  
let test ~verbose ~sem ~reduce s =
  printf "\nEvaluating:\n%s\nin %s semantics:\n\n" s sem;
  let result = (evaluate ~verbose reduce (parse s)) in
  printf "Result is: %s\n\n" (format_term result)

let test_lazy = test ~sem:"lazy" ~reduce:reduce_lazy
let test_strict = test ~sem:"strict" ~reduce:reduce_strict
let test_normal = test ~sem:"normal-order" ~reduce:reduce_normal
let test_all ~verbose s =
  test_lazy ~verbose s;
  test_strict ~verbose s;
  test_normal ~verbose s


let () =
  test_all ~verbose:true test_and_1;
  test_all ~verbose:true test_and_2;

  test_lazy ~verbose:false test_fact_l;
  test_strict ~verbose:false test_fact_s;
  test_normal ~verbose:false test_fact_l;
  test_normal ~verbose:false test_fact_s;

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
  printf "\n\nEvaluating:\n%s\nin normal-order semantics:\n\n";
  ignore (evaluate ~verbose:true reduce_normal (parse_conv s3));

  
  print_eval_tests test2;
  print_eval_tests test3;

  print_eval_tests scc_c0;
  print_eval_tests test4;
  print_eval_tests test1;
  print_eval_tests test5;
  print_eval_tests testQ1;
