(*
  Parser for lambda-calculus.
*)

open Utils
open Lexer


(* AST for lambda expressions - DO NOT MODIFY THIS TYPE *)
type term = | Variable of string
	    | Abstraction of string * term
	    | Application of term * term

(*
  Concrete Syntax:
  t ::= id | (\id.t) | (t1 t2) | (t) | let id=t1 in t2

  Abstract Syntax:
  term ::= id | \id.term | term1 term2
*)

exception SyntaxError of string

(*
  ADD FUNCTIONS BELOW
*)


let rec parse_term = function 
	| Literal id :: termList -> Variable id , termList
	| LParen :: LambdaTok :: Literal id :: DotTok :: ts	-> let (tr, tl) = parse_term ts in(							
        match tl with
        | [] -> raise (SyntaxError "Error: expected right parenthesis\n")
        | RParen :: termList -> Abstraction(id ,tr), termList
        | _ -> raise (SyntaxError "Error: expected right parenthesis\n")
    )
	| LParen :: tr -> let (h, ts) = parse_term tr in(
		match ts with
		| [] -> raise (SyntaxError "Error: expected right parenthesis\n")
		| RParen :: ts' -> h, ts'
		| _ -> let (h', ts'') = parse_term ts in(
            match ts'' with
			| [] -> raise (SyntaxError "Error: expected right parenthesis\n")
			| RParen :: termList -> Application(h,h'), termList
			| _ -> raise (SyntaxError "Error: expected right parenthesis\n")
		)
	)
	| LetTok :: Literal id :: EqTok :: ts -> let (tr, ts') = parse_term ts in(
        match ts' with
        | [] -> raise (SyntaxError "Error: expected 'In' token\n")
        | InTok :: ts'' -> let (trr, termList) = parse_term ts'' in(
            match termList with
            | _ -> Application((Abstraction (id, trr)),tr), termList
        )
        | _ -> raise (SyntaxError "Error: expected 'In' token\n")
    )
	| _ -> print_string("parse_term");raise (SyntaxError "Error: Not a Valid Term")


let parse str = 
	let (tr, tl) = str |> string_to_list |> tokenize |> parse_term in(
		match tl with
		| [] -> tr
		| _ -> raise (SyntaxError "Error: unexpected input")
	)


let rec format_term = function 
	| Variable id -> id
	| Abstraction (id, tr) -> "(\\" ^ id ^ "." ^ (format_term tr) ^ ")"
	| Application (tr1, tr2) -> "(" ^ (format_term tr1) ^ " " ^ (format_term tr2) ^ ")"