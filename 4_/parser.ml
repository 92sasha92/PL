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

let rec parse_term = function
 | (Literal id)::tl -> (Variable id),tl
 | LParen::LambdaTok::(Literal id)::DotTok::tl -> let (term, tl') = parse_term tl in (
		    match tl' with
		    | [] -> raise (SyntaxError "Right-parenthesis expected\n")
		    | RParen::tl'' -> (Abstraction (id,term)),tl''
		    | _ -> raise (SyntaxError "Upexpected token\n")
)
 | LParen::tl -> let (term1, tail1) = parse_term tl in(
                    match tail1 with
                    | [] -> raise (SyntaxError "Right-parenthesis expected\n")
		    | RParen::tl' -> term1, tl'
		    | _ -> let (term2, tail2) = parse_term tail1 in(
		            match tail2 with
			    |[] -> raise (SyntaxError "Right-parenthesis expected\n")
			    | RParen :: tl'' -> (Application (term1,term2)),tl'' 
			    | _ -> raise (SyntaxError "Right-parenthesis expected\n")
		    )
)
 | LetTok::(Literal id)::EqTok::tl -> let (term1, tail1) = parse_term tl in(
                    match tail1 with
                    | [] -> raise (SyntaxError "More tokens expected\n")
		    | InTok::tl' -> let (term2, tail2) = parse_term tl' in(
                                    match tail2 with
                                    | [] -> (Application ((Abstraction (id,term2)),term1)),[]
				    | _ -> raise (SyntaxError "To many tokens\n") 
                    )
		    | _ -> raise (SyntaxError "In token expected\n")
)
 | _ -> raise (SyntaxError "Unexpected token\n")

let parse str = 
         let (term, tl) =
		str |> string_to_list |> tokenize |> parse_term
         in
	 match tl with
	 | [] -> term
 	 | _ -> raise (SyntaxError "Unexpected input.\n")


let rec format_term = function
  |Variable v -> v
  |Abstraction (str, term) -> let s = format_term term in
                               "(\\" ^ str ^ "." ^ s ^ ")"
  |Application (term1, term2) -> let s1 = format_term term1 in
		                 let s2 = format_term term2 in
                                 "(" ^ s1 ^ " " ^ s2 ^ ")"

