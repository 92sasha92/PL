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
	| Literal x :: termList -> Variable x , termList
	| LParen :: LambdaTok :: Literal x :: DotTok :: ts	-> let (tr, tl) = parse_term ts in(							
        match tl with
        | [] -> raise (SyntaxError "Error: expected right paren\n")
        | RParen :: termList -> Abstraction(x ,tr), termList
        | _ -> raise (SyntaxError "Error: expected right paren\n")
    )
	| LParen :: tr -> let (t1, ts) = parse_term tr in(
		match ts with
		| [] -> raise (SyntaxError "Error: expected right paren\n")
		| RParen :: ts' -> t1, ts'
		| _ -> let (t2, ts'') = parse_term ts in(
            match ts'' with
			| [] -> raise (SyntaxError "Error: expected right paren\n")
			| RParen :: termList -> Application(t1, t2), termList
			| _ -> raise (SyntaxError "Error: expected right paren\n")
		)
	)
	| LetTok :: Literal x :: EqTok :: ts -> let (tr, ts') = parse_term ts in(
        match ts' with
        | [] -> raise (SyntaxError "Error: expected 'In' token\n")
        | InTok :: ts'' -> let (t, termList) = parse_term ts'' in(
            match termList with
            | _ -> Application((Abstraction (x, t)), tr), termList
        )
        | _ -> raise (SyntaxError "Error: expected 'In' token\n")
    )
	| _ -> print_string("parse_term");raise (SyntaxError "Error: not a Valid Term")


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





let rec format_term_conv = function 
	| Variable x -> x
	| Abstraction (x, t) -> "\\" ^ x ^ "." ^ (format_term_conv t)
	| Application (t1, t2) -> 
	( match t1 with 
		| Abstraction (x, tr) -> "(" ^ (format_term_conv t1) ^ ")"
		| Variable x -> format_term_conv t1
		| Application (tr1, tr2) ->
			match tr2 with
			| Abstraction (x1, tr3) ->  "(" ^ (format_term_conv t1) ^ ")"
			| _ -> format_term_conv t1
	) ^ " " ^
	( match t2 with 
		| Application (tr1, tr2) -> "(" ^ (format_term_conv t2) ^ ")"
		| Variable v -> v
		| Abstraction (x, tr) -> format_term_conv t2
	)

let rec parse_term_conv_rec (pr :term option) r =
	match r with
	| []->  (match pr with 
		| None ->  raise (SyntaxError "Error: not a Valid Term")
		| Some term ->  term,r
		)
	| InTok::tl->  (match pr with 
		| None ->  raise (SyntaxError "Error: not a Valid Term")
		| Some term ->  term,r
		)
	| RParen::tl->  (match pr with 
		| None -> raise (SyntaxError "Error: not a Valid Term")
		| Some term ->  term,r
		)
	| Literal x :: termList -> 
		(match pr with 
		| None-> parse_term_conv_rec (Some (Variable x))  termList
		| Some term -> parse_term_conv_rec (Some (Application(term, Variable(x)))) termList
		)	
	| LParen :: tl ->  let (term, tl') = parse_term_conv_rec None tl in(
		 match tl' with
		| [] -> raise (SyntaxError "Error: expected right paren\n")
		| RParen :: tl'' -> 
			(match pr with
			| None->  parse_term_conv_rec (Some(term)) tl''
			| Some term' -> parse_term_conv_rec (Some(Application(term',term))) tl''
			)
		| _ -> let (term'', tl'') = parse_term_conv_rec (Some(term)) tl' in(
			match tl'' with
			| [] -> raise (SyntaxError "Error: expected right paren\n")
			| RParen :: tl''' -> 
				(match pr with
				| None-> parse_term_conv_rec (Some(term'')) tl'''
				| Some term''' -> parse_term_conv_rec (Some(Application(term''',term''))) tl'''
				)
			| _ -> raise (SyntaxError "Error: expected right paren\n")
		)
	)
	| LambdaTok :: Literal id :: DotTok :: tl	-> let (term, tl') = parse_term_conv_rec None tl in( 
		match tl' with
		| [] ->
			(match pr with
			| None -> parse_term_conv_rec (Some (Abstraction(id, term))) tl'
			| Some term' -> parse_term_conv_rec (Some (Application(term', Abstraction(id, term)))) tl'
			)
		| RParen :: tl'' ->
			(match pr with
			| None -> parse_term_conv_rec (Some (Abstraction(id, term))) tl'
			| Some term' -> parse_term_conv_rec (Some (Application(term', Abstraction(id, term)))) tl'
			)
		| InTok:: tl'' ->
			(match pr with
			| None -> parse_term_conv_rec (Some (Abstraction(id, term))) tl'
			| Some term' -> parse_term_conv_rec (Some (Application(term', Abstraction(id, term)))) tl'
			)
		| _ -> raise (SyntaxError "Error: not a Valid Term")
	)
	| LetTok :: Literal id :: EqTok :: tl ->  let (term, tl') = parse_term_conv_rec None tl in(
        match tl' with
        | [] -> raise (SyntaxError "Error: expected 'In' token\n")
        | InTok :: tl'' -> let (term', tl''') = parse_term_conv_rec None tl'' in(
            match tl''' with
            | _ -> parse_term_conv_rec (Some (Application((Abstraction (id, term')), term))) tl'''
        )
        | _ -> raise (SyntaxError "Error: expected 'In' token\n")
    )
	| _ -> raise (SyntaxError "Error: not a Valid Term")

let rec parse_term_conv tl = parse_term_conv_rec None tl

let parse_conv str = 
	let (term, tail) = str |> string_to_list |> tokenize |> parse_term_conv in(
		match tail with
		| [] -> term
		| _ -> raise (SyntaxError "Error: unexpected input")
	)