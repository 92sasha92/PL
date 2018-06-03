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
	| Literal id :: tr -> Variable id , tr
	| LParen :: LambdaTok :: Literal id :: DotTok :: ts	-> let (tr, ts') = parse_term ts in(							
        match ts' with
        | [] -> raise (SyntaxError "Error: expected right parenthesis\n")
        | RParen :: ts'' -> Abstraction(id ,tr), ts''
        | _ -> raise (SyntaxError "Error: expected right parenthesis\n")
    )
	| LParen :: tr -> let (h, ts) = parse_term tr in(
		match ts with
		| [] -> raise (SyntaxError "Right-parenthesis expected\n")
		| RParen :: ts' -> h, ts'
		| _ -> let (h', ts'') = parse_term ts in(
            match ts'' with
			| [] -> raise (SyntaxError "Error: expected right parenthesis\n")
			| RParen :: ts''' -> Application(h,h'), ts'''
			| _ -> raise (SyntaxError "Error: expected right parenthesis\n")
		)
	)
	| LetTok :: Literal id :: EqTok :: ts -> let (tr, ts') = parse_term ts in(
        match ts' with
        | [] -> raise (SyntaxError "'In' expected\n")
        | InTok :: ts'' -> let (trr, ts''') = parse_term ts'' in(
            match ts''' with
            | _ -> Application((Abstraction (id, trr)),tr), ts'''
        )
        | _ -> raise (SyntaxError "'In' expected\n")
    )
	| _ -> print_string("parse_term");raise (SyntaxError "Not a Valid Term")

    
let parse str = 
	let (tr, arr) = parse_term (tokenize (string_to_list str))in(
		match arr with
		| [] -> tr
		| _ -> raise (SyntaxError "Error: string has more then one term")
	)

                        
let rec format_term = function 
	| Variable id -> id
	| Abstraction (id, tr) -> "(\\" ^ id ^ "." ^ (format_term tr) ^ ")"
	| Application (trr, trrr) -> "(" ^ (format_term trr) ^ " " ^ (format_term trrr) ^ ")"

let rec format_term_conv = function 
	| Variable id -> id
	| Abstraction (id, tr) -> "\\" ^ id ^ "." ^ (format_term_conv tr)
	| Application (trr, trrr) -> 
	( match trr with 
		| Abstraction (id, tr) -> "("^(format_term_conv trr) ^ ")"
		| Variable id  -> format_term_conv trr
		| Application (trr', trrr'') -> (*if rhs is abstraction, encapsulate it*) 
			match trrr'' with
			| Abstraction (id'', t'') ->  "("^(format_term_conv trr) ^ ")"
			| _-> format_term_conv trr
	) ^ " "^
	( 
		match trrr with 
		| Application (trr', trrr'') -> "("^(format_term_conv trrr)^")"
		| Variable id  -> id
		| Abstraction (id, tr) -> format_term_conv trrr
	)

let rec parse_term_conv' (acc :term option) tl0 =
	match tl0 with
	| []->  (match acc with 
		| None ->  raise (SyntaxError "Not a Valid Term")
		| Some tr' ->   tr',tl0
		)
	| RParen::tl->  (match acc with 
		| None -> raise (SyntaxError "Not a Valid Term")
		| Some tr' ->  tr',tl0
		)
	|InTok::tl->  (match acc with 
		| None ->  raise (SyntaxError "Not a Valid Term")
		| Some tr' ->  tr',tl0
		)
	| Literal id :: tl -> 
		(match acc with 
		| None->   parse_term_conv' (Some (Variable id))  tl
		| Some tr' ->  parse_term_conv' (Some(Application(tr',Variable(id)))) tl
		)	
	
	(*if starting left parenthesis*)
	(*parse the first term in the parenthesis*)
	| LParen :: tl ->  let (tr', tl') = parse_term_conv' None tl in(
		 match tl' with (*check what's left after first term... options are: RParen or another term(s) and then RParen*)
		| [] -> raise (SyntaxError "Right-parenthesis expected\n")
		| RParen :: tl'' -> 
			(match acc with (*apply the accumulated abstraction if there is one*)
			|None->  parse_term_conv' (Some(tr')) tl''
			|Some tr'' -> parse_term_conv' (Some(Application(tr'',tr'))) tl''
			)
		(*find all next terms <recursively> until orphan RParen is encountered*)
		| _ -> let (tr''', tl'') = parse_term_conv' (Some(tr')) tl' in(
			match tl'' with
			| [] -> raise (SyntaxError "Error: expected right parenthesis\n")
			(*found the expected RParen, now apply the accumulated abstraction on the content of the parenthesis*)
			| RParen :: tl''' -> 
				(match acc with
				|None-> parse_term_conv' (Some(tr''')) tl'''
				|Some tr'''' -> parse_term_conv' (Some(Application(tr'''',tr'''))) tl'''
				)
			| _ -> raise (SyntaxError "Error: expected right parenthesis\n")
		)
	)
	(*abstraction without parenthesis... until next orphan RParen or end of list*)
	| LambdaTok :: Literal id :: DotTok :: tl	-> let (tr', tl') = parse_term_conv' None tl in( 
		match tl' with
		| [] ->
			(match acc with
			|None -> parse_term_conv' (Some(Abstraction(id ,tr'))) tl'
			|Some tr'' -> parse_term_conv' (Some(Application(tr'',Abstraction(id ,tr')))) tl'
			)
		| RParen :: tl'' ->
			(match acc with
			|None -> parse_term_conv' (Some(Abstraction(id ,tr'))) tl'
			|Some tr'' -> parse_term_conv' (Some(Application(tr'',Abstraction(id ,tr')))) tl'
			)
		| InTok:: tl'' ->
			(match acc with
			|None -> parse_term_conv' (Some(Abstraction(id ,tr'))) tl'
			|Some tr'' -> parse_term_conv' (Some(Application(tr'',Abstraction(id ,tr')))) tl'
			)
		| _ -> raise (SyntaxError "Not a Valid Term")
	)
	| LetTok :: Literal id :: EqTok :: tl ->  let (tr', tl') = parse_term_conv' None tl in(
        match tl' with
        | [] -> raise (SyntaxError "'In' expected\n")
        | InTok :: tl'' -> let (tr'', tl''') = parse_term_conv' None tl'' in(
            match tl''' with
            | _ -> parse_term_conv' (Some(Application((Abstraction (id, tr'')),tr'))) tl'''
        )
        | _ -> raise (SyntaxError "'In' expected\n")
    )
	
	| _ -> raise (SyntaxError "Not a Valid Term")

let rec parse_term_conv tl =parse_term_conv' None tl

let parse_conv str = 
	let (tr, arr) = parse_term_conv (tokenize (string_to_list str))in(
		match arr with
		| [] -> tr
		| _ -> raise (SyntaxError "Error: string has more then one term")
	)

