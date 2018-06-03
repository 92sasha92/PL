(*
  Reducers (interpreters) for lambda-calculus.
*)

open Utils
open Parser


exception OutOfVariablesError


let possible_variables = List.map (fun x -> char_to_string (char_of_int x)) ((range 97 123) @ (range 65 91))


let rec fv = function
	| Variable id -> StringSet.singleton id
	| Abstraction (id, t) -> StringSet.remove id (fv t)
	| Application (t1, t2) -> StringSet.union (fv t1) (fv t2)

    
let fresh_var used : string = 
	if StringSet.is_empty (StringSet.diff (string_set_from_list(possible_variables)) used) 
	then raise (OutOfVariablesError)
	else StringSet.choose (StringSet.diff (string_set_from_list(possible_variables)) used)
    
    
let rec substitute (str : string) t1 t2 =
    match t2 with
	| Variable id when id = str -> t1
	| Variable id when id != str -> Variable id
	| Application(s1, s2) -> Application ((substitute str t1 s1), (substitute str t1 s2))
	| Abstraction (id, tr) when id = str -> Abstraction (id, tr)
	| Abstraction (id, tr) when ((id != str) && not(StringSet.mem id (fv t1))) -> Abstraction(id, substitute str t1 tr)
	| Abstraction (id, tr) when ((id != str) && StringSet.mem id (fv t1)) -> let new_var =
        fresh_var (StringSet.union (StringSet.union (fv tr) (fv t1)) (StringSet.singleton str)) in(
            Abstraction(new_var	, substitute str t1 (substitute id (Variable new_var )  tr))
        )
    (*avoid warnings*)
	| _ -> raise OutOfVariablesError
	
let rec reduce_strict term= 
	match term with
	| Variable id ->  None
	| Abstraction (id, tr) ->  None
	| Application (tr1, tr2) -> 
		let tro1= reduce_strict tr1 in 
		match tro1 with
		| Some tr' -> Some (Application(tr',tr2))
		| None ->  let tro2 = reduce_strict tr2 in 
			match tro2 with
			(*rhs has been reduced*)
			| Some tr' -> Some(Application(tr1,tr'))
			(*Nothing to do in both sides... perform abstraction*)
			| None ->  match tr1 with
				| Variable id ->None
				| Application (tr1, tr2)  -> None
				| Abstraction (id, tr) ->  Some(substitute id tr2 tr) 
			
let rec reduce_lazy term= 
	match term with
	| Variable id -> None
	| Abstraction (id, tr) -> None
	| Application (tr1, tr2) -> 
		
		let tro1= reduce_lazy tr1 in 
		match tro1 with
		| Some tr' ->Some (Application(tr',tr2))
		| None ->  match tr1 with
				| Abstraction (id, tr) ->   Some(substitute id tr2 tr) 
				| _->None

let rec reduce_normal term= 
	match term with
	| Variable id -> None
	| Application (tr1, tr2) -> (
		match tr1 with
		| Abstraction(id ,tr')-> Some(substitute id tr2 tr')
		| _->  let tro1= reduce_normal tr1 in 
			match tro1 with
			| Some tr' -> Some (Application(tr',tr2))
			| None ->  let tro2 = reduce_normal tr2 in 
				match tro2 with
				| Some tr' -> Some(Application(tr1,tr')) (*rhs has been reduced*)
				| None ->  None (*Nothing to do in both sides... and no abstraction at rhs (known from earlier) *)
		
	)
	| Abstraction (id, tr) ->   let tro = reduce_normal tr in 
		match tro with
		|None ->None
		|Some (tr') -> Some(Abstraction(id,tr'))
