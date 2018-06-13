(*
  Reducers (interpreters) for lambda-calculus.
*)

open Utils
open Parser


exception OutOfVariablesError


let possible_variables = List.map (fun x -> char_to_string (char_of_int x)) ((range 97 123) @ (range 65 91))



(*
  ADD FUNCTIONS BELOW
*)

let rec fv = function
  | Variable v -> StringSet.singleton v
  | Abstraction (v, term) -> StringSet.remove v (fv term)
  | Application (term1, term2) -> StringSet.union (fv term1) (fv term2)



let fresh_var vset =
  let rec fresh_rec vset lst =
      match lst with
      | [] -> raise OutOfVariablesError
      | (head:string)::tail -> if StringSet.mem head vset then fresh_rec vset tail
                   else head 
  in fresh_rec vset possible_variables

  let rec substitute (x:string) s t2 =
  match t2 with
  | Variable y when y = x -> s
  | Variable y -> Variable y
  | Application (term1, term2) -> Application ((substitute x s term1), (substitute x s term2))
  | Abstraction (y, term) when y = x -> Abstraction (x, term)
  | Abstraction (y, term) -> let fv_s = fv s in(
                            if StringSet.mem y fv_s then( 
                               let fv_term = fv term in
                               let vset = StringSet.add x (StringSet.union fv_s fv_term) in
                               let z = fresh_var vset
			       in Abstraction (z, (substitute x s (substitute y (Variable z) term)))    
			    )
			    else Abstraction (y, (substitute x s term))
			   
  )

let rec reduce_strict term= 
	match term with
	| Variable id ->  None
	| Abstraction (id, tr) ->  None
	| Application (tr1, tr2) -> 
		let tro1 = reduce_strict tr1 in 
		match tro1 with
		| Some tr3 -> Some (Application(tr3,tr2))
		| None ->  let tro2 = reduce_strict tr2 in 
			match tro2 with
			| Some tr3 -> Some(Application(tr1,tr3))
			| None ->  match tr1 with
				| Variable id ->None
				| Application (tr1, tr2)  -> None
				| Abstraction (id, tr) ->  Some(substitute id tr2 tr) 



let rec reduce_lazy = function
  | Variable v -> None
  | Abstraction (x, term) -> None
  | Application ((Abstraction (x, term1)), term2) ->  Some (substitute x term2 term1)
  | Application (t1, t2) -> let t13 = reduce_lazy t1 in(
    match t13 with
			| None -> None
            | Some t14 -> Some (Application (t14, t2)) 
  )



let rec reduce_normal = function
  | Variable v -> None
  | Abstraction (x, t) -> let t1 = reduce_normal t in (
    match t1 with
      | None -> None
      | Some term -> Some (Abstraction(x, term))
  )
  | Application (t1, t2) -> match t1 with
    | Abstraction (x, t) ->  Some (substitute x t2 t)
    | _ -> let t13 = reduce_normal t1 in (
      match t13 with
        | Some term1 -> Some (Application (term1, t2))
        | None -> let term2 = reduce_normal t2 in (
          match term2 with
            | Some term -> Some (Application(t1, term))
            | None -> None
        )
    )