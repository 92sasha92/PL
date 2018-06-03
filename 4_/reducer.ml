(*
  Reducers (interpreters) for lambda-calculus.
*)

open Utils
open Parser


exception OutOfVariablesError


let possible_variables = List.map (fun x -> char_to_string (char_of_int x)) ((range 97 123) @ (range 65 91))


let rec fv = function
  |Variable v -> StringSet.singleton v
  |Abstraction (str, term) -> StringSet.remove str (fv term)
  |Application (term1, term2) -> StringSet.union (fv term1) (fv term2)

let fresh_var vset =
  let rec fresh_rec vset lst =
      match lst with
      |[] -> raise OutOfVariablesError
      |(hd:string)::tail -> if StringSet.mem hd vset then fresh_rec vset tail
                   else hd 
  in fresh_rec vset possible_variables

let rec substitute (x:string) t1 t2 =
  match t2 with
  |Variable y when x = y -> t1
  |Variable y -> Variable y
  |Application (term1, term2) -> Application ((substitute x t1 term1), (substitute x t1 term2))
  |Abstraction (y, term) when x = y -> Abstraction (x, term)
  |Abstraction (y, term) -> let fv_t1 = fv t1 in(
                            if StringSet.mem y fv_t1 then( 
                               let fv_term = fv term in
                               let vset = StringSet.add x (StringSet.union fv_t1 fv_term) in
                               let z = fresh_var vset
			       in Abstraction (z, (substitute x t1 (substitute y (Variable z) term)))    
			    )
			    else Abstraction (y, (substitute x t1 term))
			   
  )

let rec reduce_strict = function 
  | Variable v -> None
  | Abstraction (x, t) -> None
  | Application ((Abstraction (x, term1)),(Abstraction (y, term2))) -> 
                 Some (substitute x (Abstraction (y, term2)) term1)
  | Application ((Abstraction (x, term1)), t2) ->  let t2'' = reduce_strict t2 in (
    match t2'' with
			| None -> None
			| Some t2' -> Some (Application ((Abstraction (x, term1)), t2'))
  )
  | Application (t1, t2) -> let t1'' = reduce_strict t1 in(
    match t1'' with
			| None -> None
      | Some t1' -> Some (Application (t1', t2)) )


let rec reduce_lazy = function
  | Variable v -> None
  | Abstraction (x, t) -> None
  | Application (t1, t2) -> match t1 with
    | Abstraction (x, term1) ->  Some (substitute x t2 term1)
		| _ -> let t1'' = reduce_lazy t1 in (
      match t1'' with
				|None -> None
        |Some t1' -> Some (Application (t1', t2))
    )



let rec reduce_normal = function
  | Variable v -> None
  | Abstraction (x, t) -> let t' = reduce_normal t in (
    match t' with
      | None -> None
      | Some t'' -> Some (Abstraction(x, t''))
  )
  | Application (t1, t2) -> match t1 with
    | Abstraction (x, term1) ->  Some (substitute x t2 term1)
    | _ -> let t1'' = reduce_normal t1 in (
      match t1'' with
        | Some t1' -> Some (Application (t1', t2))
        | None -> let t2'' = reduce_normal t2 in (
          match t2'' with
            | Some t2''' -> Some (Application(t1,t2'''))
            | None -> None
        )
    )
