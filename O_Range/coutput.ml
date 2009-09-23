(* coutput -- (non-pretty) expression printer
**
** Project:	FrontC
** File:	coutput.ml
** Version:	0.00001
** Date:	XX.XX.08
** Author:	moi
**
*)

open Cabs
open Cprint
let version = "Coutput"

let string_from_expr = 
     let rec aux currentPrio e =
	  let (str, prio) = get_operator e in
	  let result = match e with

		  NOTHING -> ""

		 | UNARY(op, arg) -> 	
			str^(aux prio arg) 			

		 | BINARY(op, arg1, arg2)  -> 	
			(aux prio arg1)^str^(aux (prio + 1) arg2)

		 | QUESTION (arg1, arg2, arg3)  -> 
			(aux 2 arg1)^"?"^(aux 2 arg2)^(aux 2 arg3)

		 | CAST (typ, arg) -> 
			"(CAST)"^(aux 15 arg) 

		 | CALL (fexpr, argl)-> 
			(aux 16 fexpr)^"("^(aux 0 (COMMA argl))^")"

		 | (COMMA l)  -> 
	 		List.fold_left (fun s arg -> s^(if (s = "") then s else ",")^(aux 1 arg)) "" l

		 | CONSTANT cst -> 
		      (match cst with
	 		 CONST_INT i -> i   
			|CONST_FLOAT f -> f
			|RCONST_INT i -> Printf.sprintf "%d" i   
			|RCONST_FLOAT f -> Printf.sprintf "%g" f
			|CONST_CHAR c -> c
			|CONST_STRING s -> "\""^s^"\""
			|CONST_COMPOUND cmp -> "[COMPOUND]"
		      )

		 | VARIABLE name -> name

		 | (EXPR_SIZEOF arg) -> 
	 		"sizeof("^(aux 0 arg)^")" 

		 | (TYPE_SIZEOF arg)-> "sizeof(TYPE)"

		 | INDEX (arg, idx) -> (aux 16 arg)^"["^(aux 0 idx)^"]"


		 | MEMBEROF (arg, field) -> (aux 16 arg)^"."^field


		 | MEMBEROFPTR (arg, field) -> (aux 16 arg)^"->"^field


		 | GNU_BODY _ -> "[GNU_BODY]"

		 | EXPR_LINE (expr, _,_ ) -> aux currentPrio expr
	 
	 
	 in if (prio < currentPrio) then "("^result^")" else result
		
      in (aux 0 )
