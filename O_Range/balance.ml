(** A module for computing {b balancing informations} about a program.
    Such computation takes as input:
    {ul
    {- The abstract syntax tree as computed by FrontC }
    {- Flow facts as computed by oRange }
    }
    The computation outputs the list of {e conditional statements} of the program
    together with a cost information about {e each possible branch}.
    This list is {e sorted} according to the difference of cost between the lightest and heaviest branch.
    @author Pascal Sotin
    @author Jakob Zwirchmayr
*)

(** {3 Utilities} *)

(** {7 General utilities} *)

let rec extract f = function
  | [] -> raise Not_found
  | e::r -> match f e with
    | None -> extract f r
    | Some x -> x

let rec min_max f = function
  | [] -> raise (Invalid_argument "empty list")
  | [x] -> f x, f x 
  | x::r -> let min_r, max_r = min_max f r in
            min (f x) min_r, max (f x) max_r

let rec fold1 f = function
  | [] -> raise (Invalid_argument "empty list")
  | [x] -> x
  | x::r -> f x (fold1 f r)

(** {7 FrontC utilities} *)

let function_def (defs: Cabs.definition list) (fname: string) =
  let body = extract (function
    | Cabs.FUNDEF ((_,_,(name,_,_,_)),(_,body))
    | Cabs.OLDFUNDEF ((_,_,(name,_,_,_)),_,(_,body)) when name = fname -> Some body
    | _ -> None) defs
  in body

let print_expr fmt (expr: Cabs.expression) =
  Cprint.current := "";
  Cprint.current_len := 0;
  Cprint.line := "";
  Cprint.line_len := 0;
  Cprint.print_expression expr ~-1;
  Cprint.commit ();
  Format.pp_print_string fmt !Cprint.line

let condition_test (stmt: Cabs.statement) =
  match stmt with
  | Cabs.IF (e,_,_)
  | Cabs.SWITCH (e,_) -> e
  | _ -> raise (Invalid_argument "not a condition")

(** {3 Types} *)

(** The flow facts requiered for the balancing analysis. *)
type ff_input = {
  loop_bound: Cabs.statement -> int option;
(**
   Provide information about a given loop.
   {ul
   {- Returns [Some n]: each time the loop is reached, it iterates {e at most} [n] times}
   {- Returns [None]: no loop bound could be computed for the loop}
   {- Raises [Not_found]: the loop statement does not exist in the flow facts}
   {- Raises [Invalid_argument]: the parameter must be [FOR], [WHILE] or [DOWHILE]}
   } *)
  branch_feasibility: Cabs.statement -> bool list;
(**
   Provide information about a given conditional.
   {ul
   {- Returns [ [b1, b2...] ]: the {e feasibility} of the first, second... branches of the conditional are respectively [b1], [b2]...}
   {- Raises [Not_found]: the conditional statement does not exist in the flow facts}
   {- Raises [Invalid_argument]: the parameter must be [IF] or [CASE]}
   }
*)
}

(** Location in the source code. *)
module Loc = struct
  (** A location in the source code. *)
  type t = { file: string; (** File name. *)
	     line: int;    (** Line number. *)
	   }

  (** Uses a Cabs.STAT_LINE statement to build a location. *)
  let of_stat_line = function
    | Cabs.STAT_LINE (_,f,l) -> { file = f; line = l }
    | _ -> raise (Invalid_argument "not a STAT_LINE")
  (** Prints a location. *)
  let print fmt loc = Format.fprintf fmt "%s:%d" loc.file loc.line
end

(** Tracks contextual information. *)
module Ctx = struct
  (** Type of the contextual information. *)
  type t = {
    cur: Loc.t option; (** A location when fresh enough. *)
    coeff: int;
    fname: string;     (** The enclosing function name. *)
  }

  (** Type indicating the distance between a context and a descendant of it. *)
  type distance =
  | Close    (** Denotes that the location is still valid. *)
  | Distant  (** Denotes that the location cannot be inherited from the context. *)

  (** Prints a location option. None means "unknown location". *)
  let print fmt (ctx: t) = Format.fprintf fmt "at %a in %s (total count=%d)"
    (fun fmt -> function
    | None -> Format.pp_print_string fmt "unknown location"
    | Some loc -> Loc.print fmt loc) ctx.cur
    ctx.fname
    ctx.coeff
  (** The empty context. *)
  let empty = { cur = None; fname = "<toplevel>"; coeff = 1 }
  (** Updating the context by a function call. *)
  let through_function_call (ctx: t) (fname: string) = { ctx with cur = None; fname = fname }
  (** Updating the context by descending in a statement.
      This might invalidate the location or not. *)
  let through_located_statement (dist: distance) (ctx: t) (stmt: Cabs.statement) =
    let latest_loc = match dist with
      | Close -> ctx.cur
      | Distant -> None in
    match stmt with
    | Cabs.STAT_LINE _ -> {ctx with cur = Some (Loc.of_stat_line stmt) }
    | _ -> { ctx with cur = latest_loc }
  (** Descend and invalidate the location. *)
  let through_statement = through_located_statement Distant
  (** Descend and keep the location valid. *)
  let through_close_statement = through_located_statement Close
end

(** A module for descending in the Abstract Syntax Tree while keeping a context. *)
module CtxNode = struct
  (** The type of a node in the contextual Abstract Syntax Tree. *)
  type t = {
    statement: Cabs.statement; (** The statement carried by the node.
			           Corresponds to a fragment of the original Abstract Syntax Tree. *)
    context: Ctx.t;            (** The context in which this statement was reached.
				   Due to the presence of functions, the complete
				   Abstract Syntax Tree is a Directed Acyclic Graph and a node can
				   be reached through different contexts. *)
  }

  (** Retrives the statement. *)
  let statement n = n.statement
  (** Retrives the context. *)
  let context n = n.context
  (** Provide the context obtained if we descend through the node. *)
  let descent_context (n: t) = Ctx.through_statement n.context n.statement
  (** Gives the node reached after descending in a given statement. *)
  let descent (n: t) (stmt: Cabs.statement) =
    { statement = stmt;
      context = descent_context n
    }
  (** Gives the node reached after descending in a given close statement.
      The location of the father is kept for the son. *)
  let close_descent (n: t) (stmt: Cabs.statement) =
    { statement = stmt;
      context = Ctx.through_close_statement n.context n.statement;
    }
  (** Gives the initial node of a function starting in a given context. *)
  let function_call (ctx: Ctx.t) (fname: string) (body: Cabs.statement) =
    { statement = body;
      context = Ctx.through_function_call ctx fname;
    }
  let loop_descent (n: int) (node: t) (stmt: Cabs.statement) =
    let ctx = descent_context node in
    { statement = stmt;
      context = { ctx with Ctx.coeff = n * ctx.Ctx.coeff }
    }
  let count (node: t) = node.context.Ctx.coeff
end

(** Code "weight".
    Encoded by an integer.
    A high value is a hint of a high contribution to the WCET. *)
type weight = int

(** Evaluation of a code fragment. *)
module CodeEval = struct
  (** The total weight of the code fragment (including the functions called). *)
  type t = weight
  (** Evaluation of a loop, providing the weights of the body and header
      together with a bound on the number of iterations. *)
  let of_loop ~header:h ~count:n ~body:b = h + n * (h + b)
  (** Evaluation of a set of alternatives (at least one). *)
  let of_alternatives = fold1 max
  (** Sum of weights *)
  let sum = List.fold_left ( + ) 0
end

(** Evaluation of a condition. *)
module CondEval = struct
  (** Result of the analysis of a conditional. *)
  type t = {
    condition: CtxNode.t;                (** The statement in the abstract syntax tree. Only [Cabs.IF] or [Cabs.SWITCH] statements. *)
    branches: (string * weight) list;    (** List of the feasible branches together with their respective weight.
					     Must be non-empty. *)
    delta: weight;                       (** Difference between the heaviest and the lightest branch. *)
  }
  let compare e1 e2 = match e2.delta - e1.delta with
    | 0 -> Pervasives.compare e1 e2
    | n -> n
  let make node brs n =
    let low, high = min_max snd brs in
    { condition = node; branches = brs; delta = n * (high - low) }
  let print fmt cond = Format.fprintf fmt "Delta %d %a : %a // %a"
    cond.delta
    Ctx.print (CtxNode.context cond.condition)
    (fun fmt -> List.iter (fun (br,w) -> Format.fprintf fmt "%s=%d; " br w)) cond.branches
    print_expr (condition_test (CtxNode.statement cond.condition))
end

(** Sets of condition evaluation. *)
module CondSet = Set.Make(CondEval)

(** {3 Main algorithm} *)

(** Relying on some flow facts and the FrontC Abstract Syntax Trees of the program, this function
    computes the conditional constructs reachable from a given entry function,
    from the most unbalanced ones to the most balanced. *)
let analysis
    (ff: ff_input)
    (defs: Cabs.definition list)
    (entry: string)
    :
    (CondEval.t list)
    =
  (* Managing a set of condition evaluations. *)
  let conds = ref CondSet.empty in
  let register_cond c = conds := CondSet.add c !conds in

  (* Three mutually recursive functions : expr -> function -> statement -> expr.
     The evaluation of the functions are cached.
     The conditions met are registered. *)

  (* Cache for the function analysis. *)
  let finfo = Hashtbl.create 10 in
  (* Analysis of a function. *)
  let rec fun_eval (ctx: Ctx.t) (fname: string) : CodeEval.t
      =
    try Hashtbl.find finfo (ctx,fname)
    with Not_found -> try 
      let body = 	
	function_def defs fname in
      let eval = stmt_eval (CtxNode.function_call ctx fname body) in
      Hashtbl.add finfo (ctx,fname) eval;
      eval
    with Not_found -> 10 (* Default weight when function not found failwith (fname^" is not a known function") in*)
  

  (* Analysis of an expression. *)
  and expr_eval (ctx: Ctx.t) (expr: Cabs.expression) : weight
      =
    let eval = expr_eval ctx in (* Evaluation in the same context. *)
    let open Cabs in
    match expr with
    | NOTHING -> 0
    | UNARY (_,e) -> 1 + eval e
    | BINARY (_,e1,e2) -> 1 + eval e1 + eval e2
    | QUESTION (e_if,e_then,e_else) -> eval e_if + (max (eval e_then) (eval e_else))
    | CALL (VARIABLE fname,el) ->
      let args = CodeEval.sum (List.map eval el) in
      let calling = List.length el in
      let execution = fun_eval ctx fname in
      args + calling + execution
    | CALL _ -> failwith "cannot resolve the call"
    | CONSTANT _ -> 0
    | VARIABLE _ -> 1
    | EXPR_SIZEOF _
    | TYPE_SIZEOF _
    | CAST _ -> 0
    | COMMA el -> CodeEval.sum (List.map eval el)
    | INDEX (e1,e2) -> 1 + (eval e1) + (eval e2)
    | MEMBEROF (e,_) -> 0 + (eval e)
    | MEMBEROFPTR (e,_) -> 1 + (eval e)
    | EXPR_LINE (e,_,_) -> eval e
    | GNU_BODY _ -> failwith "cannot handle assembly code"
  (* WARNING: the evaluation of expressions is far from realistic. *)

  (* Analysis of a statement (and substatements). *)
  and stmt_eval (node: CtxNode.t) : CodeEval.t
      =
    let stmt = CtxNode.statement node in
    let expr_eval_here e = expr_eval (CtxNode.context node) e in
    let expr_eval_under e = expr_eval (CtxNode.descent_context node) e in
    let eval s = stmt_eval (CtxNode.descent node s) in
    let eval_close s = stmt_eval (CtxNode.close_descent node s) in
    let eval_multi s n = stmt_eval (CtxNode.loop_descent n node s) in
    let open Cabs in
    match stmt with
    | STAT_LINE (sub,_,_) -> eval sub
    | COMPUTATION e
    | RETURN e -> expr_eval_here  e
    | NOP -> 0
    | BLOCK (_,sub) -> eval_close sub (* WARNING : initialisation of the declared variables is not taken into account. *)
    | SEQUENCE (sub1,sub2) ->
      let eval1 = eval_close sub1 in
      let eval2 = eval sub2 in
      eval1 + eval2
    | IF (e,s_then,s_else) ->
      let we = expr_eval_here e in

      let branches = List.concat 
            (List.map2 
                (fun (br,sub) feasible ->
                    if not feasible then []
                    else [(br,eval sub)])
                    [("then",s_then); ("else",s_else)] (ff.branch_feasibility stmt)
            ) 
      in
      register_cond (CondEval.make node branches (CtxNode.count node));
      (*let cev = CodeEval.of_alternatives (List.map snd branches) in 
      let res =  *)
      we + CodeEval.of_alternatives (List.map snd branches) (* in
      res *)
    | FOR (e_init,e_test,e_end,s_body) ->
        let wi = expr_eval_here e_init in
        let wt = expr_eval_under e_test in
        begin match ff.loop_bound stmt with
        | Some 0 -> wi + wt
        | Some n ->
          	let wbody = eval_multi s_body n in
          	let we = expr_eval_under e_end in
            Format.printf "init: %d, incr: %d, body: %d, bound: %d\n" wi we wbody n ;
          	wi + CodeEval.of_loop ~header:we ~count:n ~body:wbody;
        | None -> failwith "Unbounded for loop" end
    | WHILE (e,s_body) ->
        let we = expr_eval_under e in
        begin match ff.loop_bound stmt with
          | Some 0 -> we
          | Some n ->
              let eval_body = eval_multi s_body n in
              CodeEval.of_loop ~header:we ~count:n ~body:eval_body
          | None -> failwith "Unbounded while loop" end
    | BREAK ->
        (* HACKHACKHACK: fix breaks -- the count for 3 ops so decrease 2 *) 0
    | _ -> failwith "TODO"

  in
  (* Performing the analysis. *)
  let eval = fun_eval Ctx.empty entry in
  Format.printf ">>> Estimated costs of function: %d\n" eval;
  (* Synthesizing the list of conditionals. *)
  CondSet.elements !conds
