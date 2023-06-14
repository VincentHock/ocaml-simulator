(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | INegate
  | FNegate
  | BNegate
;;
    
type binop =
  | Plus
  | Minus
  | Times
  | Divide
  | Equals
  | LessThan
  | GreaterThan
  | FPlus
  | FMinus
  | FTimes
  | FDivide
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Float of float                       (* floats *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids) and sets of them
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars varids1 varids2 -- Tests to see if two `varid` sets have
   the same elements (for testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list varids -- Generates a set of variable names from a
   list of `varid`s (for testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars exp -- Returns the set of `varid`s corresponding to free
   variables in `exp` *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var x -> SS.singleton x
  | Num _ | Float _ | Bool _ -> SS.empty
  | Unop (_, e) -> free_vars e
  | Binop (_, e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (pred, res1, res2) -> SS.union (free_vars pred) (SS.union (free_vars res1) (free_vars res2))
  | Fun (var, e) -> SS.remove var (free_vars e)
  | Let (var, def, body) -> SS.union (free_vars def) (SS.remove var (free_vars body))
  | Letrec (var, def, body) -> SS.remove var (SS.union (free_vars def) (free_vars body))
  | App (f, e) -> SS.union (free_vars f) (free_vars e)
  | Raise | Unassigned -> SS.empty ;;

(* new_varname () -- Returns a freshly minted `varid` constructed with
   a running counter a la `gensym`. Assumes no other variable names
   use the prefix "var". (Otherwise, they might accidentally be the
   same as a generated variable name.) *)
let new_varname = 
  let count = ref 0 in
  fun () -> incr count ; 
  "var" ^ string_of_int !count
;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst var_name repl exp -- Return the expression `exp` with `repl`
   substituted for free occurrences of `var_name`, avoiding variable
   capture *)

let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  let subst_part = subst var_name repl in
  match exp with
  | Var x -> if x = var_name then repl else exp
  | Num _ | Float _ | Bool _ -> exp
  | Unop (op, e) -> Unop (op, subst_part e)
  | Binop (op, e1, e2) -> Binop (op, subst_part e1, subst_part e2)
  | Conditional (pred, res1, res2) -> Conditional (subst_part pred, subst_part res1, subst_part res2)
  | Fun (var, e) -> 
      if var = var_name then exp
      else if (SS.mem var (free_vars repl)) then
        let z = new_varname () in
        Fun (z, subst_part (subst var (Var z) e))
      else 
        Fun(var, subst_part e)
  | Let (var, def, body) -> 
      if var = var_name then Let(var, subst_part def, body)
      else if (SS.mem var (free_vars repl)) then
        let z = new_varname () in
        Let (z, subst_part def, subst_part (subst var (Var z) body))
      else 
        Let (var, subst_part def, subst_part body)
  | Letrec (var, def, body) -> 
      if var = var_name then exp
      else if (SS.mem var (free_vars repl)) then
        let z = new_varname () in
        Letrec (z, subst_part (subst var (Var z) def), subst_part (subst var (Var z) body))
      else 
        Letrec (var, subst_part def, subst_part body)
  | App (f, e) -> App (subst_part f, subst_part e)
  | Raise | Unassigned -> exp 
;;
  

     
(*......................................................................
  String representations of expressions
 *)
   
(* exp_to_concrete_string exp -- Returns a string representation of
   the concrete syntax of the expression `exp` *)

let unop_to_a_string (u : unop) : string =
  match u with
  | INegate -> "INegate"
  | BNegate -> "BNegate"
  | FNegate -> "FNegate"
;;

let unop_to_c_string (u : unop) : string =
  match u with
  | INegate -> "~-"
  | BNegate -> "~-"
  | FNegate -> "not "
;;

let binop_to_a_string (b : binop) : string =
  match b with
  | Plus -> "Plus" 
  | Minus -> "Minus"
  | Times -> "Times"
  | Divide -> "Divide"
  | FPlus -> "FPlus"
  | FMinus -> "FMinus"
  | FTimes -> "FTimes"
  | FDivide -> "FDivide"
  | Equals -> "Equals"
  | LessThan -> "LessThan"
  | GreaterThan -> "GreaterThan"
;;

let binop_to_c_string (b : binop) : string =
  match b with
  | Plus -> "+" 
  | Minus -> "-"
  | Times -> "*"
  | Divide -> "/"
  | FPlus -> "+."
  | FMinus -> "-."
  | FTimes -> "*."
  | FDivide -> "/."
  | Equals -> "="
  | LessThan -> "<"
  | GreaterThan -> ">"
;;

let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var x -> x                       
  | Num i -> string_of_int i     
  | Float f -> string_of_float f                      
  | Bool b -> if b then "true" else "false"          
  | Unop (op, e) -> unop_to_c_string op ^ exp_to_concrete_string e               
  | Binop (op, e1, e2) -> exp_to_concrete_string e1 ^ " " ^ binop_to_c_string op ^ " " ^ exp_to_concrete_string e2
  | Conditional (pred, res1, res2) -> "if " ^ exp_to_concrete_string pred ^ " then " ^ exp_to_concrete_string res1 ^ " else " ^ exp_to_concrete_string res2
  | Fun (var, e) -> "fun " ^ var ^ "-> " ^ exp_to_concrete_string e      
  | Let (var, def, body) -> "let " ^ var ^ " = " ^ exp_to_concrete_string def ^ " in " ^ exp_to_concrete_string body
  | Letrec (var, def, body) ->  "let rec" ^ var ^ " = " ^ exp_to_concrete_string def ^ " in " ^ exp_to_concrete_string body
  | Raise -> "raise"                       
  | Unassigned -> "unassigned"                
  | App (f, e) -> "(" ^ exp_to_concrete_string f ^ ") " ^ "(" ^ exp_to_concrete_string e ^ ")"   
;;
     
(* exp_to_abstract_string exp -- Return a string representation of the
   abstract syntax of the expression `exp` *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var x -> "Var(\"" ^ x ^ "\")"                       
  | Num i -> "Num(" ^ string_of_int i ^ ")"
  | Float f -> "Float(" ^ string_of_float f ^ ")"                      
  | Bool b -> if b then "Bool(true)" else "Bool(false)"          
  | Unop (op, e) -> "Unop(" ^ unop_to_a_string op ^ ", " ^ exp_to_abstract_string e ^ ")"              
  | Binop (op, e1, e2) -> "Binop(" ^ binop_to_a_string op ^ ", " ^ exp_to_abstract_string e1 ^ ", " ^ exp_to_abstract_string e2 ^ ")"
  | Conditional (pred, res1, res2) -> "Conditional(" ^ exp_to_abstract_string pred ^ ", " ^ exp_to_abstract_string res1 ^ ", " ^ exp_to_abstract_string res2 ^ ")"
  | Fun (var, e) -> "Fun(\"" ^ var ^ "\", " ^ exp_to_abstract_string e ^ ")"  
  | Let (var, def, body) -> "Let(\"" ^ var ^ "\", " ^ exp_to_abstract_string def ^ ", " ^ exp_to_abstract_string body ^ ")"
  | Letrec (var, def, body) ->  "Letrec(\"" ^ var ^ "\", " ^ exp_to_abstract_string def ^ ", " ^ exp_to_abstract_string body ^ ")"
  | App (f, e) -> "App(" ^ exp_to_abstract_string f ^ ", " ^ exp_to_abstract_string e ^ ")"  
  | Raise -> "raise"                       
  | Unassigned -> "unassigned"                
;;