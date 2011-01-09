(**********************************************************************
  jabstr  Copyright (C) 2010, 2011  Matko Botincan

  This software is distributed under a LGPL license, see LICENSE.
 **********************************************************************)


open Psyntax;;
open Apron;;
open Mpqf;;


(* Create a manager for Convex Polyhedra and Linear Equalities abstract domain *)
let manager = Polka.manager_alloc_strict();;  


(* Store non-arithmetic terms as variables indexed by their string reps.
   Store also Psyntax rep so that terms can be reconstructed back. *)
type var_arg_hashtbl = (string, Var.t * args) Hashtbl.t;;

let var_arg_table : var_arg_hashtbl = Hashtbl.create 17;;


let buffer = Buffer.create 16;;
let formatter = Format.formatter_of_buffer buffer;;

(* Gets buffer contents and clears it before return *)
let dump_buffer_contents (buf : Buffer.t) : string =
  let str = Buffer.contents buf in Buffer.clear buf; str

(* Generates variable name from term string rep *)
let gen_id (arg : args) : string =
  Format.fprintf formatter "%a%!" string_args arg;
  dump_buffer_contents buffer


let add_var_arg (arg : args) : unit =
  let id = gen_id arg in
  try ignore (Hashtbl.find var_arg_table id) with
  Not_found ->
    let var = Var.of_string id in
    Hashtbl.add var_arg_table id (var, arg)

let get_var (arg : args) : Var.t =
  fst (try Hashtbl.find var_arg_table (gen_id arg) with
    Not_found -> assert false)

let get_arg (id : string) : args =
  snd (try Hashtbl.find var_arg_table id with
    Not_found -> assert false)

let get_vars () : Var.t array =
  let var_list = Hashtbl.fold (fun id (var,arg) ls -> ls @ [var]) var_arg_table [] in
  Array.of_list var_list


let is_integer_const (s : string) : bool =
  let rxp = (Str.regexp "^\\(-?[0-9]+\\)") in 
  Str.string_match rxp s 0


(* Steps into term and create variables from non-arithmetic subterms *)
let rec create_vars_from_args (arg : args) : unit =
  match arg with
  | Arg_op ("builtin_plus", args)
  | Arg_op ("builtin_minus", args)
  | Arg_op ("builtin_mult", args) -> List.iter create_vars_from_args args
  | Arg_op ("numeric_const", [Arg_string (s)])
  | Arg_string s -> if is_integer_const s <> true then add_var_arg arg
  | Arg_var _ | Arg_op (_,_) -> add_var_arg arg
  | _ -> Format.printf "\nFailed on: %s\n%!" (gen_id arg); assert false


(* Steps into formula in order to create variables from non-arithmetic terms *)
let create_vars_from_pform_at (pf_at : pform_at) : unit =
  match pf_at with 
  | P_EQ (a1,a2)
  | P_NEQ (a1,a2)
  | P_PPred ("GT", [a1; a2])
  | P_PPred ("GT", [Arg_op ("tuple", [a1; a2])])
  | P_PPred ("LT", [a1; a2])
  | P_PPred ("LT", [Arg_op ("tuple", [a1; a2])])
  | P_PPred ("GE", [a1; a2])
  | P_PPred ("GE", [Arg_op ("tuple", [a1; a2])])
  | P_PPred ("LE", [a1; a2])
  | P_PPred ("LE", [Arg_op ("tuple", [a1; a2])]) ->
    create_vars_from_args a1; create_vars_from_args a2;
  | _ -> Format.printf "\nFailed on: %a@.\n%!" string_form_at pf_at; assert false


(* Translates term to Apron tree expression of level 1 *)
let rec tr_args (arg : args) : Texpr1.expr =
  let mk_binop op e1 e2 =
    Texpr1.Binop (op, e1, e2, Texpr1.Real, Texpr1.Near) in
  match arg with
  | Arg_op ("builtin_plus", [a1; a2]) -> 
    mk_binop Texpr1.Add (tr_args a1) (tr_args a2)
  | Arg_op ("builtin_minus", [a1; a2]) -> 
    mk_binop Texpr1.Sub (tr_args a1) (tr_args a2)
  | Arg_op ("builtin_mult", [a1; a2]) -> 
    mk_binop Texpr1.Mul (tr_args a1) (tr_args a2)
  | Arg_op ("numeric_const", [Arg_string (s)]) 
  | Arg_string s ->
    if is_integer_const s then Texpr1.Cst (Coeff.s_of_int (int_of_string s))
    else Texpr1.Var (get_var arg)
  | Arg_var _ | Arg_op (_,_) -> Texpr1.Var (get_var arg)
  | _ -> Format.printf "\nFailed on: %s\n%!" (gen_id arg); assert false


(* Translates formula to Apron tree constraint of level 1 *)
let tr_pform_at (env : Environment.t) (pf_at : pform_at) : Tcons1.t =
  let mk_sub e1 e2 = 
    Texpr1.Binop (Texpr1.Sub, e1, e2, Texpr1.Real, Texpr1.Near) in
  let mk_cons e typ =
    Tcons1.make (Texpr1.of_expr env e) typ in
  match pf_at with 
  | P_EQ (a1,a2) ->
    mk_cons (mk_sub (tr_args a1) (tr_args a2)) Tcons1.EQ
  | P_NEQ (a1,a2) ->
    mk_cons (mk_sub(tr_args a1) (tr_args a2)) Tcons1.DISEQ
  | P_PPred ("GT", [a1; a2]) | P_PPred ("GT", [Arg_op ("tuple",[a1; a2])]) ->
    mk_cons (mk_sub (tr_args a1) (tr_args a2)) Tcons1.SUP
  | P_PPred ("LT", [a1; a2]) | P_PPred ("LT", [Arg_op ("tuple",[a1; a2])]) ->
    mk_cons (mk_sub (tr_args a2) (tr_args a1)) Tcons1.SUP
  | P_PPred ("GE", [a1; a2]) | P_PPred ("GE", [Arg_op ("tuple",[a1; a2])]) ->
    mk_cons (mk_sub (tr_args a1) (tr_args a2)) Tcons1.SUPEQ
  | P_PPred ("LE", [a1; a2]) | P_PPred ("LE", [Arg_op ("tuple",[a1; a2])]) ->
    mk_cons (mk_sub (tr_args a2) (tr_args a1)) Tcons1.SUPEQ
  | _ -> Format.printf "\nFailed on: %a@.\n%!" string_form_at pf_at; assert false


let coeff_to_string (coeff : Coeff.t) : string =
  match coeff with
  | Coeff.Scalar s -> Scalar.to_string s
  | Coeff.Interval i -> assert false

let coeff_sgn (coeff : Coeff.t) : int =
  match coeff with
  | Coeff.Scalar s -> Scalar.sgn s
  | Coeff.Interval i -> assert false

let coeff_cmp (coeff : Coeff.t) (num : int) : int =
  match coeff with
  | Coeff.Scalar s -> Scalar.cmp s (Scalar.of_int num)
  | Coeff.Interval i -> assert false


(* Translates Apron tree expression of level 1 to term *)
let rec tr_texpr (texpr : Texpr1.expr) : args =
  match texpr with
  | Texpr1.Cst coeff -> Arg_string (coeff_to_string coeff)
  | Texpr1.Var var -> get_arg (Var.to_string var)
  | Texpr1.Binop (op, te1, te2, typ, _) ->
    let op_name =
      match op with
      | Texpr1.Add -> "builtin_plus"
      | Texpr1.Sub -> "builtin_minus"
      | Texpr1.Mul -> "builtin_mult"
      | _ -> assert false
    in Arg_op (op_name, [tr_texpr te1; tr_texpr te2])
  | Texpr1.Unop (op, e, typ, _) -> assert false


(* Translates Apron tree constraint of level 1 to formula *)
let tr_tcons (tcons : Tcons1.t) : pform_at =
  let zero = Arg_string "0" in
  let te = Texpr1.to_expr (Tcons1.get_texpr1 tcons) in
  let e1,e2 = 
    match te with
    | Texpr1.Binop (Texpr1.Sub, te1, te2, typ, _) -> tr_texpr te1, tr_texpr te2
    | _ -> tr_texpr te, zero
  in
  match Tcons1.get_typ tcons with
  | Tcons1.EQ -> P_EQ (e1, e2)
  | Tcons1.DISEQ -> P_NEQ (e1, e2)
  | Tcons1.SUP -> P_PPred ("LT", [e2; e1])
  | Tcons1.SUPEQ -> P_PPred ("LE", [e2; e1])
  | _ -> assert false (* no EQMOD *)


(* Translates a (coeff, var) list to term *)
let rec tr_coeff_vars (cvs : (Coeff.t * Var.t) list) : args option =
  match cvs with
  | [] -> None
  | (coeff, var) :: rest ->
    let var_arg = get_arg (Var.to_string var) in
    let arg = if (coeff_cmp coeff 1) = 0 then var_arg
      else Arg_op ("builtin_mult", [Arg_string (coeff_to_string coeff); var_arg]) in
    match tr_coeff_vars rest with
    | None -> Some arg
    | Some r_arg -> Some (Arg_op ("builtin_plus", [arg; r_arg]))
    

(* Translates Apron linear expression of level 1 to a pair of terms corresponding to 
   the left and the right hand side *)
let rec tr_linexpr (env : Environment.t) (linexpr : Linexpr1.t) : args option * args option =
  let vars,_ = Environment.vars env in (* TODO: use both integer and real vars *)
  let coeffs = Array.map (fun var -> Linexpr1.get_coeff linexpr var) vars in
  let cvs = ref [] in
  Array.iteri (fun i coeff ->
    if (Coeff.is_zero coeff) = false then cvs := !cvs @ [(coeff, vars.(i))]) coeffs;
  let pos,neg = List.partition (fun (c,_) -> coeff_sgn c > 0) !cvs in
  let neg = List.map (fun (c,v) -> (Coeff.neg c,v)) neg in
  tr_coeff_vars pos, tr_coeff_vars neg


(* Translates Apron linear constraint of level 1 to formula *)
let tr_lincons (env : Environment.t) (lincons : Lincons1.t) : pform_at =
  let zero = Arg_string "0" in
  let cst = Lincons1.get_cst lincons in
  let mk_const cst = Arg_string (coeff_to_string cst) in
  let mk_pred e1 e2 =
    match Lincons1.get_typ lincons with
    | Lincons1.EQ -> P_EQ (e1, e2)
    | Lincons1.DISEQ -> P_NEQ (e1, e2)
    | Lincons1.SUP -> P_PPred ("LT", [e2; e1])
    | Lincons1.SUPEQ -> P_PPred ("LE", [e2; e1])
    | _ -> assert false (* no EQMOD *)
  in
  match tr_linexpr env (Lincons1.get_linexpr1 lincons) with
  | None, None -> 
    if (Coeff.is_zero cst) then 
      P_Garbage 
    else 
      P_False
  | None, Some rhs ->
    if (coeff_sgn cst) < 0 then 
      mk_pred zero (Arg_op ("builtin_plus", [mk_const (Coeff.neg cst); rhs]))
    else 
      mk_pred (mk_const cst) rhs
  | Some lhs, None ->
    if (coeff_sgn cst) <= 0 then 
      mk_pred lhs (mk_const (Coeff.neg cst)) 
    else 
      mk_pred (Arg_op ("builtin_plus", [mk_const cst; lhs])) zero
  | Some lhs, Some rhs ->
    if (coeff_sgn cst) = 0 then
      mk_pred lhs rhs
    else if (coeff_sgn cst) < 0 then 
      mk_pred lhs (Arg_op ("builtin_plus", [mk_const (Coeff.neg cst); rhs]))
    else
      mk_pred (Arg_op ("builtin_plus", [mk_const cst; lhs])) rhs


(* Filters numerical formulae *)
let match_numerical (pf_at : pform_at) : bool =
  match pf_at with 
  | P_EQ (_,_) | P_NEQ(_,_) 
  | P_PPred("GT",_) | P_PPred("LT",_) | P_PPred("GE",_) | P_PPred("LE",_) -> true 
  | _ -> false


(* Abstracts each disjunction separately -- steps into top-level disjunctions only *)
let rec abs_pform (f : pform) : pform =
  (* Analogue of Array.iteri for lists *)
  let list_iteri (f : int -> 'a -> unit) (ls : 'a list) : unit =
    let rec iteri2 f n = function
      | [] -> ()
      | a::l -> f n a; iteri2 f (n+1) l 
    in
    iteri2 f 0 ls
  in
  (* Generates a list of numbers [0; ...,; n-1] *)
  let range n =
    let rec range2 i ls =
      if i = n then ls
      else range2 (i+1) (ls@[i])
    in
    range2 0 []    
  in
  match f with
  | [P_Or (f1, f2)] -> 
    [P_Or (abs_pform f1, abs_pform f2)]

  | _ -> 
    (* Split numerical formulae from the rest *)

    let (num_forms, rest) = List.partition (fun pf_at -> match_numerical pf_at) f in

    Hashtbl.clear var_arg_table;
    (* Create Apron variables *)
    List.iter create_vars_from_pform_at num_forms;

    (* Create environment with all integer variables *)
    let env = Environment.make (get_vars()) [||] in
    if Config.symb_debug() then
      Format.printf "\nEnvironment: %a@.\n%!" (fun x -> Environment.print x) env;

    (* Create array of Apron tree expressions constraints *)
    let tab = Tcons1.array_make env (List.length num_forms) in
    (* Fill the array with translated numerical formulae *)
    list_iteri (fun i pf_at -> Tcons1.array_set tab i (tr_pform_at env pf_at)) num_forms;
    if Config.symb_debug() then
      (let array_print fmt x = Tcons1.array_print fmt x in
      Format.printf "\nArray constraints: %a@.\n%!" array_print tab;);

    (* Perform the abstraction on the conjunction of the constraints *)
    let abs = Abstract1.of_tcons_array manager env tab in
    Abstract1.minimize_environment manager abs;
    if Config.symb_debug() then
      Format.printf "\nAbstracted constraints: %a@.\n%!" Abstract1.print abs;    
    
    (*
    (* Convert the abstract value back to conjunction of tree expressions constraints *)
    let tab = Abstract1.to_tcons_array manager abs in
    if Config.symb_debug() then
      (let array_print fmt x = Tcons1.array_print fmt x in
      Format.printf "\nArray constraints: %a@.\n%!" array_print tab;);

    (* Translate abstracted constraints back to Psyntax formulae *)
    let tab_indices = range (Tcons1.array_length tab) in
    let abs_num_forms = List.map (fun i -> tr_tcons (Tcons1.array_get tab i)) tab_indices in
    *)
    
    (* Convert the abstract value back to conjunction of linear constraints *)
    let tab = Abstract1.to_lincons_array manager abs in
    if Config.symb_debug() then
      (let array_print fmt x = Lincons1.array_print fmt x in
      Format.printf "\nArray constraints: %a@.\n%!" array_print tab;);

    (* Translate abstracted constraints back to Psyntax formulae *)
    let tab_indices = range (Lincons1.array_length tab) in
    let abs_num_forms = List.map (fun i -> tr_lincons env (Lincons1.array_get tab i)) tab_indices in

    (* Unite abstracted formulae with the remainder *)
    abs_num_forms @ rest


let num_abs (f : pform) : pform =
  if Config.symb_debug() then
    Format.printf "\nBefore numerical abstraction: %a@.\n%!" string_form f;
  let abs_f = abs_pform f in
  if Config.symb_debug() then
    Format.printf "\nAfter numerical abstraction: %a@.\n%!" string_form abs_f;
  abs_f


(* Plugin registration *)
let _ =
  Plugin_callback.add_abs_int (ref num_abs)
