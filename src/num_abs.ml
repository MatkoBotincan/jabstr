(**********************************************************************
  jabstr  Copyright (C) 2010, 2011  Matko Botincan

  This software is distributed under a LGPL license, see LICENSE.
 **********************************************************************)


open Psyntax;;
open Apron;;
open Mpqf;;
open Plugin;;


(* Create a manager for Convex Polyhedra and Linear Equalities abstract domain *)
let manager = Polka.manager_alloc_strict();;
type abs_type = Polka.strict Polka.t;;


(* Store variables indexed by their string reps.
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
    Not_found -> Format.printf "\nget_var failed on: %s\n%!" (gen_id arg); assert false)

let get_arg (id : string) : args =
  snd (try Hashtbl.find var_arg_table id with
    Not_found -> Format.printf "\nget_arg  failed on: %s\n%!" id; assert false)

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
  | _ -> Format.printf "\ncreate_vars_from_args failed on: %s\n%!" (gen_id arg); 
    assert false


(* Steps into formula in order to create variables from non-arithmetic terms *)
let create_vars_from_pform_at (pf_at : pform_at) : unit =
  match pf_at with 
  | P_EQ (a1, a2)
  | P_NEQ (a1, a2)
  | P_PPred ("GT", [a1; a2])
  | P_PPred ("GT", [Arg_op ("tuple", [a1; a2])])
  | P_PPred ("LT", [a1; a2])
  | P_PPred ("LT", [Arg_op ("tuple", [a1; a2])])
  | P_PPred ("GE", [a1; a2])
  | P_PPred ("GE", [Arg_op ("tuple", [a1; a2])])
  | P_PPred ("LE", [a1; a2])
  | P_PPred ("LE", [Arg_op ("tuple", [a1; a2])]) ->
    create_vars_from_args a1; create_vars_from_args a2;
  | _ -> Format.printf "\ncreate_vars_from_pform_at failed on: %a@.\n%!" string_form_at pf_at; 
    assert false


(* Translates term to Apron tree expression of level 1 *)
let rec tr_args (arg : args) : Texpr1.expr =
  let mk_binop op e1 e2 =
    Texpr1.Binop (op, e1, e2, Texpr1.Real, Texpr1.Near) in
  match arg with
  | Arg_var _ -> Texpr1.Var (get_var arg)
  | Arg_op ("numeric_const", [Arg_string (s)]) 
  | Arg_string s ->
    if is_integer_const s then Texpr1.Cst (Coeff.s_of_int (int_of_string s))
    else (Format.printf "\ntr_args failed on: %s\n%!" (gen_id arg); assert false)
  | Arg_op ("builtin_plus", [a1; a2]) -> 
    mk_binop Texpr1.Add (tr_args a1) (tr_args a2)
  | Arg_op ("builtin_minus", [a1; a2]) -> 
    mk_binop Texpr1.Sub (tr_args a1) (tr_args a2)
  | Arg_op ("builtin_mult", [a1; a2]) -> 
    mk_binop Texpr1.Mul (tr_args a1) (tr_args a2)
  | _ -> Format.printf "\ntr_args failed on: %s\n%!" (gen_id arg); 
    assert false


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
  | _ -> Format.printf "\ntr_pform_at failed on: %a@.\n%!" string_form_at pf_at;
    assert false


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


(* Determines whether given formula represents an equality setting var to a constant *)
let is_eq_var_const (pf_at : pform_at) : bool =
  match pf_at with
  | P_EQ (Arg_var _, Arg_string _)
  | P_EQ (Arg_var _, Arg_op ("numeric_const", [Arg_string (_)]))
  | P_EQ (Arg_string _, Arg_var _)
  | P_EQ (Arg_op ("numeric_const", [Arg_string (_)]), Arg_var _) -> true
  | _ -> false


(* Adds to a substitution varible set to a constant *)
let subst_eq_var_const (vs : variable_subst) (pf_at : pform_at) : variable_subst =
  let var,term =
    match pf_at with
    | P_EQ (a1, a2) ->
      (match a1, a2 with
      | Arg_var v, Arg_string _
      | Arg_var v, Arg_op ("numeric_const", [Arg_string (_)]) -> v, a2
      | Arg_string _, Arg_var v
      | Arg_op ("numeric_const", [Arg_string (_)]), Arg_var v -> v, a1
      | _ -> assert false)  
    | _ -> assert false  
  in 
  add_subst var term vs


(* Converts numerical part of the formula to Apron abstract value of level 1 leaving the remainder.
   Assumes there are no disjunctions in the formula. *)
let pform_to_abstract_val (keep_eqs : bool) (f : pform) : abs_type Abstract1.t * pform =
  (* Analogue of Array.iteri for lists *)
  let list_iteri (f : int -> 'a -> unit) (ls : 'a list) : unit =
    let rec iteri2 f n = function
      | [] -> ()
      | a::l -> f n a; iteri2 f (n+1) l 
    in
    iteri2 f 0 ls
  in
  if Config.symb_debug() then
    Format.printf "\nBefore abstraction: %a@.\n%!" string_form f;
  (* Split numerical formulae with equalities from the rest *)
  let (num_forms_eq, rest) = List.partition (fun pf_at -> is_numerical_pform_at pf_at) f in
  (* Separate equalities setting var to a constant from numerical formulae *)
  let (eqs, num_forms) = List.partition (fun pf_at -> is_eq_var_const pf_at) num_forms_eq in
  (* Create and apply a substitution for constant propagation *)
  let subst = List.fold_left (fun vs pf_at -> subst_eq_var_const vs pf_at) empty_subst eqs in
  let num_forms = subst_form subst num_forms in
  
  let num_forms,eqs =
    if keep_eqs then num_forms @ eqs, []
    else num_forms, eqs in
  if Config.symb_debug() then
    Format.printf "\nNumerical subformula: %a@.\n%!" string_form num_forms;

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
  (*let abs = Abstract1.minimize_environment manager abs in*)
  if Config.symb_debug() then
    Format.printf "\nAbstracted constraints: %a@.\n%!" Abstract1.print abs;
  
  (* Return the abstract value and the remaining part of the formula *)
  (abs, eqs @ rest)


(* Converts formula to Apron abstract value of level 1.
   Assumes there are no disjunctions in the formula. *)
let abstract_val_to_pform (abs : 'a Abstract1.t) : pform =
  (* Generates a list of numbers [0; ...,; n-1] *)
  let range n =
    let rec range2 i ls =
      if i = n then ls
      else range2 (i+1) (ls@[i])
    in
    range2 0 []    
  in
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
  let env = Abstract1.env abs in
  let tab = Abstract1.to_lincons_array manager abs in
  if Config.symb_debug() then
    (let array_print fmt x = Lincons1.array_print fmt x in
    Format.printf "\nArray constraints: %a@.\n%!" array_print tab;);

  (* Translate abstracted constraints back to Psyntax formulae *)
  let tab_indices = range (Lincons1.array_length tab) in
  let abs_pform = List.map (fun i -> tr_lincons env (Lincons1.array_get tab i)) tab_indices in
  if Config.symb_debug() then
    Format.printf "\nAfter abstraction: %a@.\n%!" string_form abs_pform;
  abs_pform


(* Returns abstract value of a formula.
   Abstracts each disjunction separately -- steps into top-level disjunctions only. *)
let rec abstract_val (f : pform) : pform =
  let abstract_val2 (f : pform) : pform =
    let (abs,rem) = pform_to_abstract_val false f in
    (abstract_val_to_pform abs) @ rem
  in
  match f with
  | [P_Or (f1, f2)] -> 
    [P_Or (abstract_val f1, abstract_val f2)]
  | _ -> abstract_val2 f


(* Determines whether two terms are equal modulo constants *)
let rec args_eq_mod_const (arg1 : args) (arg2 : args) : bool =
  match arg1, arg2 with
  | Arg_var _, Arg_var _ -> 
    Format.fprintf formatter "%a%!" string_args arg1;
    let s1 = dump_buffer_contents buffer in
    Format.fprintf formatter "%a%!" string_args arg2;
    let s2 = dump_buffer_contents buffer in
    (String.compare s1 s2) = 0
  | Arg_op ("numeric_const", [Arg_string _]), Arg_op ("numeric_const", [Arg_string _])
  | Arg_string _, Arg_string _ -> true
  | Arg_op ("builtin_plus", [a1; a2]), Arg_op ("builtin_plus", [b1; b2])
  | Arg_op ("builtin_minus", [a1; a2]), Arg_op ("builtin_minus", [b1; b2])
  | Arg_op ("builtin_mult", [a1; a2]), Arg_op ("builtin_mult", [b1; b2]) -> 
    (args_eq_mod_const a1 b1) && (args_eq_mod_const a2 b2)
  | _ -> false


(* Determines whether two formulae are equal modulo constants *)
let pform_at_eq_mod_const (f1 : pform_at) (f2 : pform_at) : bool =
  match f1, f2 with 
  | P_EQ (a1, a2), P_EQ (b1, b2)
  | P_NEQ (a1, a2), P_NEQ (b1, b2)
  | P_PPred ("GT", [a1; a2]), P_PPred ("GT", [b1; b2]) 
  | P_PPred ("GT", [Arg_op ("tuple",[a1; a2])]), P_PPred ("GT", [Arg_op ("tuple",[b1; b2])])
  | P_PPred ("LT", [a1; a2]), P_PPred ("LT", [b1; b2]) 
  | P_PPred ("LT", [Arg_op ("tuple",[a1; a2])]), P_PPred ("LT", [Arg_op ("tuple",[b1; b2])])
  | P_PPred ("GE", [a1; a2]), P_PPred ("GE", [b1; b2]) 
  | P_PPred ("GE", [Arg_op ("tuple",[a1; a2])]), P_PPred ("GE", [Arg_op ("tuple",[b1; b2])])
  | P_PPred ("LE", [a1; a2]), P_PPred ("LE", [b1; b2]) 
  | P_PPred ("LE", [Arg_op ("tuple",[a1; a2])]), P_PPred ("LE", [Arg_op ("tuple",[b1; b2])]) ->
    (args_eq_mod_const a1 b1) && (args_eq_mod_const a2 b2)
  | _ -> false


(* Determines whether two formulae are syntactically equal *)
let pform_at_eq (f1 : pform_at) (f2 : pform_at) : bool =
  Format.fprintf formatter "%a%!" string_form_at f1;
  let s1 = dump_buffer_contents buffer in
  Format.fprintf formatter "%a%!" string_form_at f2;
  let s2 = dump_buffer_contents buffer in
  (String.compare s1 s2) = 0


(* Peforms syntactic forgetting (existential quantification) on those terms of join
   that have changed only modulo constant wrt to either f1 or f2. *)
let syntactic_forget (f1 : pform) (f2 : pform) (join : pform) : pform =
  let rec filter_equal eq_pred (fs : pform_at list) (gs : pform_at list) =
    match fs with
    | [] -> (([],gs),[])
    | f :: fs ->
      let fs_eq,fs_neq = List.partition (fun g -> eq_pred f g) fs in
      let gs_eq,gs_neq = List.partition (fun g -> eq_pred f g) gs in
      let (fs_neq,gs_neq),common_eq = filter_equal eq_pred fs_neq gs_neq in
      if gs_eq = [] then
        (([f] @ fs_neq, gs_neq), common_eq)
      else
        ((fs_neq, gs_neq), gs_eq @ common_eq)
  in
  let (join_neq1,f1_neq),common_eq1 = 
    filter_equal pform_at_eq join f1 in
  let (join_neq1,f1_neq),common_eq_mod_const1 = 
    filter_equal pform_at_eq_mod_const join_neq1 f1_neq in
  let (join_neq2,f2_neq),common_eq2 = 
    filter_equal pform_at_eq join f2 in
  let (join_neq2,f2_neq),common_eq_mod_const2 = 
    filter_equal pform_at_eq_mod_const join_neq2 f2_neq in
  if (List.length common_eq1) > (List.length common_eq2) then
    common_eq1 @ join_neq1
  else if (List.length common_eq1) < (List.length common_eq2) then
    common_eq2 @ join_neq2
  else if (List.length common_eq_mod_const1) >= (List.length common_eq_mod_const2) then
    common_eq1 @ join_neq1
  else
    common_eq2 @ join_neq2


(* Returns join of two formulae.
   Assumes there are no disjunctions in the formulae. *)
let join (f1 : pform) (f2 : pform) : pform =
  if Config.symb_debug() then
    Format.printf "\nStarting join of:\n%a@.\nand:\n%a@.\n%!" string_form f1 string_form f2;
  let (abs1,rem1) = pform_to_abstract_val true f1 in
  let (abs2,rem2) = pform_to_abstract_val true f2 in
  let env = Environment.lce (Abstract1.env abs1) (Abstract1.env abs2) in
  Abstract1.change_environment_with manager abs1 env false;
  Abstract1.change_environment_with manager abs2 env false;
  let abs = Abstract1.join manager abs1 abs2 in
  Abstract1.minimize_environment_with manager abs;
  if Config.symb_debug() then
    Format.printf "\nAbstracted constraints after join: %a@.\n%!" Abstract1.print abs;
  let pform = (abstract_val_to_pform abs) @ rem1 @ rem2 in
  if Config.symb_debug() then
    Format.printf "\nFormula after join: %a@.\n%!" string_form pform;
  let pform = syntactic_forget f1 f2 pform in
  if Config.symb_debug() then
    Format.printf "\nJoin formula after syntactic forget: %a@.\n%!" string_form pform;
  pform


(* Returns meet of two formulae.
   Assumes there are no disjunctions in the formulae. *)
let meet (f1 : pform) (f2 : pform) : pform =
  if Config.symb_debug() then
    Format.printf "\nStarting meet of:\n%a@.\nand:\n%a@.\n%!" string_form f1 string_form f2;
  let (abs1,rem1) = pform_to_abstract_val true f1 in
  let (abs2,rem2) = pform_to_abstract_val true f2 in
  let env = Environment.lce (Abstract1.env abs1) (Abstract1.env abs2) in
  Abstract1.change_environment_with manager abs1 env false;
  Abstract1.change_environment_with manager abs2 env false;
  let abs = Abstract1.meet manager abs1 abs2 in
  Abstract1.minimize_environment_with manager abs;
  if Config.symb_debug() then
    Format.printf "\nAbstracted constraints after meet: %a@.\n%!" Abstract1.print abs;
  let pform = (abstract_val_to_pform abs) @ rem1 @ rem2 in
  if Config.symb_debug() then
    Format.printf "\nWhole formula after meet: %a@.\n%!" string_form pform;
  pform


let my_abs_int = {
  abstract_val = Some (ref abstract_val);
  join = Some (ref join);
  meet = Some (ref meet);
  widening = None;
}

(* Plugin registration *)
let _ =
  Plugin_callback.add_abs_int (ref my_abs_int)
