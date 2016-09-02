(*  Title:      util/smt.ML
    ID:         $Id: smt.ML,v 1.00 2016/24/08 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

SMT-LIB file reader/converter.
*)

signature SMT_CONVERTER =
sig

end

structure DB_SMT_Converter
(* : SMT_READER *)
= struct

open SMTLIB

val smt_commands =
  ["declare-datatypes",
   "define-fun-rec",
   "assert-not",
   "check-sat"]

fun available_var ctxt name =
  if exists (fn cmd => cmd = name) smt_commands
  then true
  else case try (Syntax.read_term ctxt) name of
         SOME (Free _) => true
        | _ => false

fun syms_of_tree _ tab (Num _) = tab
  | syms_of_tree _ tab (Dec _) = tab
  | syms_of_tree _ tab (Str _) = tab
  | syms_of_tree _ tab (Key _) = tab
  | syms_of_tree ctxt tab (Sym s) =
    if Str_Tab.defined tab s
    then tab
    else if available_var ctxt s
         then Str_Tab.update (s, s) tab
         else let fun find_name names =
                  let val name = singleton (Name.variant_list names) s
                  in
                    if available_var ctxt name
                    then name
                    else find_name (name :: names)
                  end
              in Str_Tab.update (s, find_name (Str_Tab.keys tab)) tab
              end
  | syms_of_tree ctxt tab (S l) =
      (tab, l)
      |> Library.foldl (fn (tab, e) => syms_of_tree ctxt tab e)

fun sanitize_tree (_, (Num i)) = Num i
  | sanitize_tree (_, (Dec i)) = Dec i
  | sanitize_tree (_, (Str s)) = Str s
  | sanitize_tree (_, (Key s)) = Key s
  | sanitize_tree (tab, (Sym s)) = Sym ((the o Str_Tab.lookup tab) s)
  | sanitize_tree (tab, (S l)) =
      l |> map (fn e => sanitize_tree (tab, e))
        |> S

fun s_expressions ctxt str =
  let fun scan [] _ _ s_exps =
            s_exps |> rev
                   |> pair (Str_Tab.empty, [])
                   |> Library.foldl
                        (fn ((tab, trees), expr) =>
                            let val (tab, e) = ((fn e => let val tab = syms_of_tree ctxt
                                                                              tab
                                                                              e
                                                   in (tab, e) end) o
                                                   SMTLIB.parse o 
                                                   single o 
                                                   String.implode) expr
                                val tree = sanitize_tree (tab, e)
                            in (tab, tree :: trees) end)
                   |> rev o snd
        | scan (c :: chars) stack s s_exps =
          case c of
            #"(" => scan chars (#"(" :: stack) (#"(" :: s) s_exps
          | #")" => let val stack = case stack of
                                     _ :: stack => stack
                                   | [] => raise ERROR "Malformed s expression"
                    in if length stack = 0
                       then scan chars stack [] ((rev (#")" :: s)) :: s_exps)
                       else scan chars stack (#")" :: s) s_exps
                    end
          | _ => scan chars stack (c :: s) s_exps
  in scan (String.explode str) [] [] [] end

fun typ_args_to_isabelle typ_args =
  typ_args |> map (fn (Sym n) => "'" ^ n
                   | _ => raise ERROR ("Malformed s expression on type argument declaration: "
                                        ^ (typ_args |> map str_of
                                                    |> space_implode ",")))
           |> space_implode ","
           |> (fn str => if str = "" 
                         then ""
                         else enclose "(" ")" str)

fun varify typ_vars n =
  if exists (fn m => n = m) typ_vars
  then "'" ^ n
  else n

fun typ_to_isabelle typ_vars (S [Sym n]) = varify typ_vars n
  | typ_to_isabelle _ (S (Sym n :: l)) =
      typ_args_to_isabelle l ^ " " ^ n
  | typ_to_isabelle _ s = raise ERROR ("Malformed s expression on type declaration: "
                                        ^ (str_of s))

fun sym_of_s_expr (S [S l]) = sym_of_s_expr (S l)
  | sym_of_s_expr (S [Sym n]) = n
  | sym_of_s_expr (Sym n) = n
  | sym_of_s_expr e = raise ERROR ("Malformed s expression on simple type argument declaration: " ^ str_of e)

fun cons_of_s_expr typ_vars (S [S l]) = cons_of_s_expr typ_vars (S l)
  | cons_of_s_expr typ_vars (S (c :: cs)) = 
      let val constructor = sym_of_s_expr c
          fun args (S [Sym n]) = n
            | args (S [Sym d, Sym c]) = "(" ^ d ^ " : \"" ^ varify typ_vars c ^ "\")"
            | args (S [Sym d, S l]) = "(" ^ d ^ " : \"" ^ typ_to_isabelle typ_vars (S l) ^ "\")"
            | args s = raise ERROR ("Malformed s expression on constructor's argument declaration: "
                                        ^ (str_of s))
      in constructor ^ " " ^ (cs |> map args
                                 |> space_implode " ") end
  | cons_of_s_expr _ (Sym n) = n
  | cons_of_s_expr _ e = raise ERROR ("Malformed s expression on type argument declaration: " ^ str_of e)

fun constructors_to_isabelle typ_vars (S [S l]) =
       constructors_to_isabelle typ_vars (S l)
  | constructors_to_isabelle typ_vars (S (n :: cs)) =
      let val lhs = sym_of_s_expr n
          val cases = cs |> map (cons_of_s_expr typ_vars)
                         |> space_implode " | "
      in lhs ^ " = " ^ cases end
  | constructors_to_isabelle _ s = raise ERROR ("Malformed s expression on constructor declaration: " ^ str_of s)

fun translate_datatype (S [Sym "declare-datatypes", S typ_args, S cs]) =
  let val typ_vars = typ_args |> map (fn (Sym n) => n
                      | _ => raise ERROR ("Malformed s expression on type argument declaration: "
                                        ^ (typ_args |> map str_of
                                                    |> space_implode ",")))
  in
    "datatype " ^ typ_args_to_isabelle typ_args ^ " " ^ constructors_to_isabelle typ_vars (S cs)
  end
  | translate_datatype s = raise ERROR ("Malformed s expression on datatype declaration: " ^ str_of s)


end

structure SMT_Converter : SMT_CONVERTER = DB_SMT_Converter

