(*  Title:      src/random_terms.ML
    ID:         $Id: random_terms.ML,v 1.000 2012/07/19 18:08:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   Universidad Politecnica de San Luis Potosi 2012

    Generation of random terms in beta normal form.
*)

signature RANDOM_TERMS =
sig
  val count_terms         : typ -> int -> int
  val random_term         : typ -> int -> term option
  val enumerate_terms     : typ -> int -> term list
  val enumerate_all_terms : typ -> int -> term list
end

structure DB_Random_Terms
(* : RANDOM_TERMS *)
= struct

fun type_cnt Env A =
    Env |> get_first (fn (typ, c) =>
                         if A = typ then SOME c
                         else NONE)
        |> the_default 0

fun type_cnt_inc Env A =
    (([],false), Env) |> Library.foldl (fn ((Env,updated), (typ, c)) =>
                                           if A = typ then (Env @ [(typ, c + 1)], true)
                                           else (Env @ [(typ, c)], updated))
                      |> (fn (Env, updated) => if updated then Env
                                               else Env @ [(A, 1)])

fun var_type A = (null o fst o strip_type) A

val arrow_type = not o var_type

val arg_type = domain_type

val res_type = range_type

fun valid_head_var_type_set A Env =
    let fun check_head Bis typ =
            if typ = A then SOME Bis
            else check_head (Bis @ [arg_type typ]) (res_type typ) handle General.Match => NONE
    in map_filter (fn (typ, _) =>
                      case check_head [] typ of
                        SOME Bis => SOME (Bis, typ)
                      | NONE => NONE) Env end

fun ndk n k = 
    let
      val offset = n - k + 2
      val max_elements = map (fn _ => offset) (1 upto k)
      val index_elements = (map (fn _ => 0) (1 upto (k - 1))) @ [~1]
      fun sumatories R index =
          case Utils.next_digit max_elements index of
            SOME index =>
            let val elements = map (fn i => i + 1) index
                val sum = Library.foldl (fn (s, i) => s + i) (0, elements)
            in if sum = n then sumatories (elements :: R) index
               else sumatories R index end
          | NONE => R
    in
      if k < 1 then []
      else if n < 1 then []
      else if n < k then []
      else sumatories [] index_elements
    end

fun count_term A Env s =
    if s < 1 then 0
    else if s = 1 then type_cnt Env A
    else if var_type A then count_head_var_term A Env s
    else (count_term (res_type A) (type_cnt_inc Env (arg_type A)) (s - 1))
         + (count_head_var_term A Env s)
and count_head_var_term A Env s =
    Library.foldl (fn (num_terms, (Bis, B)) => num_terms + count_head_var_arg_terms (Bis, B) Env s) (0, valid_head_var_type_set A Env)
and count_head_var_arg_terms (Bis, B) Env s =
    let val num_var_with_type_in_env = type_cnt Env B
        val m = length Bis
(*          val _ = tracing (string_of_int (s - 1 - m) ^ " : " ^ string_of_int m)*)
    in if num_var_with_type_in_env > 0
       then num_var_with_type_in_env *
            (Library.foldl
               (fn (num_terms, Ss) =>
                   let val multipl = if null Ss then 0
                                     else ((1,0), Ss) |> Library.foldl (fn ((m,i), si) => (m * (count_term (nth Bis i) Env si), i + 1))
                                                      |> fst
                   in num_terms + multipl end) (0, ndk (s - 1 - m) m))
       else 0
    end

(*fun count_terms A s = count_term A [] s*)

val memoized_count_terms_var =
    Synchronized.var "memoized_count_terms"
                     (IntType_Tab.empty : int IntType_Tab.table)

fun count_terms A s =
  Utils.memoize_function IntType_Tab.lookup IntType_Tab.update memoized_count_terms_var
  (fn (s, A) => count_term A [] s) (s, A)

fun index A = find_index (fn (typ, _) => typ = A)

fun normalize_closed_term level Vars _ (Free (n, _)) =
      Vars |> get_first (fn (name, l) => if name = n
                                         then SOME (Bound (level - l - 1))
                                         else NONE)
           |> the
    | normalize_closed_term level Vars Names (s $ t) =
      (normalize_closed_term level Vars Names s) $ (normalize_closed_term level Vars Names t)
    | normalize_closed_term level Vars Names (Abs (n, T, t)) =
      let val name = singleton (Name.variant_list Names) "x"
      in Abs (name, T, normalize_closed_term (level + 1) ((n, level) :: Vars) (name :: Names) t) end
    | normalize_closed_term _ _ _ _ = raise Library.ERROR "Should not be thrown"

local
  fun choose_arg_size (Bis, _) Env s num_arg_terms =
      let val rand_num = Random.random_range 0 (num_arg_terms - 1)
(*          val _ = tracing ("choose_arg_size (0, " ^ string_of_int (num_arg_terms - 1) ^ "): " ^ string_of_int rand_num)*)
          val m = length Bis
          fun semi_fold _ [] = raise Library.ERROR "Should not be thrown"
            | semi_fold num_terms (Ss :: list) =
              let val multipl = if null Ss then 0
                                else ((1,0), Ss) |> Library.foldl (fn ((m,i), si) => (m * (count_term (nth Bis i) Env si), i + 1))
                                                 |> fst
(*                  val _ = tracing ("multipl: " ^ string_of_int multipl)*)
                  val num_terms = num_terms + multipl
              (* considerar todos los Ss's que tengan a multipl > 0 *)
              in if rand_num < num_terms then Ss
                 else semi_fold num_terms list end
      in semi_fold 0 (ndk (s - 1 - m) m) end

  fun choose_head_var A Env s num_app_terms =
      let val rand_num = Random.random_range 0 (num_app_terms - 1)
(*          val vset = valid_head_var_type_set A Env*)
(*          val _ = tracing ("choose_head_var (0, " ^ string_of_int (num_app_terms - 1) ^ "): " ^
                           " valid set size: " ^ string_of_int (length vset) ^ " - " ^
                           string_of_int rand_num)*)
          fun semi_fold _ [] = raise Library.ERROR "Should not be thrown"
            | semi_fold num_terms ((Bis, B) :: list) =
              let val count_head_var = count_head_var_arg_terms (Bis, B) Env s
                  val num_terms = num_terms + count_head_var
(*                  val _ = tracing ("count_head_var: " ^ string_of_int count_head_var)*)
              (* Considerar todos los (Bis, B) cuyos count_head_var sea mayor que 0 *)
              in if rand_num < num_terms then ((Bis, B), choose_arg_size (Bis, B) Env s (count_head_var div type_cnt Env B))
                 else semi_fold num_terms list end
      in semi_fold 0 (valid_head_var_type_set A Env) end

(*  fun gen_var_term A Env =
      if type_cnt Env A = 0 then NONE
      else SOME (Free ("x." ^ string_of_int (index A Env) ^ "." ^
                       string_of_int (Random.random_range 0 (type_cnt Env A - 1)), A))*)
           
  fun gen_var_term A Env =
      let val tc = (type_cnt Env A - 1)
          val rand_num = Random.random_range 0 tc
(*          val _ = tracing ("gen_var_term (0, " ^ string_of_int tc ^ "): " ^ string_of_int rand_num)*)
      in
        if type_cnt Env A = 0 then NONE
        else SOME (Free ("x." ^ string_of_int (index A Env) ^ "." ^
                         string_of_int rand_num, A))
      end

  fun gen_term A Env s =
      if s < 1 then NONE
      else if s = 1 then
        if type_cnt Env A > 0 then gen_var_term A Env
        else NONE
      else if arrow_type A then
        let
          val total_num_term = count_term A Env s
          val num_lam_term = count_term (res_type A) (type_cnt_inc Env (arg_type A)) (s - 1)
          val rand_num = Random.random_range 0 (total_num_term - 1)
(*          val _ = tracing ("gen_term (0, " ^ string_of_int (total_num_term - 1) ^ "): " ^ 
                           " num_lambda_terms: " ^ string_of_int num_lam_term ^ 
                           " - "^ string_of_int rand_num)*)
        in if total_num_term = 0 then NONE
           else if (*Random.random_range 0 (total_num_term - 1)*) rand_num < num_lam_term
           then SOME (gen_lam_term (arg_type A) (res_type A) Env s)
           else SOME (gen_app_term A Env s (total_num_term - num_lam_term))
        end
      else SOME (gen_app_term A Env s (count_term A Env s))
  and gen_lam_term arg_typ res_typ Env s =
      let val Env = type_cnt_inc Env arg_typ
          val name = "x." ^ string_of_int (index arg_typ Env) ^ "." ^
                     string_of_int (type_cnt Env arg_typ - 1)
          val body = gen_term res_typ Env (s - 1)
      in Abs (name, arg_typ, the body) end
  and gen_app_term A Env s num_app_terms =
      let val ((Bis, B), Ss) = choose_head_var A Env s num_app_terms
          val head_var = the (gen_var_term B Env)
          val Tis = (([], 0), Ss) |> Library.foldl (fn ((Tis, i), si) => (Tis @ [the (gen_term (nth Bis i) Env si)], i + 1))
                                  |> fst
      in Library.foldl (fn (t, ti) => t $ ti) (head_var, Tis) end

in

fun random_term A s =
    case gen_term A [] s of
      SOME t => SOME (normalize_closed_term 0 [] [] t)
    | NONE => NONE

end

local
  fun choose_arg_size (Bis, _) Env s =
      let val m = length Bis
          fun semi_fold [] = []
            | semi_fold (Ss :: list) =
              let val multipl = if null Ss then 0
                                else ((1,0), Ss) |> Library.foldl (fn ((m,i), si) => (m * (count_term (nth Bis i) Env si), i + 1))
                                                 |> fst
              (* considerar todos los Ss's que tengan a multipl > 0 *)
              in if 0 < multipl then Ss :: semi_fold list
                 else semi_fold list end
      in semi_fold (ndk (s - 1 - m) m) end

(*  fun choose_arg_size (Bis, _) Env s num_arg_terms =
      let val m = length Bis
      in ndk (s - 1 - m) m end*)

  fun choose_head_var A Env s =
      let fun semi_fold _ [] = []
            | semi_fold num_terms ((Bis, B) :: list) =
              let val count_head_var = count_head_var_arg_terms (Bis, B) Env s
                  val num_terms = num_terms + count_head_var
(*                  val _ = tracing ("count_head_var: " ^ string_of_int count_head_var)*)
              (* Considerar todos los (Bis, B) cuyos count_head_var sea mayor que 0 *)
              in ((Bis, B), choose_arg_size (Bis, B) Env s) ::
                 semi_fold num_terms list
              end
      in semi_fold 0 (valid_head_var_type_set A Env) end

  fun gen_var_term A Env =
      let val tc = (type_cnt Env A - 1)
      in
        if type_cnt Env A = 0 then []
        else 0 upto tc
              |> map (fn rand_num => 
                    Free ("x." ^ string_of_int (index A Env) ^ "." ^
                         string_of_int rand_num, A))
      end

  fun gen_term A Env s =
      if s < 1 then []
      else if s = 1 then
        if type_cnt Env A > 0 then gen_var_term A Env
        else []
      else if arrow_type A then
        let
          val total_num_term = count_term A Env s
        in if total_num_term = 0 then []
           else gen_lam_term (arg_type A) (res_type A) Env s @
                gen_app_term A Env s
        end
      else gen_app_term A Env s
  and gen_lam_term arg_typ res_typ Env s =
      let val Env = type_cnt_inc Env arg_typ
          val name = "x." ^ string_of_int (index arg_typ Env) ^ "." ^
                     string_of_int (type_cnt Env arg_typ - 1)
          val bodies = gen_term res_typ Env (s - 1)
      in map (fn body => Abs (name, arg_typ, body)) bodies end
  and gen_app_term A Env s =
      let val rr = s |> choose_head_var A Env
                     |> maps (fn ((Bis, B), Sss) => map (fn Ss => ((Bis, B), Ss)) Sss)
          fun f1 ((Bis, B), Ss) =
            let val head_vars = gen_var_term B Env
              fun exhaust f head_var = 
                case f () of
                  SOME Tis => Library.foldl (fn (t, ti) => t $ ti) (head_var, Tis) ::
                              exhaust f head_var
                | NONE => []
              val Tis = map2 (fn i => fn si => gen_term (nth Bis i) Env si) (0 upto length Ss - 1) Ss
        in maps (fn x => exhaust (Utils.lazy_one_of_each Tis) x) head_vars end
      in maps f1 rr end

in

(*fun enumerate_terms A s =
    s |> gen_term A []
      |> map (fn t => normalize_closed_term 0 [] [] t)*)

val memoized_enumerate_terms_var =
    Synchronized.var "memoized_enumerate_terms"
                     (IntType_Tab.empty : term list IntType_Tab.table)

fun enumerate_terms A s =
  Utils.memoize_function IntType_Tab.lookup IntType_Tab.update memoized_enumerate_terms_var
  (fn (s, A) => s |> gen_term A []
                  |> map (fn t => normalize_closed_term 0 [] [] t)) (s, A)

fun enumerate_all_terms A s =
  1 upto s
    |> maps (enumerate_terms A)

end

end

structure Random_Terms : RANDOM_TERMS = DB_Random_Terms

