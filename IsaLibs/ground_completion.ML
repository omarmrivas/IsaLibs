(*  Title:      src/completion.ML
    ID:         $Id: completion.ML,v 2.000 2012/04/20 12:42:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Politecnica de San Luis Potosi
    Copyright   Universidad Politecnica de San Luis Potosi 2011

An implementation of Unfailing Knuth Bendix (Baader and Nipkow's "Term Rewriting and All That" 
and Leo Bachmair, Nachum Dershowwitz and David A. Plaisted's "Completion without Failure")
Completion Algorithm for Isabelle.
*)

signature COMPLETION =
sig
  exception ORIENTATION of string * thm

  val max_time_in_completion        : int Config.T

  val generate_cps                  : bool Config.T

  val unify_inst                    : Proof.context -> Envir.env -> 
                                      (ctyp * ctyp) list * (cterm * cterm) list

  val discriminate_rules            : Proof.context -> (thm list -> bool) -> 
                                      thm list -> thm list * thm list
  val scpairs                       : theory -> (thm * thm) -> thm list
  val semi_critical_pairs           : theory -> order -> thm list -> thm list -> thm list
  val memoized_joinable'            : Proof.context -> (thm list -> bool) -> (term * int) list -> 
                                      thm list -> term -> bool
  val memoized_joinable             : Proof.context -> (thm list -> bool) -> (term * int) list -> 
                                      thm list -> thm -> bool

  val run_completion                : thm list -> Proof.context -> (thm list -> bool) ->
                                      thm list -> thm -> thm list
  val run_completion'               : thm list -> Proof.context -> (thm list -> bool) ->
                                      thm list -> thm -> thm list * thm list
(*  val perform_unfailing_completion  : Attrib.binding -> Method.text -> thm list -> thm -> (thm list * thm list) option
  val get_any_ordering              : Attrib.binding -> Method.text -> thm list -> thm -> (thm list * thm list) option*)
end

structure DB_Completion
(* : COMPLETION *)
= struct

(* Error generated when an ordering cannot orient an equation *)
(* during completion.                                         *)

exception ORIENTATION of string * thm
exception RESTART_COMPLETION of string * thm list

val (max_time_in_completion, setup_max_time_in_completion) = Attrib.config_int @{binding "max_time_in_completion"} (K 180)
val (generate_cps, setup_generate_cps) = Attrib.config_bool @{binding "generate_cps"} (K true)

(*fun ord_to_str l = 
    l |> map (fn (Const (n,_),i) => n ^ string_of_int i
               | (Var ((n,idx),_),i) => n ^ string_of_int idx ^ string_of_int i
               | _ => "")
      |> space_implode ""*)

(* Power set of a set. Sets are implemented as lists *)
fun subsets s =
    let 
      val s' = map (fn e => [[],[e]]) s
      fun subsets_ t l = 
          case l of
            (h::[]) :: [] => [t @ h]
          | (h::t1) :: [] => (t @ h) :: subsets_ t [t1]
          | (h::t1) :: t2 => ((subsets_ (t @ h) t2) @
                              (subsets_ t (t1 :: t2)))
          | _ => []
    in subsets_ [] s' end

(* instantiation utilities *)
fun prep_trm thy env (x, (T, _)) =
    (Thm.cterm_of thy (Var (x, Envir.norm_type (Envir.type_env env) T)), Thm.cterm_of thy (Envir.norm_term env (Var (x, T))))

fun prep_ty thy env (x, (S, _)) =
      (Thm.ctyp_of thy (TVar (x, S)), Thm.ctyp_of thy (Envir.norm_type (Envir.type_env env) (TVar (x, S))))

fun unify_inst ctxt env = 
    let
      val ctenv = env |> Envir.term_env
                      |> Vartab.dest
                      |> map (prep_trm ctxt env)
      val ctyenv = env |> Envir.type_env
                       |> Vartab.dest
                       |> map (prep_ty ctxt env)
    in
      (ctyenv,ctenv)
    end

(* left-linear equations are preferred when any orientation is terminating *)
fun is_linear thm =
    let val (_, args) = (strip_comb o fst o Logic.dest_equals o Thm.plain_prop_of) thm
    in not (has_duplicates (op =) ((fold o fold_aterms)
                                     (fn Var (v, _) => cons v | _ => I) args [])) end

(* gives a left-linear orientation if possible *)
fun linear_if_possible R = if is_linear R then R else Utils.commute_meta_eq R

val my_abs_conv = fn ctxt => fn conv => Conv.abs_conv (fn _ => conv) ctxt

fun varify_global ctxt thm =
    let
      val frees = [] |> Term.add_frees (Thm.full_prop_of thm) |> map fst
    in [thm] |> Variable.export (snd (Variable.add_fixes frees ctxt)) ctxt
             |> hd end

fun rewrite_rule_extra_vars prems elhs erhs =
  let
    val elhss = elhs :: prems
    val tvars = fold Term.add_tvars elhss []
    val vars = fold Term.add_vars elhss []
  in
    erhs |> Term.exists_type (Term.exists_subtype
      (fn TVar v => not (member (op =) tvars v) | _ => false)) orelse
    erhs |> Term.exists_subterm
      (fn Var v => not (member (op =) vars v) | _ => false)
  end

(* Semi-Critical pairs of th1 and th2 *)
fun scpairs thy (th1, th2) =
    let
(*      val _ = tracing ("th1: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th1))
      val _ = tracing ("th2: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th2))*)
      val ctxt = Context.proof_of (Context.Theory thy)
      val (pat, rhs1) = Utils.dest_equation th1
      val th2' = Drule.incr_indexes th1 th2
      val (obj, rhs2) = Utils.dest_equation th2'
      val paty = type_of pat
      val maxidx_typ = Term.maxidx_typ paty 0
      val valid_rewrites = Pattern.pattern pat andalso Pattern.pattern obj (* Higher-order patterns *)
                           andalso not (is_Var pat) andalso not (is_Var obj) (* Not a var on lhs *)
                           andalso not (rewrite_rule_extra_vars [] pat rhs1)
                           andalso not (rewrite_rule_extra_vars [] obj rhs2) (* does not introduce new Vars or TVars *)
      (* Does pat match a subterm of obj? *)
      fun msub bounds frees obj f =
          (case obj of
             Abs (_, T, t) =>
             let
               val unifier = if can (Sign.typ_unify thy (T,paty)) (Vartab.empty,Term.maxidx_typ T maxidx_typ)
                             then Unify.unifiers (Context.Theory thy,(Envir.empty 1),[(pat,obj)]) handle ListPair.UnequalLengths => Seq.empty
                                                                                        | TERM _ => Seq.empty
                             else Seq.empty
               val (new_free,new_abs) = Term.dest_abs (Name.bound bounds, T, t)
             in Seq.append (Seq.map (pair f) unifier)
                           (msub (bounds + 1) (new_free :: frees)
                                 new_abs
                                 (f o (my_abs_conv ctxt))) end
           | t $ u => (case (fst o Term.strip_comb) obj of
                         (* According to Nipkow's definition of critical pairs, the head must not be a variable *)
                         Var _ =>  Seq.append (msub bounds frees t (f o Conv.fun_conv)) (msub bounds frees u (f o Conv.arg_conv))
                       | _ => let
                           val unifier = if can (Sign.typ_unify thy (type_of obj,paty)) (Vartab.empty,Term.maxidx_typ (type_of obj) maxidx_typ)
                                         then Unify.unifiers (Context.Theory thy,(Envir.empty 1),[(pat,obj)]) handle ListPair.UnequalLengths => Seq.empty
                                                                                                    | TERM _ => Seq.empty
                                         else Seq.empty
                         in Seq.append (Seq.map (pair f) unifier)
                                       (Seq.append (msub bounds frees t (f o Conv.fun_conv)) (msub bounds frees u (f o Conv.arg_conv))) end)
           | _ => Seq.empty)
    in if valid_rewrites then
         msub 0 [] obj I
              |> Seq.list_of
              |> map_filter (fn (conv,(env,_)) => SOME (conv,unify_inst ctxt env))
              |> map (fn (conv,inst) => (conv,apply2 (Drule.instantiate_normalize inst) (th1,th2')))
              |> map (fn (conv,(r1,r2)) => Conv.fconv_rule ((Conv.fun_conv o Conv.arg_conv o conv) (Conv.rewr_conv (varify_global ctxt r1))) r2)
              |> filter_out (fn th => EQUAL = (Term_Ord.term_ord o Utils.dest_equation) th)
       else []
    end

fun scpairs_aux thy (th1, th2) =
    let
      val cth1 = Utils.commute_meta_eq th1
      val cth2 = Utils.commute_meta_eq th2
    in
      scpairs thy (th1, th2) @
      scpairs thy (th1, cth2) @
      scpairs thy (cth1, th2) @
      scpairs thy (cth1, cth2)
    end

fun semi_critical_pairs thy ord R1 R2 =
  ([],R1) |> Library.foldl (fn (pairs,th1) => maps (fn th2 => scpairs_aux thy (th1, th2)) R2 @ pairs)
          |> map (Utils.orient_meta_rule thy ord)
          |> Utils.make_theorem_set

(* Ordered Rewriting *)

(* Empirical test for termination of ac rewriting *)
(* This test is necessarily incomplete due to the halting problem *)
fun ac_termination ctxt (equations, rules) th =
    let val max_size = (equations @ rules)
                         |> map size_of_thm
                         |> pair 0
                         |> Library.foldl (op +)
                         |> (fn c => if c = 0 then 1000 else
                                     c * Drule.size_of_thm th)
        fun update_net thm net =
          Net.insert_term (is_equal o Thm.thm_ord) (Thm.full_prop_of thm, thm) net
        fun test_procs set s (proc :: procs) term =
              let val t = simplify (ctxt addsimps [proc]) s
(*                  val _ = tracing ("Eq: " ^ Utils.str_of_thms [proc])
                  val _ = tracing ("1) s - t: " ^ Utils.str_of_thms [s, t])*)
              in if is_equal (Thm.thm_ord (s, t))
                 then test_procs set t procs term
                 else if can (update_net t) set
                 then test_procs (update_net t set) t procs term
                 else false
              end
          | test_procs set s [] term = test_rules set s (th :: rules) term
        and test_rules set s (rule :: rules) term =
              let val t = simplify (ctxt addsimps [rule]) s
(*                  val _ = tracing ("Rule: " ^ Utils.str_of_thms [rule])
                  val _ = tracing ("2) s - t: " ^ Utils.str_of_thms [s, t])
                  val _ = tracing (if is_equal (Thm.thm_ord (s, t)) then "si" else "no")*)
              in if is_equal (Thm.thm_ord (s, t))
                 then test_rules set t rules term
                 else if can (update_net t) set
                 then test_rules (update_net t set) t rules term
                 else false
              end
          | test_rules set s [] term =
              if (is_equal o Thm.thm_ord) (s, term)
              then true
              else if size_of_thm s < max_size
              then test_procs set s equations s
              else false
    fun test thm = 
      test_procs (update_net thm Net.empty) thm equations thm
  in forall test [th] end

(* This function uses only a subset of thms which is guarantied to terminate *)
fun discriminate_rules ctxt terminates thms =
    thms (*|> Utils.make_theorem_set*)
         |> map (fn th => (th, Drule.size_of_thm th))
         |> sort (int_ord o (apply2 snd))
         |> map fst
         |> pair ([],[])
         |> Library.foldl
         (fn ((equations,rules),th) =>
             if Utils.permutative_rule th
             then (th :: equations, rules)
             else (equations, th :: rules))
         |> (fn (equations, potential_rules) => ((equations, []), rev potential_rules))
         |> Library.foldl
         (fn ((equations,rules),th) =>
             if terminates (th :: rules) andalso
                ac_termination ctxt (equations, rules) th
             then (equations, th :: rules)
             else if terminates ((Utils.commute_meta_eq th) :: rules) andalso
                     ac_termination ctxt (equations, rules) (Utils.commute_meta_eq th)
             then (equations, Utils.commute_meta_eq th :: rules)
             else
               let val thy = Thm.theory_of_thm th
                   val _ = tracing ("Incompatible rule: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th))
                   val _ = tracing ("with: " ^ Utils.str_of_thms (equations @ rules))
               in (equations, rules)
               end)
(*         |> apply2 Utils.make_theorem_set*)

val discriminate_rules_var
      = Synchronized.var "discriminate_rules"
                         (Thm_List_Tab.empty : (thm list * thm list) Thm_List_Tab.table)

fun memoized_discriminate_rules ctxt terminates (thms as th :: _) =
  let val thms = thms |> Utils.make_theorem_set
                      |> sort Thm.thm_ord
      val (eqs, rules) = Utils.memoize_function Thm_List_Tab.lookup Thm_List_Tab.update discriminate_rules_var
                            (discriminate_rules ctxt terminates) thms
      val thy = Thm.theory_of_thm th
      fun test thm1 thm2 = (Pattern.equiv thy o apply2 Thm.full_prop_of) (thm1, thm2)
  in Library.foldl (fn ((eqs', rules'), th) => if exists (test th) eqs
                                               then (th :: eqs', rules')
                                               else if exists (test th) rules
                                               then (eqs', th :: rules')
                                               else (eqs', rules')) (([], []), thms)
  end
| memoized_discriminate_rules _ _ [] = ([], [])

fun ordered_simpset_without_simprocs ctxt terminates thms =
    let val ctxt = empty_simpset ctxt
        val (_,rules) = memoized_discriminate_rules ctxt terminates thms
    in ctxt addsimps rules
    end

fun ordered_simpset ctxt terminates thms =
    let val ctxt = empty_simpset ctxt
        val (equations, rules) = memoized_discriminate_rules ctxt terminates thms
    in ctxt addsimps (equations @ rules)
    end

fun rewrite_rule ctxt terminates thms =
  let val ctxt = ordered_simpset_without_simprocs ctxt terminates thms
  in simplify ctxt end

(* Ordered Rewriting *)

fun normalize_part ctxt terminates fun_arg TRS thm =
  let val ctxt = ordered_simpset_without_simprocs ctxt terminates TRS
  in Conv.fconv_rule (fun_arg (Simplifier.rewrite ctxt)) thm end
(*  in Conv.fconv_rule (fun_arg (Raw_Simplifier.rewrite ctxt true [])) thm end*)

val ground_debug = Unsynchronized.ref false
val ground_debug2 = Unsynchronized.ref false
val completion_debug = Unsynchronized.ref false

(* Ground joinability test *)

fun print_orders ctxt orders = ([], orders)
                                 |> Library.foldl (fn (s, (t, i)) => ((Syntax.string_of_term ctxt t) ^ " : " ^ Int.toString i) :: s)
                                 |> space_implode ", "
                                 |> enclose "[" "]"

fun ground_joinable ctxt terminates f_map (e, E) = 
  let (*val s_t = Thm.full_prop_of e
      val thy = Thm.theory_of_thm e*)
      val ctxt = empty_simpset ctxt
      val (equations, rules) = memoized_discriminate_rules ctxt terminates E
(*      val _ = tracing ("E: " ^ Utils.str_of_thms E)
      val _ = tracing ("Equations: " ^ Utils.str_of_thms equations)
      val _ = tracing ("Rules: " ^ Utils.str_of_thms rules)
      val _ = tracing ("e: " ^ Utils.str_of_thms [e])*)
      val f_map = sort (int_ord o (apply2 snd)) f_map
      val vars = e |> Thm.full_prop_of
                   |> (fn t => Term.add_vars t [])
                   |> map Var
  in vars
        |> Orders.extend_ord_eval
        (fn ord =>
                 ord |> pair ([],[])
                     |> Library.foldl (fn ((consts_map, vars_map), (Var V, I)) => (consts_map, (V, I) :: vars_map)
                                        | ((consts_map, vars_map), (Const C, I)) => ((C, I) :: consts_map, vars_map)
                                        | ((consts_map, vars_map), (_, _)) => (consts_map, vars_map))
(*                     |> tap (fn (cs, vs) => 
                                let val r = (map (apfst Const) cs @ map (apfst Var) vs)
                                in (tracing o print_orders ctxt) r end)*)
                     |> Orders.map_term_to_int
                     |> Term_Ord.term_lpo
                     |> (fn g_ord =>
                            let fun termless tu = (g_ord tu = LESS)
                                val ctxt = ctxt |> Simplifier.set_termless termless
                                                |> (fn ctxt => ctxt addsimps (equations @ rules))
                            in
                            e |> simplify ctxt
                              |> Utils.dest_equation
                              |> (is_equal o g_ord)
                            end)) f_map
 end

val memoized_joinability_var = Synchronized.var "memoized_joinability"
                      (Thm_Thm_List_Tab.empty : bool Thm_Thm_List_Tab.table)

fun memoized_joinable ctxt terminates f_map E e =
  let val E = sort Thm.thm_ord E
  in Utils.memoize_function Thm_Thm_List_Tab.lookup Thm_Thm_List_Tab.update memoized_joinability_var
                            (ground_joinable ctxt terminates f_map) (e, E) end

fun memoized_joinable' ctxt terminates f_map E e =
  let val e = Prover.cheat_prover ctxt e
  in memoized_joinable ctxt terminates f_map E e end

(* Heuristics to speed up completion *)

(* improve simplification by transforming something of the form *)
(* c(x) = x(y) into x = y (if the latter is a theorem) *)
local
  val pat = @{term_pat "?X (?lhs :: ?'a) \<equiv> ?X (?rhs :: ?'a)"}
  val pat' = @{term_pat "(?lhs :: ?'a) = (?rhs :: ?'a)"}
(*  val method = Method.Basic (SIMPLE_METHOD o InductiveTacs4.bef_induct_auto_tac)*)
  val method = Method.Basic (SIMPLE_METHOD o (InductiveTacs4.bef_induct_auto_tac (Unsynchronized.ref Net.empty)))
in
fun heuristic1 ctxt proof_timeOut lemmas rule : thm option =
  let val thy = Proof_Context.theory_of ctxt
      val obj = rule |> Thm.full_prop_of
                     |> Logic.unvarify_global o Term_Subst.zero_var_indexes
      val matchers = Pattern.first_order_match thy (pat,obj) (Vartab.empty, Vartab.empty)
      val conj = pat' |> Envir.subst_term matchers
                      |> HOLogic.mk_Trueprop
      val timeOut = Config.get ctxt Counter_Example.max_time_in_counter_ex
  in case Counter_Example.unfalsified_conjecture ctxt timeOut conj of
      SOME conj => Prover.prove ctxt (SOME lemmas) method conj proof_timeOut
    | NONE => NONE
  end handle Pattern.MATCH => NONE
end

fun add_rule ctxt terminates (th,E,S,R) =
    let
      fun simpl ([],E',R') = (E',R')
        | simpl (u :: U,E',U') = 
          let
            val (g,_) = Utils.dest_equation u
            val u' = normalize_part ctxt terminates (Conv.fun_conv o Conv.arg_conv) [th] u
            val (g',_) = Utils.dest_equation u'
          in
            if EQUAL = Term_Ord.term_ord (g,g') then
              let val u'' = normalize_part ctxt terminates Conv.arg_conv (th :: R @ S) u
              in simpl (U,E', u'' :: U') end
            else simpl (U,u' :: E', U')
          end
      val (E',S') = simpl (S,E,[])
      val (E'',R') = simpl (R,E',[])
    in (E'',th :: S',R') end

fun min_rule (rl,_,[],R') = (rl,R')
  | min_rule (rl,n,th::R,R') = 
    let
      val m = Utils.rule_int_ord th
    in if list_ord int_ord (m, n) = LESS then min_rule (th,m,R,rl :: R')
       else min_rule (rl,n,R,th :: R')
    end

fun choose ctxt proof_timeOut lemmas (th :: R) =
      let val (rule, rules) = min_rule (th,Utils.rule_int_ord th,R,[])
      in case heuristic1 ctxt proof_timeOut lemmas rule of
            SOME thm => (Utils.obj_to_meta thm, rule :: rules)
          | NONE => (rule, rules)
      end
  | choose _ _ _ [] = raise ERROR "Empty rule set"

fun print_completion (E,S,R) =
    let 
      fun str R = R |> map (fn th => (Thm.theory_of_thm th, Thm.full_prop_of th))
                    |> map (fn (thy, t) => Syntax.string_of_term_global thy t)
                    |> commas
      val E_str = str E
      val S_str = str S
      val R_str = str R
      val _ = tracing ("E = <" ^ E_str ^ ">")
      val _ = tracing ("S = <" ^ S_str ^ ">")
      val _ = tracing ("R = <" ^ R_str ^ ">")
    in () end

datatype ORI = NORMAL of (thm list * thm list) | RESTART of (thm list)

fun orient ctxt global_meta_rws ord terminates f_map =
    let fun ori ([],S,R) = NORMAL (S,R)
          | ori (th :: E,S,R) =
            let
              val thy = Thm.theory_of_thm th
              (*val _ = tracing ("Before simplification: " ^ Syntax.string_of_term_global thy (Thm.full_prop_of th)) *)
              val th' = rewrite_rule ctxt terminates (S @ R) (linear_if_possible th)
              (*val _ = tracing ("Antes: " ^ str_of_thms_raw [th']) *)
              val th' = th' |> Utils.meta_to_obj
(*                            |> Raw_Simplifier.rewrite_rule ctxt global_meta_rws*)
                            |> Utils.orient_rule thy ord
                            |> Utils.obj_to_meta
                            |> (fn th => if Thm.equiv_thm (@{thm "TrueI"},th)
                                         then Utils.obj_to_meta @{thm "refl"}
                                         else th)
              (*val _ = tracing ("Después: " ^ Utils.str_of_thms [th'])*)
              val (_, rules) = discriminate_rules (empty_simpset ctxt) terminates (S @ R)
              val joinable = memoized_joinable ctxt terminates f_map (S @ R) th'
              fun restart () = NONE
              val (s,t) = Utils.dest_equation th'
              val comm_th' = Utils.commute_meta_eq th'
            in
              case restart () of
                SOME thms => RESTART thms
              | NONE =>
                if joinable then ori (E,S,R)
                else if Utils.permutative_eq (s, t)
                     then ori (add_rule ctxt terminates (th',E,S,R))
                     else if terminates (th' :: rules)
                     then ori (add_rule ctxt terminates (th',E,S,R))
                     else ori (add_rule ctxt terminates (comm_th',E,S,R))
            end
    in ori end

(*fun make_irreducible _ _ _ TRS [] = TRS
  | make_irreducible ctxt terminates f_map R (th :: TRS) =
    if memoized_joinable ctxt terminates f_map (R @ TRS) th
    then R @ TRS
    else make_irreducible ctxt terminates f_map (th :: R) TRS*)

fun make_irreducible _ _ _ TRS [] = TRS
  | make_irreducible ctxt terminates f_map R (th :: TRS) =
    if memoized_joinable ctxt terminates f_map (R @ TRS) th
    then make_irreducible ctxt terminates f_map R TRS
    else make_irreducible ctxt terminates f_map (th :: R) TRS

fun complete global_meta_rws thy ctxt ord generate_cps terminates f_map E =
    let
      val proof_timeOut = Config.get ctxt Prover.max_time_in_proof
      val E = E |> map (fn th => (Utils.rule_int_ord th, th))
                |> sort ((list_ord int_ord) o (apply2 fst))
                |> map snd
      val E' = E
      fun compl (E,S,R) = case (if !completion_debug then print_completion (E,S,R) else ();
                                orient ctxt global_meta_rws ord terminates f_map (E,S,R)) of
                            NORMAL ([],R') => R'
                          | NORMAL (S',R') => let (*val lemmas = (S @ R) |> memoized_discriminate_rules terminates
                                                                           |> (fn (x, y) => x @ y)*)
                                                  val (rl,S'') = choose ctxt proof_timeOut E' S'
                                                  val _ = if !completion_debug then tracing ("Choosed: " ^ Utils.str_of_thms [rl])
                                                          else ()
                                                  val cps = if generate_cps then
                                                              ((semi_critical_pairs thy ord [rl] R') @
                                                               (semi_critical_pairs thy ord R' [rl]) @
                                                               (semi_critical_pairs thy ord [rl] [rl]))
                                                                |> Utils.make_theorem_set
                                                                |> map (fn th => (Utils.rule_int_ord th, th))
                                                                |> sort ((list_ord int_ord) o (apply2 fst))
                                                                |> map snd
(*                                                                |> map (Raw_Simplifier.rewrite_rule ctxt global_meta_rws)*)
                                                            else []
                                                  val _ = if !completion_debug then tracing ("Critical pairs: " ^ Utils.str_of_thms cps) else ()
                                              in compl (cps,S'',rl :: R') end
                          | RESTART thms => (tracing ("Restarting completion..." ^ Utils.str_of_thms (E' @ thms));
                                             complete global_meta_rws thy ctxt ord generate_cps terminates f_map (E' @ thms))
    in
      (E,[],[]) |> compl
(*                |> tap (fn TRS => tracing ("Done 0: " ^ Utils.str_of_thms TRS))*)
                |> make_irreducible ctxt terminates f_map []
                |> tap (fn TRS => tracing ("Done: " ^ Utils.str_of_thms TRS))
    end

fun run_completion global_meta_rws ctxt terminates E e =
  let val thy = ctxt |> Proof_Context.theory_of
      val generate_cps = Config.get ctxt generate_cps
      val _ = tracing ("Completing: " ^ Utils.str_of_thms E)
      val _ = tracing ("with: " ^ Utils.str_of_thms [e])
      val f_map = Utils.definitional_dependencies thy ([], Thm.full_prop_of e)
                    |> map Const
                    |> map (rpair 0)
  in [complete global_meta_rws thy ctxt LESS generate_cps terminates f_map,
      complete global_meta_rws thy ctxt GREATER generate_cps terminates f_map]
      |> Par_List.get_some (fn f => SOME (f (e :: E)))
      |> the
  end

fun run_completion' global_meta_rws ctxt terminates E e =
    let val rules = run_completion global_meta_rws ctxt terminates E e
        val additions = filter_out (fn r => exists (Thm.equiv_thm o pair r) E) rules
        val deletions = filter_out (fn e => exists (Thm.equiv_thm o pair e) rules) E
    in (additions, deletions) end

end

structure Ground_Completion : COMPLETION = DB_Completion
