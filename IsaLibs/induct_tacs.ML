(*  Title:      util/induct_tacs.ML
    ID:         $Id: induct_tacs.ML,v 1.010 2015/15/01 14:33:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

An inductive decision procedure using Isabelle's tactics.
This tactic behaves more nicely w.r.t. equivalent proofs.
e.g. F x1 ... xn = G x1 ... xn. It also considers variables
quantified at the meta level ("!!") and searches for a proof
using A* where the heuristic is: pending goals + depth of search.
*)

infix 0 INTERLEAVE INTERLEAVE'

signature INDUCTIVE_TACS =
sig
  (* Utilery tactics *)

  val INTERLEAVE  : ('a -> 'b Seq.seq) * ('a -> 'b Seq.seq) -> 'a -> 'b Seq.seq
  val INTERLEAVE' : ('a -> 'b -> 'c Seq.seq) * ('a -> 'b -> 'c Seq.seq) -> 'a -> 'b -> 'c Seq.seq
  val astar_ind_auto_tac : Proof.context -> tactic
  val iter_dep_ind_auto_tac : Proof.context -> tactic
(*  val induct_auto_tac             : term_set Unsynchronized.ref -> Proof.context -> int -> tactic
  val bef_induct_auto_tac         : term_set Unsynchronized.ref -> Proof.context -> tactic*)
end

structure DB_InductiveTacs
(* : INDUCTIVE_TACS *)
= struct

fun (tac1 INTERLEAVE tac2) st =
  Seq.interleave (tac1 st, Seq.make (fn()=> Seq.pull (tac2 st)))

fun (tac1 INTERLEAVE' tac2) x =
  tac1 x INTERLEAVE tac2 x

fun TRY' tac x = 
  TRY (tac x)

(* Function that returns valid computational induction applications *)
fun inductive_applications thy prop =
  let
    fun inductive_apps thy prop =
      let
        val (t,args) = Term.strip_comb prop
      in
        case t of
           Const _ =>
           (t |> (fst o Term.dest_Const)
              |> (fn name => name ^ ".induct")
              |> (fn name => (args, Global_Theory.get_thm thy name))
              |> (fn rule => rule :: maps (inductive_apps thy) args)
              handle ERROR _ => maps (inductive_apps thy) args
                    | TERM _ => maps (inductive_apps thy) args)
         | Abs (n, T, _) => betapply (t, Free (n, T))
                              |> inductive_apps thy
                              |> (fn res => res @ maps (inductive_apps thy) args)
         | _ =>  maps (inductive_apps thy) args
      end
    val transform = map (fn Free (n, _) => SOME n
                           | _ => NONE)
  in
    prop |> inductive_apps thy
         (* Applications with smaller arguments are considered first *)
         |> sort (fn args =>
                    args |> pairself fst
                         |> pairself (map Term.size_of_term)
                         |> pairself (fn l => Library.foldl (op +) (0, l))
                         |> int_ord)
         |> map (fn (y, z) => (transform y, z))
  end

fun computational_induction_tac ctxt =
  SUBGOAL (fn (goal, i) =>
    let val thy = Proof_Context.theory_of ctxt
        val vs_inducts = inductive_applications thy goal
    in (no_tac, vs_inducts)
         |> Library.foldl (fn (thms,(vs,th)) =>
             Induct_Tacs.induct_rules_tac ctxt [vs] [th] i
             INTERLEAVE thms)
    end)

fun cases_tac ctxt =
   SUBGOAL (fn (goal, i) =>
     let val frees = [] |> Term.add_frees goal
                        |> map fst
     in
         List.foldl (op THEN_ALL_NEW) (fn _ => all_tac)
                    (List.map (Induct_Tacs.case_tac ctxt) frees) i
     end)
   
fun structural_induction_tac ctxt =
  SUBGOAL (fn (goal, i) =>
  let val frees = Term.add_frees goal []
(*      val _ = tracing "Frees: "
      val _ = map (tracing o (Syntax.string_of_term ctxt) o Free) frees*)
      val fixes = Utils.binder_vars Const_Names.meta_forall [] goal
(*      val _ = tracing "Fixes: "
      val _ = map (tracing o (Syntax.string_of_term ctxt) o Free) fixes*)
      val var_sets = (frees @ fixes)
                        |> distinct (op =)
                        (* Select only inductive vars *)
                        |> map_filter (fn (s, T) =>
                              let val ind_rules = Induct.find_inductT ctxt T
                              in if null ind_rules
                                 then NONE
                                 else SOME ((s, T), ind_rules)
                              end)
                        (* Group sets of vars with the same type *)
                        |> Library.partition_eq (is_equal o Term_Ord.typ_ord o (pairself (snd o fst)))
                        |> maps (fn l => let val rules = (single o hd o snd o hd) l
                                             val vs = map (SOME o fst o fst) l
(*                                             val vss = Utils.subsets vs*)
                                             val vs_rules = map_product pair vs rules
                                         in vs_rules end)
  in
    (no_tac, var_sets)
      |> Library.foldl (fn (thms,(v,th)) =>
           (*let val _ = tracing ("Induction rule: " ^ (th |> Thm.full_prop_of |> Syntax.string_of_term ctxt))
           in*) Induct_Tacs.induct_rules_tac ctxt [[v]] [th] i
              INTERLEAVE thms (*end*))
  end)

fun check_fail_proof_state sts ctxt =
  SUBGOAL (fn (goal, _) =>
  let val thy = Proof_Context.theory_of ctxt
      val _ = sts := Net.insert_term_safe (Pattern.equiv thy) (goal,goal) (!sts)
  in no_tac end)

(*fun check_fail_proof_state sts ctxt tac =
  SOLVE (fn th => 
  let val thy = Proof_Context.theory_of ctxt
      val thms_seq = tac th
      val thm_list = Seq.list_of thms_seq
      val _ = tracing ((string_of_int o length) thm_list)
      val _ = thm_list |> map (fn th =>
                                    let val goal = Thm.full_prop_of th
                                        val _ = tracing ("TACTIC: " ^ Syntax.string_of_term ctxt goal)
                                    in sts := Net.insert_term_safe (Pattern.equiv thy) (goal,goal) (!sts) end)
  in thms_seq end)*)

(* simple auto tac *)
fun auto_clasimpset_tac ctxt (_:int) = CHANGED (auto_tac ctxt)

(* simple simp_all tac *)
fun simp_all_tac ctxt (_:int) = (CHANGED o PARALLEL_GOALS o ALLGOALS o full_simp_tac) ctxt

(*fun primitive_induction ctxt = (EVERY' [cases_tac ctxt INTERLEAVE'
         computational_induction_tac ctxt INTERLEAVE'
         structural_induction_tac ctxt,
         auto_clasimpset_tac ctxt])*)

fun primitive_induction ctxt = (cases_tac ctxt APPEND'
         computational_induction_tac ctxt APPEND'
         structural_induction_tac ctxt)
         THEN' auto_clasimpset_tac ctxt

      (* induct and auto tac *)
fun induct_auto_tac fails ctxt =
    SOLVE ((CHANGED o ALLGOALS)
      ((((simp_all_tac ctxt)) THEN' primitive_induction ctxt
        ORELSE' primitive_induction ctxt)
      THEN' (TRY' (check_fail_proof_state fails ctxt))))

      (* induct and auto tac *)
(*fun induct_auto_tac' fails ctxt =
    SOLVE ((CHANGED o ALLGOALS)
      ((primitive_induction ctxt)
      THEN' (check_fail_proof_state fails ctxt)))*)

fun ind_auto_tac ctxt =
    (CHANGED o ALLGOALS)
      ((TRY' (simp_all_tac ctxt)) THEN' primitive_induction ctxt)


(* Probably there is a better way to know if we have proved the theorem *)
(* this function won't work in goals with spurious premises *)
fun theorem_proved thm = 
  if Thm.no_prems thm
  then true
  else false
  
(* Our heuristic is simply the number of premises (in our interpretation... the pending goals)
   plus the depth in search (shorter proofs are preferred). *)
fun theorem_heuristic i thm = Thm.nprems_of thm + i

(* A* search: similar to BEST_FIRST but current level of search is taken into account *)
fun astar_induct_auto_tac (fails : term Net.net Unsynchronized.ref)
                          (ctxt : Proof.context) =
    ASTAR (theorem_proved,theorem_heuristic) (induct_auto_tac fails ctxt)

(* A* search: similar to BEST_FIRST but current level of search is taken into account *)
fun astar_ind_auto_tac (ctxt : Proof.context) =
  ASTAR (theorem_proved,theorem_heuristic) (ind_auto_tac ctxt)

fun iter_dep_ind_auto_tac (ctxt : Proof.context) =
  ITER_DEEPEN 10 (fn _ => true) (fn _ => ind_auto_tac ctxt)

val method_setup =
  Method.setup (Binding.name "induct_auto")
    (Scan.succeed (fn ctxt => SIMPLE_METHOD (astar_ind_auto_tac ctxt)))
    "interleave induction and auto"

val _ = Context.>> (Context.map_theory method_setup)

    
end

structure InductiveTacs : INDUCTIVE_TACS = DB_InductiveTacs
