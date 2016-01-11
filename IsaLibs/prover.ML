(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature PROVER =
sig

  val max_time_in_proof  : int Config.T

  val prove                        : local_theory -> thm list option -> Method.text -> 
                                     term -> int -> thm option

  val  cheat_prover : Proof.context -> term -> thm
end

structure DB_Prover
(* : COMMANDS *)
= struct

val (max_time_in_proof, setup_max_time_in_proof) = Attrib.config_int @{binding "max_time_in_proof"} (K 10)

val method_setup =
    Method.setup (Binding.name "spass_auto")
                 (Scan.succeed (fn ctxt => 
                                   SIMPLE_METHOD (Sledgehammer_Tactics.sledgehammer_with_metis_tac
                                                    ctxt [("timeout",Int.toString (Config.get ctxt max_time_in_proof))]
                                                    Sledgehammer_Fact.no_fact_override 1)))
                 "interleave spass and ..."

val _ = Context.>> (Context.map_theory method_setup)

val sledgehammer_method = Utils.parse Method.parse "spass_auto" |> fst o fst
val induct_auto_method = Utils.parse Method.parse "induct_auto" |> fst o fst

fun prove_from_method ctxt0 (SOME simps) method conjecture =
  let val ctxt = ctxt0 addsimps simps
      (*val ctxt = ctxt0 |> Context.Proof
                       |> Simplifier.map_ss (fn simpset => simpset addsimps simps)
                       |> Context.the_proof*)
(*                       |> tap (fn _ => tracing ("Using: " ^ Utils.str_of_thms simps))*)
      (*val ctxt = put_simpset HOL_basic_ss ctxt0 addsimps simps*)
  in prove_from_method ctxt NONE method conjecture end
| prove_from_method ctxt0 NONE method conjecture =
  let val frees = [] |> Term.add_frees conjecture |> map fst
      val _ = tracing ("Proving: " ^ (Syntax.string_of_term ctxt0 conjecture))
  in Utils.safe_eval "" NONE
     (fn ctxt0 =>
      ctxt0|> Variable.add_fixes frees
           |> snd
           |> Proof.theorem NONE (K I) [[(conjecture, [])]]
           |> Proof.apply method
           |> Seq.hd
           |> `Proof.goal
           ||> Proof.global_done_proof
           (* FIXME: facts should be used in a locale or type class context! *)
           |> (fn ({goal,...},ctxt) => 
                  if 0 = Thm.nprems_of goal 
                  then SOME (goal
                               |> Goal.finish ctxt
                               |> Thm.check_shyps (Variable.sorts_of ctxt)
                               |> Assumption.export false ctxt ctxt0
                               |> single
                               |> Variable.export ctxt ctxt0
                               |> hd
                               |> Drule.zero_var_indexes)
                        |> tap (fn _ => tracing ("Proved!: " ^ Syntax.string_of_term ctxt conjecture))
                  else NONE)) ctxt0
      end

fun prove_from_spass ctxt0 args conjecture = 
  prove_from_method ctxt0 args sledgehammer_method conjecture

fun prove ctxt args method conjecture timeOut = 
  let fun prove' ctxt args method conjecture timeOut = 
  (conjecture
    |> TimeLimit.timeLimit (Time.fromSeconds timeOut)
                           (prove_from_method ctxt args method))
      handle TimeLimit.TimeOut => NONE
  in if can Local_Theory.target_of ctxt
     then let val ctxt = Local_Theory.target_of ctxt
          in prove' ctxt args method conjecture timeOut end
     else prove' ctxt args method conjecture timeOut
  end

fun cheat_prover ctxt prop =
  (K (Skip_Proof.cheat_tac 1))
    |> Goal.prove ctxt [] [] prop


end

structure Prover : PROVER = DB_Prover



