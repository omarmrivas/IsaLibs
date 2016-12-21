theory IsaLibs
(*imports Complex_Main*)
imports "~~/src/HOL/TPTP/THF_Arith"
keywords "rec_complete" :: thy_decl and
         "complete" :: thy_goal and
         "orient_rules" :: thy_decl
begin
ML_file "$ISABELLE_HOME/src/HOL/TPTP/sledgehammer_tactics.ML"
ML_file "html.ML"
ML_file "const_names.ML"
ML_file "tables.ML"
ML_file "utils.ML"
ML_file "smt.ML"
ML_file "latex.ML"
ML_file "orders.ML"
ML_file "sat_interface.ML"
ML_file "dependency_pair.ML"
ML_file "counter_example.ML"
ML_file "random_terms.ML"
ML_file "enumerated_terms.ML"
ML_file "aprove.ML"
ML_file "prover.ML"
ML_file "induct_tacs4.ML"
ML_file "induct_tacs.ML"
ML_file "ground_completion.ML"
ML_file "proof_tools.ML"
ML_file "commands.ML"
ML_file "oriented_rules.ML"
ML_file "meta_gp_hol.ML"
ML_file "exhaust.ML"
ML_file "gnuplot.ML"
ML_file "mysql.ML"
ML_file "papers/ml_database.ML"
ML_file "papers/ESWA2016.ML"
ML_file "papers/rectilinear_crossing.ML"

(*ML_file "$ISABELLE_HOME/src/Tools/Spec_Check/base_generator.ML"
ML_file "$ISABELLE_HOME/src/Tools/Spec_Check/generator.ML"*)

(*ML {*
  val l = DB_Counter_Example.quickcheck_terms @{context} 600 500 @{typ "real"}
  val s = length l
*}

ML {*
  map (tracing o Syntax.string_of_term @{context}) l
*}

lemma "\<not>(x=real_of_rat (Fract 0 1)) \<Longrightarrow> (x::real) = real_of_rat (Fract (- 1) 1)"


ML {*
  val t = @{term "\<not>((\<forall>x. \<not>(P x))\<or>(\<forall>x. Q x))"}
  val fig = Latex_Utils.latex_tree_with_pos 0.8 3.0 t
  val _ = Utils.write_to_file "latex.txt" fig
*}*)

(*lemma eval_Suc_nat [code_post]:
   "Suc 0 = 1"
   "Suc 1 = 2"
   "Suc (numeral n) = numeral (Num.inc n)"
   unfolding One_nat_def numeral_inc by simp_all

 declare Num.inc.simps [code_post]

value "Suc 42"
value [code] "Suc 42"
value [nbe] "Suc 42"
value [simp] "Suc 42"*)

setup {*
DB_Counter_Example.setup_use_quickcheck #>
DB_Counter_Example.setup_use_nitpick #>
DB_Counter_Example.setup_simp_before #>
DB_Counter_Example.setup_max_time_in_counter_ex #>

DB_Prover.setup_max_time_in_proof #>
DB_Proof_Tools.setup_max_depth_in_meta_induction #>
DB_Proof_Tools.setup_max_num_generalizations #>
DB_Proof_Tools.setup_max_consts_in_generalizations #>
DB_Proof_Tools.setup_max_lambda_size #>
DB_Proof_Tools.setup_use_metis #>

DB_Aprove.setup_use_aprove #>
DB_DPair.setup_max_time_in_termination #>

DB_Completion.setup_generate_cps #>

DB_GP.setup_max_time_in_fitness #>

Completion_Rules.setup
*}

declare [[
  use_quickcheck = true,
  use_nitpick = false,
  simp_before = false,
  max_time_in_counter_ex = 25,
  max_time_in_proof = 60,
  max_time_in_fitness = 15,
  max_depth_in_meta_induction = 10,
  max_num_generalizations = 3,
  max_consts_in_generalizations = 4,
  max_lambda_size = 8,
  use_metis = false,
  quickcheck_quiet = true,
  use_aprove=true,
  generate_cps=false,
  max_time_in_termination = 20,
  linarith_split_limit = 10,
  eta_contract = false
  ]]

text {* Associative operators must be oriented this way to avoid non-termination
        in case they are also Commutative operators. *}
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?x (?X ?y ?z)"

ML {*
  val p1 = Multithreading.max_threads_value ()
  val p2 = Thread.numProcessors ()
  val _ = Future.ML_statistics := false
*}

(*ML {*
  val smt2_dir = "/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks"
  val destiny = "experiments/inductive_proofs2"
(*  val smt2_files = smt2_dir |> SMT_Converter.get_smt2_files destiny
                            |> filter (fn "" => false
                                      | _ => true)*)
  val smt2_files = ["/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortIsSort.smt2"]
  val names = SMT_Converter.smt2bash_to_isabelle @{context} destiny "IsaLibs" "by induct_auto" smt2_files
*}*)

(*ML {*.
  map (fn (smt2, (foo, thy)) => if foo then () else tracing (smt2 ^ " - " ^ thy ^ ".thy")) names
*}*)

(*
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/list_Interleave.smt2 - list_Interleave.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/list_weird_concat_map_bind.smt2 - list_weird_concat_map_bind.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/list_weird_is_normal.smt2 - list_weird_is_normal.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/mccarthy91_M1.smt2 - mccarthy91_M1.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/mccarthy91_M2.smt2 - mccarthy91_M2.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/mod_same.smt2 - mod_same.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/polyrec_seq_index.smt2 - polyrec_seq_index.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_AndCommutative.smt2 - propositional_AndCommutative.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_AndIdempotent.smt2 - propositional_AndIdempotent.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_AndImplication.smt2 - propositional_AndImplication.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_Okay.smt2 - propositional_Okay.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/propositional_Sound.smt2 - propositional_Sound.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/rotate_mod.smt2 - rotate_mod.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BSortCount.smt2 - sort_BSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BSortIsSort.smt2 - sort_BSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BSortPermutes.smt2 - sort_BSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BSortSorts.smt2 - sort_BSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortCount.smt2 - sort_BubSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortIsSort.smt2 - sort_BubSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortPermutes.smt2 - sort_BubSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_BubSortSorts.smt2 - sort_BubSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_HSortCount.smt2 - sort_HSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_HSortIsSort.smt2 - sort_HSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_HSortPermutes.smt2 - sort_HSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_HSortSorts.smt2 - sort_HSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBU2Count.smt2 - sort_MSortBU2Count.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBU2IsSort.smt2 - sort_MSortBU2IsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBU2Permutes.smt2 - sort_MSortBU2Permutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBU2Sorts.smt2 - sort_MSortBU2Sorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBUCount.smt2 - sort_MSortBUCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBUIsSort.smt2 - sort_MSortBUIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBUPermutes.smt2 - sort_MSortBUPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortBUSorts.smt2 - sort_MSortBUSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortTDCount.smt2 - sort_MSortTDCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortTDIsSort.smt2 - sort_MSortTDIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortTDPermutes.smt2 - sort_MSortTDPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_MSortTDSorts.smt2 - sort_MSortTDSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NMSortTDCount.smt2 - sort_NMSortTDCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NMSortTDIsSort.smt2 - sort_NMSortTDIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NMSortTDPermutes.smt2 - sort_NMSortTDPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NMSortTDSorts.smt2 - sort_NMSortTDSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSort2Count.smt2 - sort_NStoogeSort2Count.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSort2IsSort.smt2 - sort_NStoogeSort2IsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSort2Permutes.smt2 - sort_NStoogeSort2Permutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSort2Sorts.smt2 - sort_NStoogeSort2Sorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSortCount.smt2 - sort_NStoogeSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSortIsSort.smt2 - sort_NStoogeSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSortPermutes.smt2 - sort_NStoogeSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_NStoogeSortSorts.smt2 - sort_NStoogeSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_QSortCount.smt2 - sort_QSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_QSortIsSort.smt2 - sort_QSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_QSortPermutes.smt2 - sort_QSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_QSortSorts.smt2 - sort_QSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_SSortCount.smt2 - sort_SSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_SSortIsSort.smt2 - sort_SSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_SSortPermutes.smt2 - sort_SSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_SSortSorts.smt2 - sort_SSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSort2Count.smt2 - sort_StoogeSort2Count.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSort2IsSort.smt2 - sort_StoogeSort2IsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSort2Permutes.smt2 - sort_StoogeSort2Permutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSort2Sorts.smt2 - sort_StoogeSort2Sorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSortCount.smt2 - sort_StoogeSortCount.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSortIsSort.smt2 - sort_StoogeSortIsSort.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSortPermutes.smt2 - sort_StoogeSortPermutes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/sort_StoogeSortSorts.smt2 - sort_StoogeSortSorts.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/subst_SubstFreeNo.smt2 - subst_SubstFreeNo.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/subst_SubstFreeYes.smt2 - subst_SubstFreeYes.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/tree_Flatten1.smt2 - tree_Flatten1.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/tree_Flatten1List.smt2 - tree_Flatten1List.thy 
/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks/tip2015/tree_Flatten3.smt2 - tree_Flatten3.thy 
val it = [(), (), (), (), (), (), (), (), (), (), ...]: unit list
*)

end
