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
ML_file "smt.ML"
ML_file "utils.ML"
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
ML_file "papers/ESWA2016.ML"

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

ML {*
  structure K = Variable
*}

ML {*
  val g = DB_SMT_Converter.s_expressions @{context} "(declare-datatypes (a) ((list (nil) (cons (head a) (tail (list a)))))) (declare-datatypes () ((Nat (Z) (S (p Nat))))) (define-fun-rec  last    ((x (list Nat))) Nat    (match x      (case nil Z)      (case (cons y z)        (match z          (case nil y)          (case (cons x2 x3) (last z))))))"
  val s = length g
  val e1 = hd g
  val e2 = (hd o tl) g
  val str1 = SMTLIB.str_of e1
  val datatype_decl1 = DB_SMT_Converter.translate_datatype e1
  val str2 = SMTLIB.str_of e2
  val datatype_decl2 = DB_SMT_Converter.translate_datatype e2
*}

end
