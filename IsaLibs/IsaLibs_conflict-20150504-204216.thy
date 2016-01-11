theory IsaLibs
imports Main
keywords "rec_complete" :: thy_decl and
         "complete" :: thy_goal
begin
ML_file "$ISABELLE_HOME/src/HOL/TPTP/sledgehammer_tactics.ML"
ML_file "const_names.ML"
ML_file "utils.ML"
ML_file "counter_example.ML"
ML_file "enumerated_terms.ML"
(*ML_file "induct_tacs.ML"*)
ML_file "induct_tacs4.ML"
ML_file "aprove.ML"
ML_file "prover.ML"
ML_file "ground_completion.ML"
ML_file "proof_tools.ML"
ML_file "commands.ML"

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
DB_Aprove.setup_max_time_in_termination #>

DB_Completion.setup_generate_cps #>

Completion_Rules.setup
*}

declare [[
  use_quickcheck = true,
  use_nitpick = false,
  simp_before = false,
  max_time_in_counter_ex = 50,
  max_time_in_proof = 20,
  max_depth_in_meta_induction = 10,
  max_num_generalizations = 3,
  max_consts_in_generalizations = 4,
  max_lambda_size = 8,
  use_metis = false,
  quickcheck_quiet = true,
  use_aprove=true,
  generate_cps=true,
  max_time_in_termination = 10
  ]]

ML {*
 Isabelle_System.with_tmp_file "a" "b"
  (fn path => (File.write path "algo"; Isabelle_System.bash_output ("ls " ^ (Path.implode path))))
*}

ML {*
 Isabelle_System.with_tmp_file "a" "b"
  (fn path => (Isabelle_System.bash_output ("ls " )))
*}

end
