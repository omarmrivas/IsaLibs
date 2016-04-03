theory IsaLibs
(*imports Complex_Main*)
imports "~~/src/HOL/TPTP/THF_Arith"
keywords "rec_complete" :: thy_decl and
         "complete" :: thy_goal and
         "orient_rules" :: thy_decl
begin
ML_file "$ISABELLE_HOME/src/HOL/TPTP/sledgehammer_tactics.ML"
ML_file "const_names.ML"
ML_file "tables.ML"
ML_file "utils.ML"
ML_file "latex.ML"
ML_file "orders.ML"
ML_file "sat_interface.ML"
ML_file "dependency_pair.ML"
ML_file "counter_example.ML"
ML_file "random_terms.ML"
ML_file "enumerated_terms.ML"
ML_file "induct_tacs4.ML"
ML_file "aprove.ML"
ML_file "prover.ML"
ML_file "ground_completion.ML"
ML_file "proof_tools.ML"
ML_file "commands.ML"
ML_file "oriented_rules.ML"
(*ML_file "gp.ML"*)
ML_file "gp_hol.ML"
ML_file "meta_gp_hol.ML"
ML_file "exhaust.ML"
ML_file "gnuplot.ML"

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
  max_time_in_proof = 20,
  max_time_in_fitness = 500,
  max_depth_in_meta_induction = 10,
  max_num_generalizations = 3,
  max_consts_in_generalizations = 4,
  max_lambda_size = 8,
  use_metis = false,
  quickcheck_quiet = true,
  use_aprove=true,
  generate_cps=false,
  max_time_in_termination = 20
  ]]

text {* Associative operators must be oriented this way to avoid non-termination
        in case they are also Commutative operators. *}
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?x (?X ?y ?z)"

declare[[eta_contract = false]]

ML {*
  val p1 = Multithreading.max_threads_value ()
  val p2 = Thread.numProcessors ()
*}

definition scheme_const where
"scheme_const N \<equiv> \<exists>(f::int list\<Rightarrow>int). \<forall>(xs::int list) (x::int).
  (f [] = (0::int)) \<and>
  (f (x#xs) = N x
                xs
                (op + :: int\<Rightarrow>int\<Rightarrow>int)
                f)"

definition scheme_const' where
"scheme_const' N \<equiv> \<exists>(f::(int \<Rightarrow> int list \<Rightarrow> (int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> (int list \<Rightarrow> int) \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> int). \<forall>(c::nat) (xs::int list) (x::int).
  (f N (0::nat) [] = (0::int)) \<and>
  (f N (Suc c)  [] = (0::int)) \<and>
  (f N (Suc c)  (x#xs) = N x
                           xs
                           (op + :: int\<Rightarrow>int\<Rightarrow>int)
                           (f N c))"

fun f where
"f M (0::nat) _ = (0::int)"|
"f M (Suc c) [] = (0::int)"|
"f M (Suc c) ((x::int)#xs) = M x
                xs
                (op + :: int\<Rightarrow>int\<Rightarrow>int)
                (f M c)"

definition meta_scheme_const where
"meta_scheme_const N = f N"

lemma termination_scheme_const': "scheme_const' N"
apply (unfold scheme_const'_def)
apply (rule_tac x="f" in exI)
by simp

ML {*
  val ctxt = @{context}
  val t = @{thm "termination_scheme_const'"}
  val t' = @{thm "scheme_const'_def"}
  val var = t
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
                         |> map Var
                         |> hd
  val lam = @{term "(\<lambda>a b c d. c a (d b)) :: int
   \<Rightarrow> int list
      \<Rightarrow> (int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> (int list \<Rightarrow> int) \<Rightarrow> int"}
  val sigma = (map (apply2 (Thm.ctyp_of ctxt)) [],
               map (apply2 (Thm.cterm_of ctxt)) [(var, lam)])
  val a = Drule.instantiate_normalize sigma t
  val r = Proof_Tools.normalise_thm ctxt [t'] a
*}

thm f.simps
value "f (\<lambda>a b c d. c a (d b)) 100 [0,1,2,3,4,5,6,7,8,9]"

definition scheme_dest where
"scheme_dest N \<equiv> \<exists>(f::int list\<Rightarrow>int). \<forall>(xs::int list).
  f xs = N xs
           (\<lambda>x (y::int) z. if x then y else z)
           (op = :: int list\<Rightarrow>int list\<Rightarrow>bool)
           ([] :: int list)
           (op + :: int\<Rightarrow>int\<Rightarrow>int)
           (0 :: int)
           (\<lambda>xs. if xs = [] then (0::int) else hd xs)
           (tl :: int list\<Rightarrow>int list)
           f"

fun g where
"g M (0::nat) _ = (0::int)"|
"g M (Suc c) (xs :: int list)
                = M xs (\<lambda>x (y::int) z. if x then y else z)
                    (op = :: int list\<Rightarrow>int list\<Rightarrow>bool)
                    ([] :: int list)
                    (op + :: int \<Rightarrow> int \<Rightarrow> int)
                    (0 :: int)
                    (\<lambda>xs. if xs = [] then (0::int) else hd xs)
                    (tl :: int list\<Rightarrow>int list)
                    (g M c)"

thm g.simps
value "g ((\<lambda>a b c d e f g h i. b (c d a) f (e (g a) (i (h a))))) 100 [0,1,2,3,4,5,6,7,8,9]"

fun ackermann where
"ackermann 0 n = Suc n" |
"ackermann (Suc m) 0 = ackermann m 1" |
"ackermann (Suc m) (Suc n) = ackermann m (ackermann (Suc m) n)"

fun ack where
"ack M N 0 _ _ = 0" |
"ack M N (Suc c) 0 n = Suc n" |
"ack M N (Suc c) (Suc m) 0 = M m (0::nat) Suc (ack M N c) " |
"ack M N (Suc c) (Suc m) (Suc n) = N (0::nat) Suc m n (ack M N c)"

thm ackermann.simps
value "ack (\<lambda>a b c d. d a (c b)) (\<lambda>a b c d e. e c (e (b c) d)) 100 4 3"
value "ackermann 3 3"

end
