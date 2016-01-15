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

ML {*
  val f = Utils.lazy_one_of_each [[1,2,3], [1,2,3]]
  fun f_vals f = case f () of
                  SOME v => v :: f_vals f
                | NONE => []
*}

ML {*
  val vs = f_vals f
  val vss = sort (int_ord o apply2 (fn xs => Library.foldl (op +) (0, xs))) vs
*}


text {* Syntesise function @{term "f x = 2 * x * x - x + (5::rat)"} *}

(*definition scheme where
"scheme P \<equiv> \<exists>f. \<forall>x y. (f 0 y = y \<and>
                       f (Suc x) y = Suc (P x y f))"*)

(*ML {*
  val names = ["f"]
  val eqns = [@{prop "f x = x * (x::int)"}]
*}

local_setup {*
  fn lthy => 
    let val ctxt = DB_GP.mutual_function lthy (names, eqns)
        val lthy' = Proof_Context.theory_of ctxt |> Named_Target.theory_init
        val t = Const ("IsaLibs.f", @{typ "int\<Rightarrow>int"})
        val _ = tracing (Value.value ctxt (t $ Syntax.read_term ctxt "12::int")
                          |> Syntax.string_of_term ctxt)
        val _ = tracing (Syntax.string_of_term ctxt t)
    in lthy' end
*}*)

ML {*
  tracing (Syntax.string_of_term @{context} @{term "f"})
*}

definition scheme where
"scheme P \<equiv> \<exists>f::int\<Rightarrow>int. \<forall>x::int. 
  (f x = P x (1::int)
             (op + :: int\<Rightarrow>int\<Rightarrow>int)
             (op - :: int\<Rightarrow>int\<Rightarrow>int)
             (op * :: int\<Rightarrow>int\<Rightarrow>int))"

ML {*
  fun fitness ctxt =
    let fun goal x = 2 * x * x - x + 5
        val f = Const ("IsaLibs.f", @{typ "int\<Rightarrow>int"})
(*        val simps = Utils.get_rewrites (Proof_Context.theory_of ctxt) "f.simps"
        val _ = tracing (Utils.str_of_thms simps)*)
        val xs = 0 upto 10
        val ys = map goal xs
        val rs = map (fn i => (f $ Utils.numeral_of_int ctxt i)
                                |> Value.value ctxt
(*                                |> tap (fn t => tracing (Syntax.string_of_term ctxt t))*)
                                |> Utils.int_of_numeral) xs
        val ds = map2 (fn x => fn y => (x - y) * (x - y)) ys rs
    in (0, ds) |> Library.foldl (op +)
               |> Rat.rat_of_int end
  fun finish ({fit, ...} : GP.individual) = Rat.eq (Rat.zero, fit)
  val term_size = 33
  val population_size = 100
  val generations = 200
  val bests = 1
  val mut_prob = 0.05
  val scheme = @{thm "scheme_def"}
(*  val ctxt = @{context}
  val r = GP.evolve scheme ctxt fitness finish term_size population_size generations bests mut_prob*)
*}

local_setup {*
 fn lthy => 
  case GP.evolve scheme lthy fitness finish term_size population_size generations bests mut_prob of
    SOME ind => (#ctxt ind)
  | NONE => lthy
*}

thm f.simps

ML {*
  
*}

definition fitness where
"fitness (i::rat\<Rightarrow>rat) =
             (let xs = map (of_int :: int\<Rightarrow>rat) [0..10] in
              let ys = map f xs in
              let rs = map i xs in
              let ds = map2 (\<lambda>x y. (x - y) * (x - y)) ys rs in
              fold (op +) ds 0)"

term "of_int 5"

value "fitness (\<lambda>x. x)"

value "map to_rat [0..10::int]"
value "map (of_int :: int\<Rightarrow>rat) [0..10::int]"

ML {*
  val function_set = [@{term "op + :: int\<Rightarrow>int\<Rightarrow>int"},
                      @{term "op * :: int\<Rightarrow>int\<Rightarrow>int"},
                      @{term "0 :: int"},
                      @{term "\<lambda>x::int. x+1"},
                      @{term "op - :: int\<Rightarrow>int\<Rightarrow>int"}]
  val target_typ = @{typ "int\<Rightarrow>int"}
  val ctxt = @{context}
  fun f (x : int) = 2*x * x - x + 5
  fun fitness t = 
    0 upto 10
      |> List.map (fn x => (x, f x))
      |> pair 0
      |> Library.foldl (fn (err, (x, f_x)) => 
          let val x = (Syntax.read_term ctxt) (string_of_int x ^ "::int")
              val f_x' = (t $ x) |> Value.value ctxt
(*                                 |> tap (fn t => tracing (Syntax.string_of_term ctxt t))*)
                                 |> Utils.int_of_numeral
              val der = f_x - f_x'
          in err + der * der end)
      |> rpair 1
      |> Rat.rat_of_quotient
  fun finish (_, err) = Rat.eq (Rat.zero, err)
  val term_size = 22
  val population_size = 200
  val generations = 100
  val bests = 10
  val mut_prob = 0.05
  val r = GP.evolve function_set target_typ ctxt fitness finish term_size population_size generations bests mut_prob
*} 

ML {*
  val SOME ((t, rat), t') = r
  val _ = tracing (Syntax.string_of_term ctxt t)
  val _ = tracing (Syntax.string_of_term ctxt (Envir.eta_long [] t))
  val _ = tracing (Syntax.string_of_term ctxt t')
*}


ML {*
  val (t, p, q) = GP.cross' t4 t5
  val print = tracing o (Syntax.string_of_term @{context})
  val _ = map print [t4, t5, t]
*}

ML {*
  val t1 = t1
  val ps1 = Utils.positions t1
  val n1 = length ps1
  fun print_pos xs = xs |> map string_of_int
                        |> space_implode ""
  fun print (t,ty,pos) = Syntax.string_of_term @{context} t ^ " : " ^ 
                         Syntax.string_of_typ @{context} ty ^ " : " ^
                         print_pos pos
  val t2 = t2
  val ps2 = Utils.positions t2
  val n2 = length ps2
  val _ = tracing "Term 1"
  val _ = map (tracing o print) ps1
  val _ = tracing "Term 2"
  val _ = map (tracing o print) ps2
*}

ML {*
  val t = Value.value @{context} @{term "[1,2] @ [3,4::int]"}
  val _ = tracing (Syntax.string_of_term @{context} t)
*}

(*
lemma TRS: 
"rev [] \<equiv> []"
"app [] ys \<equiv> ys"
"itrev [] ysb \<equiv> ysb"
"app x [] \<equiv>x"
"app (x # xs) ysa \<equiv> x # app xs ysa"
"itrev (xb # xsb) ysc \<equiv> itrev xsb (xb # ysc)"
"app (app x xa) ys \<equiv> app x (app xa ys)"
"rev (xa # xsa) \<equiv> app (rev xsa) [xa]"
sorry

lemma R: "app (IsaLibs.rev list) x \<equiv> itrev list x"
sorry

(*ML {*
  DB_Completion.completion_debug := false;
*}*)

ML {*
  val (Const (name, _)) = @{term "itrev"}
  val r = Utils.get_rewrites @{theory} name
*}

ML {*
  val TRS = @{thms TRS}
  val TRS' = map (Utils.orient_meta_rule @{theory} LESS) TRS
*}

ML {*
  val TRS = @{thms TRS}
  val R = @{thm R}
  val terminates = Aprove.memoized_terminates @{context}
  val res = Ground_Completion.run_completion [] @{context} terminates TRS R
*}*)

(*rec_complete "itrev xs [] = rev xs"

thm compl

ML {*
  val lemmas = @{term "itrev xs [] = rev xs"}
        |> global_lemmas @{context}
        |> map Utils.obj_to_meta
  val thm = nth lemmas 8
  val lemmas' = filter_out (fn th => Thm.equiv_thm (th, thm)) lemmas
  val terminates = Aprove.memoized_terminates @{context}
  val f_map = Utils.definitional_dependencies @{theory} ([], Thm.full_prop_of thm)
                    |> map Const
                    |> map (rpair 0)
(*  val result = DB_Completion.ground_joinable @{context} terminates f_map (thm, lemmas')*)
  val (equations, rules) = DB_Completion.memoized_discriminate_rules @{context} terminates lemmas'
  val n1 = length lemmas'
  val n2 = length rules
  val ctxt = (empty_simpset @{context}) addsimps rules
  val thm' = simplify ctxt thm
*}*)


end
