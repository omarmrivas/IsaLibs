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
ML_file "GP.ML"

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

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app [] ys = ys" |
"app (x # xs) ys = x # app xs ys"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x # xs) = app (rev xs) [x]"

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"

declare[[eta_contract = false]]

ML {*
  val ff = type_of
  val t1 = @{term "\<lambda>x. (x::('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b)"}
  val typ = type_of t1
  val t2 = @{term "\<lambda>(x::('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b) y. (y::'a\<Rightarrow>'b) "}
  val t3 = @{term "\<lambda>(x::('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b) y. x (y::'a\<Rightarrow>'b) "}
  val t4 = @{term "\<lambda>(x::('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b) (y::'a\<Rightarrow>'b) z. y z "}
  val t5 = @{term "\<lambda>(x::('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b) y. x (\<lambda>z. y z)"}
  val foo = find_first (fn (_,t) => type_of t <> typ) [(1,t1), (2,t2), (3,t3), (4,t4), (5,t5)]
*}

ML {*
  val p1 = Multithreading.max_threads_value ()
  val p2 = Thread.numProcessors ()
*}

ML {*
  val rows = (2 upto 11) |> map (fn i => (i, DB_Random_Terms.enumerate_terms @{typ "(('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b)\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b"} i))
          |> tap (map (fn (i, trms) => 
              let val _ = tracing (string_of_int i) in
              map (tracing o (Syntax.string_of_term @{context})) trms
              end ))
*}

ML {*
  val terms = DB_Random_Terms.enumerate_all_terms @{typ "(('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b)\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b"} 13
                |> tap (fn l => tracing ((string_of_int o length) l))
                |> map (Envir.eta_long [])
                |> map Utils.unique_names
                |> distinct (is_equal o Term_Ord.term_ord)
                |> tap (fn l => tracing ((string_of_int o length) l))
  val t1 = nth terms 0
  val _ = tracing (Syntax.string_of_term @{context} t1)
  val t2 = nth terms 4
  val _ = tracing (Syntax.string_of_term @{context} t2)
  val cc = DB_GP.crossover t1 t2 
              |> Envir.eta_long []
  val _ = tracing (Syntax.string_of_term @{context} cc)
  val levelsep = 0.8

  val nodesep = 3.0
  val hspace = 2.0 
  val r = [t1, t2, cc] |> map (Latex_Utils.latex_tree_with_pos levelsep nodesep)
                   |> map (fn t => "$" ^ t ^ "$")
                   |> (fn trms => "" ^ Latex_Utils.latex_table "tabular" hspace [trms] ^ "")
                   |> File.write (Path.basic "articulo.txt")
*}

ML {*
  val tt = type_of t1
  val position = Utils.positions t1
    |> find_first (fn (_, _, pos) => pos = [0, 0, 0, 0, 1, 0])
(*    |> (fn SOME (_, ty, _) => ty)*)
*}

ML {*
  val typ1 = @{typ "'a\<Rightarrow>'b"}
  val typ2 = @{typ "'b"}
  val t = Abs ("x", typ1, Abs ("x", typ2, Bound 1 $ Bound 0))
  val t' = Utils.unique_names t
  val w = ML_Syntax.print_term t1
*}

ML {*
  val rows = (2 upto 11) |> map (fn i => (i, Enumerated_Terms.generate_terms' @{theory} @{typ "(('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b)\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b"} i))
          |> map (fn (i, trms) => 
              let val _ = tracing (string_of_int i) in
              map (tracing o (Syntax.string_of_term @{context})) trms
              end )
*}

ML {*
  val rows = (2 upto 11) |> map (fn i => (i, Enumerated_Terms.generate_terms' @{theory} @{typ "(('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b)\<Rightarrow>('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b"} i))
                        |> map_filter (fn (i, trms) => if null trms
                                                       then NONE
                                                       else SOME (i, trms))
                        |> map (fn (i, trms) => (string_of_int i, map Latex_Utils.latex_tree trms))
                        |> map (fn (i, trms) => [i, "$" ^ Latex_Utils.latex_table "array" [trms] ^ "$"])
  val r = rows |> Latex_Utils.latex_table "tabular"
               |> File.write (Path.basic "prueba.txt")
*}

ML {*
(*  val str = @{term "\<lambda>x y. x y"} |> Latex_Utils.latex_tree_with_pos
                                |> File.write (Path.basic "prueba.txt")*)
*}

value "to_rat (2::int)"

fun map2 where
"map2 f [] _ = []" |
"map2 f _ [] = []" |
"map2 f (x#xs) (y#ys) = f x y # map2 f xs ys"

definition scheme where
"(scheme X :: int\<Rightarrow>int) = X (op + :: int\<Rightarrow>int\<Rightarrow>int) (op * :: int\<Rightarrow>int\<Rightarrow>int) (0 :: int) (\<lambda>x::int. x+1) (op - :: int\<Rightarrow>int\<Rightarrow>int)"

definition f where
"f x = 2 * x * x - x + (5::rat)"

term "let x = 3::rat in let y = 5::rat in x * y"

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
