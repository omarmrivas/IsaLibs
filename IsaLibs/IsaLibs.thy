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

(*fun suma where
"suma 0 y = y"|
"suma (Suc x) y = Suc (suma x y)"

lemma "suma x y = suma y x"
apply induct_auto_astar*)

(*ML {*
  val simps = Utils.rules_in_simpset
    [@{term "op +"}, @{term "if x then y else z"}, @{term "[]"},
     @{term "hd"}, @{term "tl"}, @{term "Suc"}, @{term "op #"}, @{term "op -"}]
  val l = length simps
  val content = simps |> map ((fn t => HTML.plain (Utils.html_string_of_term @{context} t)) o (Thm.full_prop_of))
                      |> distinct (op =)
                      |> map single
                      |> map_index (fn (i,e) => string_of_int i :: e)
  val table = Utils.html_table (["<b>No.</b>", "<b>Rule</b>"] :: content)
  val begin = HTML.begin_document "Rewrite Rules"
  val ed = HTML.end_document
  val _ = Utils.write_to_file "rewrite_set.html" (begin ^ table ^ ed)
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

ML {*
  fun extract_filename str =
    (str |> String.explode
        |> rev
        |> find_index (fn c => c = #"/")
        |> (fn i => String.extract (str, String.size str - i, NONE)))
        handle Subscript => (tracing ("Error extracting filename: " ^ str); str)

  fun get_smt2_files dir =
    "find \"" ^ dir ^ "\" -iname '*.smt2'"
      |> Isabelle_System.bash_output
      |> fst
      |> space_explode "\n"

  fun get_thy_files dir =
    "find \"" ^ dir ^ "\" -iname '*.thy'"
      |> Isabelle_System.bash_output
      |> fst
      |> space_explode "\n"

  fun conjecture_proved elapsed str =
    if elapsed >= 80.0 then false
    else if str = "" then false
    else not (String.isSubstring "Failed to finish proof" str orelse
              String.isSubstring "Failed to apply initial proof method" str)

  val timeout = Prover.max_time_in_proof
                      |> Config.get @{context}
                      |> (fn timeout => 3 * timeout)

  val path = Path.explode "experiments/inductive_proofs/errors.log"
  val ps_log = Path.explode "experiments/inductive_proofs/ps_log.log"

  fun get_goal file str =
    str |> first_field "HTML:"
        |> (fn r => case r of
                    SOME (_, str) => str
                  | NONE => "BAD")
        |> first_field "HTML:"
        |> (fn r => case r of
                    SOME (_, str) => str
                  | NONE => "BAD")
        |> String.implode o rev o String.explode
        |> first_field ((String.implode o rev o String.explode) "</span>")
        |> (fn r => case r of
                    SOME (_, str) => (String.implode o rev o String.explode) str ^ "</span>"
                  | NONE => (tracing ("BAD! " ^ file); 
                              Utils.trace_log path ("Unknown error (" ^ file ^ "): " ^ str);
                              "BAD"))

  fun proof_call smt_file thy prover =
  let val start = Timing.start ()
  in
    ("timeout -t " ^ (string_of_int timeout) ^ " ./proof_call " ^ smt_file ^ " " ^ thy ^ " " ^ prover)
      |> Isabelle_System.bash_output
      |> (fn (out, _) => let val elapsed = start |> Timing.result
                                     |> #elapsed
                                     |> Time.toReal
                         in (conjecture_proved elapsed out, elapsed, get_goal out) end)
  end

  fun proof_call_thy smt_file thy prover =
  let val start = Timing.start ()
  in
(*    ("timeout -t " ^ (string_of_int timeout) ^ " ./proof_call_thy " ^ smt_file)*)
    (" ./proof_call_thy " ^ smt_file)
      |> Isabelle_System.bash_output
      |> (fn (out, _) => let val elapsed = start |> Timing.result
                                             |> #elapsed
                                             |> Time.toReal
                             val file = extract_filename smt_file
                         in (conjecture_proved elapsed out, elapsed, get_goal file out, file) end)
      |> tap (fn (bool, real, _, file) => Utils.trace_log ps_log (file ^ ": " ^ (if bool then "Yes" else "No") ^ " - " ^ string_of_real real))
  end
*}

ML {*
  val process_ref = Synchronized.var "process_ref" false
  fun clean_processes PID =
  let val ps_command = "ps aux -A | grep poly"
    fun get_time str =
    str |> space_explode ":"
        |> map (fn str => perhaps (try (unsuffix "0")) str)
        |> map (fn str => perhaps (try (unprefix "0")) str)
        |> (fn [min, sec] =>  Time.fromString (string_of_int (Utils.int_of_string min) ^ "." ^ Real.toString (60.0 / the (Real.fromString sec))) 
                                | _ => Time.fromString "0")
        |> the
    fun get_time_safe str =
      (case try get_time str of
        SOME time => time
        | NONE => the (Time.fromString "0"))
    val max_time = get_time "3:30.0"
    val result = ps_command |> Isabelle_System.bash_output
                          |> fst
                          |> space_explode "\n"
                          |> filter (fn line => "" <> line)
                          |> map (filter (fn line => "" <> line) o space_explode " ")
                          |> map (fn lines => nth lines 1)
                          |> map (fn pid_str => (pid_str, fst (Isabelle_System.bash_output ("ps -p " ^ pid_str ^ " -o etime="))))
                          |> map (fn (pid_str, time_str) => (Utils.int_of_string pid_str, get_time_safe time_str))
(*                          |> map (fn lines => (Utils.int_of_string (nth lines 1), get_time_safe (nth lines 9)))*)
                          |> filter (fn (pid, time) => time > max_time andalso PID <> pid)
                          |> tap (map (Utils.trace_log ps_log o (fn pid => "Killing PID: " ^ pid) o string_of_int o fst))
  in map (fn (pid, _) =>  Isabelle_System.bash_output ("kill -KILL " ^ string_of_int pid)) result end
  fun clean_loop PID () =
  if not (Synchronized.value process_ref)
  then
  let 
      val _ = clean_processes PID
      val _ = OS.Process.sleep (seconds 5.0)
  in clean_loop PID () end
  else ()
*}

ML {*.
(*  val smt_files = "/Users/omarmrivas/Programs/tip-org-benchmarks/benchmarks"
                    |> get_smt2_files*)
  val smt_files = "/Users/omarmrivas/Programs/IsaLibs/experiments/inductive_proofs"
                    |> get_thy_files
(*                    |> single o hd*)
  val _ = tracing ("Problems: " ^ (string_of_int o length) smt_files)
  val thy = "IsaHipster"
  val prover = "hipster_induct_simp"
  fun check foo = if foo then "&#x2713;" else "&#x2717;"
  val params = ({stack_limit=NONE, interrupts=false} : Simple_Thread.params)
  val PID = 83900
  val thread = Simple_Thread.fork params (clean_loop PID)
  val _ = tracing ("Is active: " ^ (if Thread.isActive thread then "yes" else "no"))
  val results = smt_files |> map_index I
                          |> Par_List.map (fn (i, file) => (Utils.trace_log ps_log (string_of_int i ^ ": " ^ file); (i, proof_call_thy file thy prover)))
                          |> map_filter (fn (i, (x, y, goal, z)) => if goal = "BAD" then NONE else SOME (i, (x, y, goal, z)))
                          |> map (fn (i, (proved, time, conjecture, file)) => [string_of_int i, conjecture, file, check proved, string_of_real time])
  val theorems_proved = Library.foldl (fn (c, [_, _, _, proved, _]) => if "&#x2713;" = proved then c + 1 else c | (c,_) => c) (0, results)
  val theorems_not_proved = length results - theorems_proved
  val theorems_proved_percent = ((Real.fromInt) theorems_proved) / ((Real.fromInt o length) results) * 100.0
  val theorems_not_proved_percent = ((Real.fromInt) theorems_not_proved) / ((Real.fromInt o length) results) * 100.0
  val average_cpu_time = (0.0, results) |> Library.foldl (fn (time, [_, _, _, _, t]) => time + (the o Real.fromString) t | (time,_) => time)
                                        |> (fn v => v / ((Real.fromInt o length) results))
  val average_cpu_time_proved = ((0,0.0), results) |> Library.foldl (fn ((c,time), [_, _, _, proved, t]) => if "&#x2713;" = proved 
                                                                                                            then (c+1,time + (the o Real.fromString) t)
                                                                                                            else (c,time) | ((c,time), _) => (c,time))
                                                   |> (fn (c,time) => time / ((Real.fromInt) c))
  val average_cpu_time_not_proved = ((0,0.0), results) |> Library.foldl (fn ((c,time), [_, _, _, proved, t]) => if "&#x2717;" = proved 
                                                                                                            then (c+1,time + (the o Real.fromString) t)
                                                                                                            else (c,time) | ((c,time), _) => (c,time))
                                                       |> (fn (c,time) => time / ((Real.fromInt) c))
  val table = Utils.html_table "alldata" (["<b>No.</b>", "<b>Conjecture</b>", "<b>File</b>", "<b>Proved</b>", "<b>Time</b>"] :: results)
  val header_content = [["<b>Proved</b>", "<b>Not proved</b>", "<b>Proved &#37;</b>", "<b>Not proved &#37;</b>", "<b>Avg cpu time</b>", "<b>Avg proved</b>", "<b>Avg not proved</b>"],
                        [string_of_int theorems_proved, 
                         string_of_int theorems_not_proved, 
                         string_of_real theorems_proved_percent ^ "&#37;", 
                         string_of_real theorems_not_proved_percent ^ "&#37;", 
                         string_of_real average_cpu_time ^ "s", 
                         string_of_real average_cpu_time_proved ^ "s", 
                         string_of_real average_cpu_time_not_proved ^ "s"]]
  val table_header = Utils.html_table "statistics" header_content
  val begin = HTML.begin_document ("Results for " ^ prover)
  val ed = HTML.end_document
  val _ = Utils.write_to_file ("experiments/inductive_proofs/" ^ prover ^ ".html") (begin ^ table_header ^ table ^ ed)
  val _ = OS.Process.sleep (seconds 6.0)
  val _ = Synchronized.change process_ref (fn _ => true)
  val _ = Simple_Thread.join thread
*}

(*
datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype Tok = X | Y | Z

datatype B2 = SB "B2" | ZB

datatype A2 = SA "A2" | ZA

datatype S = A "A2" | B "B2"

fun append :: "'a list => 'a list => 'a list" where
"append (nil2) y = y"
| "append (cons2 z xs) y = cons2 z (append xs y)"

fun linA :: "A2 => Tok list" where
"linA (SA a) =
   append (append (cons2 X (nil2)) (linA a)) (cons2 Y (nil2))"
| "linA (ZA) = cons2 X (cons2 Z (cons2 Y (nil2)))"

fun linB :: "B2 => Tok list" where
"linB (SB b) =
   append
     (append (cons2 X (nil2)) (linB b)) (cons2 Y (cons2 Y (nil2)))"
| "linB (ZB) = cons2 X (cons2 Z (cons2 Y (cons2 Y (nil2))))"

fun linS :: "S => Tok list" where
"linS (A a) = linA a"
| "linS (B b) = linB b"

theorem x0 :
  "!! (u :: S) (v :: S) . (((linS u) = (linS v)) ==> (u = v))"
apply induct_auto_astar*)

text {* Associative operators must be oriented this way to avoid non-termination
        in case they are also Commutative operators. *}
orient_rules "?X (?X (?x :: ?'a) (?y :: ?'a)) (?z :: ?'a) = ?X ?x (?X ?y ?z)"

ML {*
  val p1 = Multithreading.max_threads_value ()
  val p2 = Thread.numProcessors ()
  val _ = Future.ML_statistics := false
*}

end
