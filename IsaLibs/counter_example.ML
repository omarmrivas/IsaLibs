(*  Title:      util/counter_example.ML
    ID:         $Id: counter_example.ML,v 1.010 2009/08/07 20:07:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   University of Edinburgh 2009

Counter example checking by different tools.
The tools used are quickcheck and Nitpick.
*)

signature COUNTER_EXAMPLE =
sig
  val use_quickcheck                  : bool Config.T
  val use_nitpick                     : bool Config.T
  val simp_before                     : bool Config.T
  val max_time_in_counter_ex          : int Config.T

  val nitpick_params                  : Nitpick.params
  val counter_example                 : Proof.context -> int -> term -> bool
  val memoized_counter_example        : Proof.context -> int -> term -> bool
  val unfalsified_conjecture          : Proof.context -> int -> term -> term option
end

structure DB_Counter_Example
(* : COUNTER_EXAMPLE *)
= struct

val (use_quickcheck, setup_use_quickcheck) = Attrib.config_bool @{binding "use_quickcheck"} (K true)
val (use_nitpick, setup_use_nitpick) = Attrib.config_bool @{binding "use_nitpick"} (K true)
val (simp_before, setup_simp_before) = Attrib.config_bool @{binding "simp_before"} (K false)
val (max_time_in_counter_ex, setup_max_time_in_counter_ex) = Attrib.config_int @{binding "max_time_in_counter_ex"} (K 5)

val nitpick_params = Nitpick_Commands.default_params @{theory} []
fun simp_method ctxt = Utils.parse ctxt Method.parse "simp" |> fst o fst

fun get_nitpick_params
   ({cards_assigns: (typ option * int list) list,
     maxes_assigns: ((string * typ) option * int list) list,
     iters_assigns: ((string * typ) option * int list) list,
     bitss: int list,
     bisim_depths: int list,
     boxes: (typ option * bool option) list,
     finitizes: (typ option * bool option) list,
     monos: (typ option * bool option) list,
     wfs: ((string * typ) option * bool option) list,
     sat_solver: string,
     blocking: bool,
     falsify: bool,
     debug: bool,
     verbose: bool,
     overlord: bool,
     spy: bool,
     user_axioms: bool option,
     assms: bool,
     whacks: term list,
     merge_type_vars: bool,
     binary_ints: bool option,
     destroy_constrs: bool,
     specialize: bool,
     star_linear_preds: bool,
     total_consts: bool option,
     needs: term list option,
     peephole_optim: bool,
     datatype_sym_break: int,
     kodkod_sym_break: int,
(*     timeout: Time.time,*)
     tac_timeout: Time.time,
(*     max_threads: int,*)
     show_types: bool,
     show_skolems: bool,
     show_consts: bool,
     evals: term list,
     formats: (term option * int list) list,
     atomss: (typ option * string list) list,
     max_potential: int,
     max_genuine: int,
     check_potential: bool,
     check_genuine: bool,
     batch_size: int,
     expect: string, ...} : Nitpick.params) timeOut =
    {cards_assigns = cards_assigns,
     maxes_assigns = maxes_assigns,
     iters_assigns = iters_assigns,
     bitss = bitss,
     bisim_depths = bisim_depths,
     boxes = boxes,
     finitizes = finitizes,
     monos = monos,
     wfs = wfs,
     sat_solver = sat_solver,
     blocking = blocking,
     falsify = falsify,
     debug = debug,
     verbose = verbose,
     overlord = overlord,
     spy = spy,
     user_axioms = user_axioms,
     assms = assms,
     whacks = whacks,
     merge_type_vars = merge_type_vars,
     binary_ints = binary_ints,
     destroy_constrs = destroy_constrs,
     specialize = specialize,
     star_linear_preds = star_linear_preds,
     total_consts = total_consts,
     needs = needs,
     peephole_optim = peephole_optim,
     datatype_sym_break = datatype_sym_break,
     kodkod_sym_break = kodkod_sym_break,
     timeout = Time.fromSeconds timeOut,
     tac_timeout = tac_timeout,
     max_threads = 1,
     show_types = show_types,
     show_skolems = show_skolems,
     show_consts = show_consts,
     evals = evals,
     formats = formats,
     atomss = atomss,
     max_potential = max_potential,
     max_genuine = max_genuine,
     check_potential = check_potential,
     check_genuine = check_genuine,
     batch_size = batch_size,
     expect = expect}

fun quickcheck timeOut state =
    if Config.get (Proof.context_of state) use_quickcheck
    then
      (case Quickcheck.quickcheck [("timeout",[Int.toString timeOut])] 1 state of
         SOME _ => (true, state)
       | NONE => (false, state))
    else (false, state)

fun quickcheck_model timeOut state =
    Quickcheck.quickcheck [("timeout",[Int.toString timeOut])] 1 state

fun nitpick timeOut state =
    Config.get (Proof.context_of state) use_nitpick andalso
    (Utils.safe_eval "counter_example.ML 151:" false
      (fn step => (step |> Nitpick.pick_nits_in_subgoal state (get_nitpick_params nitpick_params timeOut) Nitpick.Normal 1
                        |> (fn (sce,_) => if "genuine" = sce then true
                                          (* FIXME: What if potential! *)
                                          (*else if "potential" = sce then
                                            null (!Nitpick_Model.reconstructed_model)*)
                                          else false))) 0)

fun quickcheck_nitpick_raw ctxt timeOut conjecture =
    ctxt |> Proof.theorem NONE (K I) [[(conjecture, [])]]
         |> (fn state => if Config.get (Proof.context_of state) simp_before
                         then Seq.hd (Proof.apply (simp_method (Proof.context_of state)) state)
                         else state)
         |> (fn state => state |> Utils.safe_eval "counter_example 164" (false, state) (quickcheck timeOut)
                               |> (fn (foo,_) => (foo, state)))
         |> (fn (foo,state) => 
                foo orelse (Utils.safe_eval "counter_example.ML 172" false (nitpick timeOut) state))

fun counter_example _ _ (_ $ Const ("HOL.True",_)) = false
  | counter_example ctxt timeOut conjecture = quickcheck_nitpick_raw ctxt timeOut conjecture

val false_set = Synchronized.var "CE_false_set" (Net.empty : term Net.net)

fun subsumed_in_net thy t net =
  let val t = Logic.varify_global t
  in t |> Net.unify_term net
       |> exists (fn t' => Pattern.matches thy (t, t')) end

fun memoized_counter_example ctxt timeOut conjecture =
  let val thy = Proof_Context.theory_of ctxt
  in if false_set |> Synchronized.value
                  |> subsumed_in_net thy conjecture
     then true
     else let val v = counter_example ctxt timeOut conjecture
              val _ = if v
                      then Synchronized.change false_set
                            (fn net => Net.insert_term_safe (Pattern.equiv thy)
                                                            (conjecture, conjecture) net)
                      else ()
          in v end
  end

fun unfalsified_conjecture ctxt timeOut conjecture =
  if memoized_counter_example ctxt timeOut conjecture
  then NONE
  else SOME conjecture


end

structure Counter_Example : COUNTER_EXAMPLE = DB_Counter_Example
