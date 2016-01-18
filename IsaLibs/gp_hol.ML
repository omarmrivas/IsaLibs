(*  Title:      util/gp.ML
    ID:         $Id: gp.ML,v 1.00 2015/15/10 12:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Genetic Programming algorithm for Simply-typed lambda calculus.
*)

signature GP =
sig
  val max_time_in_fitness  : int Config.T

  type subst = (typ * typ) list * (term * term) list
  type individual = {ctxt  : Proof.context,
                     genome: term list,
                     subst : subst,
                     norm  : term,
                     fit   : Rat.rat}

  val evolve : bool -> thm ->
    Proof.context ->
    (Proof.context -> Rat.rat) ->
    (individual -> bool) ->
    int -> int -> int -> int -> real -> individual option

end

structure DB_GP
(* : GP *)
= struct

val (max_time_in_fitness, setup_max_time_in_fitness) = Attrib.config_int @{binding "max_time_in_fitness"} (K 30)

val big_rational = Rat.rat_of_int 1000000

type subst = (typ * typ) list * (term * term) list
  type individual = {ctxt  : Proof.context,
                     genome: term list,
                     subst : subst,
                     norm  : term,
                     fit   : Rat.rat}

type gp_data = { scheme : thm,
                 term_size : int,
                 population_size : int,
                 bests : int,
                 mutation_prob : real,
                 fitness : Proof.context -> Rat.rat,
                 finish : individual -> bool,
                 term_count : (int * int) list list,
                 simps : thm list,
                 debug : bool,
                 timeout : Time.time,
                 ctxt : Proof.context}

exception DONE of individual

fun timeout_error ctxt t =
  tracing ("The term " ^ Syntax.string_of_term ctxt t ^ " is terminating but the fitness function time out.")

fun mk_individual ctxt trms subst t fit : individual = 
  {ctxt = ctxt,
   genome = trms,
   subst = subst,
   norm = t,
   fit = fit}

(*fun normalise ctxt simps t =
  if can HOLogic.dest_Trueprop t
  then Proof_Tools.normalise_conjecture ctxt simps t
  else let val typ = type_of t
           val prop = Logic.mk_equals (t, Free ("x", typ))
       in prop |> Proof_Tools.normalise_conjecture ctxt simps
               |> Logic.dest_equals
               |> fst
       end

fun prepare ctxt simps function_set lam =
  lam |> rpair function_set
      |> Envir.beta_eta_contract o list_comb
      |> normalise ctxt simps*)

(* FIXME: No type mapping *)
fun mk_subst vars trms =
  trms |> map2 (fn v => fn t => (Var v, t)) vars
       |> (fn r => ([], r))

fun prepare (data : gp_data) ((typs, terms) : subst) =
  (map (apply2 (Thm.ctyp_of (#ctxt data))) typs,
   map (apply2 (Thm.cterm_of (#ctxt data))) terms)
    |> (fn csubst => Drule.instantiate_normalize csubst (#scheme data))
    |> Proof_Tools.normalise_thm (#ctxt data) (#simps data)
    |> snd o Logic.dest_equals o Thm.full_prop_of

val fun_config =
  Function_Common.FunctionConfig { sequential=true, default= NONE (*FIXME dynamic scoping*),
    domintros=false, partials=false}

fun mutual_function lthy (names,eqns) =
    let val naming = map (fn x => ((Binding.qualified_name x), NONE, NoSyn)) names
(*        val lthy' = lthy |> Named_Target.exit
                         |> Named_Target.theory_init*)
    in
      Function_Fun.add_fun naming
                           (map (fn t => ((Binding.empty, []), t)) eqns)
                           fun_config
                           lthy
    end

fun defining_equations scheme =
  let val eqns =
        scheme |> Utils.binder_elimination Const_Names.hol_exists []
               |> fst
               |> Utils.binder_elimination Const_Names.hol_forall []
               |> HOLogic.dest_conj o fst
      val names = eqns |> map (Term.head_of o fst o HOLogic.dest_eq)
                       |> map (fn Free (n, _) => n
                                | _ => raise ERROR "Ilegal functional scheme!")
                       |> distinct (is_equal o string_ord)
  in (names, map HOLogic.mk_Trueprop eqns) end

fun well_defined lthy t =
  (t |> defining_equations
    |> try (mutual_function lthy))
    handle TERM _ => NONE

fun initial_population (data : gp_data) =
   let val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       fun new_individual i (set, unique, repeated) =
          let val trms = vars |> map2 (fn tc => fn (_, typ) =>
                                        tc |> Utils.weighted_choose
                                           |> Random_Terms.random_term typ
                                           |> the) (#term_count data)
              val t' = prep trms
          in if i < (#population_size data)
             then (if Term_Tab.defined set t'
                   then new_individual (i+1) (set, unique, repeated)
                   else let val wd = well_defined (#ctxt data) t'
                        in case wd of
                            SOME ctxt => let val _ = if (#debug data)
                                                     then tracing (".."^ string_of_int i)
                                                     else ()
                                         in (Term_Tab.update (t', wd) set, (ctxt, trms) :: unique, repeated) end
                          | NONE => new_individual (i+1) (Term_Tab.update (t', wd) set, unique, repeated)
                        end)
             else (if Term_Tab.defined set t'
                   then let val wd = the (Term_Tab.lookup set t')
                        in case wd of
                            SOME ctxt => (set, unique, (ctxt, trms) :: repeated)
                          | NONE =>  new_individual (i+1) (set, unique, repeated)
                        end
                   else let val wd = well_defined (#ctxt data) t'
                        in case wd of
                            SOME ctxt => (Term_Tab.update (t', wd) set, (ctxt, trms) :: unique, repeated)
                          | NONE => new_individual (i+1) (Term_Tab.update (t', wd) set, unique, repeated)
                        end)
          end
       fun new_individual' ((set, unique, repeated), _) =
          1 upto Multithreading.max_threads_value ()
            |> Par_List.get_some (fn _ => SOME (new_individual 0 (set, unique, repeated)))
            |> the
   in 1 upto (#population_size data)
        |> pair (Term_Tab.empty, [], [])
        |> Library.foldl new_individual'
        |> (fn (set, unique, repeated) =>
                let val uniques = 
                      unique |> Par_List.map
                                  (fn (ctxt, trms) =>
                                        let val rat = (TimeLimit.timeLimit
                                                        (#timeout data)
                                                        (#fitness data) ctxt)
                                                        handle TimeLimit.TimeOut => (timeout_error ctxt (prep trms);
                                                                                     big_rational)
                                            val ind = mk_individual ctxt
                                                                    trms
                                                                    (mk_subst vars trms)
                                                                    (prep trms)
                                                                    rat
                                        in if (#finish data) ind
                                           then raise DONE ind
                                           else ind
                                        end)
                    val tab = Library.foldl (fn (tab, ind) =>
                                                  Term_Tab.update (#norm ind, #fit ind) tab)
                                            (Term_Tab.empty, uniques)
                in (set, uniques @ map (fn (ctxt, trms) =>
                                          let val rat = trms |> prep
                                                             |> Term_Tab.lookup tab
                                                             |> the
                                          in mk_individual ctxt
                                                           trms
                                                           (mk_subst vars trms)
                                                           (prep trms)
                                                           (rat)
                                          end) repeated)
                end)
        |> (fn (set, L) => 
              (Term_Tab.empty, L) 
                |> Library.foldl (fn (g, ind) => Term_Tab.update (#norm ind, SOME ind) g)
                |> rpair (Term_Tab.keys set)
                |> Library.foldl (fn (g, t) => case Term_Tab.lookup set t of
                                                   SOME (SOME _) => g
                                                 | NONE => g
                                                 | SOME NONE => Term_Tab.update (t, NONE) g)
                |> rpair L)
        |> apsnd (sort (Rat.ord o apply2 #fit))
   end

(*Substitute new for free occurrences of old in a term*)
fun subst [] = I
  | subst pairs =
      let fun substf i u =
            case AList.lookup (op aconv) pairs u of
                SOME (Bound j) => Bound (i + j)
              | SOME _ => raise ERROR "subst must map frees to bounds"
              | NONE => (case u of Abs(a,T,t) => Abs(a, T, substf (i+1) t)
                                 | t$u' => substf i t $ substf i u'
                                 | _ => u)
      in substf 0 end

fun cross s t =
    let val s = Envir.eta_long [] s
        val t = Envir.eta_long [] t
        val ps = Utils.positions s
        val qs = Utils.positions t
        fun test dom cod =
          forall (fn (_, ty1) => exists (fn (_, ty2) => ty1 = ty2) cod) dom
        fun count (_, _, p) =
          let val qs' = qs |> map (fn (t_q, _, _) =>
                                        let val dom = Term.add_frees t_q []
                                            val cod = Utils.bounds_at_position s p
                                            val sigmas =
                                              dom |> map (fn (_, ty) =>
                                              cod |> filter (fn (_, ty') => ty = ty')
                                                  |> length)
                                        in case sigmas of
                                              [] => 1
                                            | _ :: _ => Library.foldl (op * ) (1, sigmas)
                                        end)
          in Library.foldl (op +) (0, qs') end
          val ps_weighted = ps |> map (fn (t, ty, pos) =>
                                        ((t, ty, pos), count (t, ty, pos)))
                               |> filter (fn (_, i) => i > 0)
        fun select ps_weighted =
          let
              val (s_p, tao, p) = Utils.weighted_choose ps_weighted
              val qs' = qs |> filter (fn (t_q, ty, _) =>
                                        let val dom = Term.add_frees t_q []
                                            val cod = Utils.bounds_at_position s p
                                        in ty = tao andalso
                                           test dom cod
                                        end)
          in if null qs'
             then select (remove (op = o apply2 fst) ((s_p, tao, p), 0) ps_weighted)
             else qs' |> map (fn x => (x, 1))
                      |> Utils.weighted_choose
                      |> pair (s_p, tao, p)
          end
        val ((_, _, p), (t_q, _, q)) = select ps_weighted
        val dom = Term.add_frees t_q []
        val cod = p |> Utils.bounds_at_position s
                    |> rev
                    |> map_index (fn (i, x) => (x, Bound i))
        val sigma = map (fn (s, ty) => cod |> filter (fn ((_, ty'), _) => ty = ty')
                                           |> map (fn x => (x, 1))
                                           |> Utils.weighted_choose
(*                                           |> tap (fn (x, _) => tracing (s ^ "\<longrightarrow>" ^ Syntax.string_of_term @{context} (Free x)))*)
                                           |> snd
                                           |> pair (Free (s, ty))) dom
(*    in (Utils.substitute (subst_atomic sigma t_q, p) s, p, q) end*)
    in (Utils.substitute (subst sigma t_q, p) s, p, q) end

fun print_pos pos =
  pos |> map string_of_int
      |> space_implode ", "
      |> enclose "[" "]"

fun crossover s t =
  let val (r, _, _) = cross s t
(*  let val (r, p1, p2) = cross s t
      val _ = tracing (print_pos p1)
      val _ = tracing (print_pos p2)*)
  in Envir.beta_eta_contract r end

fun Crossover (global : individual option Term_Tab.table) (data : gp_data) ss tt =
  let val (i, (s, t)) =
                   ss |> map2 pair tt
                      |> map_index (fn x => x)
                      |> map (fn (i, (s, t)) => ((i, (s, t)), size_of_term s + size_of_term t))
                      |> Utils.weighted_choose
       val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       val prefix = take i ss
       val suffix = drop (i + 1) ss
       fun f tab = let val c = crossover s t
                      val nn = prefix @ [c] @ suffix
                      val t' = prep nn
                   in case Term_Tab.lookup global t' of
                        SOME (SOME ind) => (tab, #ctxt ind, nn)
                      | SOME NONE => f tab
                      | NONE => (case Term_Tab.lookup tab t' of
                                      SOME _ => f tab
                                    | NONE => (case well_defined (#ctxt data) t' of
                                                SOME ctxt => (tab, ctxt, nn)
                                              | NONE => f (Term_Tab.update (t', ()) tab)))
                  end
  in f Term_Tab.empty
  end

(*
fun mutation prob t =
  if Random.random () <= prob
  then crossover t t
  else t*)

fun mutation (data : gp_data) t =
  let val t = Envir.eta_long [] t
      val (_, ty, q) =
              t |> Utils.positions
                |> map (rpair 1)
                |> Utils.weighted_choose
      val bounds = q |> Utils.bounds_at_position t
                     |> rev
                     |> map_index (fn (i, x) => (x, Bound i))
      val target_typ = bounds |> map (snd o fst)
                              |> (fn typs => typs ---> ty)
      val term_count = 1 upto (#term_size data)
                          |> Par_List.map (fn i => (i, Random_Terms.count_terms target_typ i))
                          |> filter (fn (_, c) => c > 0)
(*                          |> tap (map (fn (i, c) => tracing (string_of_int i ^ " : " ^ string_of_int c)))*)
      val s = term_count |> Utils.weighted_choose
                         |> Random_Terms.random_term target_typ
                         |> the
                         |> rpair (map snd bounds)
                         |> Envir.beta_eta_contract o list_comb
  in Utils.substitute (s, q) t end

fun Mutation (global : individual option Term_Tab.table)
             (data : gp_data) (tab, ctxt, ss) =
  if Random.random () <= (#mutation_prob data)
  then
  let val (i, s) = ss |> map_index (fn x => x)
                      |> map (fn (i, s) => ((i, s), size_of_term s))
                      |> Utils.weighted_choose
       val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
       fun prep trms = trms |> mk_subst vars
                            |> prepare data
       val prefix = take i ss
       val suffix = drop (i + 1) ss
       fun f tab = let val c = mutation data s
                       val nn = prefix @ [c] @ suffix
                       val t' = prep nn
                   in case Term_Tab.lookup global t' of
                        SOME (SOME ind) => (tab, #ctxt ind, nn)
                      | SOME NONE => f tab
                      | NONE => (case Term_Tab.lookup tab t' of
                                      SOME _ => f tab
                                    | NONE => (case well_defined (#ctxt data) t' of
                                                SOME ctxt => (tab, ctxt, nn)
                                              | NONE => f (Term_Tab.update (t', ()) tab)))
                  end
  in f tab
  end
  else (tab, ctxt, ss)

val rat_to_float = op / o apply2 real o Rat.quotient_of_rat

fun print_pool (pool : individual list) =
  pool |> map (fn ind => 
          tracing (Syntax.string_of_term (#ctxt ind) (#norm ind) ^ " : " ^ (string_of_real o rat_to_float) (#fit ind)))

fun print_pool' ctxt (pool : (individual * int) list) =
  pool |> map (fn (ind, i) => 
          (tracing (Syntax.string_of_term ctxt (#norm ind));
           tracing (string_of_int i)))
(*          tracing (Syntax.string_of_term ctxt t ^ " : " ^ string_of_int i))*)

fun next_generation (data : gp_data)
                    (global : individual option Term_Tab.table, pool : individual list) =
  let (*val _ = print_pool pool*)
      val vars = (#scheme data)
                         |> Thm.full_prop_of
                         |> (fn t => Term.add_vars t [])
      fun prep trms = trms |> mk_subst vars
                           |> prepare data
      fun size_of_terms trms = Library.foldl (fn (s, t) => s + size_of_term t) (0, trms)
      val av_size =
            pool |> map (size_of_terms o #genome)
                 |> pair 0
                 |> Library.foldl (op +)
                 |> (fn x => real x / real (#population_size data))
      val av_error =
            pool |> map #fit
                 |> pair Rat.zero
                 |> Library.foldl (op +/)
                 |> (fn x => x // Rat.rat_of_int (#population_size data))
      val bst_individual =
            pool |> Metis_Useful.minimum (Rat.ord o apply2 #fit)
                 |> fst
      val _ = tracing ("Average size: " ^ string_of_real av_size)
      val _ = tracing ("Average error: " ^ Rat.string_of_rat av_error ^ " (" ^ (string_of_real o rat_to_float) av_error ^ ")")
      val _ = tracing ("Best error: " ^ Rat.string_of_rat (#fit bst_individual))
(*      val _ = tracing ("Best Individual: " ^ Syntax.string_of_term (#ctxt data) (#norm bst_individual))*)
      val _ = tracing ("Normal Form: " ^ Syntax.string_of_term (#ctxt data) (#norm bst_individual))
      val pool' = map (fn {ctxt, genome,
                           subst, norm,
                           fit} => fit |> Rat.inv
                                       |> mk_individual ctxt genome subst norm) pool
      val lcm = Library.foldl (fn (lcm, ind) =>
              ind |> #fit
                  |> (snd o Rat.quotient_of_rat)
                  |> Integer.lcm lcm) (1, pool')
                  |> rpair 1
                  |> Rat.rat_of_quotient
      val pool' = pool' |> map (fn {ctxt, genome,
                                    subst, norm,
                                    fit} => lcm */ fit
                                              |> mk_individual ctxt genome subst norm)
                        |> map (fn ind => (ind, (fst o Rat.quotient_of_rat) (#fit ind)))
      val minv = pool' |> Utils.minby int_ord snd
                       |> snd
      val  pool' = map (fn (t, i) => (t, i div minv)) pool'
      val _ = if (#debug data)
              then print_pool' (#ctxt data) pool' 
                     |> (fn _ => ())
              else ()
      fun new_ind global =
          let val i1 = pool' |> Utils.weighted_choose
                             |> #genome
              val i2 = pool' |> Utils.weighted_choose
                             |> #genome
          in i2 |> Crossover global data i1
                |> Mutation global data end
      (* Slow part *)
      fun lookup (ctxt, trms) =
        let val i' = prep trms
        in
        case Term_Tab.lookup global i' of
            SOME (SOME ind) => mk_individual ctxt trms (mk_subst vars trms) 
                                             i' (#fit ind)
          | SOME NONE => raise ERROR "Ilegal individual!"
          | NONE   => let val rat = (TimeLimit.timeLimit
                                                        (#timeout data)
                                                        (#fitness data) ctxt)
                                                        handle TimeLimit.TimeOut => (timeout_error ctxt (prep trms);
                                                                                     big_rational)
                          val ind = mk_individual ctxt
                                                  trms
                                                  (mk_subst vars trms)
                                                  i'
                                                  rat
                        in if (#finish data) ind
                           then raise DONE ind
                           else ind
                        end
        end
      val rest =
        1 upto (#population_size data) - (#bests data)
          |> Par_List.map (fn _ => let val (tab, ctxt, trms) = new_ind global
                                   in (tab, lookup (ctxt, trms)) end)
      val bests = take (#bests data) pool
      val global = 
            (global, rest)
               |>  Library.foldl (fn (g, (tab, _)) => tab |> Term_Tab.keys
                                                          |> pair g
                                                          |> Library.foldl (fn (g, t) => 
                                                              Term_Tab.update (t, NONE) g))
  in bests @ map snd rest
      |> sort (Rat.ord o apply2 #fit)
      |> pair global end

fun evolve dbg scheme ctxt fitness finish term_size population_size generations bests mut_prob =
 (let val _ = tracing "Building initial population..."
      val vars = scheme
                   |> Thm.full_prop_of
                   |> (fn t => Term.add_vars t [])
      val term_count =
          vars |> 
          map (fn (_, typ) => 1 upto term_size
                          |> tap (fn _ => tracing ("Precalculating the inhabitants of type: " ^
                                                   Syntax.string_of_typ ctxt typ))
                          |> Par_List.map (fn i => (i, Random_Terms.count_terms typ i))
                          |> filter (fn (_, c) => c > 0)
                          |> tap (map (fn (i, c) => tracing (string_of_int i ^ " : " ^ string_of_int c))))
      val data : gp_data =
               { scheme = scheme,
                 term_size = term_size,
                 population_size = population_size,
                 bests = bests,
                 mutation_prob = mut_prob,
                 fitness = fitness,
                 finish = finish,
                 term_count = term_count,
                 ctxt = ctxt,
                 debug = dbg,
                 timeout = max_time_in_fitness |> Config.get ctxt
                                               |> Time.fromSeconds,
                 simps = scheme |> Thm.full_prop_of
                                |> global_simps ctxt
                                |> Utils.make_theorem_set
                                |> tap (fn _ => tracing "Simplification rules: ")
                                |> tap (tracing o Utils.str_of_thms)}
      fun loop i global_pool =
        let val _ = tracing ("Generation: " ^ string_of_int i)
        in if i < generations
           then loop (i+1) (next_generation data global_pool)
           else NONE
        end
  in data |> initial_population
          |> loop 1 end)
  handle DONE ind => let val _ = tracing (Syntax.string_of_term (#ctxt ind) (#norm ind))
                     in SOME ind end

end

structure GP : GP = DB_GP

