theory Sum
imports "IsaLibs/IsaLibs"
begin

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space.*}

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

definition scheme_const where
"scheme_const N \<equiv> \<exists>(f::int list\<Rightarrow>int). \<forall>(xs::int list) (x::int).
  (f [] = (0::int)) \<and>
  (f (x#xs) = N x
                xs
                (op + :: int\<Rightarrow>int\<Rightarrow>int)
                f)"

text {* We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise multiplication in terms of 
  addition of natural numbers.
*}

ML {*
  fun fitness ctxt consts =
    let val in_out = [(@{term "[] :: int list"},@{term "0::int"}),
                      (@{term "[1]:: int list"},@{term "1::int"}),
                      (@{term "[1,2]:: int list"},@{term "3::int"}),
                      (@{term "[1,2,3]:: int list"},@{term "6::int"}),
                      (@{term "[1,2,3,4]:: int list"},@{term "10::int"}),
                      (@{term "[1,2,3,4,5]:: int list"},@{term "15::int"}),
                      (@{term "[1,2,3,4,5,6]:: int list"},@{term "21::int"}),
                      (@{term "[1,2,3,4,5,6,7]:: int list"},@{term "28::int"}),
                      (@{term "[1,2,3,4,5,6,7,8]:: int list"},@{term "36::int"}),
                      (@{term "[1,2,3,4,5,6,7,8,9]:: int list"},@{term "45::int"})]
        val f = consts (* |> tap (map (tracing o fst)) *)
                       |> hd
                       |> Const
        val conjectures =
          in_out |> map (fn (xs,r) => ((f $ xs), r) |> HOLogic.mk_eq
                                                    |> HOLogic.mk_Trueprop)
(*                 |> tap (map (tracing o Syntax.string_of_term ctxt))*)
        val ctxt = Local_Theory.target_of ctxt
        val error = conjectures |> map (Counter_Example.counter_example ctxt 10)
                                |> map (fn foo => if foo then 1 else 0)
    in (0, error) |> Library.foldl (op +)
(*                  |> tap (tracing o string_of_int)*)
                  |> Rat.rat_of_int end
  fun finish ({fit, ...} : GP.individual) = Rat.eq (Rat.zero, fit)
  fun test ctxt consts =
      consts |> fitness ctxt
             |> pair Rat.zero
             |> Rat.eq
  val term_size = 35
  val population_size = 200
  val generations = 100
  val bests = 10
  val mut_prob = 0.05
  val scheme_dest = @{thm "scheme_dest_def"}
  val scheme_const = @{thm "scheme_const_def"}
  val experiments = 20
*}

text {* We finally call the GP algorithm. *}

local_setup {*
 fn lthy => 
    let 
        val sts2 =
      1 upto experiments
        |> map (fn _ => GP.evolve true false scheme_dest lthy fitness finish
                                  term_size population_size generations bests mut_prob)
        val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals population_size sts2
        val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
        val (nt2, allnt2) = GNU_Plot.gp_statistics_to_non_terminating sts2
        val _ = tracing ("gp_statistics_to_non_terminating Destructive: (" ^ string_of_int nt2 ^ ", " ^ string_of_int allnt2 ^ ")")
        val _ = GNU_Plot.gp_statistics_to_error_plot "SumDest" generations sts2
val sts1 =
      1 upto experiments
        |> map (fn _ => GP.evolve true false scheme_const lthy fitness finish
                                  term_size population_size generations bests mut_prob)
        val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals population_size sts1
        val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
        val (nt1, allnt1) = GNU_Plot.gp_statistics_to_non_terminating sts1
        val _ = tracing ("gp_statistics_to_non_terminating Constructive: (" ^ string_of_int nt1 ^ ", " ^ string_of_int allnt1 ^ ")")
        val _ = GNU_Plot.gp_statistics_to_error_plot "SumConsts" generations sts1

        val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot "Sum" generations sts1 sts2
    in lthy end
*}

end