theory Multiplication
imports "IsaLibs/IsaLibs"
begin

declare[[
  max_time_in_counter_ex = 4,
  max_time_in_fitness = 50]]

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space.*}

definition scheme_const where
"scheme_const M N \<equiv> \<exists>(f::nat\<Rightarrow>nat\<Rightarrow>nat) (g::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(x::nat) (y::nat).
  ((f 0 y = y) \<and>
   (f (Suc x) y = M x y Suc (0::nat) (f x)) \<and>
   (g 0 y = 0) \<and>
   (g (Suc x) y = N x y Suc (0::nat) f (g x)))"

definition scheme_dest where
"scheme_dest M N \<equiv> \<exists>(f::nat\<Rightarrow>nat\<Rightarrow>nat) (g::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(x::nat) (y::nat).
  ((f x y = M x y (0::nat) (\<lambda>x. x - (1::nat)) (\<lambda>x y z. if x then (y::nat) else z) (op = :: nat\<Rightarrow>nat\<Rightarrow>bool) f) \<and>
   (g x y = N x y (0::nat) (\<lambda>x. x - (1::nat)) (\<lambda>x y z. if x then (y::nat) else z) (op = :: nat\<Rightarrow>nat\<Rightarrow>bool) f g))"

text {* We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise multiplication in terms of 
  addition of natural numbers.
*}

ML {*
  fun fitness ctxt consts =
    let val in_out = [(@{term "0::nat"}, @{term "0::nat"} ,@{term "0::nat"}),
                      (@{term "1::nat"}, @{term "1::nat"} ,@{term "1::nat"}),
                      (@{term "2::nat"}, @{term "2::nat"} ,@{term "4::nat"}),
                      (@{term "2::nat"}, @{term "3::nat"} ,@{term "6::nat"}),
                      (@{term "3::nat"}, @{term "2::nat"} ,@{term "6::nat"}),
                      (@{term "3::nat"}, @{term "3::nat"} ,@{term "9::nat"}),
                      (@{term "2::nat"}, @{term "4::nat"} ,@{term "8::nat"}),
                      (@{term "4::nat"}, @{term "2::nat"} ,@{term "8::nat"}),
                      (@{term "3::nat"}, @{term "4::nat"} ,@{term "12::nat"}),
                      (@{term "4::nat"}, @{term "4::nat"} ,@{term "16::nat"})]
        val f = consts (* |> tap (map (tracing o fst)) *)
                       |> hd
                       |> Const
        val conjectures =
          in_out |> map (fn (x,y,r) => (f $ x $ y, r) |> HOLogic.mk_eq
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
  val term_size = 20
  val population_size = 200
  val generations = 100
  val bests = 10
  val mut_prob = 0.05
  val scheme_dest = @{thm "scheme_dest_def"}
  val scheme_const = @{thm "scheme_const_def"}
  val experiments = 20
*}

text {* We finally call the GP algorithm. *}

(*local_setup {*
 fn lthy => 
  let val Const C = @{term "op * :: nat\<Rightarrow>nat\<Rightarrow>nat"}
      val ff = fitness lthy [C, C]
      val _ = tracing (Rat.string_of_rat ff)
  in lthy end
*}*)

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
        val _ = GNU_Plot.gp_statistics_to_error_plot "MulDest" generations sts2
val sts1 =
      1 upto experiments
        |> map (fn _ => GP.evolve true false scheme_const lthy fitness finish
                                  term_size population_size generations bests mut_prob)
        val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals population_size sts1
        val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
        val (nt1, allnt1) = GNU_Plot.gp_statistics_to_non_terminating sts1
        val _ = tracing ("gp_statistics_to_non_terminating Constructive: (" ^ string_of_int nt1 ^ ", " ^ string_of_int allnt1 ^ ")")
        val _ = GNU_Plot.gp_statistics_to_error_plot "SumConsts" generations sts1

        val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot "Mul" generations sts1 sts2
    in lthy end
*}

end