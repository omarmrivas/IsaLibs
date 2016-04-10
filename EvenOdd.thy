theory EvenOdd
imports "IsaLibs/IsaLibs"
begin

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space of a destructor style functional scheme. *}

definition scheme_dest where
"scheme_dest M N \<equiv> \<exists>(f::nat\<Rightarrow>bool) (g::nat\<Rightarrow>bool). \<forall>(x::nat).
  ((f x = M x (0::nat) True False (\<lambda>x. x - (1::nat)) (\<lambda>x y z. if x then (y::bool) else z) (op = :: nat\<Rightarrow>nat\<Rightarrow>bool) g) \<and>
   (g x = N x (0::nat) True False (\<lambda>x. x - (1::nat)) (\<lambda>x y z. if x then (y::bool) else z) (op = :: nat\<Rightarrow>nat\<Rightarrow>bool) f))"

text {* Now we get the terminating closure of the destructor style functional scheme. *}

definition terminating_closure_scheme_dest where
"terminating_closure_scheme_dest M N \<equiv> \<exists>f g. \<forall>(x::nat) c\<^sub>f c\<^sub>g (v\<^sub>f::bool) (v\<^sub>g::bool).
  ((f M N 0 c\<^sub>g v\<^sub>f v\<^sub>g x = v\<^sub>f) \<and>
   (f M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g x = M x (0::nat)
                                 True False
                                 (\<lambda>x. x - (1::nat))
                                 (\<lambda>x y z. if x then (y::bool) else z)
                                 (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                 (g M N c\<^sub>f c\<^sub>g v\<^sub>f v\<^sub>g)) \<and>
   (g M N c\<^sub>f 0 v\<^sub>f v\<^sub>g x = v\<^sub>g) \<and>
   (g M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g x = N x (0::nat)
                                       True False
                                       (\<lambda>x. x - (1::nat))
                                       (\<lambda>x y z. if x then (y::bool) else z) 
                                       (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                       (f M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)))"

text {* All individuals generated by @{term "terminating_closure_scheme_dest"}
  are terminating, regardless the value of @{term "M"} and @{term "N"}. *}

fun f\<^sub>d and g\<^sub>d where
"f\<^sub>d M N 0 c\<^sub>g v\<^sub>f v\<^sub>g (x::nat) = (v\<^sub>f::bool)"|
"f\<^sub>d M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g x = M x (0::nat)
                                 True False
                                 (\<lambda>x. x - (1::nat))
                                 (\<lambda>x y z. if x then (y::bool) else z)
                                 (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                 (g\<^sub>d M N c\<^sub>f c\<^sub>g v\<^sub>f v\<^sub>g)"|
"g\<^sub>d M N c\<^sub>f 0 v\<^sub>f v\<^sub>g x = (v\<^sub>g::bool)"|
"g\<^sub>d M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g (x::nat) = N x (0::nat)
                                       True False
                                       (\<lambda>x. x - (1::nat))
                                       (\<lambda>x y z. if x then (y::bool) else z)
                                       (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                       (f\<^sub>d M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)"

thm f\<^sub>d.simps g\<^sub>d.simps

theorem "terminating_closure_scheme_dest M N"
apply (unfold terminating_closure_scheme_dest_def)
apply (rule_tac x="f\<^sub>d" in exI)
apply (rule_tac x="g\<^sub>d" in exI)
by simp

text {* Now we define the functional space of a constructor style functional scheme. *}

definition scheme_const where
"scheme_const M N \<equiv> \<exists>(f::nat\<Rightarrow>bool) (g::nat\<Rightarrow>bool). \<forall>(x::nat).
  ((f 0 = True) \<and>
   (f (Suc x) = M x Suc (0::nat) g) \<and>
   (g 0 = False) \<and>
   (g (Suc x) = N x Suc (0::nat) f))"

text {* Now we get the terminating closure of the constructor style functional scheme. *}

definition terminating_closure_scheme_const where
"terminating_closure_scheme_const M N \<equiv> \<exists>f g. \<forall>(x::nat) c\<^sub>f c\<^sub>g v\<^sub>f (v\<^sub>g::bool).
  ((f M N 0 c\<^sub>g v\<^sub>f v\<^sub>g x = v\<^sub>f) \<and>
   (f M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g 0 = True) \<and>
   (f M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g (Suc x) = M x Suc (0::nat)
                                 (g M N c\<^sub>f c\<^sub>g v\<^sub>f v\<^sub>g)) \<and>
   (g M N c\<^sub>f 0 v\<^sub>f v\<^sub>g x = v\<^sub>g) \<and>
   (g M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g 0 = False) \<and>
   (g M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g (Suc x) = N x Suc (0::nat) 
                                             (f M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)))"

text {* All individuals generated by @{term "terminating_closure_scheme_const"}
  are terminating, regardless the value of @{term "M"} and @{term "N"}. *}

fun f\<^sub>c and g\<^sub>c where
"f\<^sub>c M N 0 c\<^sub>g v\<^sub>f v\<^sub>g (x::nat) = (v\<^sub>f::bool)"|
"f\<^sub>c M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g 0 = True"|
"f\<^sub>c M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g (Suc x) = M x Suc (0::nat)
                                 (g\<^sub>c M N c\<^sub>f c\<^sub>g v\<^sub>f v\<^sub>g)"|
"g\<^sub>c M N c\<^sub>f 0 v\<^sub>f v\<^sub>g x = (v\<^sub>g::bool)"|
"g\<^sub>c M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g 0 = False"|
"g\<^sub>c M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g (Suc x) = N x Suc (0::nat)
                                             (f\<^sub>c M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)"

thm f\<^sub>c.simps g\<^sub>c.simps

theorem "terminating_closure_scheme_const M N"
apply (unfold terminating_closure_scheme_const_def)
apply (rule_tac x="f\<^sub>c" in exI)
apply (rule_tac x="g\<^sub>c" in exI)
by simp

text {* We then define the fitness function, the termination criterion,
  and other GP related parameters.
*}

ML {*
  fun fitness ctxt functions =
    let val in_out = [(@{term "0::nat"}, @{term "True"} ,@{term "False"}),
                      (@{term "1::nat"}, @{term "False"} ,@{term "True"}),
                      (@{term "2::nat"}, @{term "True"} ,@{term "False"}),
                      (@{term "3::nat"}, @{term "False"} ,@{term "True"}),
                      (@{term "4::nat"}, @{term "True"} ,@{term "False"})]
        val c = @{term "6::nat"}
        val v = @{term "False"}
        val f = hd functions
        val g = (hd o tl) functions
        val error = 
          in_out |> map (fn (x,r1,r2) => 
                          (Value.value ctxt (f $ c $ c $ v $ v $ x), Value.value ctxt (g $ c $ c $ v $ v $ x), r1, r2))
                 |> map (fn (i1, i2, r1, r2) => (if i1 = r1 then 0 else 1) + 
                                                (if i2 = r2 then 0 else 1))
    in (0, error) |> Library.foldl (op +)
                  |> Rat.rat_of_int end
  fun finish ({fit, ...} : GP.individual) = Rat.eq (Rat.zero, fit)
  fun test ctxt consts =
      consts |> fitness ctxt
             |> pair Rat.zero
             |> Rat.eq
  val term_size = 35
  val population_size = 200
  val generations = 1000
  val bests = 10
  val mut_prob = 0.05
  val scheme_dest = @{thm "scheme_dest_def"}
  val scheme_const = @{thm "scheme_const_def"}
  val functions_dest = [@{term "f\<^sub>d"}, @{term "g\<^sub>d"}]
  val functions_const = [@{term "f\<^sub>c"}, @{term "g\<^sub>c"}]
  val experiments = 20
  val recursive_calls = 1
  val bad_fitness = Rat.rat_of_int 10
*}

text {* We finally call the GP algorithm. *}

local_setup {*
 fn lthy =>
    let val sts1 =
      1 upto experiments
        |> map (fn _ => GP.evolve true false scheme_const functions_const recursive_calls bad_fitness lthy fitness finish
                                  term_size population_size generations bests mut_prob)
        val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals population_size sts1
        val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
        val _ = GNU_Plot.gp_statistics_to_error_plot ("EvenOddConsts"^string_of_int generations) generations sts1

        val sts2 =
      1 upto experiments
        |> map (fn _ => GP.evolve true false scheme_dest functions_dest recursive_calls bad_fitness lthy fitness finish
                                  term_size population_size generations bests mut_prob)
        val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals population_size sts2
        val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
        val _ = GNU_Plot.gp_statistics_to_error_plot ("EvenOddDest"^string_of_int generations) generations sts2

        val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot ("EvenOdd"^string_of_int generations) generations sts1 sts2
    in lthy end
*}

end