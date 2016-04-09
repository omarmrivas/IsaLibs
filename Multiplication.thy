theory Multiplication
imports "IsaLibs/IsaLibs"
begin

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space of a destructor style functional scheme. *}

definition scheme_dest where
"scheme_dest M N \<equiv> \<exists>(f::nat\<Rightarrow>nat\<Rightarrow>nat) (g::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(x::nat) (y::nat).
  ((f x y = M x y (0::nat) (\<lambda>x. x - (1::nat)) (\<lambda>x y z. if x then (y::nat) else z) (op = :: nat\<Rightarrow>nat\<Rightarrow>bool) f) \<and>
   (g x y = N x y (0::nat) (\<lambda>x. x - (1::nat)) (\<lambda>x y z. if x then (y::nat) else z) (op = :: nat\<Rightarrow>nat\<Rightarrow>bool) f g))"

text {* Now we get the terminating closure of the destructor style functional scheme. *}

definition terminating_closure_scheme_dest where
"terminating_closure_scheme_dest M N \<equiv> \<exists>f g. \<forall>(x::nat) (y::nat) c\<^sub>f c\<^sub>g (v\<^sub>f::nat) (v\<^sub>g::nat).
  ((f M N 0 c\<^sub>g v\<^sub>f v\<^sub>g x y = v\<^sub>f) \<and>
   (f M N (Suc c\<^sub>f) 0 v\<^sub>f v\<^sub>g x y = v\<^sub>g) \<and>
   (f M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g x y = M x y (0::nat)
                                 (\<lambda>x. x - (1::nat))
                                 (\<lambda>x y z. if x then (y::nat) else z)
                                 (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                 (f M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)) \<and>
   (g M N 0 c\<^sub>g v\<^sub>f v\<^sub>g x y = v\<^sub>f) \<and>
   (g M N (Suc c\<^sub>f) 0 v\<^sub>f v\<^sub>g x y = v\<^sub>g) \<and>
   (g M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g x y = N x y (0::nat) 
                                       (\<lambda>x. x - (1::nat)) 
                                       (\<lambda>x y z. if x then (y::nat) else z) 
                                       (op = :: nat\<Rightarrow>nat\<Rightarrow>bool) 
                                       (f M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)
                                       (g M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g)))"

text {* All individuals generated by @{term "terminating_closure_scheme_dest"}
  are terminating, regardless the value of @{term "M"} and @{term "N"}. *}

fun f\<^sub>d and g\<^sub>d where
"f\<^sub>d M N 0 c\<^sub>g v\<^sub>f v\<^sub>g (x::nat) y = (v\<^sub>f::nat)"|
"f\<^sub>d M N (Suc c\<^sub>f) 0 v\<^sub>f v\<^sub>g (x::nat) y = (v\<^sub>g::nat)"|
"f\<^sub>d M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g x (y::nat) = M x y (0::nat)
                                 (\<lambda>x. x - (1::nat))
                                 (\<lambda>x y z. if x then (y::nat) else z)
                                 (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                 (f\<^sub>d M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)"|
"g\<^sub>d M N 0 c\<^sub>g v\<^sub>f v\<^sub>g x y = v\<^sub>f"|
"g\<^sub>d M N c\<^sub>f 0 v\<^sub>f v\<^sub>g x (y::nat) = (v\<^sub>g::nat)"|
"g\<^sub>d M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g (x::nat) y = N x y (0::nat)
                                       (\<lambda>x. x - (1::nat))
                                       (\<lambda>x y z. if x then (y::nat) else z)
                                       (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                       (f\<^sub>d M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)
                                       (g\<^sub>d M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g)"

thm f\<^sub>d.simps g\<^sub>d.simps

theorem "terminating_closure_scheme_dest M N"
apply (unfold terminating_closure_scheme_dest_def)
apply (rule_tac x="f\<^sub>d" in exI)
apply (rule_tac x="g\<^sub>d" in exI)
by simp

text {* Now we define the functional space of a constructor style functional scheme. *}

definition scheme_const where
"scheme_const M N \<equiv> \<exists>(f::nat\<Rightarrow>nat\<Rightarrow>nat) (g::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(x::nat) (y::nat).
  ((f 0 y = y) \<and>
   (f (Suc x) y = M x y Suc (0::nat) f) \<and>
   (g 0 y = 0) \<and>
   (g (Suc x) y = N x y Suc (0::nat) f g))"

text {* Now we get the terminating closure of the constructor style functional scheme. *}

definition terminating_closure_scheme_const where
"terminating_closure_scheme_const M N \<equiv> \<exists>f g. \<forall>(x::nat) (y::nat) c\<^sub>f c\<^sub>g v\<^sub>f (v\<^sub>g::nat).
  ((f M N 0 c\<^sub>g v\<^sub>f v\<^sub>g x y = v\<^sub>f) \<and>
   (f M N (Suc c\<^sub>f) 0 v\<^sub>f v\<^sub>g x y = v\<^sub>g)\<and>
   (f M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g 0 y = y) \<and>
   (f M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g (Suc x) y = M x y Suc (0::nat)
                                 (f M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)) \<and>
   (g M N 0 (Suc c\<^sub>g) v\<^sub>f v\<^sub>g x y = v\<^sub>f) \<and>
   (g M N c\<^sub>f 0 v\<^sub>f v\<^sub>g x y = v\<^sub>g) \<and>
   (g M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g 0 y = 0) \<and>
   (g M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g (Suc x) y = N x y Suc (0::nat) 
                                             (f M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)
                                             (g M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g)))"

text {* All individuals generated by @{term "terminating_closure_scheme_const"}
  are terminating, regardless the value of @{term "M"} and @{term "N"}. *}

fun f\<^sub>c and g\<^sub>c where
"f\<^sub>c M N 0 c\<^sub>g v\<^sub>f v\<^sub>g (x::nat) y = (v\<^sub>f::nat)"|
"f\<^sub>c M N (Suc c\<^sub>f) 0 v\<^sub>f v\<^sub>g (x::nat) y = (v\<^sub>g::nat)"|
"f\<^sub>c M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g 0 y = y"|
"f\<^sub>c M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g (Suc x) (y::nat) = M x y Suc (0::nat)
                                 (f\<^sub>c M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)"|
"g\<^sub>c M N 0 (Suc c\<^sub>g) v\<^sub>f v\<^sub>g x y = v\<^sub>f"|
"g\<^sub>c M N c\<^sub>f 0 v\<^sub>f v\<^sub>g x (y::nat) = (v\<^sub>g::nat)"|
"g\<^sub>c M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g 0 y = 0"|
"g\<^sub>c M N (Suc c\<^sub>f) (Suc c\<^sub>g) v\<^sub>f v\<^sub>g (Suc x) y = N x y Suc (0::nat)
                                             (f\<^sub>c M N c\<^sub>f (Suc c\<^sub>g) v\<^sub>f v\<^sub>g)
                                             (g\<^sub>c M N (Suc c\<^sub>f) c\<^sub>g v\<^sub>f v\<^sub>g)"

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
    let val in_out = [(@{term "5::nat"}, @{term "3::nat"} ,@{term "15::int"}),
                      (@{term "1::nat"}, @{term "1::nat"} ,@{term "1::int"}),
                      (@{term "2::nat"}, @{term "2::nat"} ,@{term "4::int"}),
                      (@{term "2::nat"}, @{term "3::nat"} ,@{term "6::int"}),
                      (@{term "3::nat"}, @{term "2::nat"} ,@{term "6::int"}),
                      (@{term "3::nat"}, @{term "3::nat"} ,@{term "9::int"}),
                      (@{term "2::nat"}, @{term "4::nat"} ,@{term "8::int"}),
                      (@{term "4::nat"}, @{term "2::nat"} ,@{term "8::int"}),
                      (@{term "3::nat"}, @{term "4::nat"} ,@{term "12::int"}),
                      (@{term "4::nat"}, @{term "4::nat"} ,@{term "16::int"})]
        val c = @{term "20::nat"}
        val v = @{term "0 :: nat"}
        val f = (hd o tl) functions
        val to_int = @{term "(numeral o num_of_nat) :: nat\<Rightarrow>int"}
        val error = 
          in_out |> map (fn (x,y,r) => (Value.value ctxt (to_int $ (f $ c $ c $ v $ v $ x $ y)), r))
                 |> map (fn (i, r) => if i = r then 0 else 1)
    in (0, error) |> Library.foldl (op +)
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
        |> map (fn _ => GP.evolve true false scheme_const functions_const recursive_calls bad_fitness 
                                  lthy fitness finish term_size population_size generations bests mut_prob)
        val (eqs1, alleq1) = GNU_Plot.gp_statistics_to_equals population_size sts1
        val _ = tracing ("gp_statistics_to_equals Constructive: (" ^ string_of_int eqs1 ^ ", " ^ string_of_int alleq1 ^ ")")
        val _ = GNU_Plot.gp_statistics_to_error_plot ("MultiplicationConsts" ^ string_of_int generations) generations sts1

        val sts2 =
      1 upto experiments
        |> map (fn _ => GP.evolve true false scheme_dest functions_dest recursive_calls bad_fitness
                                  lthy fitness finish term_size population_size generations bests mut_prob)
        val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals population_size sts2
        val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
        val _ = GNU_Plot.gp_statistics_to_error_plot ("MultiplicationDest"^ string_of_int generations) generations sts2

        val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot ("Multiplication" ^ string_of_int generations) generations sts1 sts2
    in lthy end
*}

end