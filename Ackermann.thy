theory Ackermann
imports "IsaLibs/IsaLibs"
begin

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space of a destructor style functional scheme. *}

definition scheme_dest where
"scheme_dest M \<equiv> \<exists>(f::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(x::nat) (y::nat).
  (f x y = M x y (0::nat) Suc (\<lambda>x. x - (1::nat)) (\<lambda>x y z. if x then (y::nat) else z) (op = :: nat\<Rightarrow>nat\<Rightarrow>bool) f)"

text {* Now we get the terminating closure of the destructor style functional scheme. *}

definition terminating_closure_scheme_dest where
"terminating_closure_scheme_dest M \<equiv> \<exists>f. \<forall>(x::nat) (y::nat) c\<^sub>f (v\<^sub>f::nat).
  ((f M 0 v\<^sub>f x y = v\<^sub>f) \<and>
   (f M (Suc c\<^sub>f) v\<^sub>f x y = M x y (0::nat) Suc
                                 (\<lambda>x. x - (1::nat))
                                 (\<lambda>x y z. if x then (y::nat) else z)
                                 (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                 (f M c\<^sub>f v\<^sub>f)))"

text {* All individuals generated by @{term "terminating_closure_scheme_dest"}
  are terminating, regardless the value of @{term "M"}. *}

fun f\<^sub>d where
"f\<^sub>d M 0 v\<^sub>f (x::nat) y = (v\<^sub>f::nat)"|
"f\<^sub>d M (Suc c\<^sub>f) v\<^sub>f x (y::nat) = M x y (0::nat) Suc
                                 (\<lambda>x. x - (1::nat))
                                 (\<lambda>x y z. if x then (y::nat) else z)
                                 (op = :: nat\<Rightarrow>nat\<Rightarrow>bool)
                                 (f\<^sub>d M c\<^sub>f v\<^sub>f)"

thm f\<^sub>d.simps

theorem "terminating_closure_scheme_dest M"
apply (unfold terminating_closure_scheme_dest_def)
apply (rule_tac x="f\<^sub>d" in exI)
by simp

text {* Now we define the functional space of a constructor style functional scheme. *}

definition scheme_const where
"scheme_const M N \<equiv> \<exists>(f::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(x::nat) (y::nat).
  ((f 0 y = Suc y) \<and>
   (f (Suc x) 0 = M x Suc (0::nat) f) \<and>
   (f (Suc x) (Suc y) = N x y Suc (0::nat) f))"

text {* Now we get the terminating closure of the constructor style functional scheme. *}

definition terminating_closure_scheme_const where
"terminating_closure_scheme_const M N \<equiv> \<exists>f. \<forall>(x::nat) (y::nat) c\<^sub>f v\<^sub>f.
  ((f M N 0 v\<^sub>f x y = v\<^sub>f) \<and>
   (f M N (Suc c\<^sub>f) v\<^sub>f 0 y = Suc y) \<and>
   (f M N (Suc c\<^sub>f) v\<^sub>f (Suc x) 0 = M x Suc (0::nat)
                                 (f M N c\<^sub>f v\<^sub>f)) \<and>
   (f M N (Suc c\<^sub>f) v\<^sub>f (Suc x) (Suc y) = N x y Suc (0::nat)
                                 (f M N c\<^sub>f v\<^sub>f)))"

text {* All individuals generated by @{term "terminating_closure_scheme_const"}
  are terminating, regardless the value of @{term "M"} and @{term "N"}. *}

fun f\<^sub>c where
"f\<^sub>c M N 0 v\<^sub>f x y = v\<^sub>f"|
"f\<^sub>c M N (Suc c\<^sub>f) v\<^sub>f 0 y = Suc y"|
"f\<^sub>c M N (Suc c\<^sub>f) v\<^sub>f (Suc x) 0 = M x Suc (0::nat)
                                 (f\<^sub>c M N c\<^sub>f v\<^sub>f)"|
"f\<^sub>c M N (Suc c\<^sub>f) v\<^sub>f (Suc x) (Suc y) = N x y Suc (0::nat)
                                 (f\<^sub>c M N c\<^sub>f v\<^sub>f)"

thm f\<^sub>c.simps

theorem "terminating_closure_scheme_const M N"
apply (unfold terminating_closure_scheme_const_def)
apply (rule_tac x="f\<^sub>c" in exI)
by simp

text {* We then define the fitness function, the termination criterion,
  and other GP related parameters.
*}

ML {*
  fun fitness ctxt functions =
    let val in_out = [(@{term "0::nat"},@{term "0::nat"},@{term "Suc 0"}), (@{term "1::nat"},@{term "0::nat"},@{term "Suc (Suc 0)"}), (@{term "0::nat"},@{term "1::nat"},@{term "Suc(Suc 0)"}),
                      (@{term "1::nat"},@{term "1::nat"},@{term "Suc (Suc (Suc 0))"}), (@{term "1::nat"},@{term "2::nat"},@{term "Suc(Suc(Suc(Suc 0)))"}), (@{term "2::nat"},@{term "1::nat"},@{term "Suc(Suc(Suc(Suc(Suc 0))))"}),
                      (@{term "2::nat"},@{term "2::nat"},@{term "Suc(Suc(Suc(Suc(Suc(Suc(Suc 0))))))"}), (@{term "Suc (Suc 0)"},@{term "0::nat"},@{term "Suc(Suc(Suc 0))"}), (@{term "0::nat"},@{term "2::nat"},@{term "Suc(Suc(Suc 0))"})]
        val f = hd functions
        val c = @{term "100::nat"}
        val v = @{term "0 :: nat"}
        val error = 
          in_out |> map (fn (x,y,r) => (Value.value ctxt (f $ c $ v $ x $ y), r))
                 |> map (fn (i, r) => let val _ = tracing (Syntax.string_of_term ctxt i)
                                          val _ = tracing (Syntax.string_of_term ctxt r)
                                      in if i = r then 0 else 1 end)
    in (0, error) |> Library.foldl (op +)
                  |> Rat.rat_of_int end
  fun finish ({fit, ...} : GP.individual) = Rat.eq (Rat.zero, fit)
  fun test ctxt consts =
      consts |> fitness ctxt
             |> pair Rat.zero
             |> Rat.eq
  val term_size = 25
  val population_size = 200
  val generations = 1000
  val bests = 10
  val mut_prob = 0.05
  val scheme_dest = @{thm "scheme_dest_def"}
  val scheme_const = @{thm "scheme_const_def"}
  val functions_dest = [@{term "f\<^sub>d"}]
  val functions_const = [@{term "f\<^sub>c"}]
  val experiments = 20
  val recursive_calls = 2
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
        val _ = GNU_Plot.gp_statistics_to_error_plot ("AckermannConsts"^ string_of_int generations) generations sts1

        val sts2 =
      1 upto experiments
        |> map (fn _ => GP.evolve true false scheme_dest functions_dest recursive_calls bad_fitness
                                  lthy fitness finish term_size population_size generations bests mut_prob)
        val (eqs2, alleq2) = GNU_Plot.gp_statistics_to_equals population_size sts2
        val _ = tracing ("gp_statistics_to_equals Destructive: (" ^ string_of_int eqs2 ^ ", " ^ string_of_int alleq2 ^ ")")
        val _ = GNU_Plot.gp_statistics_to_error_plot ("AckermannDest"^ string_of_int generations) generations sts2

        val _ = GNU_Plot.gp_statistics_to_cumulative_prob_plot ("Ackermann"^ string_of_int generations) generations sts1 sts2
    in lthy end
*}

end