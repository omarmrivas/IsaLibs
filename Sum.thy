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
           (hd :: int list\<Rightarrow>int)
           (tl :: int list\<Rightarrow>int list)
           f"

definition scheme_const where
"scheme_const M N \<equiv> \<exists>(f::int list\<Rightarrow>int). \<forall>(xs::int list) (x::int).
  (f [] = M (0::int)) \<and>
  (f (x#xs) = N x
                xs
                (op + :: int\<Rightarrow>int\<Rightarrow>int)
                f)"

(*lemma "scheme_dest (\<lambda>a b c d e f g h i. b (c d a) f (e (g a) (i (h a))))"
apply (unfold scheme_dest_def)*)

(*lemma "scheme_const (\<lambda>a. a) (\<lambda>a b c d. c a (d b))"
apply (unfold scheme_const_def)*)

ML {*
  val sizes = DB_EXHAUST.calculate_search_space @{thm scheme_dest_def} 50
  val _ = tracing "sizes scheme_dest_def"
  val _ = map (tracing o string_of_int o fst) sizes
  val _ = tracing "terms scheme_dest_def"
  val _ = map (tracing o string_of_int o snd) sizes
*}

ML {*
  val sizes = DB_EXHAUST.calculate_search_space @{thm scheme_const_def} 50
  val _ = tracing "sizes scheme_const_def"
  val _ = map (tracing o string_of_int o fst) sizes
  val _ = tracing "terms scheme_const_def"
  val _ = map (tracing o string_of_int o snd) sizes
*}

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
  val term_size = 50
  val population_size = 200
  val generations = 200
  val bests = 10
  val mut_prob = 0.05
  val scheme = @{thm "scheme_def"}
*}

text {* We finally call the GP algorithm. *}

(*local_setup {*
 fn lthy => 
  case DB_EXHAUST.exhaust true lthy scheme term_size [] test of
    SOME (ctxt, t, trms) => 
      let val _ = map (tracing o (Syntax.string_of_term ctxt)) trms
      in ctxt end
  | NONE => lthy
*}*)

(*local_setup {*
 fn lthy => 
  case GP.evolve true false scheme lthy fitness finish term_size population_size generations bests mut_prob of
    SOME ind => (#ctxt ind)
  | NONE => lthy
*}*)

text {* Genome is composed by: 
@{term "\<lambda>x xa xb xc xd. xd"}
@{term "\<lambda>x xa xb. xb"}
@{term "\<lambda>x xa xb xc. xb"}
@{term "\<lambda>x xa xb. x"} *}

thm f.simps
thm g.simps

ML {*
  val Const C = @{term "g"}
  val r = fitness @{context} [C,C]
*}

value "g 0 0"

lemma "g x y = ackermann x y"
nitpick

text {* Invented functions are well-defined *}
lemma "scheme (\<lambda>x xa xb. x) (\<lambda>x xa xb xc. xb) (\<lambda>x xa xb. xb) (\<lambda>x xa xb xc xd. xd)"
apply (unfold scheme_def)
apply (rule_tac x="f" in exI)
apply (rule_tac x="g" in exI)
apply simp
done

end