theory Ackermann
imports "IsaLibs/IsaLibs"
begin

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space.*}

fun Iter :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"Iter f 0 = f 1"|
"Iter f (Suc n) = f (Iter f n)"
fun Ack where
"Ack 0 = Suc"|
"Ack (Suc n) = Iter (Ack n)"

value "Ack 0 0"

fun ackermann where
"ackermann 0 n = Suc n" |
"ackermann (Suc m) 0 = ackermann m 1" |
"ackermann (Suc m) (Suc n) = ackermann m (ackermann (Suc m) n)"

value "ackermann 0 0"

definition scheme where
"scheme Q R S \<equiv> \<exists>(f::(nat\<Rightarrow>nat)\<Rightarrow>nat\<Rightarrow>nat) (g::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(n::nat) (i::nat\<Rightarrow>nat).
  ((f i 0 = i (Suc 0)) \<and>
   (f i (Suc n) = Q i (f i) n) \<and>
   (g 0 = R Suc) \<and>
   (g (Suc n) = S n f (g n)))"

thm scheme_def

text {* We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise multiplication in terms of 
  addition of natural numbers.
*}

ML {*
  fun fitness ctxt consts =
    let fun ackermann 0 n = n + 1
          | ackermann m 0 = ackermann (m-1) 1
          | ackermann m n = ackermann (m-1) (ackermann m (n-1))
        val in_out = [(0,0), (1,0), (0,1),
                      (1,1), (1,2), (2,1),
                      (2,2), (2,0), (0,2)]
                       |> map (fn (x,y) => ((x,y), ackermann x y))
        val f = consts (* |> tap (map (tracing o fst)) *)
                       |> hd o tl
                       |> Const
        val conjectures =
          in_out |> map (fn ((x,y),r) => ((Utils.numeral_of_nat ctxt x,
                                           Utils.numeral_of_nat ctxt y),
                                           Utils.numeral_of_nat ctxt r))
                 |> map (fn ((x,y),r) => ((f $ x $ y), r) |> HOLogic.mk_eq
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
  val generations = 200
  val bests = 10
  val mut_prob = 0.05
  val scheme = @{thm "scheme_def"}
*}

text {* We finally call the GP algorithm. *}

(*local_setup {*
 fn lthy => 
  case DB_EXHAUST.exhaust false lthy scheme term_size [] test of
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