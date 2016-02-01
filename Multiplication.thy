theory Multiplication
imports "IsaLibs/IsaLibs"
begin

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space.*}

definition scheme where
"scheme P Q R S \<equiv> \<exists>(f::nat\<Rightarrow>nat\<Rightarrow>nat) (g::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(x::nat) (y::nat).
  ((f 0 y = P y Suc (0::nat)) \<and>
   (f (Suc x) y = Q x y Suc (0::nat) (f x y)) \<and>
   (g 0 y = R y Suc (0::nat)) \<and>
   (g (Suc x) y = S x y Suc (0::nat) (f y) (g x y)))"

thm scheme_def

text {* We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise multiplication in terms of 
  addition of natural numbers.
*}

ML {*
  fun fitness ctxt consts =
    let fun goal x y = x * y
        val f = consts (* |> tap (map (tracing o fst)) *)
                       |> hd o tl
                       |> Const
        val xs = 0 upto 9
        val xs' = 1 upto (Utils.binomial_coefficient 10 2 - 1)
                    |> map (Utils.choose xs 2)
                    |> map (fn l => case l of
                                      [x,y] => (x,y)
                                    | _ => raise ERROR "")
        val ys = map (fn (x,y) => goal x y) xs'
        val rs = map (fn (x,y) => (f $ Utils.numeral_of_nat ctxt x $ Utils.numeral_of_nat ctxt y)
                                |> (fn t => @{term "num_of_nat"} $ t)
                                |> Value.value ctxt
                                |> (fn t => @{term "numeral :: num\<Rightarrow>nat"} $ t)
                                |> Utils.int_of_numeral) xs'
        val ds = map2 (fn x => fn y => (x - y) * (x - y)) ys rs
    in (0, ds) |> Library.foldl (op +)
               |> Rat.rat_of_int end
  fun finish ({fit, ...} : GP.individual) = Rat.eq (Rat.zero, fit)
  fun test ctxt consts =
      consts |> fitness ctxt
             |> pair Rat.zero
             |> Rat.eq
  val term_size = 13
  val population_size = 100
  val generations = 100
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

local_setup {*
 fn lthy => 
  case GP.evolve false scheme lthy fitness finish term_size population_size generations bests mut_prob of
    SOME ind => (#ctxt ind)
  | NONE => lthy
*}

text {* Genome is composed by: 
@{term "\<lambda>x xa xb xc xd. xd"}
@{term "\<lambda>x xa xb. xb"}
@{term "\<lambda>x xa xb xc. xb"}
@{term "\<lambda>x xa xb. x"} *}

thm f.simps
thm g.simps

text {* Invented functions are well-defined *}
lemma "scheme (\<lambda>x xa xb. x) (\<lambda>x xa xb xc. xb) (\<lambda>x xa xb. xb) (\<lambda>x xa xb xc xd. xd)"
apply (unfold scheme_def)
apply (rule_tac x="f" in exI)
apply (rule_tac x="g" in exI)
apply simp
done

end