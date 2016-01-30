theory Multiplication
imports "IsaLibs/IsaLibs"
begin

section {* Multiplication on Natural Numbers *}

text {* This theory file shows how to find a function that multiplies natural numbers in Isabelle/HOL *}

text {* We first define the functional space.*}

definition scheme where
"scheme P Q R S \<equiv> \<exists>(f::nat\<Rightarrow>nat\<Rightarrow>nat) (g::nat\<Rightarrow>nat\<Rightarrow>nat). \<forall>(x::nat) (y::nat).
  ((f 0 y = P y Suc (0::nat)) \<and>
   (f (Suc x) y = Q x y Suc (0::nat) (f x)) \<and>
   (g 0 y = R y Suc (0::nat)) \<and>
   (g (Suc x) y = S x y Suc (0::nat) f (g x)))"

ML {*
  val typ_p = @{typ "nat\<Rightarrow>(nat\<Rightarrow>nat)\<Rightarrow>nat\<Rightarrow>nat"}
  val size = 4
  val cnt = Random_Terms.count_terms typ_p size
  val trms = Random_Terms.enumerate_terms typ_p size
  val _ = map (tracing o Syntax.string_of_term @{context}) trms
*}

ML {*
  val typ_q = @{typ "nat => nat => (nat => nat) => nat => (nat => nat) => nat"}
  val size = 10
  val cnt = Random_Terms.count_terms typ_q size
  val trms = Random_Terms.enumerate_terms typ_q size
  val _ = map (tracing o Syntax.string_of_term @{context}) trms
*}

ML {*
  val typ_r = @{typ "nat => (nat => nat) => nat => nat"}
  val size = 4
  val cnt = Random_Terms.count_terms typ_r size
  val trms = Random_Terms.enumerate_terms typ_r size
  val _ = map (tracing o Syntax.string_of_term @{context}) trms
*}

ML {*
  val typ_s = @{typ "nat => nat => (nat => nat) => nat => (nat => nat => nat) => (nat => nat) => nat"}
  val size = 13
  val cnt = Random_Terms.count_terms typ_s size
  val trms = Random_Terms.enumerate_terms typ_s size
  val _ = map (tracing o Syntax.string_of_term @{context}) trms
*}

lemma "scheme (\<lambda>x xa xb. x) (\<lambda>x xa xb xc xd. xb (xd xa)) (\<lambda>x xa xb. xb) (\<lambda>x xa xb xc xd xe. xd (xe xa) xa)"
apply (unfold scheme_def)
oops

thm scheme_def

text {* We then define the fitness function as the quadratic error, the termination criterion,
  and other GP related parameters. The function we want to synthesise multiplication in terms of 
  addition of natural numbers.
*}

ML {*
  fun fitness ctxt consts =
    let fun goal x y = x * y
        val f = consts |> hd o tl
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
  val population_size = 400
  val generations = 200
  val bests = 1
  val mut_prob = 0.05
  val scheme = @{thm "scheme_def"}
*}

text {* We finally call the GP algorithm. *}

local_setup {*
 fn lthy => 
  case DB_EXHAUST.exhaust true lthy scheme term_size [] test of
    SOME (ctxt, t, trms) => ctxt
  | NONE => lthy
*}

(*local_setup {*
 fn lthy => 
  case GP.evolve true scheme lthy fitness finish term_size population_size generations bests mut_prob of
    SOME ind => (#ctxt ind)
  | NONE => lthy
*}*)

thm f.simps

end