(*  Title:      util/equivalence_terms.ML
    ID:         $Id: const_names.ML,v 1.00 2017/28/04 17:28:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2017

Equivalence relation over terms
*)

signature EQ_TERMS =
sig

end

structure DB_EQ_Terms
(* : EQ_TERMS *)
= struct

fun preprocess_conjecture ctxt size n conjecture =
  let val typsub = 
             [] |> Term.add_tfrees conjecture
                |> map (fn f => (TFree f, @{typ "int"}))
                |> subst_atomic_types
      val conjecture = typsub conjecture
(*      val frees = Term.add_frees conjecture []
      val conjecture = [(conjecture, [])] |> Quickcheck_Common.instantiate_goals ctxt frees
                                          |> fst o snd o snd o split_last o hd*)
      val frees = Term.add_frees conjecture []
      val typs = frees |> map snd
                       |> Type_Tab.make_set
                       |> Type_Tab.dest
                       |> map fst
      val thy = Proof_Context.theory_of ctxt
      val ts = typs |> map (fn ty => 
                  let val ts = (1 upto n)
                                |> map_filter (fn _ => Random_Terms.random_term ctxt size ty)
                                |> Utils.make_term_set thy
                  in (ty, ts) end)
      val table = Type_Tab.make ts
      val tss = map (fn (_,ty) =>
          case Type_Tab.lookup table ty of
            SOME ts => ts
            | NONE  => (1 upto n)
                         |> map_filter (fn _ => Random_Terms.random_term ctxt size ty)
                         |> tap (fn _ => tracing "Re processing random terms!")
                         |> Utils.make_term_set thy
                         |> (fn ts => ts)) frees
      fun take n f =
        if n = 0 then []
        else case f () of
          SOME r => (frees ~~ r) :: take (n-1) f
          | NONE => []
      val termsubts  = tss |> Utils.lazy_one_of_each
                           |> take (size * n)
                           |> map (map (fn (v, t) => (Free v, t)))
                           |> map Term.subst_free
  in (table, typsub, termsubts, conjecture) end

(* Finds a potential valid equation using tests
   terms: must be sorted from more general to less general
          to find general equations first. They also must
          be in normal form w.r.t. simps *)
fun equation ctxt timeOut tab typsub tsubsts simps terms =
  let fun find tab [] = NONE
        | find tab (t::ts) =
            let val t' = typsub t
                val key = map (fn subst => Utils.normalise_term ctxt simps (subst t')) tsubsts
            in case Term_List_Tab.lookup tab key of
                SOME s => let val equation = (s, t) |> HOLogic.mk_eq
                                                    |> HOLogic.mk_Trueprop
                          in if Counter_Example.counter_example ctxt timeOut equation
                             then (tracing "More tests are required!";
                                   raise ERROR "More tests are required!")
                             else SOME equation end
              | NONE => find (Term_List_Tab.update (key, t) tab) ts
            end
  in find tab terms end

end

structure EQ_Terms : EQ_TERMS = DB_EQ_Terms

