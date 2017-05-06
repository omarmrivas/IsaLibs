(*  Title:      util/equivalence_terms.ML
    ID:         $Id: const_names.ML,v 1.00 2017/28/04 17:28:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2017

Equivalence relation over terms
*)

signature EQ_TERMS =
sig

val  equation : Proof.context -> int -> int -> int -> term list Type_Tab.table ->
              (term -> term) -> thm list -> (term -> bool) -> term list -> term option
val counter_example: Proof.context -> int -> int -> term list Type_Tab.table ->
                     (term -> term) -> term -> bool

end

structure DB_EQ_Terms
(* : EQ_TERMS *)
= struct

fun substitutions ctxt size n tab term =
  let val thy = Proof_Context.theory_of ctxt
      val frees = [] |> Term.add_frees term
                     |> sort (prod_ord string_ord Term_Ord.typ_ord)
      val tss = map (fn (_,ty) =>
          case Type_Tab.lookup tab ty of
            SOME ts => ts
            | NONE  => (1 upto n)
                         |> map_filter (fn _ => Random_Terms.random_term ctxt size ty)
                         |> tap (fn _ => tracing "Re processing random terms!")
                         |> tap (fn _ => tracing ("Type: " ^ Syntax.string_of_typ ctxt ty))
                         |> Utils.make_term_set thy) frees
      fun take f =
        case f () of
          SOME r => (frees ~~ r) :: take f
          | NONE => []
      val termsubts  = tss |> Utils.lazy_one_of_each
                           |> take
                           |> map (map (fn (v, t) => (Free v, t)))
                           |> map Term.subst_free
  in (map Free frees, termsubts) end

fun preprocess_conjecture ctxt size n conjecture =
  let val typsub = 
             [] |> Term.add_tfrees conjecture
                |> map (fn f => (TFree f, @{typ "int"}))
                |> subst_atomic_types
      val conjecture = typsub conjecture
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
  in (table, typsub) end

fun counter_example ctxt size n table typsub (conjecture : term) =
  let val t' = typsub conjecture
      val (_, tsubsts) = substitutions ctxt size n table t'
      val conjs = map (fn subst => subst t') tsubsts
  in exists (fn conj => Utils.normalise_term ctxt [] conj = @{prop "False"}) conjs end

(* Finds a potential valid equation using tests
   terms: must be sorted from more general to less general
          to find general equations first. They also must
          be in normal form w.r.t. simps *)
fun equation ctxt timeOut size n table typsub simps subsumed terms =
  let val thy = Proof_Context.theory_of ctxt
      fun null_frees t =
          [] |> Term.add_frees t
             |> null
      val terms = Library.foldl (fn (net, t) =>
            t |> Utils.subterms_no_loose_no_funs
              |> map (Utils.normalise_term ctxt simps)
              |> filter (not o null_frees)
              |> pair net
              |> Library.foldl (fn (net, t) =>
                  Net.insert_term_safe (is_equal o Term_Ord.fast_term_ord)
                                       (t, t) net)) (Net.empty, terms)
              |> Net.content
              |> Utils.sort_by_general thy
      fun find _ [] = NONE
        | find tab (t::ts) =
            let val t' = typsub t
                val (frees, tsubsts) = substitutions ctxt size n table t'
                val results = map (fn subst => Utils.normalise_term ctxt simps (subst t')) tsubsts
                val key = frees @ results
                fun check insert s =
                          let val equation = (s, t) |> HOLogic.mk_eq
                                                    |> HOLogic.mk_Trueprop
                              val equation' = (HOLogic.mk_Trueprop o Utils.swap_eq o HOLogic.dest_Trueprop) equation
                              val better = not (subsumed equation orelse subsumed equation')
                          in if better
                             then (if counter_example ctxt size n table typsub equation (*Counter_Example.counter_example ctxt timeOut equation*)
                                   then (tracing "More tests are required!";
                                         tracing ("Bad equiation: " ^ Utils.str_of_terms ctxt [equation]);
                                        raise ERROR "More tests are required!")
                                   else SOME equation)
                              else find (insert tab) ts end
            in case Term_List_Tab.lookup tab key of
                SOME s => check I s
              | NONE => let val v = hd results
                        in if forall (fn v' => v = v') results
                           then check (Term_List_Tab.update (key, t)) v
                           else find (Term_List_Tab.update (key, t) tab) ts end
            end
  in find Term_List_Tab.empty terms end

end

structure EQ_Terms : EQ_TERMS = DB_EQ_Terms

