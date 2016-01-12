structure Term_Tab = Table(type key = term val ord = Term_Ord.term_ord)

structure Type_Tab = Table(type key = typ val ord = Term_Ord.typ_ord)

structure IntType_Tab = Table(type key = int * typ val ord = prod_ord int_ord Term_Ord.typ_ord)

structure Thm_List_Tab = Table(type key = thm list val ord = list_ord (Term_Ord.term_ord o apply2 Thm.full_prop_of))

structure Thm_Thm_List_Tab = Table(
  type key = thm * thm list 
  val ord = prod_ord (Term_Ord.term_ord o apply2 Thm.full_prop_of) (list_ord (Term_Ord.term_ord o apply2 Thm.full_prop_of)))

structure Completion_Rules = Named_Thms
  (val name = @{binding "compl"}
   val description = "Theorems for IsaLib")

