(*  Title:      util/const_names.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Names for important Pure and HOL constants.
*)

signature CONST_NAMES =
sig
  (* Names for important HOL constants *)
  val meta_forall                      : string
  val meta_imp                         : string
  val meta_eq                          : string
  val protectC_name                    : string
  val hol_trueprop                     : string
  val hol_forall                       : string
  val hol_exists                       : string
  val hol_eq                           : string
  val hol_implies                      : string
  val hol_not                          : string
  val hol_conj                         : string
  val hol_disj                         : string

  val hol_less                         : string

  val Bit0                             : string
  val Bit1                             : string
  val One                              : string
  val One_class                        : string
  val Zero_class                       : string
  val Minus                            : string
  val Numeral                          : string

  val undefined_name                   : string

end

structure DB_Const_Names
(* : CONST_NAMES *)
= struct

val (Const (meta_forall, _) $ _) =   @{term "\<And>x. x"}
val Const (meta_imp, _) = @{term "Pure.imp"}
val Const (meta_eq, _) $ _ $ _ = @{prop "x \<equiv> y"}
val Const (protectC_name, _) = Logic.protectC
val Const (hol_trueprop, _) = @{term "HOL.Trueprop"}
val Const (hol_forall, _) = @{term "HOL.All"}
val Const (hol_exists, _) = @{term "HOL.Ex"}
val Const (hol_eq, _) = @{term "HOL.eq"}
val Const (hol_implies, _) = @{term "HOL.implies"}
val Const (hol_not, _) = @{term "HOL.Not"}
val Const (hol_conj, _) = @{term "HOL.conj"}
val Const (hol_disj, _) = @{term "HOL.disj"}

val Const (Bit0, _) = @{const "Num.num.Bit0"}
val Const (Bit1, _) = @{const "Num.num.Bit1"}
val Const (One, _) = @{const "Num.num.One"}
val Const (One_class, _) = @{term "1::int"}
val Const (Zero_class, _) = @{term "0::int"}
val Const (Minus, _) $ _ = @{term "-1::int"}
val Const (Numeral, _) $ _ = @{term "2::int"}

(* SAT *)
val Const (hol_less, _) = @{term "Orderings.ord_class.less"}

(* Partial Functions *)
val Const (undefined_name, _) = @{term "undefined"}

end

structure Const_Names : CONST_NAMES = DB_Const_Names

