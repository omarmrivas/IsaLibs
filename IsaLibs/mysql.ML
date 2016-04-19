(*  Title:      util/gnuplot.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Production of GNU Plot Files.
*)

signature MYSQL =
sig

val new_experiment :  string -> int -> int -> int -> GP.gp_result -> unit

end

structure DB_MYSQL
(* : MYSQL *)
= struct

open GP

fun evaluate r name expression =
  let val flags = ML_Compiler.flags
      val tokens = ML_Lex.read (name ^ " = SOME (" ^ expression ^ ")")
      val pos = Position.none
      val _ = ML_Context.eval flags pos tokens
  in the (!r) end

fun escape_string str =
  let fun escape c =
        case c of
            #"\"" => [#"\\", #"\""]
          | #"'" => [#"#"]
          | c => single c
  in
    str |> String.explode
        |> maps escape
        |> String.implode
  end

fun descape_string str =
  let fun escape c =
        case c of
            #"#" => [#"'"]
          | c => single c
  in
    str |> String.explode
        |> maps escape
        |> String.implode
  end

fun get_max_id table =
  let val max_id = "SELECT MAX(id) FROM " ^ table
  in ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ max_id ^ "' isalibs")
      |> Isabelle_System.bash_output
      |> fst
      |> space_explode "\n"
      |> (hd o tl)
      |> Utils.int_of_string
  end

fun search_individual ctxt (individual : individual) : (int * individual) option =
  let val norm_str = escape_string (ML_Syntax.print_term (#norm individual))
      val search_individual = "SELECT * FROM `individuals` WHERE `norm`=\""^ norm_str ^"\" limit 1"
      val result = ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ search_individual ^ "' isalibs")
                    |> Isabelle_System.bash_output
                    |> fst
  in if result = ""
     then NONE
     else let val genome_ref = Unsynchronized.ref (NONE : term list option)
              val subst_ref = Unsynchronized.ref (NONE : subst option)
              val norm_ref = Unsynchronized.ref (NONE : term option)
              val fit_ref = Unsynchronized.ref (NONE : (int * int) option)
          in
          result |> tap tracing
                 |> space_explode "\n"
                 |> (hd o tl)
                 |> space_explode "\t"
                 |> map descape_string
                 |> (fn l => case l of
                                [id, genome, subst, norm, fit] => 
                                 (Utils.int_of_string id, {ctxt = ctxt,
                                   genome = evaluate genome_ref "genome_ref" genome,
                                   subst = evaluate subst_ref "subst_ref" subst,
                                   norm = evaluate norm_ref "norm_ref" norm,
                                   fit = Rat.rat_of_quotient (evaluate fit_ref "fit_ref" fit)})
                              | _ => raise ERROR "Error")
                 |> SOME
          end
  end

fun insert_individual (individual : individual) =
  let val genome_str = escape_string (ML_Syntax.print_list ML_Syntax.print_term (#genome individual))
      val typs = ML_Syntax.print_list (ML_Syntax.print_pair ML_Syntax.print_typ ML_Syntax.print_typ)
      val terms = ML_Syntax.print_list (ML_Syntax.print_pair ML_Syntax.print_term ML_Syntax.print_term)
      val subst_str = escape_string (ML_Syntax.print_pair typs terms (#subst individual))
      val norm_str = escape_string (ML_Syntax.print_term (#norm individual))
      val fit_str = escape_string ((string_of_real o Utils.rat_to_float) (#fit individual))
      val insert_individual = "INSERT INTO `individuals`(`genome`, `subst`, `norm`, `fit`) VALUES (\"" ^genome_str^ "\",\"" ^ subst_str ^"\",\"" ^ norm_str ^ "\","^fit_str^")"
      val _ = Isabelle_System.bash_output ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ insert_individual ^ "' isalibs")
  in (#norm individual, get_max_id "individuals")  end

fun insert_statistics m experiment (statistic : gp_statistic) =
  let val best = (the o (Term_Tab.lookup m) o #norm) (#best_individual statistic)
      val best_str = string_of_int best
      val size_str = string_of_real (#average_size statistic)
      val error_str = string_of_real (#average_error statistic)
      val equals_str = string_of_int (#equals statistic)
      val experiment_str = string_of_int experiment
      val insert_statistics = "INSERT INTO `statistics`(`best`, `average_size`, `average_error`, `equals`, `experiment`) VALUES (" ^best_str^ "," ^ size_str ^"," ^ error_str ^ ","^equals_str^","^experiment_str ^ ")"
      val _ = Isabelle_System.bash_output ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ insert_statistics ^ "' isalibs")
  in () end

fun insert_experiment solution thy_name generations termsize population =
  let val solution_str = string_of_int solution
      val generations_str = string_of_int generations
      val termsize_str = string_of_int termsize
      val population_str = string_of_int population
      val insert_experiment = "INSERT INTO `experiments`(`solution`, `theory`, `generations`, `termsize`, `population`) VALUES (" ^solution_str^ ",\"" ^ thy_name ^"\"," ^ generations_str ^ ","^termsize_str^","^population_str ^ ")"
      val _ = Isabelle_System.bash_output ("mysql -u isalibs --password='isalibs' -h 'localhost' -e '" ^ insert_experiment ^ "' isalibs")
  in get_max_id "experiments" end

fun new_experiment thy_name generations termsize population (Solved (ind, statistics)) =
  let val individuals = ind :: map #best_individual statistics
                          |> distinct (fn (ind1, ind2) => Term.aconv (#norm ind1, #norm ind2))
                          |> map insert_individual
                          |> Term_Tab.make
      val experiment_id = insert_experiment ((the o (Term_Tab.lookup individuals) o #norm) ind) thy_name generations termsize population
      val _ = map (insert_statistics individuals experiment_id) statistics
  in () end
  | new_experiment thy_name generations termsize population (Unsolved (statistics)) =
  let val individuals = map #best_individual statistics
                          |> distinct (fn (ind1, ind2) => Term.aconv (#norm ind1, #norm ind2))
                          |> map insert_individual
                          |> Term_Tab.make
      val experiment_id = insert_experiment ~1 thy_name generations termsize population
      val _ = map (insert_statistics individuals experiment_id) statistics
  in () end
end

structure MySQL : MYSQL = DB_MYSQL

