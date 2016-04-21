(*  Title:      util/gnuplot.ML
    ID:         $Id: const_names.ML,v 1.00 2015/15/01 13:01:00 omar Exp $
    Author:     Omar Montano Rivas, Universidad Polit'ecnica de San Luis Potos'i
    Copyright   Universidad Polit'ecnica de San Luis Potos'i 2015

Production of GNU Plot Files.
*)

signature GNU_PLOT =
sig
  val gp_statistics_to_error_plot           : string -> int -> GP.gp_result list -> unit
  val gp_statistics_to_cumulative_prob_plot : string -> int -> GP.gp_result list -> 
                                              GP.gp_result list -> unit
  val gp_statistics_to_equals               : int -> GP.gp_result list -> int * int
end

structure DB_GNU_Plot
(* : GNU_PLOT *)
= struct

open GP

fun gp_statistics_to_error_plot file generations (sts : gp_result list) =
  let fun div_by_10 x = x / 10.0
      fun extract (Solved (ind, [])) = (div_by_10 o Utils.rat_to_float o the o #fit) ind
        | extract (Solved (_, (st :: _))) = (div_by_10 o Utils.rat_to_float o the o #fit o #best_individual) st
        | extract (Unsolved []) = raise ERROR "Can not get statistics"
        | extract (Unsolved (st :: _)) = (div_by_10 o Utils.rat_to_float o the o #fit o #best_individual) st
      fun reduce (Solved (ind, [])) = Solved (ind, [])
        | reduce (Solved (ind, _ :: sts)) = Solved (ind, sts)
        | reduce (Unsolved []) = raise ERROR "Can not reduce"
        | reduce (Unsolved (_ :: sts)) = Unsolved sts
      val datafile = file ^ "Error.data"
      val plotfile = file ^ "Error.plot"
      val experiments = length sts
      val _ =
        let val header =["set terminal epslatex color\n",
                         "set output \"" ^ file ^ "Error.tex\"\n",
                         "set format xy \"$%g$\"\n",
                         "set title \"Error\"\n",
                         "set xrange [0.0:100.0]\n",
                         "set yrange [0.0:1.0]\n",
                         "set xlabel \"Generation\"\n",
                         "set ylabel \"Minimum error\"\n"]
            val body = 3 upto experiments + 2
                        |> map (fn i => "     \"" ^ datafile ^ "\" using 1:" ^ string_of_int i ^
                                        " title \"\" with lines lt rgb \"#7F7F7F\", \\\n")
                        |> (fn strs => ("plot \"" ^ datafile ^ "\" using 1:2" ^
                                        " title \"\" with lines lw 3 lt rgb \"#000000\", \\\n") :: strs)
        in (header @ body)
            |> File.write_list (Path.explode plotfile) end
  in 0 upto generations - 1
       |> pair ([], sts)
       |> Library.foldl (fn ((R, sts), i) =>
            let val row = map extract sts
                val avg = (Library.foldl (op +) (0.0, row)) / ((real o length) row)
            in ((real i :: avg :: row) :: R, map reduce sts) end)
       |> rev o fst
       |> map ((fn str => str ^ "\n") o space_implode " " o map string_of_real)
       |> File.write_list (Path.explode datafile)
  end

fun gp_statistics_to_cumulative_prob generations (sts : gp_result list) =
  let fun extract (Solved (ind, [])) = (the o #fit) ind
        | extract (Solved (_, st :: _)) = (the o #fit o #best_individual) st
        | extract (Unsolved []) = raise ERROR "Can not get statistics"
        | extract (Unsolved (st :: _)) = (the o #fit o #best_individual) st
      fun reduce (Solved (ind, [])) = Solved (ind, [])
        | reduce (Solved (ind, _ :: sts)) = Solved (ind, sts)
        | reduce (Unsolved []) = raise ERROR "Can not reduce"
        | reduce (Unsolved (_ :: sts)) = Unsolved sts
      val trials = real (length sts)
  in 0 upto generations - 1
       |> pair ([], sts)
       |> Library.foldl (fn ((R, sts), _) =>
            let val row = map extract sts
                val cum = (0, row)
                            |> Library.foldl (fn (cum, n) => if Rat.eq (Rat.zero, n)
                                                             then cum + 1
                                                             else cum)
                            |> real
                            |> (fn x => x / trials)
            in (cum :: R, map reduce sts) end)
       |> rev o fst
  end

fun gp_statistics_to_cumulative_prob_plot file generations (sts1 : gp_result list) (sts2 : gp_result list) =
  let val datafile = file ^ "Cumulative.data"
      val plotfile = file ^ "Cumulative.plot"
      val cums1 = gp_statistics_to_cumulative_prob generations sts1
      val cums2 = gp_statistics_to_cumulative_prob generations sts2
      val _ =
        let val header =["set terminal epslatex color\n",
                         "set output \"" ^ file ^ "Cumulative.tex\"\n",
                         "set format xy \"$%g$\"\n",
                         "set title \"Cumulative Probability of Success (CPS)\"\n",
                         "set xrange [0.0:100.0]\n",
                         "set yrange [0.0:1.0]\n",
                         "set xlabel \"Generation\"\n",
                         "set ylabel \"CPS\"\n"]
            val body = ["plot \"" ^ datafile ^ "\" using 1:2" ^
                        " title \"Constructive\" with lines lw 3 lt rgb \"#0000FF\", \\\n",
                        "     \"" ^ datafile ^ "\" using 1:3" ^
                        " title \"Destructive\" with lines lw 3 lt rgb \"#FF0000\", \\\n"]
        in (header @ body)
            |> File.write_list (Path.explode plotfile) end
  in 0 upto generations - 1
       |> pair ([], cums1, cums2)
       |> Library.foldl (fn ((R, sts1, sts2), i) =>
            let val row = [hd sts1, hd sts2]
            in ((real i :: row) :: R, tl sts1, tl sts2) end)
       |> rev o (fn (x, _, _) => x)
       |> map ((fn str => str ^ "\n") o space_implode " " o map string_of_real)
       |> File.write_list (Path.explode datafile)
  end

fun gp_result_to_equals (Solved (_, sts)) =
  Library.foldl (fn (s, st) => #equals st + s) (0, sts)
  | gp_result_to_equals (Unsolved sts) =
  Library.foldl (fn (s, st) => #equals st + s) (0, sts)

fun gp_statistics_to_equals population_size (sts : gp_result list) =
  let fun processed (Solved (_, sts)) = population_size * length sts
        | processed (Unsolved sts) = population_size * length sts
      val eqs = sts |> map gp_result_to_equals
         |> pair 0
         |> Library.foldl (op +)
      val all = sts |> map processed
         |> pair 0
         |> Library.foldl (op +)
  in (eqs, all)
  end

end

structure GNU_Plot : GNU_PLOT = DB_GNU_Plot

