set terminal epslatex color
set output "SumCumulative.tex"
set format xy "$%g$"
set title "Cumulative Probability of Success (CPS)"
set xrange [0.0:100.0]set yrange [0.0:1.0]set xlabel "Generation"
set ylabel "CPS"
plot "SumCumulative.data" using 1:2 title "Constructive" with lines lt rgb "#0000FF", \
     "SumCumulative.data" using 1:3 title "Destructive" with lines lt rgb "#FF0000", \
