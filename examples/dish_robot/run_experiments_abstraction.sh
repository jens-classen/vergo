#!/bin/bash

FILE=results_abstraction.csv

swipl -g "experiment( 1, 1, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 1, 2, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 2, 1, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 2, 2, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 3, 1, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 1, 3, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 2, 3, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 3, 2, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 3, 3, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 5, 5, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment(10,10, true,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 1, 1,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 1, 2,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 2, 1,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 2, 2,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 3, 1,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 1, 3,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 2, 3,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 3, 2,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 3, 3,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment( 5, 5,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
swipl -g "experiment(10,10,false,'$FILE',300,300)." -t "halt(1)" eval_abstraction.pl
