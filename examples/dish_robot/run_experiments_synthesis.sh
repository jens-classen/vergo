#!/bin/bash

FILE=results_synthesis.csv

swipl -g "experiment( 1, 1,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 1, 2,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 1, 3,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 2, 1,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 2, 2,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 2, 3,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 3, 1,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 3, 2,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 3, 3,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 5, 5,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment(10,10,main,prop1,'$FILE',1200)." -t "halt(1)" eval_synthesis.pl
