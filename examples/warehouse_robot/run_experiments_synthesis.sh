#!/bin/bash

FILE=results_warehouse.csv

swipl -g "experiment( 2, 1,main,prop2,'$FILE',14400)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 2, 2,main,prop2,'$FILE',14400)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 2, 3,main,prop2,'$FILE',14400)." -t "halt(1)" eval_synthesis.pl
