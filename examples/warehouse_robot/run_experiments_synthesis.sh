#!/bin/bash

FILE=results_warehouse.csv

swipl -g "experiment( 2, 1,simple,prop2,'$FILE',1500)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 2, 2,simple,prop2,'$FILE',1500)." -t "halt(1)" eval_synthesis.pl
swipl -g "experiment( 2, 3,simple,prop2,'$FILE',1500)." -t "halt(1)" eval_synthesis.pl
