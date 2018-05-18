#!/bin/bash

FILE=results_cgraph.csv

swipl -g "experiment(1,'$FILE',360,60)." -t "halt(1)" eval_fct_cgraphs.pl
swipl -g "experiment(2,'$FILE',360,60)." -t "halt(1)" eval_fct_cgraphs.pl
swipl -g "experiment(3,'$FILE',360,60)." -t "halt(1)" eval_fct_cgraphs.pl
