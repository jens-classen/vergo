#!/bin/bash

TESTFILES=" \
    coffee_robot/coffee_bat_fct.pl \
    dish_robot/dish_robot_bat.pl \
    dish_robot/dish_robot_bat_dl.pl \
    office_robot/office_robot_bat.pl \
    teacher/teacher.pl \
    test/blocks/blocks.pl \
    test/conditionals/conditionals.pl \
    test/deontic/deontic_test.pl \
    test/pddl/pddl_test.pl \
"

echo ""
for file in $TESTFILES;
do
    echo "Testing ${file}..."
    DIR=`dirname ${file}`
    BAS=`basename ${file}`
    WD=`pwd`
    cd $DIR
    swipl -g "run_tests." -t "halt(1)" ${BAS} >/dev/null
    cd $WD
    echo ""
done
