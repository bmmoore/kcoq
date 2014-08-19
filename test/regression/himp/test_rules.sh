#!/bin/bash
echo "Testing HIMP Rules"
kcoq --simple-names --no-quotes rules --extra-rules fun_aux_steps.txt himp.labeled_rules fun_steps_test.v \
 && diff fun_steps.v fun_steps_test.v
rm -f fun_steps_test.v
