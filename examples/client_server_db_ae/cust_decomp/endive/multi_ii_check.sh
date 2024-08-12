#!/bin/sh

for i in $(seq 1 10)
do
    echo "trial $i"
    java -jar ~/bin/tla2tools.jar -deadlock -workers 25 D0_ii.tla | tee ii_out.log
    violations=$(grep 'Error: Invariant IndInv is violated.' ii_out.log | wc -l)
    if [ ${violations} -ne 0 ]
    then
        echo
        echo "violations were detected, the candidate is not an II!!"
        break
    fi
    echo
done
