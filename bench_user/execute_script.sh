#!/bin/bash

FNAMES=(`find . -name '*.smt2'`)
ADTIND=/home/lucas/Desktop/aeval/build/tools/adt/ind
COUNTER=0

for i in ${FNAMES[*]}; do
  COUNTER=$((COUNTER + 1))
  result="./results/test_$COUNTER.txt"
  dir="./results/dir_$COUNTER.txt"
  time_file="./results/time_$COUNTER.txt"
  echo "$i" >> $dir
  echo "now testing $i"
  /usr/bin/time -o $time_file -f "%E, %U, %S\n" timeout 120 /home/lucas/Desktop/aeval/build/tools/adt/ind $i 2>&1 >> $result 2> $result 
done
