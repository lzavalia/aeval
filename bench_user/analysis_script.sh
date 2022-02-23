#!/bin/bash

COUNTER=1
FLAG=0

while [ $FLAG -lt 1 ]
do
   FILES=(`find ./results -name "*_$COUNTER.txt"`)
   IFS=$'\n' FILES=(`sort <<<"${FILES[*]}"`); unset IFS
   if [ -z "$FILES" ]
   then
      echo "NO MORE FILES"
      FLAG=1
   else
      name=(`cat ${FILES[0]}`)
      name=${name:2}
      name_len=$((${#name} - 5))
      name=${name:0:$name_len}
      name=$name", "
      line_count=$(wc -l < ${FILES[2]})
      if [ $((line_count)) -gt 2 ]
      then
         values=(`tail -n 2 ${FILES[2]}`)
      else
         values=(`cat ${FILES[2]}`)
      fi
      v=""
      for i in ${values[*]};
      do
         v=$v" "
	      v=$v$i
      done
      result=$name$v
      test_tail=(`tail -n 3 ${FILES[1]}`)
      if [[ $test_tail =~ "Proved" ]];
      then
         result=$result", Proved"
      else
         result=$result", Unknown"
      fi
      echo $result >> ./results/data.csv
   fi
   COUNTER=$((COUNTER + 1))
done
