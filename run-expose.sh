#!/bin/bash

DIR=`dirname $(readlink -f "$0")`
IN_DIR=$DIR/test/ExpoSE
JAL=$DIR/../src/js/commands/jalangi.js
TMP=tmp.log
TIMEOUT=300
OUTPUT=output.log
ERRORS=errors.log
RESULTS=results.log

for solver in G-Strings cvc4 z3 z3str
do
  echo "Running $solver"
  export SOLVER=$solver
  tot_cov=0
#  for j in `cat recover_list | grep both`
  for j in `find $IN_DIR -depth -name "*.js" | grep -v _jalangi_ | sort`
  do
    echo "Testing $j"
    header="$solver|$j"
    echo >> $OUTPUT 
    echo $header >> $OUTPUT
    echo >> $ERRORS
    echo $header >> $ERRORS
    time -p (timeout $TIMEOUT node $JAL --analysis ./ $j >>$OUTPUT 2>>$ERRORS) 2>$TMP
    ret=$?
    if
      [ $ret -ne 0 ]
    then
      time=$TIMEOUT
      if
        [ $ret -eq 124 ]
      then
        echo "Timeout expired!"
      else
        echo "Error!"
      fi
    else
      time=`cat $TMP | awk -v s=0.0 'NR == 1 {s += $2} END {print s}'`
    fi
    if 
      [ -s inputlog.json ]
    then
      ilog=`basename $j | awk -F"." '{print $1}'`.inputlog.json
      cat inputlog.json | sed 's/^,$/{},/g' > $ilog
      echo "===== INPUT ===== "
      if
        [ -z `grep "]" $ilog` ]
      then
        echo -e "\n]" >> $ilog
      fi
      cat $ilog
      nyc node $DIR/../experiments/bin/replay-inputs.js $j 2>/dev/null | strings | \
      grep '  '`basename "$j"` | awk -F"|" '{print $2}' | sed 's/ //g' > $TMP
      cov=`cat $TMP`
      rm $ilog $TMP
    else
      cov=0
    fi  
    echo "Stmt coverage: $cov%"
    header="$header|$ret|$cov|$time"
    if
      [[ "$cov" != "100" ]]
    then
      echo -e "Not 100% for $j!\n=========\n"
  #    gedit $j
  #    exit 1
    else
      echo -e "All good!\n=========\n"
    fi
    if
      [ $cov != "0" ]
    then
      tot_cov=$(awk "BEGIN {print $tot_cov + $cov; exit}")
    fi
    echo $header >> $RESULTS
    cp $RESULTS ~/Dropbox
  done
  echo -e "Cumulative coverage for $solver: $tot_cov\n=========\n"
done
