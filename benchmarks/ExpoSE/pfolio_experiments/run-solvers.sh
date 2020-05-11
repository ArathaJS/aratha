#!/bin/bash

DIR=`dirname $(readlink -f "$0")`
IN_DIR=$DIR/..
OUT_DIR=$DIR
ARATHA_DIR=$HOME/aratha
TMP=tmp.log
TIMEOUT=300
OUTPUT=$OUT_DIR/output-solvers.log
ERRORS=$OUT_DIR/errors-solvers.log
RESULTS=$OUT_DIR/results-solvers.log

cd $ARATHA_DIR
for solver in G-Strings cvc4 z3
do
  echo "Running $solver"
  export SOLVER=$solver
  tot_stmt=0
#  for j in `cat recover_list`
  for j in `find $IN_DIR -depth -name "*.js" | grep -v _jalangi_ | sort`
  do
    echo "Testing $j"
    header="$solver|$j"
    echo >> $OUTPUT 
    echo $header >> $OUTPUT
    echo >> $ERRORS
    echo $header >> $ERRORS
    time -p (timeout $TIMEOUT npm run analyze -- $j >>$OUTPUT 2>>$ERRORS) 2>$TMP
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
      cat inputlog.json | sed 's/^,$/{},/g' | sed '/^$/d' > $ilog
      echo "===== INPUT ===== "
      if
        [[ -z `grep "]" $ilog` ]]
      then
        echo -e "\n]" >> $ilog
      fi
      cat $ilog
      nimp=`cat $ilog | grep ^"{" | sed 's/,$//g' | sort | uniq | wc -l`
      cp $j $ARATHA_DIR
      nyc node bin/replay-inputs.js `basename $j` 2>/dev/null | strings | \
      grep '  '`basename "$j"` | awk -F"|" '{print $2,",",$3,",",$4,",",$5}' | sed 's/ //g' > $TMP
      if
        [ -s $TMP ]
      then
        stmt=`cat $TMP   | awk -F"," '{print $1}'`
        branch=`cat $TMP | awk -F"," '{print $2}'`
        func=`cat $TMP   | awk -F"," '{print $3}'`
        line=`cat $TMP   | awk -F"," '{print $4}'`
      else
        stmt=0
        branch=0
        func=0
        line=0
      fi
      rm $ilog $TMP $ARATHA_DIR/`basename $j`
    else      
      stmt=0
      branch=0
      func=0
      line=0
    fi  
    echo "Stmt coverage: $stmt%"
    echo "Branch coverage: $branch%"
    echo "Functions coverage: $func%"
    echo "Lines coverage: $line%"
    header="$header|$ret|$stmt|$branch|$func|$line|$nimp|$time"
    if
      [ $stmt != "0" ]
    then
      tot_stmt=$(awk "BEGIN {print $tot_stmt + $stmt; exit}")
    fi
    echo $header >> $RESULTS
    cp $RESULTS ~/Dropbox
  done
  echo -e "Cumulative coverage for $solver: $tot_stmt\n=========\n"
  sleep 10
done
