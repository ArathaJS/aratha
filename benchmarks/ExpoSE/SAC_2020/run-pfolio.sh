DIR=`dirname $(readlink -f "$0")`
IN_DIR=$DIR/test/ExpoSE
OUT_DIR=$HOME/jalangi2-concolic/experiments
ARATHA_DIR=$HOME/aratha
NOGOODS=$ARATHA_DIR/nogoods.json
TMP=tmp.log
TIMEOUT=300
INPUT=$OUT_DIR/input.log
OUTPUT=$OUT_DIR/output.log
ERRORS=$OUT_DIR/errors.log
RESULTS=$OUT_DIR/results-pfolio.log
PFOLIO=(G-Strings z3 cvc4)
NUM_SOLVERS=${#PFOLIO[@]}
USE_NOGOODS=1
TOUT=100

cd $ARATHA_DIR
echo "Running portfolio [${PFOLIO[@]}]"
export SOLVER=$PFOLIO
tot_stmt=0
for j in `find $IN_DIR -depth -name "*.js" | grep -v _jalangi_ | sort`
do
  echo "Testing $j"
  header=`echo ${PFOLIO[@]} | sed 's/ /,/g'`"|$j"
  echo >> $OUTPUT 
  echo $header >> $OUTPUT
  echo >> $ERRORS
  echo $header >> $ERRORS
  echo '' > $INPUT
  echo '' > $NOGOODS
  tot_time=0.0
  i=0
  for solver in ${PFOLIO[@]}
  do
    i=$((i+1))
    echo "Running $solver"
    export SOLVER=$solver
    time -p (timeout $TOUT npm run analyze -- $j >>$OUTPUT 2>>$ERRORS) 2>$TMP
    ret=$?
    if
      [ $ret -ne 0 ]
    then
      if
        [ $ret -eq 124 ]
      then
        echo "Timeout expired for $solver!"
      else
        echo "Error! $solver finished with code $ret"
      fi
    fi
    time=`cat $TMP | awk -v s=0.0 'NR == 1 {s += $2} END {print s}'`    
    tot_time=`echo | awk -v x=$tot_time -v y=$time '{x += y} END {print x}'`
    echo "$solver finished in $time seconds (tot. time: $tot_time seconds)"
    if 
      [ -s inputlog.json ]
    then
      ilog=`basename $j | awk -F"." '{print $1}'`.inputlog.json
      cat inputlog.json | sed 's/^,$/{},/g' | sed '/^$/d' > $ilog
      cat $INPUT $ilog | sed 's/,$//g' | sed '/^$/d' | grep -v ^"\[" | grep -v ^"\]" | sort | uniq > $TMP
      mv $TMP $INPUT
      echo -e "[\n" > $TMP
      N=`wc -l $INPUT | awk '{print $1}'`
      cat $INPUT | awk -v n=$N '{if (NR < n) {print $0,","} else {print $0}}' >> $TMP
      echo -e "\n]" >> $TMP
      cat $TMP | sed '/^$/d' | sed "s/ ,$/,/g" > $ilog
      echo "===== INPUT ===== "
      cat $ilog
      if
        [ $USE_NOGOODS -eq 1 ]
      then
        cat $ilog >> $NOGOODS
      fi
      nimp=`cat $ilog | grep ^"{" | sed 's/,$//g' | sort | uniq | wc -l`
      cp $j $ARATHA_DIR
      time -p (nyc node bin/replay-inputs.js `basename $j` 2>/dev/null | strings | \
      grep '  '`basename "$j"` | awk -F"|" '{print $2,",",$3,",",$4,",",$5}' | sed 's/ //g' > $TMP) \
        2>$TMP.time
      time=`cat $TMP.time | awk -v s=0.0 'NR == 1 {s += $2} END {print s}'`
      if 
        [ $i -ne $NUM_SOLVERS ]
      then
        tot_time=`echo | awk -v x=$tot_time -v y=$time '{x += y} END {print x}'`  
      fi
      rm $TMP.time
      if
        [ -s $TMP ]
      then
        stmt=`cat $TMP   | awk -F"," '{print $1}'`
        branch=`cat $TMP | awk -F"," '{print $2}'`
        func=`cat $TMP   | awk -F"," '{print $3}'`
        line=`cat $TMP   | awk -F"," '{print $4}'`
        if
          (( $(echo "$stmt == 100" |bc -l) ));
        then
          echo "Maximum coverage reached!"
          break  
        fi        
      else
        stmt=0
        branch=0
        func=0
        line=0
      fi
    fi
  done
  rm $ilog $TMP $ARATHA_DIR/`basename $j`
  echo "Stmt coverage: $stmt%"
  echo "Branch coverage: $branch%"
  echo "Functions coverage: $func%"
  echo "Lines coverage: $line%"
  header="$header|$ret|$stmt|$branch|$func|$line|$nimp|$tot_time"
  echo $header
  if
    [ $stmt != "0" ]
  then
    tot_stmt=$(awk "BEGIN {print $tot_stmt + $stmt; exit}")
  fi
  exit
  echo $header >> $RESULTS
  cp $RESULTS ~/Dropbox
done
echo -e "Cumulative coverage for [${PFOLIO[@]}]: $tot_stmt\n=========\n"
