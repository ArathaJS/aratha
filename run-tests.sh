#!/bin/bash

DIR=`dirname $(readlink -f "$0")`
TDIR=$DIR/test/examples
JAL=$DIR/../src/js/commands/jalangi.js
N_TESTS=26
COV=(NaN 37.5 75 75 100 100 100 88.89 83.33 100 100 80 100 100 66.67 100 100 \
     66.67 100 100 100 100 100 100 100 100 100)
ERR=err.log
     
for (( i=1; i<=$N_TESTS; i++ ))
do
  j=$TDIR/example"$i".js
  echo "Testing $j"
  SOLVER=G-Strings INCREMENTAL=0 node $JAL --analysis ./ $j >/dev/null 2>$ERR
  cat $ERR
  ilog=`basename $j | awk -F"." '{print $1}'`.inputlog.json
  mv inputlog.json $ilog
  echo "===== INPUT ===== "
  cat $ilog
  nyc node $DIR/../experiments/bin/replay-inputs.js $j 2>/dev/null | strings | \
    grep '  '`basename "$j"` | awk -F"|" '{print $5}' | sed 's/ //g' > x
  cov=`cat x`
  rm x $ilog
  echo "Coverage: $cov%"
  echo "Expected: ${COV[$i]}%"
  if
    [[ "$cov" != "${COV[$i]}" ]]
  then
    echo "Error!"
    exit 1
  else
    echo -e "All good!\n=========\n"
  fi
done
rm $ERR
