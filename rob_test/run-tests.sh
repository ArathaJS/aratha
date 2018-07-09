#!/bin/sh

DIR=`dirname $(readlink -f "$0")`
JAL=$DIR/../../src/js/commands/jalangi.js

for j in `ls $DIR/test*.js`
do
  echo "Testing $j..."
  SOLVER=G-Strings node $JAL --analysis ./ $j 1>/dev/null
  diff $DIR/`basename $j | awk -F"." '{print $1}'`.json $PWD/inputlog.json
  ret=$?
  rm $DIR/*_jalangi_*
  if
    [ $ret -eq 0 ]
  then
    echo "All good!"
  else
    echo "Error!"
    exit 1
  fi
done
