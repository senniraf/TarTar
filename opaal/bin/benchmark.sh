#!/bin/bash

MODELS="explode_tp4.xml"
SEARCHORDERS="dfs bfs"
UPDATES="3"
#THREADS="1 2 4 8 16"
THREADS="8 16"
RUNS=2

OUTPUT="benchmarks.log"
OUTPUT_DIR="benchmarks/"

for m in $MODELS; do
    echo "**************  $m **************" 
    for run in `seq $RUNS`; do
        for o in $SEARCHORDERS; do
            for u in $UPDATES; do
                for t in $THREADS; do
                    cmd="python bin/opaal_ltsmin --state=table -s 25 --threads=$t -o $o -u$u $m"
                    out="$OUTPUT_DIR/$m-$o-u$u-$t-$run.log"
                    echo $cmd
                    #echo $out
                    echo $cmd > $out 
                    time $cmd >> $out 2>&1
                done
            done
        done
    done
done
