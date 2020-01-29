#!/bin/bash

#get filename with extension .xml
file_in=$1
file=$(echo "$(basename "${file_in}")" | rev | cut -d"." -f2- | rev)

#if no second argument create name of output 
file_out=$2
if [ $# -lt 2 ]
then
file_out=$(echo "$(basename "${file_in}")" | cut -f 1 -d ".")
#file_out=$file_out.xml
file_out=$file"_lts.xml"
fi

./bin/opaal_ltsmin --only-compile $file_in

#compile $file.cpp
g++  -shared -O0 -fPIC -I/usr/local/uppaal/include -L/usr/local/uppaal/lib  -o $file.so $file.cpp -ludbm

mem=$(free | awk '/^Mem:/{print $4}')
#run reachability by ltsmin and write TS to $file.gcf
mem2=$(echo "l(0.9*$mem)/l(2)" | bc -l)
mem3=${mem2%.*}
echo --------------------------------------------------------------------------------------------------
opaal2lts-mc --state=table -s=$mem3 --threads=1 --strategy=dfs -u=1 $file.so $file_out 

rm $file.so
rm $file.cpp

# afterwards ltsmin-compare --trace file1 file2
echo "a.b.c.txt" | rev | cut -d"." -f2-  | rev
echo $mem
echo $mem3
