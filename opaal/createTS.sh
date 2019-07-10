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



#echo $file
#echo $file_in
#echo $file_out
#echo $folder_out
#read
#folder_out=$(dirname "${file_out}")
#create $file.cpp
#folder_cmd=$(pwd)
#echo $folder_cmd

./bin/opaal_ltsmin --only-compile $file_in

#compile $file.cpp
g++  -shared -O0 -fPIC -I/usr/local/uppaal/include -L/usr/local/uppaal/lib  -o $file.so $file.cpp -ludbm


#run reachability by ltsmin and write TS to $file.gcf
opaal2lts-mc --state=table -s=25 --threads=1 --strategy=dfs -u=1 $file.so $file_out

rm $file.so
rm $file.cpp

# afterwards ltsmin-compare --trace file1 file2
echo "a.b.c.txt" | rev | cut -d"." -f2-  | rev
