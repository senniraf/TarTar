BASEDIR=/files/windata/Tausch/3Uni/opaal/opaal
export PATH=$BASEDIR/ltsmin-3.0.2/src/pins2lts-mc/:$BASEDIR/opaal/bin:$PATH
export PYTHONPATH=$BASEDIR/pyuppaal:$BASEDIR/opaal:$BASEDIR/usr/lib/python2.7/site-packages/:.:$PYTHONPATH

#python opaal/model_parsers/pyuppaal/gensuccgen.py 3state.xml 3state.cpp
#read
#Execute the following command to compile model:
#g++ -g -shared -O0 -fPIC -I../usr/uppaal/include/ -L../usr/uppaal/lib/ -o 3state.so 3state.cpp -ludbm
#opaal-ltsmin: g++  -shared -O0 -fPIC -I/usr/local/uppaal/include -L/usr/local/uppaal/lib  -o "3state.so" "3state.cpp" -ludbm 
g++  -shared -O0 -fPIC -I/usr/local/uppaal/include -L/usr/local/uppaal/lib  -o "1msg.so" "1msg.cpp" -ludbm 
#read
#To verify the model run:
#opaal2lts-mc --strategy=cndfs -u1 --threads=1 3state.so -v
#opaal-ltsmin: opaal2lts-mc --state=table -s 25  --strategy=sbfs   -u1 "3state.so"

#opaal2lts-mc --debug "loggi.txt" --write-state --state=table -s 25 --threads 1 --strategy=dfs  --trace="trace.txt"  -u1 "3state.so"

opaal2lts-mc --state=table -s 25 --threads 1 --strategy=dfs  -u1 "3state.so"

#opaal2lts-mc --state=table -s=25 --threads=1 --strategy=dfs  --trace="trace.txt"  -u=1 "3state.so" lts.gcf
#ltsmin-compare --trace lts.gcf lts2.gcf

#./bin/opaal_draw_statespace 4state.xml out.pdf

#    //  get_state_variable_type_value(type,value);
#    printf("state: %s %d->", get_state_variable_type_value(1, in->Process), in->Process);
#    printf("%s %d\n", get_state_variable_type_value(1, out->Process), out->Process);

#    //printf("lattice %s\n", opaal_get_string_label(0,0,in));
#    //printf("lattice %s\n", opaal_get_string_label(0,0,out));
    
#    printf("succ_cb(1): %p\n", in->fed);
#    std::cout << "succ_cb(1): " << in->fed->toString(clockNames) << std::endl;

#    printf("succ_cb(2): %p\n", out->fed);
#    std::cout << "succ_cb(2): " << out->fed->toString(clockNames) << std::endl;
