 
BASEDIR=/home/martin/opaal-ltsmin
#echo $BASEDIR
#read
export PATH=$BASEDIR/ltsmin-3.0.2/src/pins2lts-mc/:$BASEDIR/opaal/bin:$PATH
export PYTHONPATH=$BASEDIR/pyuppaal:$BASEDIR/opaal:$BASEDIR/usr/lib/python2.7/site-packages/:.:$PYTHONPATH
echo $PATH
echo $PYTHONPATH
