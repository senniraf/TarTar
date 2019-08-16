

# TarTar

### Table of Contents
**[License](#license)**

**[Get TarTar](#get-tartar)**

**[Installation](#installation)**

**[Usage Instructions](#usage-instructions)**

## License
TarTar itself is licensed by the MIT license.
 
 TarTar includes several other tools that are published under other licenses:
 - [LTSmin](https://ltsmin.utwente.nl/)
 - [opaal](http://opaal-modelchecker.com/opaal-ltsmin/)
 - [pyuppaal](https://launchpad.net/pyuppaal)
 - [pydbm](http://people.cs.aau.dk/~adavid/UDBM/)
 - [Uppaal](http://www.uppaal.org/) (download necessary)
 - [Z3](https://github.com/Z3Prover/z3) (download necessary)
 - [UPPAAL DBM Library](http://people.cs.aau.dk/~adavid/UDBM/)(download necessary)

## Get TarTar
Download TarTar directly from github. You will need to download [Uppaal](http://www.uppaal.org/) (4.1.19) and [Z3](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.3) (4.8.3) from their websites.
```
git clone https://github.com/sen-uni-kn/tartar
```

## Installation
The following instructions were tested on and are written for Ubuntu 18.04.2. 
### UPPAAL
Simply extract the archive into the tartar directory and make sure you have the latest Java Development Kit (JDK).

We used:
```
sudo apt install openjdk-11-jdk
```
### Z3
Simply extract the archive into the tartar directory.
### pyuppaal
Pyuppaal depend on the following Ubuntu packages:
```
sudo apt install python-pygraphviz python-ply
```
To run tests of the installation you can run:
```
sh tests/run_tests.sh
```
### UPPAAL DBM Library
Download the patched version from http://mcc.uppaal.org/opaal/UPPAAL-dbm-2.0.8-opaal3.tar.gz

Unpack the archive into the tartar directory.

You need the following packages:
```
sudo apt install libboost-all-dev
```
To install it, after unpacking:
```
./setup.sh
```
Choose build dir, install path (you will have to use this directory in the setup.py for pydbm later), and compiler.
Choose compile options "2" and configuration options "6 11".

Then
```
make
sudo make install
```
You might get an error similar to "unable to find a string literal operator" in this case you need to adjust the used C++ standard in setup.sh. At the bottom of the file add 'std=c++03' to the CFLAGS variable.

### pydbm
You need swig, so:
```
sudo apt install swig
```
You should make sure that the install path for the DBM library is correctly set in `setup.py`, we recommend making the path absolute.

To install:
```
python setup.py build
sudo python setup.py install
```
To test:
```
python test.py
```
### Opaal
You need the following packages:
```
sudo apt install libopenmpi-dev python-dev openmpi-bin python-numpy python-matplotlib python-nose
```
At this point you should add the Opaal and pyuppaal directories to you `PYTHONPATH` variable in your `.bashrc`, by adding the line:
```
export PYTHONPATH=$BASEDIR/tartar/opaal:$BASEDIR/tartar/pyuppaal
```

If you followed the above steps, you should now be able to run opaal.

To check everything is alright, you can run the command "nosetests" from the opaal root directory, and you should get only one error (you do not need to install mpi4py).

### LTSmin
You need the following packages:
```
sudo apt install bison flex zlib1g-dev libpopt-dev ant
```
First you should do:
```
git submodule update --init
autoreconf -i
```
Now install with
```
./configure PKG_CONFIG="/path/to/pkgconfig"
make
sudo make install
```

## Usage Instructions
Usage instructions will be added soon.
