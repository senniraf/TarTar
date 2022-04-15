

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
 - [UPPAAL DBM Library](http://people.cs.aau.dk/~adavid/UDBM/)

## Get TarTar
Download TarTar directly from github. You will need to download [Uppaal](http://www.uppaal.org/) (4.1.23) and [Z3](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.3) (4.8.3) from their websites.
```
git clone https://github.com/sen-uni-kn/tartar
```

## Installation
The following instructions were tested on and are written for Ubuntu 18.04.2. 
### UPPAAL
Simply extract the archive into the tartar directory crated by cloning the github project and make sure you have the latest Java Development Kit (JDK).

We used:
```
sudo apt install openjdk-11-jdk
```
### Z3
Simply extract the archive into the tartar directory crated by cloning the github project and run the following commands:
```
python scripts/mk_make.py –java
cd build; make
sudo make install
```
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
At this point you should add the Opaal and pyuppaal directories to you `PYTHONPATH` variable in your `.bashrc`, by adding the lines:
```
export PYTHONPATH=$BASEDIR/tartar/opaal:$BASEDIR/tartar/pyuppaal
export PATH="$BASEDIR/tartar/ltsmin-3.0.2/src/pins2lts-mc/:$BASEDIR/tartar/opaal/bin/:${PATH}"
export PYTHONPATH="$BASEDIR/tartar/pyuppaal:$BASEDIR/tartar/opaal:${PYTHONPATH}"
```
You now need to allow for the execution of createTS.sh and opaal_ltsmin by running the following commands:
```
cd opaal
chmod +x createTS.sh
chmod +x bin/opaal_ltsmin
```

If you followed the above steps, you should now be able to run opaal.

To check everything is alright, you can run the command "nosetests" from the opaal root directory, and you should get only one error (you do not need to install mpi4py).

### LTSmin
You need the following packages:
```
sudo apt install bison flex zlib1g-dev libpopt-dev ant
sudo apt-get install autoconf
```
First you should execute ltsminreconf, you may have to make it executable first:
```
chmod +x ltsminreconf
./ltsminreconf
```
Now install with
```
./configure PKG_CONFIG="/path/to/pkgconfig"
make
sudo make install
```

### Maven
To install Maven run:
```
sudo apt-cache search maven
sudo apt-get install maven
```
You can check if the installation succeeded by checking the version with:
```
mvn –version
```
To install TarTar you need to navigate to the tartar directory and then use Maven to start the installation:
```
cd tartar
mvn install
```
All parts should successfully install.

### Eclipse
Install [Eclipse](https://www.eclipse.org/downloads/) for Java Developers.
To import the TarTar files into an Eclipse project navigate to
```
File > Open Projects from File System > Select the TarTar folder
```
You can then use Maven to import the project by navigation to
```
File > Import > Existing Maven Projects > Select the TarTar folder
```

## Usage Instructions
Usage instructions will be added soon.
