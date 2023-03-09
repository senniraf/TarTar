# TarTar

### Table of Contents

**[License](#license)**

**[Docker Installation (Recommended)](#docker-installation-recommended)**

**[Using TarTar in a Docker container](#using-tartar-in-a-docker-container)**

**[Local Installation (Deprecated)](#local-installation-deprecated)**

**[Usage Instructions](#usage-instructions)**

## License

TarTar itself is licensed by the MIT license. TarTar includes several other tools that are published under other licenses:

* [LTSmin](https://ltsmin.utwente.nl/)
* [opaal](http://opaal-modelchecker.com/opaal-ltsmin/)
* [pyuppaal](https://launchpad.net/pyuppaal)
* [pydbm](http://people.cs.aau.dk/~adavid/UDBM/)
* [Uppaal](http://www.uppaal.org/) (download necessary)
* [Z3](https://github.com/Z3Prover/z3) (download necessary)
* [UPPAAL DBM Library](http://people.cs.aau.dk/~adavid/UDBM/)

## Docker Installation (Recommended)

The repository includes a [Dockerfile](Dockerfile) which can be used to create a docker image including TarTar and all needed dependencies. To built the image you need a [Docker-Installation](https://www.docker.com/) which supports linux-based Docker images. Running a container based on the image is currently only supported on linux.

The image can be built with executing the following command in the cloned repository:

```sh
docker build -t tartar .
```

To reduce build time you can pass the number of parallel jobs used during make compilation by adding the `--build-arg JOBS={NUM_OF_JOBS}` flag. Using the command above the image is tagged with `tartar:latest`.

## Using TarTar in a Docker container

We are assuming you have built a Docker image of TarTar tagged with `tartar:latest` (as described in the [previous section](#docker-installation-recommended)). 

### Running TarTar

Because TarTar needs a GUI, running the image as a container is a bit tricky. The following steps are applicable for Linux environments. You can try running it with:

```sh
docker run -v $PWD/input:/input -v $PWD/result:/tartar/tartar/result -v /tmp/.X11-unix:/tmp/.X11-unix -e DISPLAY --network="host" tartar java -cp /tartar/tartar/tartar.main/target/tartar.main-3.1.0-jar-with-dependencies.jar kn.uni.sen.joblibrary.tartar.web.TarTarMain
```

This can however lead to the error: `Authorization required, but no authorization protocol specified`. This requires a bit more effort. First you have to execute the following command on your host machine:

```sh
xauth list
```

which produces output that looks like:

```plain
blabla/unix:1  MIT-MAGIC-COOKIE-1  8934587934bc9878352
bla/unix:1  MIT-MAGIC-COOKIE-1  1254387a34d49b7af43
```

Save one of the rows somewhere. If there is no number behind the "`:`" in your output run `echo $DISPLAY` and add the number in the result behind the "`:`". Now, start the container with:

```sh
docker run -v $PWD/input:/input -v $PWD/result:/tartar/tartar/result -v /tmp/.X11-unix:/tmp/.X11-unix -e DISPLAY --network="host" -it tartar
```

This will open a shell in the container. Execute the following command in the container shell and replace `{token}` with the row you saved before:

```sh
xauth add {token}
```

Run TarTar by executing the following command in the container shell:

```sh
java -cp /tartar/tartar/tartar.main/target/tartar.main-3.1.0-jar-with-dependencies.jar kn.uni.sen.joblibrary.tartar.web.TarTarMain
```

For more information on how to run a GUI application in a Docker container, see: [https://www.howtogeek.com/devops/how-to-run-gui-applications-in-a-docker-container/](https://www.howtogeek.com/devops/how-to-run-gui-applications-in-a-docker-container/).

### Using TarTar

You can use TarTar by placing inputs in the directory `./input` relative to the directory you started the container with `docker run`. The results of the computation are put in the `./result` directory. You can produce trace-files for TarTar by using the `verifyta` binary which is shipped within your UPPAAL installation. For linux machines it's in the `bin-Linux` directory in the UPPAAL installation location. Trace files are computed by executing

```sh
verifyta -X ./input -t 0 {input-model}
```

on a model `{input-model}` containing unsatisfied queries. The traces are saved to `./input`. In the TarTar GUI select the model with the trace and compute the repairs. Both the trace and the model must be located in the `./input` directory which is mapped to `/input` in the container. The repairs are saved to a new directory with a timestamp in `./result`.

## Local Installation (Deprecated)

The following instructions were tested on and are written for Ubuntu 18.04.2.
### UPPAAL

Download from the [Website](http://www.uppaal.org/). Simply extract the archive into the tartar directory crated by cloning the github project and make sure you have the latest Java Development Kit (JDK).

We used:
```
sudo apt install openjdk-11-jdk
```
### Z3
Download [Z3 v4.8.3](https://github.com/Z3Prover/z3/releases/tag/z3-4.8.3), extract it and run the following commands in the extracted folder:
```
python scripts/mk_make.py --java
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
To install it after unpacking navigate to the modules folder and execute:
```
./setup.sh
```
You may need to allow for execution of the setup.sh and configure file in the respective file settings.
Choose build dir, install path (you will have to use this directory in the setup.py for pydbm later), and compiler.
Choose compile options "2" and configuration options "6 11".

Then
```
make
sudo make install
```
You might get an error similar to "unable to find a string literal operator" in this case you need to adjust the used C++ standard in setup.sh. At the bottom of the file add `-std=c++03` to the CFLAGS variable.

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
./configure #PKG_CONFIG="/path/to/pkgconfig"
sudo make
./configure #PKG_CONFIG="/path/to/pkgconfig"
sudo make install #src/pins-lib
sudo make
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

TarTar can be started by the `main` in the class `MainGui` in different modes.

The call arguments of `main()` control which mode is started:
- without argument -> Gui
- with `-web` -> web application
- otherwise TarTar is executed in the console (`-h` for more information)

The experiments from the papers are created with the respective experiment name as argument e.g. `experiment_cav2020`.
This created the experiment and can be executed by calling the script `result/result-date-time/experiment_cav2020.sh`. 
