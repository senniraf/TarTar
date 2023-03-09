FROM ubuntu:18.04

# Number of make jobs
ARG JOBS=1

# Install dependencies
RUN apt update && apt install -y --no-install-recommends \
    openjdk-11-jdk \
    python-dev \
    python-pip \
    build-essential \
    ant \
    pkgconf \
    libtool \
    bison \
    flex \
    swig \
    libgraphviz-dev \
    libboost-all-dev \
    libpopt-dev \
    curl \
    ca-certificates

# Install z3 with Java bindings
WORKDIR /deps
RUN curl -LO https://github.com/Z3Prover/z3/archive/refs/tags/z3-4.12.1.tar.gz
RUN tar -xf z3-4.12.1.tar.gz
RUN rm z3-4.12.1.tar.gz
WORKDIR /deps/z3-z3-4.12.1
RUN python scripts/mk_make.py --java
WORKDIR /deps/z3-z3-4.12.1/build
RUN make -j${JOBS}
RUN make install

# Install UPPAAL DBM Library
WORKDIR /deps
RUN curl -LO https://github.com/UPPAALModelChecker/UDBM/archive/refs/tags/v2.0.9.tar.gz
RUN tar -xf v2.0.9.tar.gz
RUN rm v2.0.9.tar.gz
WORKDIR /deps/UDBM-2.0.9
RUN CFLAGS="-std=c++03 -fPIC" ./configure
RUN make -j${JOBS}
RUN make install

# Install LTSmin
WORKDIR /deps
RUN curl -LO http://github.com/utwente-fmt/ltsmin/releases/download/v3.0.2/ltsmin-v3.0.2-source.tgz
RUN tar -xf ltsmin-v3.0.2-source.tgz
RUN rm ltsmin-v3.0.2-source.tgz
WORKDIR /deps/ltsmin-3.0.2
RUN ./configure
RUN make -j${JOBS}
RUN make install


# Install pydbm
COPY ./pydbm /tartar/pydbm
WORKDIR /tartar/pydbm
RUN python setup.py build
RUN python setup.py install

# Install opaal
RUN apt install -y --no-install-recommends \
    python-setuptools
RUN pip install numpy==1.16.6 \
    matplotlib==2.2.5
COPY ./opaal /tartar/opaal
WORKDIR /tartar/opaal
RUN chmod +x createTS.sh
RUN chmod +x bin/opaal_ltsmin

# Install pyuppaal
RUN apt install -y --no-install-recommends \
    python-pygraphviz \
    python-ply \
    python-nose
COPY ./pyuppaal /tartar/pyuppaal

# Install JobScheduler
RUN apt install -y --no-install-recommends \
    maven
COPY ./JobScheduler /tartar/JobScheduler
WORKDIR /tartar
RUN mvn install:install-file \
    -Dfile=JobScheduler/jobscheduler.common-1.6.0.jar \
    -DgroupId=kn.uni.sen.jobscheduler \
    -DartifactId=jobscheduler.common \
    -Dversion=1.6.0 \
    -Dpackaging=jar \
    -DgeneratePom=true
RUN mvn install:install-file \
    -Dfile=JobScheduler/jobscheduler.common-1.6.0-tests.jar \
    -DgroupId=kn.uni.sen.jobscheduler \
    -DartifactId=jobscheduler.common \
    -Dversion=1.6.0 \
    -Dpackaging=jar \
    -Dclassifier=tests \
    -DgeneratePom=true
RUN mvn install:install-file \
    -Dfile=JobScheduler/jobscheduler.console-1.6.0.jar \
    -DgroupId=kn.uni.sen.jobscheduler \
    -DartifactId=jobscheduler.console \
    -Dversion=1.6.0 \
    -Dpackaging=jar \
    -DgeneratePom=true
RUN mvn install:install-file \
    -Dfile=JobScheduler/jobscheduler.core-1.6.0.jar \
    -DgroupId=kn.uni.sen.jobscheduler \
    -DartifactId=jobscheduler.core \
    -Dversion=1.6.0 \
    -Dpackaging=jar \
    -DgeneratePom=true

ENV PYTHONPATH=/tartar/opaal:/tartar/pyuppaal
ENV PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/tartar/ltsmin-3.0.2/src/pins2lts-mc/:/tartar/opaal/bin/

# Install Tartar
COPY ./tartar /tartar/tartar
WORKDIR /tartar/tartar
RUN mvn clean install -DskipTests

# Install GUI sharing
RUN apt install -y --no-install-recommends \
    xauth

# run with docker run -v /tmp/.X11-unix:/tmp/.X11-unix -e DISPLAY --network="host"
# xauth add from xauth list
# CMD [ "java", "-cp", "/tartar/tartar/tartar.main/target/tartar.main-3.1.0-jar-with-dependencies.jar", "kn.uni.sen.joblibrary.tartar.gui.MainGui" ]
