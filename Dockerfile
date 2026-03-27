FROM ubuntu:20.04

WORKDIR /root/
ENV JAVA_HOME "/usr/lib/jvm/java-11-openjdk-amd64"
ENV D4J_HOME "/root/defects4j"
ENV TZ "America/Los_Angeles"


# Install prerequistes
RUN apt -y update && apt -y install software-properties-common && apt -y install build-essential \
&& apt -y install curl make patch unzip bubblewrap \
&& apt -y install openjdk-8-jdk openjdk-11-jdk \
&& apt -y install git maven \
&& apt -y install sqlite3 autoconf libev-dev libgmp-dev libmpfr-dev libpcre3-dev libsqlite3-dev m4 pkg-config zlib1g-dev \
&& add-apt-repository ppa:deadsnakes/ppa && apt -y install python3.10
RUN bash -c "python3.10 <(curl -fsSL https://bootstrap.pypa.io/get-pip.py)"

# Install opam
RUN bash -c "echo /usr/local/bin | sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"

# Install Infer
COPY ./tool ./tool
RUN cd tool/sabfl && ./build-infer.sh java -y

# Install D4J
COPY ./utils ./utils
RUN apt -y install perl libdbi-perl subversion cpanminus
RUN git clone https://github.com/rjust/defects4j && defects4j/init.sh
RUN cd defects4j && cpanm --installdeps .; exit 0
RUN cp $D4J_HOME/major/bin/ant $D4J_HOME/major/bin/ant.1.8.4 \
&& ln -s $PWD/utils/apache-ant-1.10.12/bin/ant $D4J_HOME/major/bin/ant.1.10.12

# Install sprint-components
RUN cd ./tool/components/ && mvn -DskipTests install

# Copy scipts
COPY ./scripts ./scripts
RUN rm /usr/bin/python3 && ln -s /usr/bin/python3.10 /usr/bin/python3
RUN pip3 install dacite colorama pandas slacker
