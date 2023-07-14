FROM ubuntu:22.04

# https://askubuntu.com/questions/909277/avoiding-user-interaction-with-tzdata-when-installing-certbot-in-a-docker-contai
ARG DEBIAN_FRONTEND=noninteractive

# Load mono keys so we can install PPA to get a recent version (ubuntu ships
# with 4.x; we want 6.x)
RUN apt-get update
RUN apt-get install -y ca-certificates gnupg2
RUN apt-key adv --keyserver keyserver.ubuntu.com --recv-keys A6A19B38D3D831EF

COPY docker-contents/mono-official-stable.list /etc/apt/sources.list.d/

RUN apt-get update
RUN apt-get install -y git make vim emacs

RUN apt-get install -y opam
RUN apt-get install -y libgmp-dev

# set up coq
COPY docker-contents/setup-coq.sh /root
RUN /bin/bash /root/setup-coq.sh
RUN echo 'eval $(opam env)' >> /root/.bashrc

# set up Leaf
WORKDIR /root
RUN mkdir leaf
# copy from docker-contents/clean-src to make sure we get a clean version, no contamination from .vo files etc.
COPY docker-contents/clean-src/src /root/leaf/src
COPY docker-contents/clean-src/external /root/leaf/external
COPY Makefile /root/leaf
COPY _CoqProject /root/leaf

WORKDIR /root/leaf
