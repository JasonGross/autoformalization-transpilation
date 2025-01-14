FROM ubuntu:20.04

## BEGIN: RUNS AS ROOT

# Create a user

ARG USERNAME=cis5000
ARG USER_UID=1000
ARG USER_GID=$USER_UID

RUN apt-get update -y

RUN groupadd --gid $USER_GID $USERNAME \
    && useradd --uid $USER_UID --gid $USER_GID -m $USERNAME --shell /bin/zsh \
    #
    # [Optional] Add sudo support. Omit if you don't need to install software after connecting.
    && apt-get install -y sudo \
    && echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME \
    && chmod 0440 /etc/sudoers.d/$USERNAME

## Hack needs root permissions

# See hack.sh
COPY hack.sh /tmp/hack.sh
RUN chmod +x /tmp/hack.sh
RUN /tmp/hack.sh

RUN apt-get install -y build-essential
RUN apt-get install -y linux-libc-dev
RUN apt-get install -y m4
RUN apt-get install -y opam
RUN apt-get install -y time
RUN apt-get install -y zip
RUN apt-get install -y zsh
RUN apt-get install -y libgmp3-dev
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y pkg-config

## Set up user environmnent
COPY .zshrc /home/$USERNAME/


## Run in usermode

# [Optional] Set the default user. Omit if you want to keep the default as root.
USER $USERNAME

# Configure opam/ocaml
RUN opam init -y --disable-sandboxing --compiler=4.14.0
RUN opam switch 4.14.0
RUN opam install -y num
RUN opam repo add -y coq-released https://coq.inria.fr/opam/released
RUN opam pin add -y coq 8.19.1
RUN opam install -y coq-simple-io
RUN opam install -y vscoq-language-server
RUN opam update -y
RUN opam upgrade -y
RUN eval `opam config env`

