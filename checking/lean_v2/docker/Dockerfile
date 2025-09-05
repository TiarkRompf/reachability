FROM ubuntu:24.04
RUN apt update -y
RUN apt install -y curl git python3-matplotlib python3-numpy && apt clean
USER ubuntu
WORKDIR /work
ADD --chown=ubuntu https://elan.lean-lang.org/elan-init.sh elan-init.sh
RUN sh elan-init.sh -y --default-toolchain none
ADD --chown=ubuntu mech.tar.gz reachability
ENV PATH="/home/ubuntu/.elan/bin:$PATH"
WORKDIR reachability
RUN lake clean
RUN lake exe cache get Mathlib/Data/Finset/Basic.lean Mathlib/Data/Finset/Image.lean Mathlib/Data/Finset/Sort.lean
ADD --chown=ubuntu bench.tar.gz .