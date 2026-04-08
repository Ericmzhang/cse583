FROM ubuntu:18.04

ENV DEBIAN_FRONTEND=noninteractive

# Install LLVM 8 specifically
RUN apt-get update && apt-get install -y \
    llvm-8 \
    llvm-8-dev \
    clang-8 \
    cmake \
    make \
    g++

WORKDIR /project