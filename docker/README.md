# Docker Infrastructure

## Overview

This directory includes two sub-directories, `develop`, and `deploy`, and `odroidxu4`.

The `develop` directory contains scripts to build a Docker image
containing all of the UxAS prerequsite software, as well as scripts to
then build UxAS and run the UxAS tests in a container.

The `deploy` directory contains scripts to build a Docker image that
includes the `uxas` binary produced by the `develop` scripts, and the
libraries required at run-time. That image can then be used to run UxAS
in a directory mounted from the host computer.

The `odroidxu4` directory contains scripts to build a Docker image for
cross-compiling UxAS onto an ODROID-XU4 Buildroot Linux image. For
more, see the README in that directory.

## Details

The Docker infrastructure for x86_64 uses Ubuntu 17.10 as a base
image, and then installs development tools and libraries needed
to build and test UxAS (the `develop` image). Another image installs
only the shared libraries required by the resulting executable, in
order to make a deployment as small as possible (the `deploy` image).

### Ubuntu

Ubuntu is currently used as a base because it has historically been a
supported platform for UxAS. However, this may change in the future to
a distribution like Alpine Linux in order to reduce the size of
deployment images.

### Self-Contained

While the basic UxAS build system can use Meson wrap dependencies to
satisfy most of its third party requirements, the `develop` image
provides those dependencies in the usual system locations (e.g.,
`/usr/lib` and `/usr/local/lib`). This means that the `develop` image
can build UxAS from start to finish without a network connection.

### Owned By Root

The main rough edge with the Docker infrastructure is the need to use
`sudo` to clean up after it.

The scripts in this directory often invoke Docker with a local disk
mount option so that local development is reflected in the build
container, and so that the build process does not have to start from a
fresh Meson build directory for each Docker-based build.

Since the user within the Docker container is `root` by default, the
files touched during the build therefore become owned by `root`, which
is not what one expects to see in their build tree. You can run `sudo
chown -R youruser:yourgroup` on your OpenUxAS directory, but we are
working on better options.
