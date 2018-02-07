The files in this directory are used to construct and deploy a Docker
image that is used to build UxAS. The image is intended to be
self-contained; once built, it should not need a network connection to
build a cloned UxAS source tree.

### Before Building UxAS
LmcpGen must be cloned into the same directory as this repository
(OpenUxAS). OpenAMASE can also be cloned as a sibling of OpenUxAS and
LmcpGen, but is optional:

* `/`
  * `LmcpGen/`
  * `OpenAMASE/` (optional)
  * `OpenUxAS/`

### Directory contents

- `01_buildImage_uxas_develop.sh` uses Docker commands to construct the
  `uxas_develop` Docker image.

- `02_buildUxAS_WithDocker.sh` uses the `uxas_develop` Docker image
  to build UxAS.

- `03_stopAndRemoveBuildContainer.sh` uses Docker commands to stop and
  remove the `uxas_develop` Docker container.

- `04_runUxAS_Tests.sh` runs the UxAS test suite within a `uxas_develop`
  container.

- `Dockerfile.uxas_develop` is the DockerFile that defines the
  `uxas_develop` Docker image.

- `buildUxAS.sh` calls the appropriate Meson and Ninja from inside the
  `uxas_develop` Docker image. Not meant to be used manually.

- `InstallLibraries` contains scripts for installing UxAS prequisites
  from source. Not meant to be used manually.
