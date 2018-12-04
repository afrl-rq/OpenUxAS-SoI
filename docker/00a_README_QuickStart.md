# UxAS/ Docker Quickstart

* Updated - `7/16/2018`

## Prerequisites

* `Docker` - [https://docs.docker.com](https://docs.docker.com)

* `Python`

* `Internet Connection`

## Before Building UxAS

LmcpGen must be cloned into the same directory as this repository
(OpenUxAS). OpenAMASE can also be cloned as a sibling of OpenUxAS and
LmcpGen, but is optional. The directory structure should look like this:

```
   |
   |- `LmcpGen/`
   |- `OpenAMASE/` (optional)
   |- `OpenUxAS/`

## Build and Run UxAS

1) `prepare` the `3rd` libraries, build and run LMCPGen:
   `python 01_PrepareAndBuildLmcp.py`
2) build UxAS and construct the `uxas-deploy` image:
   `python 02_BuildDeploy_UxAS.py`
3) the directory `03_test` contains a script and configuration file to test run the containerized UxAS
