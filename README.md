<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# SPropTools

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[docker-action-shield]: https://github.com/kyoDralliam/sproptools/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/kyoDralliam/sproptools/actions?query=workflow:"Docker%20CI"

[nix-action-shield]: https://github.com/kyoDralliam/sproptools/workflows/Nix%20CI/badge.svg?branch=master
[nix-action-link]: https://github.com/kyoDralliam/sproptools/actions?query=workflow:"Nix%20CI"


[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://kyoDralliam.github.io/sproptools


Strict propositions as described in Gilbert et al's paper Definitional
Proof-Irrelevance without K are accessible in Coq through the sort SProp. This
library extends Coq's standard library providing more extensive support for
strict propositions (definitions, notations and tactics)

## Meta

- Author(s):
  - Kenji Maillard (initial)
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies: none
- Coq namespace: `Sproptools`
- Related publication(s):
  - [Definitional Proof-Irrelevance without K](https://hal.inria.fr/hal-01859964v2/document) 

## Building and installation instructions

The easiest way to install the latest released version of SPropTools
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-sproptools
```

To instead build and install manually, do:

``` shell
git clone https://github.com/kyoDralliam/sproptools.git
cd sproptools
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


SPropTools is a small coq library containing definitions and notations for working with strict propositions.
Currently the only documentation is directly in the sources.

## Building & Installing

From the top directory
```shell
$ make
$ make install
```
