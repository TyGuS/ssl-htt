# HTT Tactics for SSL

Coq tactics for the [HTT](https://github.com/imdea-software/htt) framework to support certified program synthesis using [SuSLik](https://github.com/TyGuS/suslik).

## Requirements

* [Coq](https://coq.inria.fr/download) (>= "8.10.0" & < "8.12~")
* [Mathematical Components](http://math-comp.github.io/math-comp/) `ssreflect` (>= "1.10.0" & < "1.12~")
* [FCSL-PCM](https://github.com/imdea-software/fcsl-pcm) (>= "1.0.0" & < "1.3~")
- [Hoare Type Theory](https://github.com/TyGuS/htt)

## Installing

### With OPAM

We recommend installing with [OPAM](https://opam.ocaml.org/doc/Install.html).

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq-htt git+https://github.com/TyGuS/htt\#master --no-action --yes
opam pin add coq-ssl-htt git+https://github.com/TyGuS/ssl-htt\#master --no-action --yes
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm coq-htt coq-ssl-htt
```

### Manually

Run `make clean && make install` in the project root.

