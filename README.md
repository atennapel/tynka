Experimental implementation of a "dysfunctional" programming language.
The idea originates from this presentation by Andras Kovacs: https://www.youtube.com/watch?v=ai4vU1Naopk .

We have a language with two layers, one compile-time layer with full dependent types and a runtime-layer with a simply-typed language without higher-order functions or closures. We can get back higher-order functions and polymorphism in the compile-time layer, but after staging we get a very simple language that is easy to compile.

References:
- https://github.com/AndrasKovacs/elaboration-zoo
- https://github.com/AndrasKovacs/staged/tree/main/demo
- https://github.com/AndrasKovacs/staged/tree/main/old/mono_staged
- https://julesjacobs.com/notes/patternmatching/patternmatching.pdf

Try it out:
```
sbt "run examples/IOExample"
java examples/IOExample
```

TODO:
- [x] Unification
- [x] Elaboration
- [x] Definitions
- [x] Primitives
- [x] Recursive definitions
- [x] Pretty
- [x] Datatypes
  - [x] Type constructor
  - [x] Value constructor
  - [x] Case split
  - [x] Match without scrutinee
- [x] Postponing
- [x] Pattern matching
  - [x] Pattern elaboration
  - [x] Operators in patterns
  - [x] Multi-match
  - [x] As-patterns
- [ ] Pattern guards
- [ ] Or-patterns
- [ ] Pattern lambdas, lets and binds
- [ ] Recursive meta definitions (?)
- [ ] Meta datatypes
- [ ] More postponing (?) (con and match)
- [ ] Join points
