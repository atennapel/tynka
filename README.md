Experimental implementation of a "dysfunctional" programming language.
The idea originates from this presentation by Andras Kovacs: https://www.youtube.com/watch?v=ai4vU1Naopk .

We have a language with two layers, one compile-time layer with full dependent types and a runtime-layer with a simply-typed language without higher-order functions or closures. We can get back higher-order functions and polymorphism in the compile-time layer, but after staging we get a very simple language that is easy to compile.

Try it out:
```
sbt "run examples/IO"
java IO
```

TODO:
- [x] Datatype monomorphization
- [x] Match expressions
- [ ] If expressions
- [ ] Pair and unit syntax
- [ ] Pair projections
- [ ] Improve unification with globals
- [ ] Higher-kinded type parameters for datatypes
- [ ] Recursion check in datatypes definitions
- [ ] JVM bytecode generation
- [ ] Foreign datatypes and operations
- [ ] IO
