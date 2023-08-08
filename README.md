Experimental implementation of a "dysfunctional" programming language.
The idea originates from this presentation by Andras Kovacs: https://www.youtube.com/watch?v=ai4vU1Naopk .

We have a language with two layers, one compile-time layer with full dependent types and a runtime-layer with a simply-typed language without higher-order functions or closures. We can get back higher-order functions and polymorphism in the compile-time layer, but after staging we get a very simple language that is easy to compile.

Try it out:
```
sbt "run examples/IOExample"
java examples/IOExample
```

TODO:
- [x] Datatype monomorphization
- [x] Match expressions
- [x] IO
- [x] Interpreter
- [x] Implicit generalization
- [x] JVM bytecode generation
- [x] Foreign datatypes
- [x] Foreign operations
- [x] Integrate foreign with IO
- [x] Do syntax for monads
- [x] Imports
- [x] Add arrays in IO
- [x] Add linearity in Ty
- [x] ST monad
- [x] Opaque definitions
- [ ] Modules
- [ ] Support trampolines
- [ ] Improve syntax for recursive functions
- [ ] Recursion check in datatypes definitions
- [ ] Higher-kinded type parameters for datatypes
- [ ] Records/variants
- [ ] Val Rep: Boxed or Unboxed

BUGS:
- [ ] Fix duplicate definitions import bug
- [ ] Fix naming issues in datatypes and generated JVM bytecode
