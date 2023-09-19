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
- [x] Safe field access in Con
- [x] Access to Con in pattern matching
- [x] Add IdM, BoolM and IFixM to Meta-level
- [x] Try to write n-ary State monad
- [ ] Modules
  - [x] Renaming
  - [x] Qualified imports
  - [x] Import hiding
  - [x] Fix modules in staging/compilation
  - [x] Rewrite lib and examples to use modules
  - [ ] Exporting imports
  - [ ] Private/public definitions
- [x] Some form of type classes
  - [x] Search globals
  - [x] Approximate unification for globals
  - [x] Search locals
  - [x] Fix autos from imports
  - [x] Order globals
  - [ ] Rename auto?
  - [ ] Better syntax for unnamed auto parameters
- [ ] Remove implicit generalization
- [ ] Linear pairs
- [ ] Try to get rid of `boolean bl = false;` in JVM bytecode due to IO
- [ ] Support trampolines
- [ ] Improve syntax for recursive functions
- [ ] Higher-kinded type parameters for 
- [ ] Partially-static data
- [ ] Records/variants
- [ ] Val Rep: Boxed or Unboxed

BUGS:
- [ ] Fix duplicate definitions import bug
- [ ] Fix naming issues in datatypes and generated JVM bytecode
