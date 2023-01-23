Experimental implementation of a "dysfunctional" programming language.
The idea originates from this presentation by Andras Kovacs: https://www.youtube.com/watch?v=ai4vU1Naopk .

We have a language with two layers, one compile-time layer with full dependent types and a runtime-layer with a simply-typed language without higher-order functions or closures. We can get back higher-order functions and polymorphism in the compile-time layer, but after staging we get a very simple language that is easy to compile.

Try it out:
```
sbt "run examples/Test"
javac jvmstd/Pair.java
javac jvmstd/List.java
javac jvmstd/Either.java
java Test
```

TODO:
- [x] IR fix with parameters
- [x] Remove lambdas from IR language
- [ ] Unit type in meta level
- [ ] Eta expand during elaboration?
- [ ] Lift lambda over let during elaboration?
- [ ] Eta expansion after staging?
