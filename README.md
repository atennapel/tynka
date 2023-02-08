Experimental implementation of a "dysfunctional" programming language.
The idea originates from this presentation by Andras Kovacs: https://www.youtube.com/watch?v=ai4vU1Naopk .

We have a language with two layers, one compile-time layer with full dependent types and a runtime-layer with a simply-typed language without higher-order functions or closures. We can get back higher-order functions and polymorphism in the compile-time layer, but after staging we get a very simple language that is easy to compile.

Try it out:
```
sbt "run examples/IO"
java IO
```

TODO:
- [x] JVM bytecode generation
- [x] Tail recursion
- [x] Datatypes
- [x] Improve `fix` type inference
- [x] More primitive operations for `Int`
- [x] Fix weakening bug in pretty printing `case`
- [x] Optimize `Bool`-like types
- [x] Optimize `Unit`-like types
- [x] Optimize `Void`-like types
- [x] Optimize finite types to `Int`
- [x] Syntax sugar for datatype definitions
- [x] Optimize constructor elimination (only bind used values)
- [x] Boxing
- [x] Optimize single constructor types (product-like)
- [x] Add new-types
- [x] Basic file importing
- [x] Modules, or a way to handle name clashes
- [ ] Cannot access operators in modules
- [ ] Public/private definitions
- [ ] Do not export imported definitions
- [ ] Relative file including
- [ ] Remove unused defs (starting from main)
- [ ] Rename symbol names in JVM generator
- [ ] Improve inference for if condition
- [ ] Value level strings
- [ ] Value level syntax for unit
- [ ] Arrays
- [ ] Should foreign always return in IO?
- [ ] Keep generics signature in JVM bytecode output
- [ ] Records
- [ ] Irregular/nested datatype recursion
- [ ] Closures, thunks, JVM generics
- [ ] Delay IO execution
- [ ] Coercion over constructors
- [ ] Dependency ordering of surface definitions
