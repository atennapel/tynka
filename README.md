Experimental implementation of a "dysfunctional" programming language.
The idea originates from this presentation by Andras Kovacs: https://www.youtube.com/watch?v=ai4vU1Naopk .

We have a language with two layers, one compile-time layer with full dependent types and a runtime-layer with a simply-typed language without higher-order functions or closures. We can get back higher-order functions and polymorphism in the compile-time layer, but after staging we get a very simple language that is easy to compile.

```
Runtime type hierarchy:

Rep : Meta
ByteRep : Rep
ShortRep : Rep
IntRep : Rep
LongRep : Rep
FloatRep : Rep
DoubleRep : Rep
CharRep : Rep
BoolRep : Rep

Boxity : Meta
Boxed : Boxity
Unboxed : Rep -> Boxity

CV : Meta
Comp : CV
Val : Boxity -> CV

Ty : CV -> Meta
Fun : {b : Boxity} -> Ty (Val b) -> {cv : CV} -> Ty cv -> Ty Comp
IO : {b : Boxity} -> Ty (Val b) -> Ty Comp

Bool : Ty (Val (Unboxed BoolRep))
Int : Ty (Val (Unboxed IntRep))
etc.

Array : {l : Boxity} -> Ty (Val l) -> Ty (Val Boxed)
Enums : Ty (Val (Unboxed ...)) -- smallest Rep that fits all enum members
ADTs : Ty (Val Boxed)
```

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
  - [x] Pattern guards
  - [x] Multi-match check against pi type
- [x] Join points
- [x] Unboxed and newtypes
- [x] JVM interop
  - [x] Primitive datatypes
  - [x] Array datatype
  - [x] Int literals
  - [x] Labels
  - [x] Class types
  - [x] String literals
  - [x] JVM interop calls
  - [x] IO monad
- [x] Newtypes
- [x] Meta datatypes
- [ ] Sigma types
  - [x] Sigma, pair and projection syntax
  - [x] Nested pair syntax
  - [x] Sigma, pair and projection core syntax
  - [x] Sigma, pair and projection core values
  - [ ] Sigma Unification
  - [ ] Sigma elaboration
  - [ ] Pair elaboration
  - [ ] Projection elaboration
  - [ ] Array literals
- [ ] Label operations: eqLabel and appendLabel
- [ ] Con
- [ ] Opaque definitions and unfolding
- [ ] Boxing
- [ ] Null
- [ ] Modules
- [ ] Products
- [ ] Constant folding for primitives
- [ ] Non-Int primitive literals
- [ ] Recursive meta definitions (?)
- [ ] Or-patterns
- [ ] Pattern lambdas, lets and binds
- [ ] Infer multi-match lambda
- [ ] Fix bug with postponed Universe metas
