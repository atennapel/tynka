```
Meta : Meta

ValTy : Meta
Bool : ValTy

Ty : Meta
Val : ValTy -> Ty
Fun : ValTy -> Ty -> Ty

^ : Ty -> Meta
` : {A : Ty} -> A -> ^A
$ : {A : Ty} -> ^A -> A
```
