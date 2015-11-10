# Synquid #

Synquid synthesizes programs from refinement types.

For example, given the following type as the specification:
```
#!haskell

replicate :: n:Nat -> x:a -> {v: List a | len v = n}
```
and an appropriate set of components, Synquid will automatically generate a program: 
```
#!haskell

replicate = \n . \x . 
  if n <= 0
    then Nil
    else Cons x (replicate (dec n) x)
```

Synquid is based on the combination of [bidirectional synthesis](http://dl.acm.org/citation.cfm?doid=2737924.2738007) and [liquid types](http://dl.acm.org/citation.cfm?doid=1375581.1375602).

**This project is still under construction; the first release will be out soon!**