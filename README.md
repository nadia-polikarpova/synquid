This is a snapshot of the code for PLDI'16 atifact evaluation.

# Synquid #

Synquid synthesizes programs from refinement types.

For example, given the following type as the specification:
```
#!haskell

replicate :: n:Nat -> x:a -> {List a | len _v = n}
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

## Try Synquid ##

* **Try [in your browser](http://comcom.csail.mit.edu/comcom/#Synquid)!**
* **Build from sources:** you will need recent versions of [GHC and Cabal](https://www.haskell.org/platform/) (we are using GHC 7.10.2 and Cabal 1.22.6.0). You will also need [z3](https://github.com/Z3Prover/z3) version 4.3.2. Clone this repository and then run ```cabal install``` from its top-level directory.

## Testimonials ##

![testimonial.png](https://bitbucket.org/repo/qXe57A/images/104717122-testimonial.png)