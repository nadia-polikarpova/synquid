# Synquid #

Synquid synthesizes programs from refinement types.

For example, given the following type as the specification:
```haskell

replicate :: n:Nat -> x:a -> {List a | len _v = n}
```

and an appropriate set of components, Synquid will automatically generate a program:
```haskell

replicate = \n . \x .
  if n <= 0
    then Nil
    else Cons x (replicate (dec n) x)
```

Synquid is based on the combination of [bidirectional synthesis](http://dl.acm.org/citation.cfm?doid=2737924.2738007) and [liquid types](http://dl.acm.org/citation.cfm?doid=1375581.1375602).

## News ##

*June 18, 2016*: [Synquid mode](https://github.com/cpitclaudel/synquid-emacs) for Emacs is now available on MELPA! Thanks to [Clément Pit--Claudel](https://github.com/cpitclaudel)!

*June 16, 2016*: The [Synquid paper](http://people.csail.mit.edu/polikarn/publications/pldi16.pdf) was presented at [PLDI'16](http://conf.researchr.org/home/pldi-2016) in Santa Barbara!

## Try Synquid ##

* **Try [in your browser](http://comcom.csail.mit.edu/comcom/#Synquid)!**
* **Build from source:** You will need [stack](https://docs.haskellstack.org/en/stable/README/) and [z3](https://github.com/Z3Prover/z3/releases/tag/z3-4.7.1) version 4.7.1. Clone this repository and then run ```stack setup && stack build``` from its top-level directory.  You can then run synquid using ```stack exec -- synquid [args]```.

## Testimonials ##

![testimonial.png](https://bitbucket.org/repo/qXe57A/images/104717122-testimonial.png)
