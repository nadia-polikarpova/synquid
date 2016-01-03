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

* **Try [in your browser](http://ec2-52-25-255-117.us-west-2.compute.amazonaws.com/comcom/#Synquid)!**
* **Build from sources:** you will need recent versions of [GHC and Cabal](https://www.haskell.org/platform/) (we are using GHC 7.10.2 and Cabal 1.22.6.0). Clone this repository and then run ```cabal install``` from its top-level directory.