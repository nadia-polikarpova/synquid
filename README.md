# Lifty #

This branch is the implementatin of **Lifty** (Liquid Information Flow TYpes), a domain-specific language for data centric applications that manipulate sensitive data.

The major changes relative to Synquid as follows:

- The [PolicyChecker](src/Synquid/PolicyChecker.hs) module implements the fault localization and repair logic.
- The Lifty standard library is in two lifty source files: [Prelude](test/security/taggedio/Prelude.sq) and [Tagged](test/security/taggedio/Tagged.sq) (the latter is where the TIO monad is defined).
- Lifty benchmarks and case studies as [here](test/security/taggedio).

There are other minor changes throughout the code, such as support for maps in the refinement logic.

### Building Instructions ###

1. Download [Z3 4.7.1](https://github.com/Z3Prover/z3/releases) and unpack it into some directory `z3home`
2. Make sure that the Z3 headers (from `z3home/include`) and `libz3.so` (from `z3home/bin`) are visible to your Haskell build. One way to achieve this is to copy them into `/usr/include` and `/usr/lib` respectively; another way is to add the following to  `stack.yaml` at the root of this repository: 
  
```  
  extra-include-dirs:
    - z3-home/include
  extra-lib-dirs:
    - z3-home/bin  
```
3. From the root of this repository, run `stack install`

**Note:** You can also use newer versions of Z3, but you might need to change the value of `extra-deps` in `stack.yaml`. For example, changing it from `z3-4.3.1` to `z3-408.1` works with Z3 4.8.6.
