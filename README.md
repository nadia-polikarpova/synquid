# Lifty #

This branch is the implementatin of **Lifty** (Liquid Information Flow TYpes), a domain-specific language for data centric applications that manipulate sensitive data.

The major changes relative to Synquid as follows:

- The [PolicyChecker](src/Synquid/PolicyChecker.hs) module implements the fault localization and repair logic.
- The Lifty standard library is in two lifty source files: [Prelude](test/security/taggedio/Prelude.sq) and [Tagged](test/security/taggedio/Tagged.sq) (the latter is where the TIO monad is defined).
- Lifty benchmarks and case studies as [here](test/security/taggedio).

There are other minotr changes throughout the code, such as support for maps in the refinement logic.
