# schulze-voting-lean

Implementation of the Schulze voting method in Lean 4.

This repository contains the source code developed as part of the Bachelor's thesis:

> **Formalization and Implementation of the Schulze Voting Method in Lean**

The project provides a modular and executable implementation of Markus Schulze's voting method in the Lean 4 theorem prover. The implementation closely follows the original mathematical specification while adapting it where necessary to obtain a constructive and executable formalization.

## Features

- Formal representation of the mathematical concepts used by the Schulze method in Lean 4
- Executable implementation of the complete winner computation
- Modular project structure
- Reuse of Lean's Mathlib wherever possible
- Abstract interface for different link comparison strategies (`StrengthOrder`)
- Implementation of the Schulze's *margin* comparison
- Conversion functions from user-friendly inputs to the formal data structures
- Example election

## Project Structure

```text
├── SchulzeMethod
│
└── SchulzeMethod/
    ├── Input/
    │   ├── CandidateSet
    │   ├── Ballot
    │   └── Profile
    │
    ├── LinkStrength/
    │   ├── PairwisePreference
    │   └── LinkStrength
    │
    ├── StrengthOrder/
    │   ├── StrengthOrder
    │   ├── MinLink
    │   ├── MaxLink
    │   └── Margin
    │
    ├── Path/
    │   ├── Path
    │   ├── AllPathsPermutation
    │   └── StrongestPath
    │
    ├── WinnerComputation/
    │   ├── WinnerRelation
    │   └── Winner
    │
    └── Examples/
        └── ExampleElection
```


## References

- Markus Schulze. *A New Monotonic, Clone-Independent, Reversal Symmetric, and Condorcet-Consistent Single-Winner Election Method*. 2011.
- Lean 4: https://lean-lang.org/
- Mathlib: https://github.com/leanprover-community/mathlib4