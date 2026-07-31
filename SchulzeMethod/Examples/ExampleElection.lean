import Mathlib.Data.Finset.Insert

import SchulzeMethod.SchulzeMethod
import SchulzeMethod.StrengthOrder.Margin

namespace Schulze

inductive MyCandidate
  | A
  | B
  | C
  | D
  deriving DecidableEq, Repr

open MyCandidate

instance : Fintype MyCandidate where
  elems := {A, B, C, D}
  complete := by intro x; cases x <;> trivial


def exampleElection : Except String (List MyCandidate) :=
  let candidates := [A, B, C, D]
  let ballots := [
    [A, B, C, D], [A, B, C, D], [A, B, C, D],
    [A, C, B, D], [A, C, B, D],
    [B, C, D, A], [B, C, D, A],
    [B, D, A, C],
    [C, A, B, D],
    [D, C, B, A]
  ]
  schulzeMethod margin candidates CandidateSet.fromList ballots Profile.fromLists


#eval exampleElection


end Schulze
