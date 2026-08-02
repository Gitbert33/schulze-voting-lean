import Mathlib.Data.Finset.Insert

import SchulzeMethod
import SchulzeMethod.StrengthOrder.Margin

namespace Schulze

inductive Candidate
  | a
  | b
  | c
  | d
  deriving DecidableEq, Repr

open Candidate

instance : Fintype Candidate where
  elems := {a, b, c, d}
  complete := by intro x; cases x <;> trivial


def exampleElection : Except String (List Candidate) :=
  let candidates := [a, b, c, d]
  let ballots := [
    [b, c], [b, c], [b, c],
    [c, d, a], [c, d, a],
    [a, b], [a, b],
    [d], [d],
    [d, c]
  ]
  schulzeMethod margin candidates CandidateSet.fromList ballots Profile.fromLists


#eval exampleElection

/-
Output of #eval-statement:
  Except.ok [Schulze.Candidate.b]
-/


end Schulze
