import Mathlib.Data.Fintype.Defs

import SchulzeMethod.Path.StrongestPath

namespace Schulze

variable {Candidate : Type}

def winsAgainst
    [DecidableEq Candidate]
    (candidates : CandidateSet Candidate)
    (profile : Profile Candidate)
    (d : StrengthOrder)
    (a b : Candidate)
    : Prop :=
  if h : a = b then false else
    d.compare
      (strongestPathStrength candidates profile d a b (by grind only))
      (strongestPathStrength candidates profile d b a (by grind only))

instance
    [DecidableEq Candidate]
    (candidates : CandidateSet Candidate)
    (profile : Profile Candidate)
    (d : StrengthOrder)
    (a b : Candidate)
    : Decidable (winsAgainst candidates profile d a b) := by
  unfold winsAgainst
  infer_instance


def isWinner
    [Fintype Candidate]
    [DecidableEq Candidate]
    (candidates : CandidateSet Candidate)
    (profile : Profile Candidate)
    (d : StrengthOrder)
    (a : Candidate)
    : Prop :=
  (candidates.list.erase a).all
    fun b => ¬ winsAgainst candidates profile d b a

instance
    [Fintype Candidate]
    [DecidableEq Candidate]
    (candidates : CandidateSet Candidate)
    (profile : Profile Candidate)
    (d : StrengthOrder)
    (a : Candidate)
    : Decidable (isWinner candidates profile d a) := by
  unfold isWinner
  infer_instance

end Schulze
