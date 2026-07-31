import Mathlib.Data.List.Basic

namespace Schulze

variable {Candidate : Type}

structure CandidateSet (Candidate) where
  list : List Candidate

  lengthGeqTwo : 2 ≤ list.length

  nodup : list.Nodup


namespace CandidateSet

def fromList
    [DecidableEq Candidate]
    (l : List Candidate) :
    Except String (CandidateSet Candidate) :=
  if hLen : 2 ≤ l.length then
    if hNoDup : l.Nodup then
      Except.ok ⟨l, hLen, hNoDup⟩
    else
      Except.error "Candidate list contains duplicates"
  else
    Except.error "Candidate list must contain at least two candidates"

def length (candidates : CandidateSet Candidate) : ℕ :=
  candidates.list.length

def contains (candidates : CandidateSet Candidate) (c : Candidate) : Prop :=
  c ∈ candidates.list

theorem nonEmpty
    (candidates : CandidateSet Candidate)
    : candidates.list ≠ [] :=
  (candidates.list.length_pos_iff_ne_nil.mp
      (Nat.lt_of_lt_of_le Nat.zero_lt_two candidates.lengthGeqTwo))

end CandidateSet

end Schulze
