import SchulzeMethod.Input.CandidateSet

namespace Schulze

variable {Candidate : Type}

structure Ballot (Candidate) where
  prefers : Candidate → Candidate → Prop

  prefersDecidable : DecidableRel prefers

  isStrictWeakOrder : IsStrictWeakOrder Candidate prefers


instance (ballot : Ballot Candidate) :
    DecidableRel ballot.prefers :=
  ballot.prefersDecidable


namespace Ballot

def fromList
    [DecidableEq Candidate]
    (l : List Candidate)
    (candidates : CandidateSet Candidate)
    : Except String (Ballot Candidate) :=
  if hValid : l.all (fun a => a ∈ candidates.list) then
    if hNoDup : l.Nodup then
      let pref := fun a b =>
        if a ∈ l then
          if b ∈ l then
            l.idxOf a < l.idxOf b
          else True
        else False
      Except.ok {
        prefers := pref
        prefersDecidable := inferInstance
        isStrictWeakOrder := {
          irrefl := by
            intro x hx
            dsimp [pref] at hx
            split_ifs at hx
            omega
          trans := by
            intro x y z hxy hyz
            dsimp [pref] at *
            split_ifs at *
            omega
          incomp_trans := by
            intro x y z hxy hyz
            dsimp [pref] at *
            split_ifs at * <;> try contradiction
            · omega
            · omega
        }
      }
    else
      Except.error "Candidate list contains duplicates"
  else
    Except.error "Candidate list includes invalid candidates"

theorem prefers_equalsIndexComparison
    [DecidableEq Candidate]
    {l : List Candidate} {candidates : CandidateSet Candidate} {b : Ballot Candidate}
    (h_ok : Ballot.fromList l candidates = Except.ok b)
    {x y : Candidate} (hx : x ∈ l) (hy : y ∈ l)
    : b.prefers x y ↔ l.idxOf x < l.idxOf y := by
  unfold fromList at h_ok
  split_ifs at h_ok with hValid hNoDup
  · injection h_ok with h_eq
    subst h_eq
    dsimp [Ballot.prefers]
    split_ifs
    rfl

theorem prefers_listedCandidates
    [DecidableEq Candidate]
    {l : List Candidate} {candidates : CandidateSet Candidate} {b : Ballot Candidate}
    (h_ok : Ballot.fromList l candidates = Except.ok b)
    {x y : Candidate} (hx : x ∈ l) (hy : y ∉ l)
    : b.prefers x y := by
  unfold fromList at h_ok
  split_ifs at h_ok with hValid hNoDup
  · injection h_ok with h_eq
    subst h_eq
    dsimp [Ballot.prefers]
    split_ifs

theorem prefers_notListedCandidates
    [DecidableEq Candidate]
    {l : List Candidate} {candidates : CandidateSet Candidate} {b : Ballot Candidate}
    (h_ok : Ballot.fromList l candidates = Except.ok b)
    {x y : Candidate} (hx : x ∉ l) :
    ¬ b.prefers x y := by
  unfold fromList at h_ok
  split_ifs at h_ok with hValid hNoDup
  · injection h_ok with h_eq
    subst h_eq
    dsimp [Ballot.prefers]
    split_ifs
    trivial

end Ballot

end Schulze
