import SchulzeMethod.WinnerComputation.Winner

namespace Schulze

variable {Candidate : Type}

def schulzeMethod {α β}
    [Fintype Candidate]
    [DecidableEq Candidate]
    (d : StrengthOrder)
    (candidates : α)
    (parseCandidates : α → Except String (CandidateSet Candidate))
    (ballots : β)
    (parseProfile : β → CandidateSet Candidate → Except String (Profile Candidate))
    : Except String (List Candidate) := do
  let candidateSet ← parseCandidates candidates
  let profile ← parseProfile ballots candidateSet
  return getWinners candidateSet profile d

end Schulze
