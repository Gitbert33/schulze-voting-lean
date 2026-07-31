import Mathlib.Data.Multiset.Count

import SchulzeMethod.Input.Profile

namespace Schulze

variable {Candidate : Type}

def pairwisePreference
    (profile : Profile Candidate)
    (a b : Candidate) : ℕ :=
  profile.countP
    (fun ballot => ballot.prefers a b)

end Schulze
