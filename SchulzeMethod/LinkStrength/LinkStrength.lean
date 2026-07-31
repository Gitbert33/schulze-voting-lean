import SchulzeMethod.LinkStrength.PairwisePreference

namespace Schulze

variable {Candidate : Type}

structure LinkStrength where
  support : ℕ
  opposition : ℕ


def newLinkStrength
    (profile : Profile Candidate)
    (a b : Candidate) :
    LinkStrength :=
{
  support := pairwisePreference profile a b
  opposition := pairwisePreference profile b a
}

end Schulze
