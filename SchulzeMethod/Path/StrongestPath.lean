import SchulzeMethod.Path.AllPathsPermutation
import SchulzeMethod.StrengthOrder.MaxLink

namespace Schulze

variable {Candidate : Type}

def strongestPathStrength
    [DecidableEq Candidate]
    (candidates : CandidateSet Candidate)
    (profile : Profile Candidate)
    (d : StrengthOrder)
    (From To : Candidate)
    (h : From ≠ To)
    : LinkStrength :=
  let allPaths := allPaths From To candidates h
  let pathStrengths := allPaths.map (fun p => p.Strength profile d)
  maxLink d pathStrengths (by simp[pathStrengths, allPaths, allPaths_nonEmpty])


end Schulze
