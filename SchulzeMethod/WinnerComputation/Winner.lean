import SchulzeMethod.WinnerComputation.WinnerRelation

namespace Schulze

variable {Candidate : Type}

def getWinnersHelper
    [Fintype Candidate]
    [DecidableEq Candidate]
    (remaining : List Candidate)
    (candidates : CandidateSet Candidate)
    (profile : Profile Candidate)
    (d : StrengthOrder)
    : List Candidate :=
  match remaining with
  | [] => []
  | x :: xs => if isWinner candidates profile d x
    then x :: getWinnersHelper xs candidates profile d
    else getWinnersHelper xs candidates profile d


def getWinners
    [Fintype Candidate]
    [DecidableEq Candidate]
    (candidates : CandidateSet Candidate)
    (profile : Profile Candidate)
    (d : StrengthOrder)
    : List Candidate :=
  getWinnersHelper candidates.list candidates profile d

end Schulze
