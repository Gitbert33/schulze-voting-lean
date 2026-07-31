import Mathlib.Data.Multiset.Defs

import SchulzeMethod.Input.Ballot

namespace Schulze

variable {Candidate : Type}

abbrev Profile (Candidate : Type) :=
  Multiset (Ballot Candidate)


namespace Profile

def fromLists
    [DecidableEq Candidate]
    (lists : List (List Candidate))
    (candidates : CandidateSet Candidate)
    : Except String (Profile Candidate) :=
  let ballots := lists.filterMap fun l =>
    match Ballot.fromList l candidates with
    | Except.ok b => some b
    | Except.error _ => none
  Except.ok (Multiset.ofList ballots)

def fromListsStrict
    [DecidableEq Candidate]
    (lists : List (List Candidate))
    (candidates : CandidateSet Candidate)
    : Except String (Profile Candidate) := do
  let ballots ← lists.mapM (fun l => Ballot.fromList l candidates)
  return Multiset.ofList ballots

end Profile

end Schulze
