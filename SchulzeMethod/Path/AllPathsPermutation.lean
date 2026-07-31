import Mathlib.Data.List.Permutation

import SchulzeMethod.Path.Path

namespace Schulze

variable {Candidate : Type}

private def candidatesWithoutFrom
    [DecidableEq Candidate]
    (candidates : List Candidate)
    (From : Candidate)
    : List Candidate :=
  candidates.filter (· ≠ From)

private def allPermutations
    (candidates : List Candidate)
    : List (List Candidate) :=
  candidates.permutations

private def prefixBefore
    [DecidableEq Candidate]
    (To : Candidate)
    : List Candidate → List Candidate
  | [] => []
  | x :: xs =>
      if x = To then
        []
      else
        x :: prefixBefore To xs

theorem ToNotInPrefixBefore
    [DecidableEq Candidate]
    (To : Candidate)
    (l : List Candidate) :
    To ∉ prefixBefore To l := by
  induction l <;> aesop (add simp prefixBefore)

theorem prefixBeforeSubset
    [DecidableEq Candidate]
    {To : Candidate}
    {l : List Candidate}
    : (prefixBefore To l) ⊆ l := by
  induction l <;> aesop (add simp prefixBefore)

theorem prefixBeforeNoAddedElements
    [DecidableEq Candidate]
    {From To : Candidate}
    {l : List Candidate}
    (h : From ∉ l) :
    From ∉ prefixBefore To l := by
  induction l <;> simp_all only [List.mem_cons, not_or, prefixBefore,
  List.mem_ite_nil_left, not_false_eq_true, or_self, and_false]

theorem prefixBeforeNodup
    [DecidableEq Candidate]
    {To : Candidate}
    {l : List Candidate}
    (h : l.Nodup) :
    (prefixBefore To l).Nodup := by
  induction l with
  | nil =>
      simp [prefixBefore]
  | cons x xs ih =>
      by_cases hx : x = To
      · simp [prefixBefore, hx]
      · simp only [List.nodup_cons, hx, not_false_eq_true, prefixBefore, ↓reduceIte] at *
        constructor
        · exact prefixBeforeNoAddedElements h.left
        · exact ih h.right

private def addFromAndTo
    (list : List Candidate)
    (From To : Candidate)
    : List Candidate :=
  From :: list ++ [To]

theorem addFromAndToNoDup
    (middle : List Candidate)
    (From To : Candidate)
    (h0 : middle.Nodup)
    (h1 : From ∉ middle)
    (h2 : To ∉ middle)
    (h3 : From ≠ To) :
    (addFromAndTo middle From To).Nodup := by
  simp only [addFromAndTo, List.cons_append, List.nodup_cons, List.mem_append, h1, List.mem_cons,
    List.not_mem_nil, or_false, false_or, List.nodup_append, h0, not_false_eq_true, List.nodup_nil,
    and_self, ne_eq, forall_eq, true_and]
  simp_all only [ne_eq, not_false_eq_true, true_and]
  intro a a_1
  apply Aesop.BuiltinRules.not_intro
  intro a_2
  subst a_2
  simp_all only

theorem lengthFromMiddleTo
    (middle : List Candidate)
    (From To : Candidate) :
    2 ≤ (From :: middle ++ [To]).length :=
    by simp

def allSequences
    [DecidableEq Candidate]
    (From To : Candidate)
    (candidates : List Candidate) : List (List Candidate) :=
  let withoutFrom := candidatesWithoutFrom candidates From
  let permutations := allPermutations withoutFrom
  permutations.map (fun perm => addFromAndTo (prefixBefore To perm) From To)

theorem allSequences_nodup
    [DecidableEq Candidate]
    (From To : Candidate)
    (candidates : List Candidate)
    (h_nodup : candidates.Nodup)
    (h_ne : From ≠ To) :
    ∀ seq ∈ allSequences From To candidates, seq.Nodup := by
  intro seq h_in
  simp only [allSequences, allPermutations, candidatesWithoutFrom,
            List.mem_map, List.mem_permutations] at h_in
  rcases h_in with ⟨perm, h_perm_in, rfl⟩
  have h_perm : (List.filter (· ≠ From) candidates).Perm perm := h_perm_in.symm
  have h_perm_nodup : perm.Nodup := by
    have h_wf_nodup : (candidates.filter (· ≠ From)).Nodup := h_nodup.filter (· ≠ From)
    exact List.Perm.nodup h_perm h_wf_nodup
  apply addFromAndToNoDup
  · exact prefixBeforeNodup h_perm_nodup
  · have h_from_not_in_perm : From ∉ perm := by
      rw [← List.Perm.mem_iff h_perm]
      simp
    intro h_mem
    exact h_from_not_in_perm (prefixBeforeSubset h_mem)
  · exact ToNotInPrefixBefore To perm
  · exact h_ne

theorem allSequences_length
    [DecidableEq Candidate]
    (From To : Candidate)
    (candidates : List Candidate) :
    ∀ seq ∈ allSequences From To candidates, 2 ≤ seq.length := by
  intro seq h_in
  simp only [allSequences, allPermutations, candidatesWithoutFrom, ne_eq, decide_not,
    List.mem_map, List.mem_permutations] at h_in
  rcases h_in with ⟨perm, _, rfl⟩
  exact lengthFromMiddleTo (prefixBefore To perm) From To


def allPaths
    [DecidableEq Candidate]
    (From To : Candidate)
    (candidates : CandidateSet Candidate)
    (h : From ≠ To) : List (Path Candidate) :=
  let sequences := allSequences From To candidates.list
  have h_all_nodup := allSequences_nodup From To candidates.list candidates.nodup h
  have h_all_length := allSequences_length From To candidates.list
  sequences.attach.map (fun ⟨seq, h_seq_in⟩ =>
    createPath seq
      (h_all_length seq h_seq_in)
      (h_all_nodup seq h_seq_in)
  )

private theorem allPermutations_nonEmpty
    (l : List Candidate)
    : allPermutations l ≠ [] := by
  rw [allPermutations]
  exact List.ne_nil_of_mem (List.mem_permutations.mpr (List.Perm.refl l))


theorem allPaths_nonEmpty
    [DecidableEq Candidate]
    (From To : Candidate)
    (candidates : CandidateSet Candidate)
    (h : From ≠ To) :
    allPaths From To candidates h ≠ [] := by
  simp only [allPaths, allSequences, ne_eq, List.map_eq_nil_iff,
    List.attach_eq_nil_iff]
  exact allPermutations_nonEmpty (candidatesWithoutFrom candidates.list From)


end Schulze
