import SchulzeMethod.StrengthOrder.MinLink

namespace Schulze

variable {Candidate : Type}

structure Path (Candidate) where
  nodes : List Candidate

  lengthGeqTwo : 2 ≤ nodes.length

  noDup : nodes.Nodup


def createPath
    (list : List Candidate)
    (h0 : 2 ≤ list.length)
    (h1 : list.Nodup)
    : Path Candidate :=
{
  nodes := list

  lengthGeqTwo := h0

  noDup := h1
}

namespace Path

theorem nonEmpty
    (p : Path Candidate)
    : p.nodes ≠ [] :=
  (p.nodes.length_pos_iff_ne_nil.mp
      (Nat.lt_of_lt_of_le Nat.zero_lt_two p.lengthGeqTwo))

def length (p : Path Candidate) : ℕ :=
  p.nodes.length

def contains (p : Path Candidate) (c : Candidate) : Prop :=
  c ∈ p.nodes

def From (p : Path Candidate) : Candidate :=
  p.nodes.head p.nonEmpty

def To (p : Path Candidate) : Candidate :=
  p.nodes.getLast p.nonEmpty

private def toLinkStrengthsHelper
    (profile : Profile Candidate)
    (candidates : List Candidate)
    : List LinkStrength :=
  match candidates with
  | [] => []
  | [_] => []
  | a :: b :: tail =>
    newLinkStrength profile a b ::
    toLinkStrengthsHelper profile (b :: tail)


def toLinkStrengths (profile : Profile Candidate)
    (p : Path Candidate) : List LinkStrength :=
  toLinkStrengthsHelper profile p.nodes


private theorem toLinkStrengthsHelper_length
    (profile : Profile Candidate)
    (candidates : List Candidate) :
    (toLinkStrengthsHelper profile candidates).length
      = candidates.length - 1 := by
  induction candidates with
  | nil => simp [toLinkStrengthsHelper]
  | cons a tail =>
      cases tail with
      | nil => simp [toLinkStrengthsHelper]
      | cons b tail =>
          simp [toLinkStrengthsHelper]
          grind

theorem toLinkStrengths_length
    (profile : Profile Candidate)
    (p : Path Candidate) :
    (toLinkStrengths profile p).length =
      p.nodes.length - 1 := by
  exact toLinkStrengthsHelper_length profile p.nodes

theorem toLinkStrengths_nonEmpty
    (profile : Profile Candidate)
    (p : Path Candidate) :
    toLinkStrengths profile p ≠ [] := by
  apply List.length_pos_iff_ne_nil.mp
  apply Nat.lt_of_lt_of_le Nat.zero_lt_one
  rw [toLinkStrengths_length]
  have h : 1 ≤ p.nodes.length - 1 := by
    apply Nat.le_sub_one_of_lt
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2) p.lengthGeqTwo
  exact h


def Strength
    (p : Path Candidate)
    (profile : Profile Candidate)
    (d : StrengthOrder)
    : LinkStrength :=
  minLink d (p.toLinkStrengths profile) (p.toLinkStrengths_nonEmpty profile)

end Path

end Schulze
