import SchulzeMethod.StrengthOrder.StrengthOrder

namespace Schulze

private def linkToMargin (x : LinkStrength) : ℤ :=
  (x.support : ℤ) - (x.opposition : ℤ)

private def marginCompare (x y : LinkStrength) : Prop :=
  linkToMargin x > linkToMargin y

instance : DecidableRel marginCompare := by
  intro x y
  dsimp [marginCompare]
  infer_instance

def margin : StrengthOrder where
  compare := marginCompare

  compareDecidable := inferInstance

  isStrictWeakOrder := {
    irrefl := by
      intro x hx
      dsimp [marginCompare] at hx
      omega
    trans := by
      intro x y z hxy hyz
      dsimp [marginCompare] at *
      omega
    incomp_trans := by
      intro x y z hxy hyz
      dsimp [marginCompare] at *
      omega
  }

end Schulze
