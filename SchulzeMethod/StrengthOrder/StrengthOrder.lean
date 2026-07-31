import SchulzeMethod.LinkStrength.LinkStrength

namespace Schulze

structure StrengthOrder where
  compare : LinkStrength → LinkStrength → Prop

  compareDecidable : DecidableRel compare

  isStrictWeakOrder : IsStrictWeakOrder LinkStrength compare


instance (d : StrengthOrder) :
    DecidableRel d.compare :=
  d.compareDecidable

end Schulze
