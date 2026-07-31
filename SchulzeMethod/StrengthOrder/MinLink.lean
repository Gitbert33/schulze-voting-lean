import SchulzeMethod.StrengthOrder.StrengthOrder

namespace Schulze

private def minLinkHelper (d : StrengthOrder)
    (l : List LinkStrength) (min : LinkStrength)
    : LinkStrength :=
  match l with
  | [] => min
  | head :: tail =>
    minLinkHelper d tail
    (if d.compare min head then head else min)

def minLink (d : StrengthOrder)
    (l : List LinkStrength) (h : l ≠ [])
    : LinkStrength :=
  match l with
  | head :: tail => minLinkHelper d tail head


end Schulze
