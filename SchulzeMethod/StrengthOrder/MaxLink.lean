import SchulzeMethod.StrengthOrder.StrengthOrder

namespace Schulze

private def maxLinkHelper (d : StrengthOrder)
    (l : List LinkStrength) (max : LinkStrength)
    : LinkStrength :=
  match l with
  | [] => max
  | head :: tail =>
    maxLinkHelper d tail
    (if d.compare head max then head else max)

def maxLink (d : StrengthOrder)
    (l : List LinkStrength) (h : l ≠ [])
    : LinkStrength :=
  match l with
  | head :: tail => maxLinkHelper d tail head

end Schulze
