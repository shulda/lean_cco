import CCO.StrongExact.ThetaGraphBridge
import CCO.StrongExact.ThetaWordLineReadout

/-!
# C07: homomorphic readout of every original typed theta branch

For every genuinely specified diversity letter the selected theta
diagram stores exactly the old letter after its two necessary sort
transports. A homomorphism respecting these old edges therefore
realizes every private positive word between the SAME shared roots.
No injectivity, CCO, SAP, or pseudoidentity is assumed.
-/

universe u v w a

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Retype BOTH actual real endpoints and their old diversity atom
using exactly the same two original named-sort equalities. -/
private theorem colour_cast_both
    {s t s' t' : ι}
    (hs : s = s') (ht : t = t')
    (a : S.Atom s' t') (x : X s) (y : X t)
    (hxy : S.colour x y =
      some (hs.symm ▸ (ht.symm ▸ a))) :
    S.colour (hs ▸ x) (ht ▸ y) = some a := by
  cases hs
  cases ht
  simpa using hxy

private theorem cast_eq_mp {s t : ι} (h : s = t) (x : X s) :
    (h ▸ x) = Eq.mp (congrArg X h) x := by
  cases h
  rfl

private theorem cast_at_equal_vertex_mp
    {α : Type a} (sort : α → ι)
    (point : ∀ x : α, X (sort x))
    {x y : α} {t : ι}
    (hxy : x = y) (hs : sort x = t) (ht : t = sort y) :
    Eq.mp (congrArg X ht) (hs ▸ point x) = point y := by
  cases hxy
  cases hs
  cases ht
  rfl

/-!
The complete branch-word readout is a separate pending proof. The
previous attempts are retained in Git history, not certified as C07.
-/

end CCO.StrongExact
