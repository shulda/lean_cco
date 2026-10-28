import CCO.StrongExact.PCConverse

/-!
# C13 boundary: two distinct formal roots, no intermediate vertex

On the genuine two-vertex off-diagonal network, every PC support test
through a third vertex is vacuous. Hence the initial singleton/Top
domains are already fixed, in particular the unrecorded edge yields
exactly the ORIGINAL typed diversity Top, not a fake identity menu.
This simple instance independently guards the empty-profile-list
case in the later canonical PC path formula.

No SAP, CCO, source homogeneity or existence of a diversity atom is
needed to prove the Boolean identity.
-/

universe u v w

namespace CCO.StrongPC

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource ι X}
variable (D : PartialDiagram S (Fin 2))

/-- There cannot be a third distinct formal vertex among two roots. -/
private theorem no_third (p : DistinctPair (Fin 2)) (z : Fin 2)
    (hx : p.src ≠ z) (hy : z ≠ p.dst) : False := by
  have hp : p.src.val ≠ p.dst.val := by
    intro h
    exact p.ne (Fin.ext h)
  have hz : z.val = p.src.val ∨ z.val = p.dst.val := by
    have h1 := p.src.isLt
    have h2 := p.dst.isLt
    have h3 := z.isLt
    omega
  rcases hz with hleft | hright
  · exact hx (Fin.ext hleft.symm)
  · exact hy (Fin.ext hright)

/-- The synchronous STRONG PC operator acts identically on every
two-root typed Boolean network. -/
theorem step_two_roots (N : Network D) : step D N = N := by
  funext p
  apply Set.Subset.antisymm
  · exact step_refines D N p
  · intro a ha
    refine ⟨ha, ?_⟩
    intro z hxz hzy
    exact False.elim (no_third p z hxz hzy)

/-- There is no pruning at any finite iteration on just two roots. -/
theorem iterate_two_roots (N : Network D) (n : Nat) :
    iterate D N n = N := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change step D (iterate D N n) = N
      rw [ih]
      exact step_two_roots D N

/-- C13 empty-path-family boundary: the canonical final domains of a
two-root partial diagram equal its initial old singleton/Top menus. -/
theorem fixedNetwork_two_roots :
    fixedNetwork D = initial D := by
  change iterate D (initial D) (fixedIndex D) = initial D
  exact iterate_two_roots D (initial D) (fixedIndex D)

end CCO.StrongPC
