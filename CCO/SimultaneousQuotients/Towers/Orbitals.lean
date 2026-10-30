import CCO.SimultaneousQuotients.Towers.Flattening
import CCO.RawExact.CanonicalQuotients

/-! Class flattening preserves the COMPLETE original-group orbital language.
This includes quotient equality and all cross-sort orbitals. It needs no
coherent lift of full quotient automorphisms. -/

namespace CCO.SimultaneousQuotients.Towers
open RawExact.CanonicalQuotients

section OneCarrier
variable {G A : Type*} [Group G] [MulAction G A]
variable (J : Setoid A) [Invariant G J]
variable (F : Setoid (Quotient J)) [Invariant G F]

def totalKernelInvariant : Invariant G (totalKernel J F) where
  invariant g x y hxy := by
    change F (g • (Quotient.mk'' x : Quotient J))
      (g • (Quotient.mk'' y : Quotient J))
    exact Invariant.invariant g _ _ hxy

theorem flatten_equivariant (g : G) (q : Quotient F) :
    letI := totalKernelInvariant (G := G) J F
    flatten J F (g • q) = g • flatten J F q := by
  letI := totalKernelInvariant (G := G) J F
  induction q using Quotient.inductionOn with
  | _ r => induction r using Quotient.inductionOn with | _ x => rfl
end OneCarrier

section Pair
variable {G A B : Type*} [Group G] [MulAction G A] [MulAction G B]
variable (J : Setoid A) [Invariant G J] (K : Setoid B) [Invariant G K]
variable (F : Setoid (Quotient J)) [Invariant G F]
variable (L : Setoid (Quotient K)) [Invariant G L]

/-- C46: the canonical class maps preserve and reflect every complete
binary orbital, so canonical orbital atom names correspond bijectively. -/
theorem flatten_orbital_iff (a x : Quotient F) (b y : Quotient L) :
    letI := totalKernelInvariant (G := G) J F
    letI := totalKernelInvariant (G := G) K L
    GroupActions.orbital (G := G) a b x y ↔
      GroupActions.orbital (G := G) (flatten J F a) (flatten K L b)
        (flatten J F x) (flatten K L y) := by
  letI := totalKernelInvariant (G := G) J F
  letI := totalKernelInvariant (G := G) K L
  constructor
  · rintro ⟨g,rfl,rfl⟩
    exact ⟨g,(flatten_equivariant J F g a).symm,
      (flatten_equivariant K L g b).symm⟩
  · rintro ⟨g,hgx,hgy⟩
    refine ⟨g,?_,?_⟩
    · apply (flatten J F).injective
      rw [flatten_equivariant]
      exact hgx
    · apply (flatten K L).injective
      rw [flatten_equivariant]
      exact hgy

/-- The direct orbital is the inverse image, under class flattening, of
the iterated orbital. This is a literal represented block equality. -/
theorem flatten_orbital_block (a : Quotient F) (b : Quotient L) :
    letI := totalKernelInvariant (G := G) J F
    letI := totalKernelInvariant (G := G) K L
    GroupActions.orbital (G := G) a b =
      GroupActions.pullback (flatten J F) (flatten K L)
        (GroupActions.orbital (G := G) (flatten J F a) (flatten K L b)) := by
  letI := totalKernelInvariant (G := G) J F
  letI := totalKernelInvariant (G := G) K L
  funext x y
  exact propext (flatten_orbital_iff J K F L a x b y)

end Pair
end CCO.SimultaneousQuotients.Towers
