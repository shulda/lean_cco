import CCO.TerminalLattice.FullCoverUniformPowers
import CCO.TerminalLattice.QuotientPowerSemigroup

/-!
# B050 C18: uniform quotient powers lift to pinned old real diversity pairs

This combines C17's ONE quotient-walk threshold, including all quotient
diagonal pairs, with the earlier C12 positive-length semigroup identity
whose fresh-fibre hypothesis is ACTUALLY derived from the old source SAP.

The result is equality of full OLD real diversity predicates (NOT yet
an identification with original fine-atom `S.product` profiles). No
global NR2, CCO, exactness, distributivity or mixed-sort groupoid is
imported; only an ORIGINAL full invariant J⋖K cover, J>Id, original
homogeneous SAP, and local [K:J] != 2.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- C18 RELATION-LEVEL bridge: for one complete OLD quotient orbital,
every positive old power after the C17 threshold is EXACTLY the actual
original K-diversity relation, including old x≠y in the same J-class.

The word `power` is represented by genuine positive strong relation
composition, never by an artificial identity factor. A separate
fine-colour lemma will turn this into the source's literal STRONG
atomic-palette power `T^{star n}`. -/
theorem originalQuotient_uniform_strong_relation_powers
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (hNotTwo : relativeIndex J.val K.val a ≠ 2) :
    ∃ N : Nat, 0 < N ∧
      ∀ n, N ≤ n →
        strongDiversityPower
          (quotientDiversity J.val
            (originalQuotientOrbital S (G := G) J a b)) (n-1) =
          (fun x y : X i => x ≠ y ∧ K x y) := by
  obtain ⟨N, hN, hUniform⟩ :=
    originalQuotient_uniform_full_powers S H J K hJK
      a b hab hne hNotTwo
  refine ⟨N, hN, ?_⟩
  intro n hn
  have hnPos : 0 < n := lt_of_lt_of_le hN hn
  have hnEq : n-1+1 = n := by omega
  rw [original_quotient_strongPower S H sap J hJ
    (originalQuotientOrbital S (G := G) J a b) (n-1),
    hnEq]
  funext x y
  apply propext
  constructor
  · rintro ⟨hxy, hWalk⟩
    have hKquot :=
      (hUniform n hn (Quotient.mk J.val x) (Quotient.mk J.val y)).mp hWalk
    exact ⟨hxy, (originalUpperSetoid_mk S J K hJK.le x y).mp hKquot⟩
  · rintro ⟨hxy, hK⟩
    refine ⟨hxy, ?_⟩
    exact (hUniform n hn (Quotient.mk J.val x) (Quotient.mk J.val y)).mpr
      ((originalUpperSetoid_mk S J K hJK.le x y).mpr hK)

end CCO.TerminalLattice
