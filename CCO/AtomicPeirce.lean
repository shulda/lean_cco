import CCO.Supports
import CCO.RawOrbitals

/-!
# Typed atomic RAW Peirce over actual represented pair colours

Logical identity is the optional real diagonal colour `none`, whereas
`some a` is a diversity atom. The occurrence premise rules out
nonexistent "identity" atoms on a pair of distinct named sorts.
All arguments use real witnesses and pair homogeneity; there is no
SAP, CCO, or exactness assumption.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {i j k : ι}

/-- RAW singleton of an actual optional atomic pair colour. -/
def rawAtomRel (a : Option (S.Atom i j)) : TRel X i j :=
  fun x y => S.colour x y = a

section GroupAction

variable {G : Type*} [Group G]
variable [MulAction G (X i)] [MulAction G (X j)] [MulAction G (X k)]

theorem rawAtomRel_invariant (a : Option (S.Atom i j))
    (hColour : S.ColourInvariant (G := G) (i := i) (j := j)) :
    TRel.Invariant (G := G) (S.rawAtomRel a) := by
  intro g x y hxy
  change S.colour (g • x) (g • y) = a
  rw [hColour g x y]
  exact hxy

/-- Precisely typed RAW Peirce for actual singleton orbitals, including
the *real* diagonal when the code is `none`.  The right side is a
witness for `a ∩ (c ; Bᵒᵖ)`.  Pair homogeneity propagates this one
witness to every pair of colour `c`. -/
theorem raw_atomic_peirce
    (a : Option (S.Atom i j)) (c : Option (S.Atom i k))
    (B : TRel X j k)
    (hcReal : ∃ x : X i, ∃ z : X k, S.colour x z = c)
    (hColour : S.ColourInvariant (G := G) (i := i) (j := j))
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := k))
    (hInvB : TRel.Invariant (G := G) B) :
    (∀ x z, S.rawAtomRel c x z →
      TRel.comp (S.rawAtomRel a) B x z) ↔
      ∃ x y, S.rawAtomRel a x y ∧
        TRel.comp (S.rawAtomRel c) (TRel.converse B) x y := by
  constructor
  · intro h
    obtain ⟨x, z, hz⟩ := hcReal
    obtain ⟨y, hxy, hyz⟩ := h x z hz
    exact ⟨x, y, hxy, z, hz, hyz⟩
  · rintro ⟨x, y, hxy, z, hxz, hyz⟩ u v huv
    have hcol : S.colour x z = S.colour u v :=
      hxz.trans huv.symm
    obtain ⟨g, hgx, hgz⟩ := hPair x u z v hcol
    have hA : S.rawAtomRel a (g • x) (g • y) := by
      change S.colour (g • x) (g • y) = a
      rw [hColour g x y]
      exact hxy
    have hB : B (g • y) (g • z) := hInvB g y z hyz
    exact ⟨g • y, by simpa only [hgx] using hA,
      by simpa only [hgz] using hB⟩

end GroupAction

section PairFlip

variable {G : Type*} [Group G] {i : ι}
variable [MulAction G (X i)]

/-- On a symmetric original sort, actual pair homogeneity gives a
simultaneous group flip. This discharges the pair-flip assumption
of the same-sort RAW commutation/join calculus. -/
theorem pair_flip_of_pair_homogeneous
    (hPair : S.PairHomogeneous (G := G) (i := i) (j := i)) :
    RawSymmetric.PairFlip (G := G) (A := X i) := by
  intro x y
  have hcol : S.colour x y = S.colour y x := by
    cases hc : S.colour x y with
    | none =>
        have htag : (⟨i, x⟩ : Sigma X) = ⟨i, y⟩ :=
          (S.colour_none_iff x y).mp hc
        have hrev : S.colour y x = none :=
          (S.colour_none_iff y x).mpr htag.symm
        exact hrev.symm
    | some a =>
        have hrev : S.colour y x = some (S.conv a) :=
          (S.colour_swap x y a).mp hc
        rw [S.symmetricLoop a] at hrev
        exact hrev.symm
  exact hPair x y y x hcol

end PairFlip

end CCO.AtomicSource
