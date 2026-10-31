import CCO.TerminalLattice.QuotientPowerSemigroup
import CCO.RawExact.CanonicalQuotients
import CCO.ParityHasse.Original.OrbitalAlgebra

/-!
# B050 C13: old full-group quotient orbitals and FULL-cover transfer

All quotient motions are induced by the *same* original ambient group G
acting on the entire named-sorted source. We never enlarge G to the
automorphisms of an induced one-sort reduct. An original FULL cover
also controls every G-invariant quotient equivalence via literal
pullback along the ORIGINAL quotient map.

These are the required source-level structural prerequisites to the
quotient-graph connectedness/parity argument; no CCO or SAP is used.
-/

universe u v w t
namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- The actual original action on classes of a FULL invariant
equivalence, derived from old `HomogeneousSource` rather than an
independent quotient-action axiom. -/
@[instance_reducible] def originalQuotientAction (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) : MulAction G (Quotient J.val) := by
  letI : RawExact.CanonicalQuotients.Invariant G J.val :=
    ⟨colourInvariant_groupInvariant S H J.2⟩
  infer_instance

/-- Literal quotient projection commutes with the SAME old G motion. -/
theorem originalQuotient_mk_smul (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) :
    letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
    ∀ (g : G) (x : X i),
      g • (Quotient.mk J.val x) = Quotient.mk J.val (g • x) := by
  intro g x
  rfl

/-- A complete OLD quotient orbital is the image of one actual pair
under the original full group. There is no second quotient automorphism
group and no arbitrary fine subset of the orbital. -/
def originalQuotientOrbital {i : ι} (J : ColourEq S i)
    (a b : X i) : Quotient J.val → Quotient J.val → Prop :=
  fun q r => ∃ g : G,
    Quotient.mk J.val (g • a) = q ∧
    Quotient.mk J.val (g • b) = r

theorem originalQuotientOrbital_root {i : ι}
    (J : ColourEq S i) (a b : X i) :
    originalQuotientOrbital S (G := G) J a b
      (Quotient.mk J.val a) (Quotient.mk J.val b) := by
  exact ⟨1, by simp, by simp⟩

/-- A complete quotient orbital is symmetric because same-sort fine
pairs are symmetric under one old group element. -/
theorem originalQuotientOrbital_symmetric
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b : X i) :
    ∀ q r, originalQuotientOrbital S (G := G) J a b q r →
      originalQuotientOrbital S (G := G) J a b r q := by
  intro q r h
  obtain ⟨g, hgq, hgr⟩ := h
  obtain ⟨k, hka, hkb⟩ := S.pair_flip_of_homogeneous H a b
  refine ⟨g*k, ?_, ?_⟩
  · change Quotient.mk J.val ((g*k) • a) = r
    rw [mul_smul, hka]
    exact hgr
  · change Quotient.mk J.val ((g*k) • b) = q
    rw [mul_smul, hkb]
    exact hgq

/-- Complete quotient orbitals are equivariant under the derived old
quotient action, not automatically under any larger reduct group. -/
theorem originalQuotientOrbital_invariant
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b : X i) :
    letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
    ∀ (g : G) q r,
      originalQuotientOrbital S (G := G) J a b q r →
      originalQuotientOrbital S (G := G) J a b (g • q) (g • r) := by
  letI : MulAction G (Quotient J.val) := originalQuotientAction S H J
  intro g q r
  rintro ⟨k, hkq, hkr⟩
  refine ⟨g*k, ?_, ?_⟩
  · change Quotient.mk J.val ((g*k) • a) = g • q
    rw [mul_smul]
    have h := congrArg (fun q : Quotient J.val => g • q) hkq
    change Quotient.mk J.val (g • (k • a)) = g • q at h
    exact h
  · change Quotient.mk J.val ((g*k) • b) = g • r
    rw [mul_smul]
    have h := congrArg (fun q : Quotient J.val => g • q) hkr
    change Quotient.mk J.val (g • (k • b)) = g • r at h
    exact h

/-- Non-J root endpoints make the complete quotient orbital genuinely
irreflexive. In particular quotient diagonal is not a graph edge. -/
theorem originalQuotientOrbital_irreflexive
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b : X i)
    (hab : ¬ J a b) :
    ∀ q, ¬ originalQuotientOrbital S (G := G) J a b q q := by
  rintro q ⟨g, hgq, hgr⟩
  have hJ : J (g • a) (g • b) :=
    Quotient.exact (hgq.trans hgr.symm)
  have hback :=
    colourInvariant_groupInvariant S H J.2 g⁻¹ (g • a) (g • b) hJ
  exact hab (by simpa only [inv_smul_smul] using hback)

/-- The quotient-to-upper-class map respects the actual original
equivalence J ≤ K, without any quotient action assumption. -/
def originalQuotientToUpper {i : ι} (J K : ColourEq S i)
    (hJK : J ≤ K) : Quotient J.val → Quotient K.val :=
  Quotient.map id (fun {x y} h => hJK h)

theorem originalQuotientToUpper_mk {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K) (x : X i) :
    originalQuotientToUpper S J K hJK (Quotient.mk J.val x) =
      Quotient.mk K.val x := rfl

/-- True equivalence on J-classes given by the original K quotient
map; this relation includes the QUOTIENT diagonal. -/
def originalUpperSetoid {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K) : Setoid (Quotient J.val) where
  r := fun q r =>
    originalQuotientToUpper S J K hJK q =
      originalQuotientToUpper S J K hJK r
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

theorem originalUpperSetoid_mk {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K)
    (x y : X i) :
    originalUpperSetoid S J K hJK
      (Quotient.mk J.val x) (Quotient.mk J.val y) ↔ K x y := by
  change Quotient.mk K.val x = Quotient.mk K.val y ↔ K x y
  exact Quotient.eq

/-- Every OLD quotient-invariant equivalence pulls back to a genuine
element of the FULL original invariant-equivalence lattice, not to
a merely exact/represented sublattice. -/
def originalQuotientEqToColour
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (E : Setoid (Quotient J.val))
    (hE : letI : MulAction G (Quotient J.val) :=
      originalQuotientAction S H J
      ∀ (g : G) q r, E q r → E (g • q) (g • r)) :
    ColourEq S i := by
  letI : MulAction G (Quotient J.val) :=
    originalQuotientAction S H J
  refine ⟨Setoid.comap (Quotient.mk J.val) E, ?_⟩
  apply groupInvariant_colourInvariant S H
  intro g x y hxy
  have h := hE g (Quotient.mk J.val x) (Quotient.mk J.val y) hxy
  simpa [Setoid.comap, originalQuotient_mk_smul S H J] using h

/-- A FULL original cover has no intermediate G-invariant quotient
equivalence: its old pullback is literally J or literally K.
This is the source-13 firewall excluding a synthetic quotient cover. -/
theorem originalFullCover_quotient_eq_or_upper
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ⋖ K)
    (E : Setoid (Quotient J.val))
    (hE : letI : MulAction G (Quotient J.val) :=
      originalQuotientAction S H J
      ∀ (g : G) q r, E q r → E (g • q) (g • r))
    (hEK : ∀ x y : X i,
      E (Quotient.mk J.val x) (Quotient.mk J.val y) → K x y) :
    (∀ x y : X i,
      E (Quotient.mk J.val x) (Quotient.mk J.val y) ↔ J x y) ∨
    (∀ x y : X i,
      E (Quotient.mk J.val x) (Quotient.mk J.val y) ↔ K x y) := by
  let P : ColourEq S i := originalQuotientEqToColour S H J E hE
  have hP (x y : X i) :
      P x y ↔ E (Quotient.mk J.val x) (Quotient.mk J.val y) := by
    simp [P, originalQuotientEqToColour, Setoid.comap]
  have hJP : J ≤ P := by
    intro x y hxy
    apply (hP x y).2
    exact Quotient.sound hxy ▸ E.refl _
  have hPK : P ≤ K := by
    intro x y hxy
    exact hEK x y ((hP x y).1 hxy)
  rcases hJK.eq_or_eq hJP hPK with hh | hh
  · left
    intro x y
    have hv : P x y ↔ J x y := by rw [hh]
    exact (hP x y).symm.trans hv
  · right
    intro x y
    have hv : P x y ↔ K x y := by rw [hh]
    exact (hP x y).symm.trans hv

end CCO.TerminalLattice
