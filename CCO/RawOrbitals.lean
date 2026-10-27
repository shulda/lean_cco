import CCO.GroupActions
import CCO.TypedRelation

/-!
# Elementary RAW orbital algebra

All compositions here include genuine equality. The atom Peirce statement
uses *actual pair orbits*, with no extra triangle-closure hypothesis.
Commutation and equivalence joins are only for a single original sort
where every pair has a simultaneous flip in the acting group.
-/

universe u v

namespace CCO.TRel

variable {ι : Type u} {X : ι → Type v}
variable {i j k : ι}
variable {G : Type*} [Group G]
variable [MulAction G (X i)] [MulAction G (X j)]
variable [MulAction G (X k)]

theorem invariant_comp (R : TRel X i j) (S : TRel X j k)
    (hR : Invariant (G := G) R) (hS : Invariant (G := G) S) :
    Invariant (G := G) (comp R S) := by
  rintro g x z ⟨y, hxy, hyz⟩
  exact ⟨g • y, hR g x y hxy, hS g y z hyz⟩

theorem invariant_converse (R : TRel X i j)
    (h : Invariant (G := G) R) :
    Invariant (G := G) (converse R) := by
  intro g y x hxy
  exact h g x y hxy

theorem comp_nonempty_of_serial (R : TRel X i j) (S : TRel X j k)
    (hR : Nonempty R) (hS : Serial S) :
    Nonempty (comp R S) := by
  obtain ⟨x, y, hxy⟩ := hR
  obtain ⟨z, hyz⟩ := hS y
  exact ⟨x, z, y, hxy, hyz⟩

theorem comp_nonempty_invariant (R : TRel X i j) (S : TRel X j k)
    (hR : Nonempty R) (hS : Nonempty S)
    (invS : Invariant (G := G) S)
    (transJ : ∀ x y : X j, ∃ g : G, g • x = y) :
    Nonempty (comp R S) :=
  comp_nonempty_of_serial R S hR
    (invariant_serial (G := G) S transJ invS hS)

theorem top_comp_invariant (R : TRel X j k)
    (h : Nonempty R) (hInv : Invariant (G := G) R)
    (transK : ∀ x y : X k, ∃ g : G, g • x = y) :
    comp (top X i j) R = top X i k :=
  top_comp R (invariant_coserial (G := G) R transK hInv h)

theorem comp_top_invariant (R : TRel X i j)
    (h : Nonempty R) (hInv : Invariant (G := G) R)
    (transI : ∀ x y : X i, ∃ g : G, g • x = y) :
    comp R (top X j k) = top X i k :=
  comp_top R (invariant_serial (G := G) R transI hInv h)

/-- For a real output pair-orbital, one witnessed product point propagates
to the whole orbital. Thus this is atom-level typed RAW Peirce. -/
theorem actual_orbital_peirce
    (a : X i) (c : X k)
    (R : TRel X i j) (B : TRel X j k)
    (hR : Invariant (G := G) R)
    (hB : Invariant (G := G) B) :
    (∀ x z, GroupActions.orbital (G := G) a c x z → comp R B x z) ↔
      (∃ x z, GroupActions.orbital (G := G) a c x z ∧
        comp R B x z) := by
  constructor
  · intro h
    exact ⟨a, c, GroupActions.orbital_nonempty a c, h a c
      (GroupActions.orbital_nonempty a c)⟩
  · rintro ⟨x, z, ⟨g, hga, hgc⟩, hcomp⟩
    have invProd := invariant_comp (G := G) R B hR hB
    have hbase : comp R B a c := by
      have hback := invProd g⁻¹ x z hcomp
      rw [← hga, ← hgc] at hback
      simpa only [inv_smul_smul] using hback
    intro x' z' horb
    obtain ⟨h, rfl, rfl⟩ := horb
    exact invProd h a c hbase

theorem comp_peirce_witness (R : TRel X i j) (B : TRel X j k)
    (x : X i) (z : X k) :
    comp R B x z ↔ ∃ y, R x y ∧ converse B z y :=
  Iff.rfl


end CCO.TRel

namespace CCO.RawSymmetric

variable {A : Type*} {G : Type*}
variable [Group G] [MulAction G A]

abbrev Rel := A → A → Prop

/-- The ambient group can flip *every* ordered pair of the same original
sort. A homogeneous symmetric atomic colouring yields this property. -/
def PairFlip : Prop :=
  ∀ x y : A, ∃ g : G, g • x = y ∧ g • y = x


/-- Equivalence is stated as a property of an *actual* binary relation.
This avoids implicitly restricting to the represented exact sublattice. -/
structure EquivRel (R : Rel) : Prop where
  refl : ∀ x, R x x
  symm : ∀ x y, R x y → R y x
  trans : ∀ x y z, R x y → R y z → R x z

theorem invariant_commute (R S : Rel)
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y))
    (hS : ∀ (g : G) x y, S x y → S (g • x) (g • y))
    (hflip : PairFlip (G := G) (A := A)) :
    TRel.comp R S = TRel.comp S R := by
  have hProd : ∀ (g : G) x y, TRel.comp R S x y →
      TRel.comp R S (g • x) (g • y) := by
    rintro g x y ⟨z, hxz, hzy⟩
    exact ⟨g • z, hR g x z hxz, hS g z y hzy⟩
  have hSymR : ∀ x y, R x y → R y x := by
    intro x y hxy
    obtain ⟨g, hgx, hgy⟩ := hflip x y
    simpa only [hgx, hgy] using hR g x y hxy
  have hSymS : ∀ x y, S x y → S y x := by
    intro x y hxy
    obtain ⟨g, hgx, hgy⟩ := hflip x y
    simpa only [hgx, hgy] using hS g x y hxy
  have hSymProd : ∀ x y, TRel.comp R S x y →
      TRel.comp R S y x := by
    intro x y hxy
    obtain ⟨g, hgx, hgy⟩ := hflip x y
    simpa only [hgx, hgy] using hProd g x y hxy
  funext x y
  apply propext
  constructor
  · intro h
    obtain ⟨z, hyz, hzx⟩ := hSymProd x y h
    exact ⟨z, hSymS y z hyz, hSymR z x hzx⟩
  · rintro ⟨z, hxz, hzy⟩
    have hyx : TRel.comp R S y x :=
      ⟨z, hSymR z y hzy, hSymS x z hxz⟩
    exact hSymProd y x hyx

/-- The product of two invariant equivalences is their join: in addition
to being an equivalence, it contains both and is below every equivalence
containing both. -/
theorem comp_equivalences_is_join (E F : Rel)
    (hE : EquivRel E) (hF : EquivRel F)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (invF : ∀ (g : G) x y, F x y → F (g • x) (g • y))
    (hflip : PairFlip (G := G) (A := A)) :
    EquivRel (TRel.comp E F) ∧
      (∀ x y, E x y → TRel.comp E F x y) ∧
      (∀ x y, F x y → TRel.comp E F x y) ∧
      (∀ H : Rel, EquivRel H →
        (∀ x y, E x y → H x y) →
        (∀ x y, F x y → H x y) →
        ∀ x y, TRel.comp E F x y → H x y) := by
  have hComm := invariant_commute E F invE invF hflip
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      exact ⟨x, hE.refl x, hF.refl x⟩
    · rintro x y ⟨z, hxz, hzy⟩
      have hswap : TRel.comp F E y x :=
        ⟨z, hF.symm z y hzy, hE.symm x z hxz⟩
      rw [hComm]
      exact hswap
    · rintro x y z ⟨u, hxu, huy⟩ ⟨v, hyv, hvz⟩
      have huv : TRel.comp F E u v := ⟨y, huy, hyv⟩
      rw [hComm] at huv
      obtain ⟨w, huw, hwv⟩ := huv
      exact ⟨w, hE.trans x u w hxu huw, hF.trans w v z hwv hvz⟩
  constructor
  · intro x y hxy
    exact ⟨y, hxy, hF.refl y⟩
  constructor
  · intro x y hxy
    exact ⟨x, hE.refl x, hxy⟩
  · intro H hH he hf x y hxy
    obtain ⟨z, hxz, hzy⟩ := hxy
    exact hH.trans x z y (he x z hxz) (hf z y hzy)

end CCO.RawSymmetric
