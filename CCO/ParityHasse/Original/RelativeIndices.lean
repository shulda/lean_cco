import CCO.ParityHasse.Original.OrbitalAlgebra
import Mathlib.Logic.Equiv.Sum

/-!
# Actual finite relative indices

The maps are maps of equivalence classes of original real points. Source
transitivity gives uniformity; a quotient map with equally sized fibres
gives multiplication. No endpoint exactness or SAP premise is used.
-/

universe u v w t
namespace CCO.ParityHasse.Original

section Structural
variable {A : Type v}

instance relativeClass_nonempty (E F : Setoid A) (a : A) :
    Nonempty (RelativeClass E F a) := ⟨Quotient.mk _ ⟨a, F.refl a⟩⟩

/-- Restricting the containing class induces an injective map of E-classes. -/
def relativeInclusion (E F K : Setoid A) (hFK : F ≤ K) (a : A) :
    RelativeClass E F a → RelativeClass E K a :=
  Quotient.map (fun x => (⟨x.val, hFK x.property⟩ : {x // K a x}))
    (fun _ _ h => h)

theorem relativeInclusion_injective (E F K : Setoid A) (hFK : F ≤ K) (a : A) :
    Function.Injective (relativeInclusion E F K hFK a) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x y h
  apply Quotient.sound
  have he := Quotient.exact h
  exact he

/-- Coarsening the inner equivalence gives a surjection of relative classes. -/
def relativeCoarsening (E F K : Setoid A) (hEF : E ≤ F) (a : A) :
    RelativeClass E K a → RelativeClass F K a :=
  Quotient.map id (fun _ _ h => hEF h)

theorem relativeCoarsening_surjective (E F K : Setoid A) (hEF : E ≤ F) (a : A) :
    Function.Surjective (relativeCoarsening E F K hEF a) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact ⟨Quotient.mk _ x, rfl⟩

theorem finite_relative_left (E F K : Setoid A) (hFK : F ≤ K) (a : A)
    [Finite (RelativeClass E K a)] : Finite (RelativeClass E F a) :=
  Finite.of_injective _ (relativeInclusion_injective E F K hFK a)

theorem finite_relative_right (E F K : Setoid A) (hEF : E ≤ F) (a : A)
    [Finite (RelativeClass E K a)] : Finite (RelativeClass F K a) :=
  Finite.of_surjective _ (relativeCoarsening_surjective E F K hEF a)

/-- A fibre of the actual quotient map is the E-quotient of the
corresponding real F-class. -/
def relativeFibreMap (E F K : Setoid A) (hEF : E ≤ F) (hFK : F ≤ K)
    (a : A) (y : {x // K a x}) :
    RelativeClass E F y.val →
      {q : RelativeClass E K a // relativeCoarsening E F K hEF a q = Quotient.mk _ y} :=
  Quotient.lift (fun x : {x // F y.val x} =>
    ⟨Quotient.mk _ (⟨x.val, K.trans y.property (hFK x.property)⟩ : {x // K a x}),
      Quotient.sound (F.symm x.property)⟩) (by
        intro x z hxz
        apply Subtype.ext
        exact Quotient.sound hxz)

theorem relativeFibreMap_injective (E F K : Setoid A) (hEF : E ≤ F) (hFK : F ≤ K)
    (a : A) (y : {x // K a x}) :
    Function.Injective (relativeFibreMap E F K hEF hFK a y) := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro x z h
  have hv := congrArg Subtype.val h
  apply Quotient.sound
  have he := Quotient.exact hv
  exact he

theorem relativeFibreMap_surjective (E F K : Setoid A) (hEF : E ≤ F) (hFK : F ≤ K)
    (a : A) (y : {x // K a x}) :
    Function.Surjective (relativeFibreMap E F K hEF hFK a y) := by
  rintro ⟨q, hq⟩
  revert hq
  refine Quotient.inductionOn q ?_
  intro x hx
  have hxy := Quotient.exact hx
  refine ⟨Quotient.mk _ (⟨x.val, F.symm hxy⟩ : {x // F y.val x}), ?_⟩
  apply Subtype.ext
  rfl

noncomputable def relativeFibreEquiv (E F K : Setoid A) (hEF : E ≤ F) (hFK : F ≤ K)
    (a : A) (y : {x // K a x}) :
    RelativeClass E F y.val ≃
      {q : RelativeClass E K a // relativeCoarsening E F K hEF a q = Quotient.mk _ y} :=
  Equiv.ofBijective _ ⟨relativeFibreMap_injective E F K hEF hFK a y,
    relativeFibreMap_surjective E F K hEF hFK a y⟩

end Structural

section Uniformity
variable {A : Type v} {G : Type t} [Group G] [MulAction G A]

/-- An actual group motion transports relative classes bijectively. -/
def relativeClassMotion (E F : Setoid A)
    (hE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (hF : ∀ (g : G) x y, F x y → F (g • x) (g • y))
    (g : G) (a : A) : RelativeClass E F a ≃ RelativeClass E F (g • a) where
  toFun := Quotient.map (fun x => ⟨g • x.val, hF g a x.val x.property⟩)
    (fun _ _ h => hE g _ _ h)
  invFun := Quotient.map (fun x =>
    ⟨g⁻¹ • x.val, by simpa only [inv_smul_smul] using hF g⁻¹ _ _ x.property⟩)
    (fun _ _ h => hE g⁻¹ _ _ h)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    apply congrArg (Quotient.mk _)
    exact Subtype.ext (inv_smul_smul g x.val)
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    apply congrArg (Quotient.mk _)
    exact Subtype.ext (smul_inv_smul g x.val)

end Uniformity

section OriginalSource
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- C08 uniformity is supplied by actual original-sort transitivity. -/
noncomputable def uniformRelativeClassEquiv (H : HomogeneousSource S G)
    (E F : ColourEq S i) (a b : X i) :
    RelativeClass E.val F.val a ≃ RelativeClass E.val F.val b := by
  let h := S.original_sort_transitive_of_homogeneous H i a b
  let g := Classical.choose h
  have hg : g • a = b := Classical.choose_spec h
  rw [← hg]
  exact relativeClassMotion E.val F.val (colourInvariant_groupInvariant S H E.2)
    (colourInvariant_groupInvariant S H F.2) g a

theorem relativeIndex_uniform (H : HomogeneousSource S G)
    (E F : ColourEq S i) (a b : X i) :
    relativeIndex E.val F.val a = relativeIndex E.val F.val b :=
  Nat.card_congr (uniformRelativeClassEquiv S H E F a b)

/-- A relative class of an equivalence inside itself has exactly one class. -/
theorem relativeIndex_self (E : Setoid (X i)) (a : X i) :
    relativeIndex E E a = 1 := by
  have hs : Subsingleton (RelativeClass E E a) := by
    constructor
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y
    exact Quotient.sound (E.trans (E.symm x.property) y.property)
  exact Nat.card_eq_one_iff_unique.mpr ⟨hs, inferInstance⟩

/-- In a transitive source, local relative index one is exactly equality
of the two globally invariant equivalences. -/
theorem relativeIndex_eq_one_iff (H : HomogeneousSource S G)
    (E F : ColourEq S i) (hEF : E ≤ F) (a : X i) :
    relativeIndex E.val F.val a = 1 ↔ E = F := by
  constructor
  · intro hcard
    apply le_antisymm hEF
    intro x y hxy
    have hx : Nat.card (RelativeClass E.val F.val x) = 1 :=
      (relativeIndex_uniform S H E F a x).symm.trans hcard
    letI : Subsingleton (RelativeClass E.val F.val x) :=
      (Nat.card_eq_one_iff_unique.mp hx).1
    let qx : RelativeClass E.val F.val x := Quotient.mk _ ⟨x, F.val.refl x⟩
    let qy : RelativeClass E.val F.val x := Quotient.mk _ ⟨y, hxy⟩
    have he := Quotient.exact (Subsingleton.elim qx qy)
    exact he
  · intro h
    subst F
    exact relativeIndex_self E.val a

/-- C08: actual finite relative indices multiply along a nested chain. -/
theorem relativeIndex_mul (H : HomogeneousSource S G)
    (E F K : ColourEq S i) (hEF : E ≤ F) (hFK : F ≤ K) (a : X i)
    [Finite (RelativeClass E.val K.val a)] :
    relativeIndex E.val K.val a =
      relativeIndex E.val F.val a * relativeIndex F.val K.val a := by
  classical
  letI : Finite (RelativeClass F.val K.val a) :=
    finite_relative_right E.val F.val K.val hEF a
  letI : Fintype (RelativeClass F.val K.val a) := Fintype.ofFinite _
  let f := relativeCoarsening E.val F.val K.val hEF a
  have hfib : ∀ q : RelativeClass F.val K.val a,
      Nat.card {p : RelativeClass E.val K.val a // f p = q} =
        relativeIndex E.val F.val a := by
    intro q
    refine Quotient.inductionOn q ?_
    intro y
    have hcard := (Nat.card_congr (relativeFibreEquiv E.val F.val K.val hEF hFK a y)).symm
    exact hcard.trans (relativeIndex_uniform S H E F y.val a)
  calc
    relativeIndex E.val K.val a =
        Nat.card (Σ q : RelativeClass F.val K.val a,
          {p : RelativeClass E.val K.val a // f p = q}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ q : RelativeClass F.val K.val a,
          Nat.card {p : RelativeClass E.val K.val a // f p = q} := Nat.card_sigma
    _ = Nat.card (RelativeClass F.val K.val a) * relativeIndex E.val F.val a := by
      simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Nat.card_eq_fintype_card]
    _ = relativeIndex E.val F.val a * relativeIndex F.val K.val a := Nat.mul_comm _ _

/-- Relative index two is a cover in the FULL invariant equivalence
poset. No intermediate exactness premise is imposed. -/
theorem index_two_covBy (H : HomogeneousSource S G)
    (E F : ColourEq S i) (hEF : E ≤ F) (a : X i)
    [Finite (RelativeClass E.val F.val a)]
    (htwo : relativeIndex E.val F.val a = 2) : E ⋖ F := by
  have hne : E ≠ F := by
    intro heq
    have hone := (relativeIndex_eq_one_iff S H E F hEF a).mpr heq
    omega
  refine ⟨lt_of_le_of_ne hEF hne, ?_⟩
  intro K hEK hKF
  letI : Finite (RelativeClass E.val K.val a) :=
    finite_relative_left E.val K.val F.val hKF.le a
  letI : Finite (RelativeClass K.val F.val a) :=
    finite_relative_right E.val K.val F.val hEK.le a
  have hmul := relativeIndex_mul S H E K F hEK.le hKF.le a
  have hn : relativeIndex E.val K.val a ≠ 1 := by
    intro hn
    exact hEK.ne ((relativeIndex_eq_one_iff S H E K hEK.le a).mp hn)
  have hm : relativeIndex K.val F.val a ≠ 1 := by
    intro hm
    exact hKF.ne ((relativeIndex_eq_one_iff S H K F hKF.le a).mp hm)
  have hnpos : 0 < relativeIndex E.val K.val a := Nat.card_pos
  have hmpos : 0 < relativeIndex K.val F.val a := Nat.card_pos
  have hn2 : 2 ≤ relativeIndex E.val K.val a := by omega
  have hm2 : 2 ≤ relativeIndex K.val F.val a := by omega
  have hfour := Nat.mul_le_mul hn2 hm2
  rw [← hmul, htwo] at hfour
  omega

/-- The equality to two already forces finiteness for `Nat.card`, so the
full-cover conclusion can be exported without a separate finite instance. -/
theorem covBy_of_relativeIndex_two (H : HomogeneousSource S G)
    (E F : ColourEq S i) (hEF : E ≤ F) (a : X i)
    (htwo : relativeIndex E.val F.val a = 2) : E ⋖ F := by
  letI : Finite (RelativeClass E.val F.val a) :=
    Nat.finite_of_card_ne_zero (by change relativeIndex E.val F.val a ≠ 0; omega)
  exact index_two_covBy S H E F hEF a htwo

end OriginalSource
end CCO.ParityHasse.Original
