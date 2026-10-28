import CCO.ExactCRT.AbstractHelly
import Mathlib.Data.Fintype.EquivFin

/-! B008 C04–07: the natural quotient-coordinate map, its exact kernel,
and finite compatible-tuple surjectivity. Infinite CRT is not asserted. -/

universe u v
namespace CCO.ExactCRT.Abstract
variable {A : Type u} {I : Type v}

def familyMeet (E : I → Setoid A) : Setoid A where
  r x y := ∀ i, E i x y
  iseqv := ⟨fun x i => (E i).refl x, fun h i => (E i).symm (h i),
    fun h h' i => (E i).trans (h i) (h' i)⟩

@[simp] theorem familyMeet_rel (E : I → Setoid A) (x y : A) :
    familyMeet E x y ↔ ∀ i, E i x y := Iff.rfl

/-- This map and its injectivity require no commutation/distributivity. -/
def coordinates (E : I → Setoid A) (q : Quotient (familyMeet E)) :
    ∀ i, Quotient (E i) := fun i => quotientMap (show familyMeet E ≤ E i from fun _ _ h => h i) q

@[simp] theorem coordinates_mk (E : I → Setoid A) (x : A) (i : I) :
    coordinates E (Quotient.mk _ x) i = Quotient.mk (E i) x := rfl

theorem coordinates_injective (E : I → Setoid A) :
    Function.Injective (coordinates E) := by
  intro q r heq
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      intro i
      exact Quotient.exact (congrFun heq i)

/-- C04's exact kernel formula on original representatives. -/
theorem coordinates_kernel (E : I → Setoid A) (x y : A) :
    coordinates E (Quotient.mk _ x) = coordinates E (Quotient.mk _ y) ↔
      familyMeet E x y := by
  constructor
  · intro h i
    exact Quotient.exact (congrFun h i)
  · intro h
    funext i
    exact Quotient.sound (h i)

/-- Agreement is in the ACTUAL ambient join quotient. -/
def Compatible (E : I → Setoid A) (q : ∀ i, Quotient (E i)) : Prop :=
  ∀ i j, quotientMap (show E i ≤ E i ⊔ E j from le_sup_left) (q i) =
    quotientMap (show E j ≤ E i ⊔ E j from le_sup_right) (q j)

theorem coordinates_compatible (E : I → Setoid A) (q : Quotient (familyMeet E)) :
    Compatible E (coordinates E q) := by
  induction q using Quotient.inductionOn with
  | _ x => intro i j; rfl

def compatibleCoordinates (E : I → Setoid A) (q : Quotient (familyMeet E)) :
    {q : ∀ i, Quotient (E i) // Compatible E q} :=
  ⟨coordinates E q, coordinates_compatible E q⟩

theorem compatibleCoordinates_injective (E : I → Setoid A) :
    Function.Injective (compatibleCoordinates E) := by
  intro q r h
  exact coordinates_injective E (congrArg Subtype.val h)

/-- C05: the compatibility predicate is independent of chosen representatives. -/
theorem compatible_iff_pairwise (E : I → Setoid A)
    (comm : ∀ i j, Permutes (E i) (E j)) (q : ∀ i, Quotient (E i)) :
    Compatible E q ↔ ∀ i j, ∃ x, E i ((q i).out) x ∧ E j ((q j).out) x := by
  constructor
  · intro h i j
    apply (quotient_images_eq_iff (E i) (E j) (comm i j) _ _).mp
    simpa only [Quotient.out_eq] using h i j
  · intro h i j
    have h' := (quotient_images_eq_iff (E i) (E j) (comm i j) _ _).mpr (h i j)
    simpa only [Quotient.out_eq] using h'

variable (S : Sublattice (Setoid A))

/-- Reindexing exports the Fin n definition at arbitrary finite universes. -/
theorem classHelly_finite (helly : ClassHelly S) {J : Type v} [Finite J]
    (E : J → S) (centre : J → A)
    (pair : ∀ i j, ∃ x, (E i).val (centre i) x ∧ (E j).val (centre j) x) :
    ∃ x, ∀ i, (E i).val (centre i) x := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  obtain ⟨x, hx⟩ := helly _ (fun i => E (e.symm i))
    (fun i => centre (e.symm i)) (fun i j => pair _ _)
  refine ⟨x, fun i => ?_⟩
  exact Eq.mp (congrArg (fun j => (E j).val (centre j) x) (e.symm_apply_apply i)) (hx (e i))

/-- C06: Helly gives every compatible finite tuple a real representative. -/
theorem compatibleCoordinates_surjective (comm : Commutes S) (helly : ClassHelly S)
    {J : Type v} [Finite J] (E : J → S) :
    Function.Surjective (compatibleCoordinates (fun i => (E i).val)) := by
  intro q
  have hp := (compatible_iff_pairwise (fun i => (E i).val)
    (fun i j => comm (E i) (E j)) q.val).mp q.property
  obtain ⟨x, hx⟩ := classHelly_finite S helly E (fun i => (q.val i).out) hp
  refine ⟨Quotient.mk _ x, ?_⟩
  apply Subtype.ext
  funext i
  exact (Quotient.sound ((E i).val.symm (hx i))).trans (Quotient.out_eq _)

/-- Literal finite set-level CRT; no assertion about infinite families. -/
noncomputable def crtEquiv (comm : Commutes S) (helly : ClassHelly S)
    {J : Type v} [Finite J] (E : J → S) :
    Quotient (familyMeet (fun i => (E i).val)) ≃
      {q : ∀ i, Quotient (E i).val // Compatible (fun i => (E i).val) q} :=
  Equiv.ofBijective _ ⟨compatibleCoordinates_injective _,
    compatibleCoordinates_surjective S comm helly E⟩

@[simp] theorem crtEquiv_apply (comm : Commutes S) (helly : ClassHelly S)
    {J : Type v} [Finite J] (E : J → S) (x : A) (i : J) :
    (crtEquiv S comm helly E (Quotient.mk _ x)).val i = Quotient.mk (E i).val x := rfl

/-- Only nonempty finite CRT families are required in the converse. -/
def FiniteCRT : Prop := ∀ n (E : Fin (n+1) → S),
  Function.Surjective (compatibleCoordinates (fun i => (E i).val))

/-- C07, with the empty class family discharged separately from inhabitedness. -/
theorem classHelly_of_finiteCRT [Nonempty A] (comm : Commutes S)
    (crt : FiniteCRT S) : ClassHelly S := by
  intro n E centre pair
  cases n with
  | zero =>
    obtain ⟨x⟩ := ‹Nonempty A›
    exact ⟨x, fun i => Fin.elim0 i⟩
  | succ n =>
    let q : ∀ i, Quotient (E i).val := fun i => Quotient.mk _ (centre i)
    have hq : Compatible (fun i => (E i).val) q := by
      intro i j
      exact (quotient_images_eq_iff (E i).val (E j).val (comm _ _) _ _).mpr (pair i j)
    obtain ⟨r, hr⟩ := crt n E ⟨q, hq⟩
    induction r using Quotient.inductionOn with
    | _ x =>
      refine ⟨x, fun i => ?_⟩
      have hi := congrFun (congrArg Subtype.val hr) i
      have hrel : (E i).val x (centre i) := Quotient.exact hi
      exact (E i).val.symm hrel

/-- The three source conditions, without finite/inhabited sublattice assumptions. -/
theorem helly_iff_finiteCRT [Nonempty A] (comm : Commutes S) :
    ClassHelly S ↔ FiniteCRT S :=
  ⟨fun helly _ E => compatibleCoordinates_surjective S comm helly E,
    classHelly_of_finiteCRT S comm⟩

end CCO.ExactCRT.Abstract
