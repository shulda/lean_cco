import CCO.SIR.Positive.Direct.Amalgamation
import CCO.Selectors.NR2
import CCO.ParityHasse.Original.RelativeIndices

namespace CCO.SIR.Positive.Direct
open CCO.Selectors CCO.ParityHasse.Original

@[simp] theorem sheetSetoid_rel (x y : Point) : sheetSetoid x y ↔ E x y := Iff.rfl
@[simp] theorem parentSetoid_rel (x y : Point) : parentSetoid x y ↔ F x y := Iff.rfl

theorem sheet_colourInvariant : ColourInvariantSetoid source (i := ()) sheetSetoid := by
  intro x y u v hc
  exact (coordinates_of_colour_eq hc).2.2

theorem parent_colourInvariant : ColourInvariantSetoid source (i := ()) parentSetoid := by
  intro x y u v hc
  exact (coordinates_of_colour_eq hc).2.1

def leftRep (_ : Colour) : Point := (0,false,0)
def rightRep : Colour → Point
  | .e => (0,false,1)
  | .d => (0,true,0)
  | .n => (1,false,0)

@[simp] theorem rep_colour (a : Colour) : colour (leftRep a) (rightRep a) = some a := by
  cases a <;> decide

private theorem transfer {R : Setoid Point}
    (hR : ColourInvariantSetoid source (i := ()) R) {a : Colour} {x y : Point}
    (hc : colour x y = some a) (hr : R (leftRep a) (rightRep a)) : R x y :=
  (hR _ _ _ _ (hc.trans (rep_colour a).symm)).mpr hr

private theorem from_pair {R : Setoid Point}
    (hR : ColourInvariantSetoid source (i := ()) R) {a : Colour} {x y : Point}
    (hc : colour x y = some a) (hr : R x y) : R (leftRep a) (rightRep a) :=
  (hR _ _ _ _ (hc.trans (rep_colour a).symm)).mp hr

private theorem d_forces_e {R : Setoid Point}
    (hR : ColourInvariantSetoid source (i := ()) R)
    (hd : R (leftRep .d) (rightRep .d)) : R (leftRep .e) (rightRep .e) := by
  have hz : R (rightRep .d) (rightRep .e) := transfer hR (a := .d) (by decide) hd
  exact R.trans hd hz

private theorem n_forces_top {R : Setoid Point}
    (hR : ColourInvariantSetoid source (i := ()) R)
    (hn : R (leftRep .n) (rightRep .n)) : R = ⊤ := by
  apply Setoid.ext
  intro x y
  constructor
  · intro _; trivial
  · intro _
    let z : Point := (parent x + parent y + 1,false,0)
    have hxz : colour x z = some .n := by
      rw [colour_n]
      change parent x ≠ parent x + parent y + 1
      omega
    have hzy : colour z y = some .n := by
      rw [colour_n]
      change parent x + parent y + 1 ≠ parent y
      omega
    exact R.trans (transfer hR hxz hn) (transfer hR hzy hn)

/-- The FULL invariant equivalence lattice of the old language contains
exactly Id,E,F,Top. This quantifies over ALL invariant setoids. -/
theorem full_colour_lattice (R : Setoid Point)
    (hR : ColourInvariantSetoid source (i := ()) R) :
    R = ⊥ ∨ R = sheetSetoid ∨ R = parentSetoid ∨ R = ⊤ := by
  classical
  by_cases hn : R (leftRep .n) (rightRep .n)
  · exact Or.inr (Or.inr (Or.inr (n_forces_top hR hn)))
  by_cases hd : R (leftRep .d) (rightRep .d)
  · right; right; left
    have he := d_forces_e hR hd
    apply Setoid.ext
    intro x y
    constructor
    · intro hxy
      by_contra hF
      exact hn (from_pair hR ((colour_n x y).mpr hF) hxy)
    · intro hF
      by_cases hxy : x = y
      · exact hxy ▸ R.refl x
      by_cases hE : sheet x = sheet y
      · exact transfer hR ((colour_e x y).mpr ⟨hxy,hF,hE⟩) he
      · exact transfer hR ((colour_d x y).mpr ⟨hF,hE⟩) hd
  by_cases he : R (leftRep .e) (rightRep .e)
  · right; left
    apply Setoid.ext
    intro x y
    constructor
    · intro hxy
      have hF : F x y := by
        by_contra hF
        exact hn (from_pair hR ((colour_n x y).mpr hF) hxy)
      have hs : sheet x = sheet y := by
        by_contra hs
        exact hd (from_pair hR ((colour_d x y).mpr ⟨hF,hs⟩) hxy)
      exact ⟨hF,hs⟩
    · intro hE
      by_cases hxy : x = y
      · exact hxy ▸ R.refl x
      · exact transfer hR ((colour_e x y).mpr ⟨hxy,hE⟩) he
  · left
    apply Setoid.ext
    intro x y
    constructor
    · intro hxy
      change x = y
      cases hc : colour x y with
      | none => exact (colour_none x y).mp hc
      | some a =>
          have ha := from_pair hR hc hxy
          cases a with
          | e => exact False.elim (he ha)
          | d => exact False.elim (hd ha)
          | n => exact False.elim (hn ha)
    · intro hxy
      change x = y at hxy
      exact hxy ▸ R.refl x

theorem full_invariant_lattice (R : Setoid Point)
    (hR : InvariantSetoid (X := fun _ : Unit => Point) (G := Aut) (i := ()) R) :
    R = ⊥ ∨ R = sheetSetoid ∨ R = parentSetoid ∨ R = ⊤ :=
  full_colour_lattice R (colourInvariantSetoid_of_invariant source homogeneous R hR)

theorem full_lattice_strict :
    (⊥ : Setoid Point) < sheetSetoid ∧ sheetSetoid < parentSetoid ∧
      parentSetoid < (⊤ : Setoid Point) := by
  constructor
  · apply lt_iff_le_not_ge.mpr
    refine ⟨bot_le,?_⟩
    intro h
    have hh : (leftRep .e) = rightRep .e := h ((colour_e _ _).mp (rep_colour .e)).2
    have : (0 : ℕ) = 1 := congrArg index hh
    omega
  constructor
  · apply lt_iff_le_not_ge.mpr
    refine ⟨fun _ _ h => h.1,?_⟩
    intro h
    have hh := h (show parentSetoid (leftRep .d) (rightRep .d) from rfl)
    have : (false : Bool) = true := hh.2
    contradiction
  · apply lt_iff_le_not_ge.mpr
    refine ⟨le_top,?_⟩
    intro h
    have hh := h (show (⊤ : Setoid Point) (leftRep .n) (rightRep .n) from trivial)
    have : (0 : ℕ) = 1 := hh
    omega

/-- Both represented sheets occur in every parent; a finite substructure
may of course represent only one of them. -/
theorem relativeIndexTwo : RelativeIndexTwo sheetSetoid parentSetoid := by
  constructor
  · intro x y h; exact h.1
  · intro x
    let y : Point := (parent x, Bool.not (sheet x), 0)
    refine ⟨y,rfl,?_,?_⟩
    · intro h
      have hh : sheet x = Bool.not (sheet x) := h.2
      cases hs : sheet x <;> simp [hs] at hh
    · intro z
      constructor
      · intro hF
        by_cases hs : sheet x = sheet z
        · exact Or.inl ⟨hF,hs⟩
        · right
          refine ⟨hF,?_⟩
          change Bool.not (sheet x) = sheet z
          cases hx : sheet x <;> cases hz : sheet z <;> simp_all
      · rintro (h | h)
        · exact h.1
        · exact h.1

theorem violates_originalNR2 : ¬ OriginalNR2 source := by
  intro h
  exact h () sheetSetoid parentSetoid sheet_colourInvariant parent_colourInvariant relativeIndexTwo

def sheetClassMap (a : Point) : RelativeClass sheetSetoid parentSetoid a → Bool :=
  Quotient.lift (fun x => sheet x.val) (fun _ _ h => h.2)

theorem sheetClassMap_bijective (a : Point) : Function.Bijective (sheetClassMap a) := by
  constructor
  · intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y h
    exact Quotient.sound ⟨x.property.symm.trans y.property,h⟩
  · intro b
    exact ⟨Quotient.mk _ (⟨(parent a,b,0),rfl⟩ : {x // parentSetoid a x}),rfl⟩

noncomputable def sheetClassEquiv (a : Point) :
    RelativeClass sheetSetoid parentSetoid a ≃ Bool :=
  Equiv.ofBijective (sheetClassMap a) (sheetClassMap_bijective a)

theorem actual_relative_index (a : Point) : relativeIndex sheetSetoid parentSetoid a = 2 := by
  exact (Nat.card_congr (sheetClassEquiv a)).trans (by simp [Nat.card_eq_fintype_card])

/-- Every E fibre has infinitely many REAL points. -/
theorem infinite_sheet (a : Point) : Infinite {x // sheetSetoid a x} := by
  apply Infinite.of_injective (fun n : ℕ => (⟨(parent a,sheet a,n),rfl,rfl⟩ : {x // sheetSetoid a x}))
  intro m n h
  exact congrArg (fun x : {x // sheetSetoid a x} => index x.val) h

private theorem infinite_quotient_of_le_parent (R : Setoid Point) (hR : R ≤ parentSetoid) :
    Infinite (Quotient R) := by
  apply Infinite.of_injective (fun n : ℕ => Quotient.mk R (n,false,0))
  intro m n h
  exact hR (Quotient.exact h)

/-- Every PROPER full invariant equivalence has infinite GLOBAL index;
the relative two-sheet interval is nevertheless finite. -/
theorem infinite_global_quotient (R : Setoid Point)
    (hR : InvariantSetoid (X := fun _ : Unit => Point) (G := Aut) (i := ()) R) (hproper : R ≠ ⊤) : Infinite (Quotient R) := by
  rcases full_invariant_lattice R hR with rfl | rfl | rfl | ht
  · exact infinite_quotient_of_le_parent _ bot_le
  · exact infinite_quotient_of_le_parent _ (fun _ _ h => h.1)
  · exact infinite_quotient_of_le_parent _ le_rfl
  · exact False.elim (hproper ht)

/-- Every finite induced old object is a nested E≤F structure and every
represented parent has at most two represented sheets. -/
theorem finite_age_two_sheets (A : FiniteInduced (X := fun _ : Unit => Point))
    (p : ℕ) : ∀ x : ↥A.vertices, parent x.val.2 = p →
      E x.val.2 (p,false,0) ∨ E x.val.2 (p,true,0) := by
  intro x hp
  cases hs : sheet x.val.2
  · exact Or.inl ⟨hp,hs⟩
  · exact Or.inr ⟨hp,hs⟩

/-- Converse age description: any finite nested pair of equivalences with
at most two lower classes in each upper class embeds into the LITERAL
real model. The lower fibres need not both be represented. -/
theorem finite_age_realization {V : Type*} [Finite V] (e f : Setoid V)
    (hef : e ≤ f)
    (htwo : ∀ x y z, f x y → f x z → e x y ∨ e x z ∨ e y z) :
    ∃ φ : V ↪ Point, (∀ x y, F (φ x) (φ y) ↔ f x y) ∧
      (∀ x y, E (φ x) (φ y) ↔ e x y) := by
  classical
  obtain ⟨code,hcode⟩ := Countable.exists_injective_nat (Quotient f)
  obtain ⟨idx,hidx⟩ := Countable.exists_injective_nat V
  let sh : V → Bool := fun x => decide (e (Quotient.mk f x).out x)
  have hsh {x y : V} (hxy : f x y) : sh x = sh y ↔ e x y := by
    have hq : Quotient.mk f x = Quotient.mk f y := Quotient.sound hxy
    let a := (Quotient.mk f x).out
    have hax : f a x := Quotient.mk_out x
    have hay : f a y := f.trans hax hxy
    change decide (e a x) = decide (e (Quotient.mk f y).out y) ↔ _
    rw [←hq]
    change decide (e a x) = decide (e a y) ↔ _
    constructor
    · intro hs
      by_cases hEx : e a x
      · have hEy : e a y := by
          have hh : decide (e a y) = true := hs ▸ (by simp [hEx])
          simpa using hh
        exact e.trans (e.symm hEx) hEy
      · have hEy : ¬ e a y := by
          intro hy
          have hh : decide (e a x) = true := hs.trans (by simp [hy])
          exact hEx (by simpa using hh)
        exact ((htwo a x y hax hay).resolve_left hEx).resolve_left hEy
    · intro hE
      have hh : e a x ↔ e a y :=
        ⟨fun h => e.trans h hE,fun h => e.trans h (e.symm hE)⟩
      simp only [hh]
  let φ : V ↪ Point := ⟨fun x => (code (Quotient.mk f x),sh x,idx x),by
    intro x y h
    exact hidx (congrArg index h)⟩
  refine ⟨φ,?_,?_⟩
  · intro x y
    change code (Quotient.mk f x) = code (Quotient.mk f y) ↔ f x y
    exact ⟨fun h => Quotient.exact (hcode h),fun h => congrArg code (Quotient.sound h)⟩
  · intro x y
    change (code (Quotient.mk f x) = code (Quotient.mk f y) ∧ sh x = sh y) ↔ e x y
    constructor
    · rintro ⟨hp,hs⟩
      exact (hsh (Quotient.exact (hcode hp))).mp hs
    · intro hE
      have hF := hef hE
      exact ⟨congrArg code (Quotient.sound hF),(hsh hF).mpr hE⟩

end CCO.SIR.Positive.Direct
