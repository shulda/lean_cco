import CCO.RealClosure.Bounds.Examples.CycleConsistency
import CCO.SIR.Positive.Direct.Homogeneity
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod

/-! C55/C56 use the actual countably infinite pure clone source, with one
common Boolean phase across all original named sorts. The original language
names only tagged pair XOR and logical equality, never an individual phase. -/

namespace CCO.SimultaneousQuotients.Boundaries.Phase

variable (I : Type) [Fintype I] [DecidableEq I]

structure Point (i : I) where
  phase : Bool
  index : ℕ
  deriving DecidableEq

instance pointCountable (i : I) : Countable (Point I i) := by
  apply Function.Injective.countable (f := fun x : Point I i => (x.phase,x.index))
  rintro ⟨b,n⟩ ⟨c,m⟩ h
  cases h
  rfl

instance pointInfinite (i : I) : Infinite (Point I i) :=
  Infinite.of_injective (fun n : ℕ => (⟨false,n⟩ : Point I i)) (by
    intro n m h
    exact congrArg Point.index h)

abbrev Tagged := Sigma (Point I)

def colour {i j : I} (x : Point I i) (y : Point I j) : Option Bool :=
  if (⟨i,x⟩ : Tagged I) = ⟨j,y⟩ then none else some (x.phase ^^ y.phase)

@[simp] theorem colour_none {i j : I} (x : Point I i) (y : Point I j) :
    colour I x y = none ↔ (⟨i,x⟩ : Tagged I) = ⟨j,y⟩ := by simp [colour]

theorem colour_some {i j : I} (x : Point I i) (y : Point I j) (a : Bool) :
    colour I x y = some a ↔
      (⟨i,x⟩ : Tagged I) ≠ ⟨j,y⟩ ∧ (x.phase ^^ y.phase) = a := by
  unfold colour
  split_ifs <;> simp_all

theorem colour_reverse {i j : I} (x : Point I i) (y : Point I j) :
    colour I x y = colour I y x := by simp only [colour,eq_comm,Bool.xor_comm]

def source : AtomicSource I (Point I) where
  Atom := fun _ _ => Bool
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => ⟨⟨false,0⟩⟩
  conv := id
  conv_invol := fun _ => rfl
  symmetricLoop := fun _ => rfl
  colour := colour I
  colour_none_iff := colour_none I
  colour_swap := fun x y a => congrArg (· = some a) (colour_reverse I x y) |>.to_iff
  realized := by
    intro i j a
    refine ⟨⟨false,0⟩,⟨a,1⟩,(colour_some I _ _ a).mpr ⟨?_,?_⟩⟩
    · intro h
      have hi := congrArg (fun p : Tagged I => p.2.index) h
      cases hi
    · simp

@[simp] theorem source_colour {i j : I} (x : Point I i) (y : Point I j) :
    (source I).colour x y = colour I x y := rfl

def taggedPhase (x : Tagged I) : Bool := x.2.phase
def taggedIndex (x : Tagged I) : ℕ := x.2.index

theorem read_phase {i j : I} (x : Point I i) (y : Point I j) :
    (colour I x y).getD false = (x.phase ^^ y.phase) := by
  unfold colour
  split_ifs with h
  · have hp := congrArg (taggedPhase I) h
    change x.phase = y.phase at hp
    simp only [Option.getD_none]
    change (false = (x.phase ^^ y.phase))
    rw [hp,Bool.xor_self]
  · rfl

theorem phase_of_tagged_colour (x y x' y' : Tagged I)
    (h : taggedColour (source I) x y = taggedColour (source I) x' y') :
    (taggedPhase I x ^^ taggedPhase I y) =
      (taggedPhase I x' ^^ taggedPhase I y') := by
  have hh := congrArg (fun c : Σ _ : I, Σ _ : I, Option Bool => c.2.2.getD false) h
  simpa only [taggedColour,source_colour,read_phase,taggedPhase] using hh

theorem equality_of_tagged_colour (x y x' y' : Tagged I)
    (h : taggedColour (source I) x y = taggedColour (source I) x' y') :
    x = y ↔ x' = y' := by
  have hh := congrArg (fun c : Σ _ : I, Σ _ : I, Option Bool => c.2.2) h
  change colour I x.2 y.2 = colour I x'.2 y'.2 at hh
  exact (colour_none I x.2 y.2).symm.trans ((congrArg (· = none) hh).to_iff.trans
    (colour_none I x'.2 y'.2))

theorem tagged_ext (x y : Tagged I) (hs : x.1 = y.1)
    (hb : taggedPhase I x = taggedPhase I y)
    (hn : taggedIndex I x = taggedIndex I y) : x = y := by
  rcases x with ⟨i,⟨b,n⟩⟩
  rcases y with ⟨j,⟨c,m⟩⟩
  cases hs
  change b = c at hb
  change n = m at hn
  cases hb
  cases hn
  rfl

/-- The FULL original named-sort automorphism group: every family of
permutations preserving the literal original colours, with no extra names. -/
def autGroup : Subgroup (∀ i, Equiv.Perm (Point I i)) where
  carrier := {g | ∀ i j x y, colour I (g i x) (g j y) = colour I x y}
  one_mem' := by intro i j x y; rfl
  mul_mem' := by
    intro g h hg hh i j x y
    exact (hg i j (h i x) (h j y)).trans (hh i j x y)
  inv_mem' := by
    intro g hg i j x y
    have h := hg i j ((g i).symm x) ((g j).symm y)
    simpa using h.symm

abbrev Aut := autGroup I

instance pointAction (i : I) : MulAction (Aut I) (Point I i) where
  smul g x := g.val i x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def motionPerm (δ : Bool) (τ : ∀ i : I, Bool → Equiv.Perm ℕ) (i : I) :
    Equiv.Perm (Point I i) where
  toFun x := ⟨δ ^^ x.phase,τ i x.phase x.index⟩
  invFun x := ⟨δ ^^ x.phase,(τ i (δ ^^ x.phase)).symm x.index⟩
  left_inv := by
    rintro ⟨b,n⟩
    cases δ <;> cases b <;> simp
  right_inv := by
    rintro ⟨b,n⟩
    cases δ <;> cases b <;> simp

theorem motion_colour (δ : Bool) (τ : ∀ i : I, Bool → Equiv.Perm ℕ)
    (i j : I) (x : Point I i) (y : Point I j) :
    colour I (motionPerm I δ τ i x) (motionPerm I δ τ j y) = colour I x y := by
  have hi : Function.Injective (fun p : Tagged I =>
      (⟨p.1,motionPerm I δ τ p.1 p.2⟩ : Tagged I)) := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hs : i = j := congrArg Sigma.fst h
    cases hs
    have hx : motionPerm I δ τ i x = motionPerm I δ τ i y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h
    exact congrArg (Sigma.mk i) ((motionPerm I δ τ i).injective hx)
  unfold colour
  simp only [hi.eq_iff (a := (⟨i,x⟩ : Tagged I)) (b := ⟨j,y⟩)]
  have hp : ((motionPerm I δ τ i x).phase ^^ (motionPerm I δ τ j y).phase) =
      (x.phase ^^ y.phase) := by
    change ((δ ^^ x.phase) ^^ (δ ^^ y.phase)) = _
    cases δ <;> cases x.phase <;> cases y.phase <;> rfl
  rw [hp]

def motion (δ : Bool) (τ : ∀ i : I, Bool → Equiv.Perm ℕ) : Aut I :=
  ⟨motionPerm I δ τ,motion_colour I δ τ⟩

theorem finite_extension {V : Type*} [Finite V] (f h : V → Tagged I)
    (hc : ∀ v w, taggedColour (source I) (f v) (f w) =
      taggedColour (source I) (h v) (h w)) :
    ∃ g : Aut I, ∀ v, g • f v = h v := by
  classical
  have hs : ∀ v, (f v).1 = (h v).1 := fun v =>
    congrArg (fun z : Σ _ : I, Σ _ : I, Option Bool => z.1) (hc v v)
  by_cases hv : Nonempty V
  · let v0 := Classical.choice hv
    let δ := taggedPhase I (h v0) ^^ taggedPhase I (f v0)
    have hp : ∀ v, (δ ^^ taggedPhase I (f v)) = taggedPhase I (h v) := by
      intro v
      have hh := phase_of_tagged_colour I _ _ _ _ (hc v v0)
      dsimp only [δ]
      cases hf : taggedPhase I (f v) <;> cases hh' : taggedPhase I (h v) <;>
        cases hf0 : taggedPhase I (f v0) <;> cases hh0 : taggedPhase I (h v0) <;> simp_all
    have hτ : ∀ i b, ∃ τ : Equiv.Perm ℕ,
        ∀ v : {v // (f v).1 = i ∧ taggedPhase I (f v) = b},
          τ (taggedIndex I (f v.val)) = taggedIndex I (h v.val) := by
      intro i b
      apply SIR.Positive.Direct.exists_perm_of_kernel
      intro v w
      have hEq := equality_of_tagged_colour I _ _ _ _ (hc v.val w.val)
      have fEq : f v.val = f w.val ↔ taggedIndex I (f v.val) = taggedIndex I (f w.val) := by
        exact ⟨congrArg (taggedIndex I),fun hh => tagged_ext I _ _
          (v.property.1.trans w.property.1.symm) (v.property.2.trans w.property.2.symm) hh⟩
      have hEq' : h v.val = h w.val ↔ taggedIndex I (h v.val) = taggedIndex I (h w.val) := by
        have hi : (h v.val).1 = (h w.val).1 :=
          (hs v.val).symm.trans (v.property.1.trans (w.property.1.symm.trans (hs w.val)))
        have hb : taggedPhase I (h v.val) = taggedPhase I (h w.val) := by
          rw [← hp v.val, ← hp w.val,v.property.2,w.property.2]
        exact ⟨congrArg (taggedIndex I),fun hh => tagged_ext I _ _ hi hb hh⟩
      exact fEq.symm.trans (hEq.trans hEq')
    choose τ hτ using hτ
    refine ⟨motion I δ τ,fun v => ?_⟩
    refine tagged_ext I _ _ ?_ ?_ ?_
    · exact hs v
    · exact hp v
    · exact hτ (f v).1 (taggedPhase I (f v)) ⟨v,rfl,rfl⟩
  · exact ⟨1,fun v => False.elim (hv ⟨v⟩)⟩

theorem homogeneous : HomogeneousSource (source I) (Aut I) where
  preserves_sort := by rintro g ⟨i,x⟩; rfl
  preserves_colours := by
    rintro g ⟨i,x⟩ ⟨j,y⟩
    change (⟨i,j,colour I (g.val i x) (g.val j y)⟩ : Σ _ : I, Σ _ : I, Option Bool) = _
    rw [g.property i j x y]
    rfl
  extends_finite_diagram := finite_extension I

theorem semanticCCO : SemanticCCO (source I) := by
  intro V D hcycles
  classical
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite _
  let read : RealClosure.Bounds.Examples.CycleConsistency.Reader (source I) := fun a => a
  obtain ⟨b,hb⟩ := RealClosure.Bounds.Examples.CycleConsistency.phase_labels
    (source I) D read (fun _ => rfl) (fun _ x => x.phase)
    (fun x y a h => ((colour_some I x y a).mp h).2) hcycles
  let code := Fintype.equivFin V
  refine ⟨{ point := fun v => ⟨b v,(code v).val⟩, preserves_edge := ?_ }⟩
  intro v w h a ha
  apply (colour_some I _ _ a).mpr
  refine ⟨?_,hb v w h a ha⟩
  intro heq
  have hh := congrArg (taggedIndex I) heq
  exact h (code.injective (Fin.ext hh))

end CCO.SimultaneousQuotients.Boundaries.Phase
