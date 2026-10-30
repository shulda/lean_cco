import CCO.CloneSAP.Basic
import CCO.TerminalPowers.FullSource
import Mathlib.Data.Set.Finite.Range

universe u v w t
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
open TerminalPowers

/-- Forget only the new clone diversity atom, producing old logical equality. -/
def eraseAtom {i j : ι} : Atom S i j → Option (S.Atom i j)
  | .inl a => some a
  | .inr _ => none

@[simp] theorem colour_erase {i j : ι} (x : Carrier X i) (y : Carrier X j) :
    ((source S).colour x y).bind (eraseAtom S) = S.colour x.1 y.1 := by
  classical
  change (colour S x y).bind (eraseAtom S) = _
  unfold colour
  split_ifs with h hindex
  · simpa only [Option.bind_none] using h.symm
  · simpa only [Option.bind_some,eraseAtom] using h.symm
  · cases hc : S.colour x.1 y.1 with
    | none => exact (h hc).elim
    | some a => rfl

/-- C03: full clone pair type preservation descends to literal old pair types. -/
theorem tagged_owner_eq {p q r s : Sigma (Carrier X)}
    (h : taggedColour (source S) p q = taggedColour (source S) r s) :
    taggedColour S (owner p) (owner q) = taggedColour S (owner r) (owner s) := by
  let erase : (Σ i, Σ j, Option ((source S).Atom i j)) →
      (Σ i, Σ j, Option (S.Atom i j)) := fun a => ⟨a.1,a.2.1,a.2.2.bind (eraseAtom S)⟩
  have he := congrArg erase h
  simpa only [erase,taggedColour,owner,colour_erase] using he

/-- A finite partial map with precisely matching equality patterns extends
on the ambient set, even when the indexing tuple has repetitions. -/
theorem exists_permutation_of_eq_pattern {V : Type*} [Finite V] {Y : Type*}
    (f h : V → Y) (heq : ∀ a b, f a = f b ↔ h a = h b) :
    ∃ e : Equiv.Perm Y, ∀ a, e (f a) = h a := by
  classical
  let D := Set.range f
  letI : Finite D := (Set.finite_range f).to_subtype
  let lift : D → V := fun d => d.property.choose
  have lift_spec (d : D) : f (lift d) = d.val := d.property.choose_spec
  let hh : D → Y := fun d => h (lift d)
  have hh_inj : Function.Injective hh := by
    intro a b hab
    apply Subtype.ext
    exact (lift_spec a).symm.trans (((heq _ _).mpr hab).trans (lift_spec b))
  obtain ⟨e,he⟩ := Equiv.Perm.exists_extending_pair Subtype.val hh
    Subtype.val_injective hh_inj
  refine ⟨e,fun a => ?_⟩
  let d : D := ⟨f a,⟨a,rfl⟩⟩
  exact (he d).trans ((heq _ _).mp (lift_spec d))

/-- Every old automorphism and independent bijections of its infinite fibres
combine into a whole sort-preserving bijection. -/
def liftEquiv (g : FullAut S) (σ : ∀ i, X i → Equiv.Perm ℕ) (i : ι) :
    Equiv.Perm (Carrier X i) where
  toFun x := (g.val i x.1, σ i x.1 x.2)
  invFun y := ((g.val i).symm y.1,(σ i ((g.val i).symm y.1)).symm y.2)
  left_inv x := by simp
  right_inv y := by simp

/-- The constructed whole bijection preserves actual complete clone colours. -/
theorem lift_colour (g : FullAut S) (σ : ∀ i, X i → Equiv.Perm ℕ)
    {i j : ι} (x : Carrier X i) (y : Carrier X j) :
    (source S).colour (liftEquiv S g σ i x) (liftEquiv S g σ j y) =
      (source S).colour x y := by
  change colour S (liftEquiv S g σ i x) (liftEquiv S g σ j y) = colour S x y
  apply Option.ext
  intro a
  cases a with
  | inl a =>
    simp only [Option.mem_def,colour_old_iff]
    exact congrArg (fun c => c = some a) (g.property i j x.1 y.1) |>.to_iff
  | inr e =>
    rcases e with ⟨e⟩
    subst j
    simp only [Option.mem_def,colour_clone_iff,Sigma.mk.injEq,heq_eq_eq,true_and]
    change ((g.val i x.1 = g.val i y.1) ∧ σ i x.1 x.2 ≠ σ i y.1 y.2) ↔
      x.1 = y.1 ∧ x.2 ≠ y.2
    constructor
    · rintro ⟨he,hi⟩
      have ho := (g.val i).injective he
      refine ⟨ho,?_⟩
      intro hn
      exact hi (by rw [ho,hn])
    · rintro ⟨he,hi⟩
      refine ⟨congrArg (g.val i) he,?_⟩
      rw [he]
      exact fun hn => hi ((σ i y.1).injective hn)

/-- The lift is a genuine member of the full clone automorphism group. -/
def liftAut (g : FullAut S) (σ : ∀ i, X i → Equiv.Perm ℕ) :
    FullAut (source S) := ⟨liftEquiv S g σ,fun _ _ x y => lift_colour S g σ x y⟩

/-- C04: infinite pure clones are homogeneous. No old AP, SAP, CCO,
triangle-definedness, countability or infinite old carrier is required. -/
theorem homogeneous {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) : HomogeneousSource (source S) (FullAut (source S)) where
  preserves_sort := by intro g p; rfl
  preserves_colours := by
    rintro g ⟨i,x⟩ ⟨j,y⟩
    exact congrArg (fun c => (⟨i,j,c⟩ : Σ i, Σ j, Option ((source S).Atom i j)))
      (g.property i j x y)
  extends_finite_diagram := by
    classical
    intro V _ f h hc
    have howner : ∀ a b, taggedColour S (owner (f a)) (owner (f b)) =
        taggedColour S (owner (h a)) (owner (h b)) :=
      fun a b => tagged_owner_eq S (hc a b)
    obtain ⟨g,hg⟩ := (full_homogeneous S H).extends_finite_diagram
      (fun a => owner (f a)) (fun a => owner (h a)) howner
    have hsort (a : V) : (f a).1 = (h a).1 := by
      have he := congrArg (fun c => c.1) (hc a a)
      exact he
    have equality (a b : V) : f a = f b ↔ h a = h b := by
      have hh := congrArg (fun z : Σ i, Σ j, Option ((source S).Atom i j) => z.2.2.isNone) (hc a b)
      have ff : ((source S).colour (f a).2 (f b).2).isNone = true ↔ f a = f b := by
        rw [Option.isNone_iff_eq_none,(source S).colour_none_iff]
      have hg' : ((source S).colour (h a).2 (h b).2).isNone = true ↔ h a = h b := by
        rw [Option.isNone_iff_eq_none,(source S).colour_none_iff]
      exact ff.symm.trans ((congrArg (fun z => z = true) hh).to_iff.trans hg')
    let I (i : ι) (q : X i) := {a : V // owner (f a) = ⟨i,q⟩}
    have pattern (i : ι) (q : X i) (a b : I i q) :
        (f a.val).2.2 = (f b.val).2.2 ↔ (h a.val).2.2 = (h b.val).2.2 := by
      have fo : owner (f a.val) = owner (f b.val) := a.property.trans b.property.symm
      have ho : owner (h a.val) = owner (h b.val) := by rw [← hg,← hg,fo]
      constructor
      · intro he
        exact congrArg (fun p => p.2.2) ((equality _ _).mp (pointEquiv.injective (Prod.ext fo he)))
      · intro he
        exact congrArg (fun p => p.2.2) ((equality _ _).mpr (pointEquiv.injective (Prod.ext ho he)))
    choose σ hσ using fun i q => exists_permutation_of_eq_pattern
      (fun a : I i q => (f a.val).2.2) (fun a : I i q => (h a.val).2.2) (pattern i q)
    refine ⟨liftAut S g σ,fun a => ?_⟩
    apply pointEquiv.injective
    apply Prod.ext
    · exact hg a
    · exact hσ (f a).1 (f a).2.1 ⟨a,rfl⟩

end CCO.CloneSAP
