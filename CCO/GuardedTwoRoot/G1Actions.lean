import CCO.GuardedTwoRoot.G1Model
import CCO.PairHomogeneity
import CCO.UnaryFreshFrames.Examples.FiniteExtension

/-! Genuine old motions and finite homogeneity of the FG1 source.
Blocks permute, each block's TWO bit classes permute, and every
block/bit fibre has its own infinite permutation of real clones. -/

namespace CCO.GuardedTwoRoot.G1
open CCO.UnaryFreshFrames.Examples
noncomputable section

theorem real_ext {x y : Real} (hb : block x = block y)
    (hd : bit x = bit y) (hn : clone x = clone y) : x = y := by
  rcases x with ⟨⟨b,d⟩,n⟩
  rcases y with ⟨⟨b',d'⟩,n'⟩
  simp_all [block,bit,clone]

def wreath (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) : Equiv.Perm Real where
  toFun x := ((a (block x),c (block x) (bit x)),b (block x,bit x) (clone x))
  invFun x :=
    ((a.symm (block x),(c (a.symm (block x))).symm (bit x)),
      (b (a.symm (block x),(c (a.symm (block x))).symm (bit x))).symm (clone x))
  left_inv := by rintro ⟨⟨q,d⟩,n⟩; simp [block,bit,clone]
  right_inv := by rintro ⟨⟨q,d⟩,n⟩; simp [block,bit,clone]

theorem wreath_block (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Real) :
    block (wreath a c b x) = a (block x) := rfl

theorem wreath_bit (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Real) :
    bit (wreath a c b x) = c (block x) (bit x) := rfl

theorem wreath_clone (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x : Real) :
    clone (wreath a c b x) = b (block x,bit x) (clone x) := rfl

theorem wreath_colour (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) (x y : Real) :
    colour (wreath a c b x) (wreath a c b y) = colour x y := by
  have hb : block (wreath a c b x) = block (wreath a c b y) ↔ block x = block y :=
    a.injective.eq_iff
  by_cases h : x = y
  · subst y
    exact (colour_none _ _).mpr rfl |>.trans ((colour_none _ _).mpr rfl).symm
  · have hw : wreath a c b x ≠ wreath a c b y := (wreath a c b).injective.ne h
    by_cases hblock : block x = block y
    · have hbit : bit (wreath a c b x) = bit (wreath a c b y) ↔ bit x = bit y := by
        change c (block x) (bit x) = c (block y) (bit y) ↔ _
        rw [hblock]
        exact (c (block y)).injective.eq_iff
      simp only [colour,if_neg h,if_neg hw,if_pos hblock,if_pos (hb.mpr hblock)]
      by_cases hd : bit x = bit y
      · simp [hd,hbit.mpr hd]
      · have hd' : bit (wreath a c b x) ≠ bit (wreath a c b y) :=
          fun he => hd (hbit.mp he)
        simp [hd,hd']
    · have hblock' : block (wreath a c b x) ≠ block (wreath a c b y) :=
        fun he => hblock (hb.mp he)
      simp [colour,h,hw,hblock,hblock']

def wreathAut (a : Equiv.Perm ℕ) (c : ℕ → Equiv.Perm Bool)
    (b : (ℕ × Bool) → Equiv.Perm ℕ) : Aut :=
  ⟨wreath a c b,wreath_colour a c b⟩

theorem finite_extension {V : Type*} [Finite V] (f h : V → Real)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w)) :
    ∃ g : Aut, ∀ v, g • f v = h v := by
  classical
  obtain ⟨a,ha⟩ := extend_equal_kernels (fun v => block (f v))
    (fun v => block (h v)) (fun v w => block_of_colour (hc v w))
  let I (q : ℕ) := {v : V // block (f v) = q}
  have hC (q : ℕ) : ∃ c : Equiv.Perm Bool,
      ∀ v : I q, c (bit (f v.val)) = bit (h v.val) := by
    apply extend_equal_kernels
    intro v w
    have hbf : block (f v.val) = block (f w.val) := v.property.trans w.property.symm
    have hbh : block (h v.val) = block (h w.val) :=
      (ha v.val).symm.trans ((congrArg a hbf).trans (ha w.val))
    have hfine := fine_of_colour (hc v.val w.val)
    exact ⟨fun hd => (hfine.mp ⟨hbf,hd⟩).2,
      fun hd => (hfine.mpr ⟨hbh,hd⟩).2⟩
  let c : ℕ → Equiv.Perm Bool := fun q => (hC q).choose
  have hbit (v : V) : c (block (f v)) (bit (f v)) = bit (h v) :=
    (hC (block (f v))).choose_spec ⟨v,rfl⟩
  let J (p : ℕ × Bool) := {v : V // block (f v) = p.1 ∧ bit (f v) = p.2}
  have hB (p : ℕ × Bool) : ∃ b : Equiv.Perm ℕ,
      ∀ v : J p, b (clone (f v.val)) = clone (h v.val) := by
    apply extend_equal_kernels
    intro v w
    have hbf : block (f v.val) = block (f w.val) := v.property.1.trans w.property.1.symm
    have hdf : bit (f v.val) = bit (f w.val) := v.property.2.trans w.property.2.symm
    have hbh : block (h v.val) = block (h w.val) :=
      (ha v.val).symm.trans ((congrArg a hbf).trans (ha w.val))
    have hdh : bit (h v.val) = bit (h w.val) := by rw [← hbit v.val,← hbit w.val,hbf,hdf]
    have he : f v.val = f w.val ↔ h v.val = h w.val := by
      rw [← colour_none,← colour_none,hc]
    exact (show clone (f v.val) = clone (f w.val) ↔ f v.val = f w.val from
      ⟨fun hn => real_ext hbf hdf hn,congrArg clone⟩).trans
        (he.trans ⟨congrArg clone,fun hn => real_ext hbh hdh hn⟩)
  let b : (ℕ × Bool) → Equiv.Perm ℕ := fun p => (hB p).choose
  refine ⟨wreathAut a c b,fun v => real_ext (ha v) (hbit v) ?_⟩
  exact (hB (block (f v),bit (f v))).choose_spec ⟨v,rfl,rfl⟩

theorem tagged_ext {x y : Sigma (fun _ : Unit => Real)} (h : x.2 = y.2) : x = y := by
  rcases x with ⟨⟨⟩,x⟩
  rcases y with ⟨⟨⟩,y⟩
  exact congrArg (Sigma.mk ()) h

theorem homogeneous : HomogeneousSource source Aut where
  preserves_sort := by rintro g ⟨i,x⟩; rfl
  preserves_colours := by
    rintro g ⟨i,x⟩ ⟨j,y⟩
    exact congrArg (fun c => (⟨i,j,c⟩ : Σ _ : Unit, Σ _ : Unit, Option Atom))
      (aut_colour g x y)
  extends_finite_diagram := by
    intro V _ f h hc
    obtain ⟨g,hg⟩ := finite_extension (fun v => (f v).2) (fun v => (h v).2)
      (fun v w => congrArg (fun c : Σ _ : Unit, Σ _ : Unit, Option Atom => c.2.2) (hc v w))
    exact ⟨g,fun v => tagged_ext (hg v)⟩

end
end CCO.GuardedTwoRoot.G1
