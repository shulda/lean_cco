import CCO.FiniteKernel.Countercontrols.HiddenParity
import CCO.FiniteKernel.ActualMarginals
import Mathlib.Data.Finite.Perm

/-! The hidden-parity countercontrol at the LITERAL actual intrinsic/binding
group interfaces. All one-owner binding images equal the intrinsic groups;
all three ABC actual pair images are full products, but the ABC projection
still has its genuine parity constraint. -/

namespace CCO.FiniteKernel.Countercontrols.HiddenParity

local instance (i : Fin 4) : Fintype (partition.Fibre i) :=
  inferInstanceAs (Fintype {x : Point // owner x = i})

def shiftKernel (s : Shift) : partition.kernel :=
  ⟨shiftAut s,(partition.mem_kernel_iff _).mpr (owner_act s)⟩

theorem shiftAut_mul (s t : Shift) : shiftAut (sumShift s t) = shiftAut s * shiftAut t := by
  apply Subtype.ext
  apply Equiv.ext
  exact act_sum s t

theorem fullAut_exponent_two (g : source.Aut) : g * g = 1 := by
  obtain ⟨s,rfl⟩ := shiftAut_surjective g
  apply Subtype.ext
  apply Equiv.ext
  exact act_invol s

set_option maxRecDepth 10000 in
/-- Any permutation of a whole two-point axis is a restriction of a genuine
global shift. This finite calculation quantifies over ALL such permutations.
-/
theorem axis_permutation_shift : ∀ (i : Fin 3)
    (g : Equiv.Perm (partition.Fibre i.castSucc)),
    ∃ s : Shift, ∀ x, (g x).val = act s x.val := by
  intro i
  fin_cases i <;> decide

theorem central_intrinsic_shift (g : partition.Intrinsic 3) :
    ∃ s : Shift, ∀ x, (g.val x).val = act s x.val := by
  let rr : partition.Fibre 3 := ⟨root,by decide⟩
  have hr : source.binary (root,root) (g.val rr).val (g.val rr).val :=
    (BinaryStructure.Aut.binary (partition.fibreStructure 3) g (root,root) rr rr).mpr
      ⟨(false,false),act_zero root,act_zero root⟩
  obtain ⟨s,hs,_⟩ := hr
  refine ⟨s,?_⟩
  intro x
  have hx : source.binary (root,x.val) (g.val rr).val (g.val x).val :=
    (BinaryStructure.Aut.binary (partition.fibreStructure 3) g (root,x.val) rr x).mpr
      ⟨(false,false),act_zero root,act_zero x.val⟩
  obtain ⟨t,ht,htx⟩ := hx
  have hts : t = s := root_injective (ht.trans hs.symm)
  exact htx.symm.trans (congrArg (fun t => act t x.val) hts)

theorem intrinsic_shift (i : Fin 4) (g : partition.Intrinsic i) :
    ∃ s : Shift, ∀ x, (g.val x).val = act s x.val := by
  fin_cases i
  · exact axis_permutation_shift 0 g.val
  · exact axis_permutation_shift 1 g.val
  · exact axis_permutation_shift 2 g.val
  · exact central_intrinsic_shift g

theorem intrinsic_binding_surjective (i : Fin 4) :
    Function.Surjective (partition.restrictFibre i) := by
  intro g
  obtain ⟨s,hs⟩ := intrinsic_shift i g
  refine ⟨shiftKernel s,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  exact (hs x).symm

theorem all_binding_intrinsic (i : Fin 4) : partition.binding i = ⊤ := by
  apply top_unique
  intro g _
  exact intrinsic_binding_surjective i g

theorem intrinsic_exponent_two (i : Fin 4) (g : partition.Intrinsic i) : g * g = 1 := by
  obtain ⟨s,hs⟩ := intrinsic_shift i g
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change (g.val (g.val x)).val = x.val
  rw [hs,hs,act_invol]

theorem all_axis_perms_aut (i : Fin 3) (g : Equiv.Perm (partition.Fibre i.castSucc)) :
    g ∈ (partition.fibreStructure i.castSucc).autGroup := by
  obtain ⟨s,hs⟩ := axis_permutation_shift i g
  have heq : (partition.restrictFibre i.castSucc (shiftKernel s)).val = g := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact (hs x).symm
  rw [←heq]
  exact (partition.restrictFibre i.castSucc (shiftKernel s)).property

def axisIntrinsicEquivPerm (i : Fin 3) :
    partition.Intrinsic i.castSucc ≃ Equiv.Perm (partition.Fibre i.castSucc) where
  toFun g := g.val
  invFun g := ⟨g,all_axis_perms_aut i g⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

theorem axis_fibre_card (i : Fin 3) : Nat.card (partition.Fibre i.castSucc) = 2 := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i <;> decide

theorem axis_intrinsic_card (i : Fin 3) : Nat.card (partition.Intrinsic i.castSucc) = 2 := by
  rw [Nat.card_congr (axisIntrinsicEquivPerm i),Nat.card_perm,axis_fibre_card]
  rfl

noncomputable def centralIntrinsicEquiv : Shift ≃ partition.Intrinsic 3 :=
  Equiv.ofBijective (fun s => partition.restrictFibre 3 (shiftKernel s)) (by
    constructor
    · intro s t hh
      apply root_injective
      exact congrArg (fun g : partition.Intrinsic 3 => (g.val ⟨root,by decide⟩).val) hh
    · intro g
      obtain ⟨s,hs⟩ := central_intrinsic_shift g
      refine ⟨s,?_⟩
      apply Subtype.ext
      apply Equiv.ext
      intro x
      apply Subtype.ext
      exact (hs x).symm)

theorem central_intrinsic_card : Nat.card (partition.Intrinsic 3) = 4 := by
  rw [←Nat.card_congr centralIntrinsicEquiv,Nat.card_eq_fintype_card]
  decide

theorem two_axis_shifts : ∀ (i j : Fin 3), i ≠ j → ∀ (s t : Shift),
    ∃ u : Shift, axisShift u i = axisShift s i ∧ axisShift u j = axisShift t j := by decide

theorem act_same_axis : ∀ (i : Fin 3) (s t : Shift) (x : Point),
    owner x = i.castSucc → axisShift s i = axisShift t i → act s x = act t x := by decide

theorem two_axes_permutations_shift : ∀ (i j : Fin 3), i ≠ j →
    ∀ (g : Equiv.Perm (partition.Fibre i.castSucc))
      (g' : Equiv.Perm (partition.Fibre j.castSucc)),
    ∃ s : Shift, (∀ x, (g x).val = act s x.val) ∧
      ∀ y, (g' y).val = act s y.val := by
  intro i j hij g g'
  obtain ⟨s,hs⟩ := axis_permutation_shift i g
  obtain ⟨t,ht⟩ := axis_permutation_shift j g'
  obtain ⟨u,hu,hv⟩ := two_axis_shifts i j hij s t
  exact ⟨u,fun x => (hs x).trans (act_same_axis i s u x.val x.property hu.symm),
    fun y => (ht y).trans (act_same_axis j t u y.val y.property hv.symm)⟩

/-- Actual pair projections onto any two of A,B,C are the entire product of
their intrinsic groups, not merely pairwise compatibility of abstract data.
-/
theorem actual_pair_axes_full (i j : Fin 3) (hij : i ≠ j) :
    partition.actualPair i.castSucc j.castSucc = ⊤ := by
  apply top_unique
  rintro ⟨g,g'⟩ _
  obtain ⟨s,hs,hs'⟩ := two_axes_permutations_shift i j hij g.val g'.val
  refine ⟨shiftKernel s,?_⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact (hs x).symm
  · apply Subtype.ext
    apply Equiv.ext
    intro y
    apply Subtype.ext
    exact (hs' y).symm

theorem actual_whole_ABC_iff (a b c : Bool) :
    (∃ g : source.Aut,
      (∀ x, g.val (A x) = A (a ^^ x)) ∧
      (∀ x, g.val (B x) = B (b ^^ x)) ∧
      (∀ x, g.val (C x) = C (c ^^ x))) ↔ c = (a ^^ b) := by
  constructor
  · rintro ⟨g,hA,hB,hC⟩
    exact (actual_ABC_iff a b c).mp
      ⟨g,by simpa using hA false,by simpa using hB false,by simpa using hC false⟩
  · intro hc
    subst c
    refine ⟨shiftAut (a,b),?_,?_,?_⟩
    · exact act_A (a,b)
    · exact act_B (a,b)
    · exact act_C (a,b)

theorem eliminated_odd_motion :
    (∃ g : source.Aut, g.val (A false) = A true ∧ g.val (B false) = B false) ∧
    (∃ g : source.Aut, g.val (A false) = A true ∧ g.val (C false) = C false) ∧
    (∃ g : source.Aut, g.val (B false) = B false ∧ g.val (C false) = C false) ∧
    ¬ ∃ g : source.Aut, g.val (A false) = A true ∧ g.val (B false) = B false ∧
      g.val (C false) = C false := by
  refine ⟨actual_AB_unrestricted _ _,actual_AC_unrestricted _ _,actual_BC_unrestricted _ _,?_⟩
  intro hg
  have hh := (actual_ABC_iff true false false).mp hg
  cases hh

end CCO.FiniteKernel.Countercontrols.HiddenParity
