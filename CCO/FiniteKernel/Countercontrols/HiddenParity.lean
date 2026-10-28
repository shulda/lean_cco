import CCO.FiniteKernel.Partition
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

/-!
# The actual canonical binary hidden-parity countercontrol

The named disjoint fibres are A=B=C=F₂ and D=F₂². Every actual ordered-pair
orbital of the four displayed shifts is named. The FULL automorphism group
is proved to be exactly those shifts, using the orbitals through D(0,0).
No homogeneity, CCO, SAP or exact-source claim is made.
-/

namespace CCO.FiniteKernel.Countercontrols.HiddenParity

abbrev Shift := Bool × Bool
abbrev Point := (Fin 3 × Bool) ⊕ (Bool × Bool)

def axisShift (s : Shift) (i : Fin 3) : Bool :=
  if i = 0 then s.1 else if i = 1 then s.2 else s.1 ^^ s.2

def act (s : Shift) : Point → Point
  | .inl (i,b) => .inl (i,axisShift s i ^^ b)
  | .inr (a,b) => .inr (s.1 ^^ a,s.2 ^^ b)

def sumShift (s t : Shift) : Shift := (s.1 ^^ t.1,s.2 ^^ t.2)

theorem act_zero : ∀ x, act (false,false) x = x := by decide
theorem act_invol : ∀ s x, act s (act s x) = x := by decide
theorem act_sum : ∀ s t x, act (sumShift s t) x = act s (act t x) := by decide

def shiftPerm (s : Shift) : Equiv.Perm Point where
  toFun := act s
  invFun := act s
  left_inv := act_invol s
  right_inv := act_invol s

def owner : Point → Fin 4
  | .inl (i,_) => ⟨i.val,by omega⟩
  | .inr _ => 3

theorem owner_act : ∀ s x, owner (act s x) = owner x := by decide

/-- Every actual ordered-pair orbital is named; duplicate names are harmless. -/
def orbital (p q x y : Point) : Prop := ∃ s : Shift, act s p = x ∧ act s q = y

instance (p q x y : Point) : Decidable (orbital p q x y) :=
  inferInstanceAs (Decidable (∃ s : Shift, act s p = x ∧ act s q = y))

def source : BinaryStructure Point where
  Unary := Fin 4
  Binary := Point × Point
  unary i x := owner x = i
  binary r x y := orbital r.1 r.2 x y

theorem orbital_shift_iff (s : Shift) (p q x y : Point) :
    orbital p q (act s x) (act s y) ↔ orbital p q x y := by
  constructor
  · rintro ⟨t,htp,htq⟩
    refine ⟨sumShift s t,?_,?_⟩
    · rw [act_sum,htp,act_invol]
    · rw [act_sum,htq,act_invol]
  · rintro ⟨t,htp,htq⟩
    exact ⟨sumShift s t,by rw [act_sum,htp],by rw [act_sum,htq]⟩

def shiftAut (s : Shift) : source.Aut := ⟨shiftPerm s,by
  constructor
  · intro r x
    change owner (act s x) = r ↔ owner x = r
    rw [owner_act]
  · intro r x y
    exact orbital_shift_iff s r.1 r.2 x y⟩

def root : Point := .inr (false,false)

theorem root_injective : Function.Injective (fun s => act s root) := by decide

/-- FULL automorphisms are determined by their image on D(0,0), rather than
merely containing the displayed shift group as a subgroup.
-/
theorem fullAut_eq_shift (g : source.Aut) : ∃ s : Shift, ∀ x, g.val x = act s x := by
  have hroot : source.binary (root,root) (g.val root) (g.val root) :=
    (BinaryStructure.Aut.binary source g (root,root) root root).mpr
      ⟨(false,false),act_zero root,act_zero root⟩
  obtain ⟨s,hs,_⟩ := hroot
  refine ⟨s,?_⟩
  intro x
  have hx : source.binary (root,x) (g.val root) (g.val x) :=
    (BinaryStructure.Aut.binary source g (root,x) root x).mpr
      ⟨(false,false),act_zero root,act_zero x⟩
  obtain ⟨t,ht,htx⟩ := hx
  have hts : t = s := root_injective (ht.trans hs.symm)
  exact htx.symm.trans (congrArg (fun t => act t x) hts)

theorem shiftAut_injective : Function.Injective shiftAut := by
  intro s t h
  apply root_injective
  exact congrArg (fun g : source.Aut => g.val root) h

theorem shiftAut_surjective : Function.Surjective shiftAut := by
  intro g
  obtain ⟨s,hs⟩ := fullAut_eq_shift g
  refine ⟨s,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  exact fun x => (hs x).symm

noncomputable def fullAutEquiv : Shift ≃ source.Aut := Equiv.ofBijective shiftAut
  ⟨shiftAut_injective,shiftAut_surjective⟩

theorem fullAut_card : Nat.card source.Aut = 4 := by
  rw [←Nat.card_congr fullAutEquiv]
  rw [Nat.card_eq_fintype_card]
  decide

def A (b : Bool) : Point := .inl (0,b)
def B (b : Bool) : Point := .inl (1,b)
def C (b : Bool) : Point := .inl (2,b)
def D (a b : Bool) : Point := .inr (a,b)

theorem act_A : ∀ s b, act s (A b) = A (s.1 ^^ b) := by decide
theorem act_B : ∀ s b, act s (B b) = B (s.2 ^^ b) := by decide
theorem act_C : ∀ s b, act s (C b) = C ((s.1 ^^ s.2) ^^ b) := by decide

theorem actual_ABC_iff (a b c : Bool) :
    (∃ g : source.Aut, g.val (A false) = A a ∧ g.val (B false) = B b ∧
      g.val (C false) = C c) ↔ c = (a ^^ b) := by
  constructor
  · rintro ⟨g,hA,hB,hC⟩
    obtain ⟨s,hs⟩ := fullAut_eq_shift g
    rw [hs,act_A] at hA
    rw [hs,act_B] at hB
    rw [hs,act_C] at hC
    have h : ∀ s : Shift, ∀ a b c,
        A (s.1 ^^ false) = A a → B (s.2 ^^ false) = B b →
        C ((s.1 ^^ s.2) ^^ false) = C c → c = (a ^^ b) := by decide
    exact h s a b c hA hB hC
  · intro hc
    subst c
    exact ⟨shiftAut (a,b),by simp [shiftAut,shiftPerm,act_A],
      by simp [shiftAut,shiftPerm,act_B],by simp [shiftAut,shiftPerm,act_C]⟩

theorem actual_AB_unrestricted (a b : Bool) :
    ∃ g : source.Aut, g.val (A false) = A a ∧ g.val (B false) = B b := by
  obtain ⟨g,hA,hB,_⟩ := (actual_ABC_iff a b (a ^^ b)).mpr rfl
  exact ⟨g,hA,hB⟩

theorem actual_AC_unrestricted (a c : Bool) :
    ∃ g : source.Aut, g.val (A false) = A a ∧ g.val (C false) = C c := by
  have hh : c = (a ^^ (a ^^ c)) := by cases a <;> cases c <;> decide
  obtain ⟨g,hA,_,hC⟩ := (actual_ABC_iff a (a ^^ c) c).mpr hh
  exact ⟨g,hA,hC⟩

theorem actual_BC_unrestricted (b c : Bool) :
    ∃ g : source.Aut, g.val (B false) = B b ∧ g.val (C false) = C c := by
  have hh : c = ((b ^^ c) ^^ b) := by cases b <;> cases c <;> decide
  obtain ⟨g,_,hB,hC⟩ := (actual_ABC_iff (b ^^ c) b c).mpr hh
  exact ⟨g,hB,hC⟩

theorem all_owners_fixed (g : source.Aut) (x : Point) : owner (g.val x) = owner x := by
  obtain ⟨s,hs⟩ := fullAut_eq_shift g
  rw [hs,owner_act]

def partition : FinitePartition source (Fin 4) where
  owner := owner
  surjective := by decide
  finite_fibre _ := inferInstance
  invariant g x y := by rw [all_owners_fixed g x,all_owners_fixed g y]

theorem owner_kernel_full : partition.kernel = ⊤ := by
  apply top_unique
  intro g _
  exact partition.mem_kernel_iff g |>.mpr (all_owners_fixed g)

/-- The actual domain contains the WHOLE three binary fibres. -/
def ABC : Finset Point := Finset.univ.filter (fun x => owner x ≠ 3)

def flipA : Point → Point
  | .inl (i,b) => if i = 0 then .inl (i,!b) else .inl (i,b)
  | .inr p => .inr p

theorem flipA_invol : ∀ x, flipA (flipA x) = x := by decide

def partialFlip : ↥ABC → Point := fun x => flipA x.val

theorem partialFlip_injective : Function.Injective partialFlip := by
  intro x y h
  apply Subtype.ext
  exact (flipA_invol x.val).symm.trans ((congrArg flipA h).trans (flipA_invol y.val))

theorem partialFlip_unary : ∀ r x, source.unary r (partialFlip x) ↔ source.unary r x.val := by
  change ∀ (r : Fin 4) (x : ↥ABC), owner (flipA x.val) = r ↔ owner x.val = r
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem partialFlip_binary : ∀ r x y,
    source.binary r (partialFlip x) (partialFlip y) ↔ source.binary r x.val y.val := by
  change ∀ (r : Point × Point) (x y : ↥ABC),
    orbital r.1 r.2 (flipA x.val) (flipA y.val) ↔ orbital r.1 r.2 x.val y.val
  decide

theorem partialFlip_not_extendible :
    ¬ ∃ g : source.Aut, ∀ x : ↥ABC, g.val x.val = partialFlip x := by
  rintro ⟨g,hg⟩
  have hA := hg ⟨A false,by decide⟩
  have hB := hg ⟨B false,by decide⟩
  have hC := hg ⟨C false,by decide⟩
  have hp := (actual_ABC_iff true false false).mp ⟨g,hA,hB,hC⟩
  cases hp

theorem not_homogeneous : ¬ source.Homogeneous := by
  intro hH
  exact partialFlip_not_extendible
    (hH ABC partialFlip partialFlip_injective partialFlip_unary partialFlip_binary)

end CCO.FiniteKernel.Countercontrols.HiddenParity
