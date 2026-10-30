import CCO.FiniteKernel.Named.Axes
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Bool

/-! B041 C56: the actual fine and coarse full binary phase groups. Fine
has two named two-point phase sorts. Coarse collapses the first sort to a
singleton and retains the second. The resulting full-group homomorphism has
trivial kernel, whereas the full intrinsic first-axis group has a nontrivial
swap. These are full named binary groups, not a chosen proper acting subgroup.
The infinite homogeneous clone source and exact phase cuts are supplied by
the separate PhaseSource boundary module. -/

namespace CCO.SimultaneousQuotients.Boundaries.PhaseKernel
open FiniteKernel

abbrev FinePoint := Bool × Bool
abbrev CoarsePoint := Option Bool

def fine : BinaryStructure FinePoint where
  Unary := Bool
  Binary := Bool
  unary s p := p.1 = s
  binary c p q := Bool.xor p.2 q.2 = c

def coarse : BinaryStructure CoarsePoint where
  Unary := Bool
  Binary := Bool
  unary s p := p.isSome = s
  binary c p q := match p,q with
    | some x, some y => Bool.xor x y = c
    | _,_ => False

abbrev FineAut := fine.Aut
abbrev CoarseAut := coarse.Aut

@[simp] theorem fine_sort (g : FineAut) (p : FinePoint) : (g.val p).1 = p.1 :=
  (g.property.1 p.1 p).mpr rfl

def restrictV (g : FineAut) : Equiv.Perm Bool where
  toFun b := (g.val (true,b)).2
  invFun b := (g⁻¹.val (true,b)).2
  left_inv b := by
    have hp : g.val (true,b) = (true,(g.val (true,b)).2) :=
      Prod.ext (fine_sort g (true,b)) rfl
    have h := congrArg Prod.snd (g.val.symm_apply_apply (true,b))
    rw [hp] at h
    exact h
  right_inv b := by
    have hp : g⁻¹.val (true,b) = (true,(g⁻¹.val (true,b)).2) :=
      Prod.ext (fine_sort g⁻¹ (true,b)) rfl
    have h := congrArg Prod.snd (g.val.apply_symm_apply (true,b))
    change (g.val (g⁻¹.val (true,b))).2 = b at h
    rw [hp] at h
    exact h

@[simp] theorem fine_on_V (g : FineAut) (b : Bool) :
    g.val (true,b) = (true,restrictV g b) :=
  Prod.ext (fine_sort g (true,b)) rfl

def coarsePerm (g : FineAut) : Equiv.Perm CoarsePoint := (restrictV g).optionCongr

@[simp] theorem coarsePerm_none (g : FineAut) : coarsePerm g none = none := rfl
@[simp] theorem coarsePerm_some (g : FineAut) (b : Bool) :
    coarsePerm g (some b) = some (restrictV g b) := rfl

def descend (g : FineAut) : CoarseAut := by
  refine ⟨coarsePerm g, ?_⟩
  constructor
  · intro s p
    cases p <;> exact Iff.rfl
  · intro c p q
    cases p with
    | none => exact Iff.rfl
    | some x =>
      cases q with
      | none => exact Iff.rfl
      | some y =>
        exact g.property.2 c (true,x) (true,y)

def descent : FineAut →* CoarseAut where
  toFun := descend
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    cases p <;> rfl
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    cases p with
    | none => rfl
    | some b =>
      change some ((g.val (h.val (true,b))).2) =
        some ((g.val (true,(h.val (true,b)).2)).2)
      rw [fine_on_V h b]

/-- Fixing just the second phase sort pointwise already fixes the entire fine
structure, because cross XOR determines every other phase. -/
theorem fineAut_eq_one_of_fixes_V (g : FineAut)
    (h : ∀ b, g.val (true,b) = (true,b)) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  have hx := (g.property.2 p.2 p (true,false)).mpr (by
    change Bool.xor p.2 false = p.2
    cases p.2 <;> rfl)
  change Bool.xor (g.val p).2 (g.val (true,false)).2 = p.2 at hx
  rw [h false] at hx
  have hx' : (g.val p).2 = p.2 := by simpa only [Bool.xor_false] using hx
  exact Prod.ext (fine_sort g p) hx'

/-- The pointwise fine/coarse owner kernel is TRIVIAL, although the first
intrinsic axis below has a genuine nonidentity automorphism. -/
theorem descent_injective : Function.Injective descent := by
  apply (descent.ker_eq_bot_iff).mp
  apply Subgroup.ext
  intro g
  change descent g = 1 ↔ g = 1
  constructor
  · intro hg
    apply fineAut_eq_one_of_fixes_V g
    intro b
    have hb := congrArg (fun a : CoarseAut => a.val (some b)) hg
    change some (restrictV g b) = some b at hb
    rw [fine_on_V]
    exact congrArg (Prod.mk true) (Option.some.inj hb)
  · intro hg
    subst g
    exact descent.map_one

theorem pointwise_kernel_trivial : descent.ker = ⊥ :=
  descent.ker_eq_bot_iff.mpr descent_injective

/-- Full intrinsic binary structure of the first named fine sort. -/
def intrinsic : BinaryStructure Bool where
  Unary := Bool
  Binary := Bool
  unary s _ := false = s
  binary c x y := Bool.xor x y = c

def swap : intrinsic.Aut := by
  refine ⟨Equiv.boolNot, ?_⟩
  constructor
  · intro s x
    exact Iff.rfl
  · intro c x y
    change Bool.xor (!x) (!y) = c ↔ Bool.xor x y = c
    cases c <;> cases x <;> cases y <;> decide

theorem swap_ne_one : swap ≠ 1 := by
  intro h
  have hh := congrArg (fun g : intrinsic.Aut => g.val false) h
  change true = false at hh
  cases hh

/-- Therefore an intrinsic-binding isomorphism for the owner kernel cannot
exist, even though the fine full-group pair image remains subdirect. -/
theorem no_intrinsic_binding : ¬ Nonempty (descent.ker ≃* intrinsic.Aut) := by
  rintro ⟨e⟩
  have hk : Subsingleton descent.ker := by
    rw [pointwise_kernel_trivial]
    infer_instance
  have hswap : swap = 1 := by
    have h := Subsingleton.elim (e.symm swap) (e.symm 1)
    exact e.symm.injective h
  exact swap_ne_one hswap

end CCO.SimultaneousQuotients.Boundaries.PhaseKernel
