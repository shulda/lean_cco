import CCO.FiniteKernel.Named.Axes
import Mathlib.Data.Bool.Basic
import Mathlib.Logic.Equiv.Bool
import Mathlib.SetTheory.Cardinal.Finite

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

/-- Every permutation of a two-point phase set preserves XOR difference. -/
theorem perm_preserves_xor (e : Equiv.Perm Bool) (x y : Bool) :
    Bool.xor (e x) (e y) = Bool.xor x y := by
  have hne : e false ≠ e true := e.injective.ne (by decide)
  cases h0 : e false <;> cases h1 : e true <;> cases x <;> cases y <;> simp_all

def globalPhase (e : Equiv.Perm Bool) : FineAut := by
  refine ⟨Equiv.prodCongr (Equiv.refl Bool) e, ?_⟩
  constructor
  · intro c p
    exact Iff.rfl
  · intro c p q
    change Bool.xor (e p.2) (e q.2) = c ↔ Bool.xor p.2 q.2 = c
    rw [perm_preserves_xor]

def coarseOfPerm (e : Equiv.Perm Bool) : CoarseAut := by
  refine ⟨e.optionCongr, ?_⟩
  constructor
  · intro c p
    cases p <;> exact Iff.rfl
  · intro c p q
    cases p with
    | none => exact Iff.rfl
    | some x =>
      cases q with
      | none => exact Iff.rfl
      | some y =>
        change Bool.xor (e x) (e y) = c ↔ Bool.xor x y = c
        rw [perm_preserves_xor]

theorem coarse_fixes_none (g : CoarseAut) : g.val none = none := by
  have h := (g.property.1 false none).mpr rfl
  change (g.val none).isSome = false at h
  cases hp : g.val none with
  | none => rfl
  | some b => rw [hp] at h; cases h

def coarseEquivPerm : CoarseAut ≃ Equiv.Perm Bool where
  toFun g := g.val.removeNone
  invFun := coarseOfPerm
  left_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    cases p with
    | none => exact (coarse_fixes_none g).symm
    | some b =>
      apply Equiv.removeNone_some g.val
      have h := (g.property.1 true (some b)).mpr rfl
      change (g.val (some b)).isSome = true at h
      cases hp : g.val (some b) with
      | none => rw [hp] at h; cases h
      | some c => exact ⟨c,rfl⟩
  right_inv e := Equiv.removeNone_optionCongr e

theorem coarse_card_two : Nat.card CoarseAut = 2 := by
  rw [Nat.card_congr coarseEquivPerm, Nat.card_eq_fintype_card, Fintype.card_perm]
  rfl

/-- Every full coarse automorphism has a fine lift in this concrete model;
its unique pointwise kernel element is nevertheless only the identity. -/
theorem descent_surjective : Function.Surjective descent := by
  intro g
  refine ⟨globalPhase (coarseEquivPerm g), ?_⟩
  exact coarseEquivPerm.left_inv g

noncomputable def fineCoarseEquiv : FineAut ≃* CoarseAut :=
  MulEquiv.ofBijective descent ⟨descent_injective,descent_surjective⟩

theorem fine_card_two : Nat.card FineAut = 2 := by
  rw [Nat.card_congr fineCoarseEquiv.toEquiv]
  exact coarse_card_two

/-- The full fine group acts by ONE common phase permutation on both sorts,
so its two-coordinate image is the diagonal two-element group. -/
theorem fine_action_diagonal (g : FineAut) (s b : Bool) :
    g.val (s,b) = (s,restrictV g b) := by
  have h := (g.property.2 false (s,b) (true,b)).mpr (by
    change Bool.xor b b = false
    cases b <;> rfl)
  change Bool.xor (g.val (s,b)).2 (g.val (true,b)).2 = false at h
  have he : (g.val (s,b)).2 = (g.val (true,b)).2 := by
    cases hx : (g.val (s,b)).2 <;> cases hy : (g.val (true,b)).2 <;> simp_all
  exact Prod.ext (fine_sort g (s,b)) he

theorem full_pair_diagonal (eU eV : Equiv.Perm Bool) :
    (∃ g : FineAut, (∀ b, g.val (false,b) = (false,eU b)) ∧
      (∀ b, g.val (true,b) = (true,eV b))) ↔ eU = eV := by
  constructor
  · rintro ⟨g,hU,hV⟩
    apply Equiv.ext
    intro b
    have hu := congrArg Prod.snd ((hU b).symm.trans (fine_action_diagonal g false b))
    have hv := congrArg Prod.snd ((hV b).symm.trans (fine_action_diagonal g true b))
    exact hu.trans hv.symm
  · intro h
    subst eV
    exact ⟨globalPhase eU,fun _ => rfl,fun _ => rfl⟩

def intrinsicEquivPerm : intrinsic.Aut ≃* Equiv.Perm Bool where
  toFun := Subtype.val
  invFun e := ⟨e, ⟨fun _ _ => Iff.rfl, fun c x y => by
    change Bool.xor (e x) (e y) = c ↔ Bool.xor x y = c
    rw [perm_preserves_xor]⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem intrinsic_card_two : Nat.card intrinsic.Aut = 2 := by
  rw [Nat.card_congr intrinsicEquivPerm.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm]
  rfl

def firstAxis : Set FinePoint := {p | p.1 = false}

def firstAxisEquiv : Bool ≃ ↥firstAxis where
  toFun b := ⟨(false,b),rfl⟩
  invFun p := p.val.2
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext p.property.symm rfl)

/-- The displayed intrinsic structure is exactly the induced binary language
on the ENTIRE first fine sort, under this explicit carrier equivalence. -/
def intrinsicToAxis (g : intrinsic.Aut) : (fine.induced firstAxis).Aut := by
  refine ⟨firstAxisEquiv.symm.trans (g.val.trans firstAxisEquiv), ?_⟩
  constructor
  · intro c p
    change false = c ↔ p.val.1 = c
    rw [p.property]
  · intro c p q
    exact g.property.2 c p.val.2 q.val.2

def axisToIntrinsic (g : (fine.induced firstAxis).Aut) : intrinsic.Aut := by
  refine ⟨firstAxisEquiv.trans (g.val.trans firstAxisEquiv.symm), ?_⟩
  constructor
  · intro c p
    exact Iff.rfl
  · intro c p q
    exact g.property.2 c (firstAxisEquiv p) (firstAxisEquiv q)

def intrinsicEquivInduced : intrinsic.Aut ≃* (fine.induced firstAxis).Aut where
  toFun := intrinsicToAxis
  invFun := axisToIntrinsic
  left_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl
  right_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change firstAxisEquiv (firstAxisEquiv.symm
      (g.val (firstAxisEquiv (firstAxisEquiv.symm x)))) = g.val x
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change firstAxisEquiv (g.val (h.val (firstAxisEquiv.symm x))) =
      firstAxisEquiv (g.val (firstAxisEquiv.symm
        (firstAxisEquiv (h.val (firstAxisEquiv.symm x)))))
    rw [Equiv.symm_apply_apply]

theorem actual_intrinsic_card_two : Nat.card (fine.induced firstAxis).Aut = 2 := by
  rw [Nat.card_congr intrinsicEquivInduced.symm.toEquiv]
  exact intrinsic_card_two

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

/-- The same failure for the literal induced full first-axis group. -/
theorem no_actual_intrinsic_binding :
    ¬ Nonempty (descent.ker ≃* (fine.induced firstAxis).Aut) := by
  rintro ⟨e⟩
  exact no_intrinsic_binding ⟨e.trans intrinsicEquivInduced.symm⟩

end CCO.SimultaneousQuotients.Boundaries.PhaseKernel
