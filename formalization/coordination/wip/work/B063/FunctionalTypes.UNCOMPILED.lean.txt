import CCO.AutomaticEPCore.FunctionalOriginal
import CCO.AutomaticEPCore.SourceLoopless

/-!
# Actual original functional actions on all realized prefix types

C14–C20 construct the label permutation from the support of the ORIGINAL
functional graph. Its totality, symmetry and square-identity are proved
on the actual unary reduct, using current homogeneous alignment. The
original functional permutation need not preserve any chosen marking.
-/

universe u v w r
namespace CCO.AutomaticEPCore

open CCO.APCharacter.Towers CCO.ExactEPGeometry CCO.ParityHasse.Original

noncomputable section

variable (A B : CurrentSource.{u,v,w,r})
variable (P : UnaryReduct A.source B.source)
variable (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)

/-- Actual support of the graph of one ORIGINAL equivariant permutation. -/
def originalFunctionalSupport (h : OriginalFunctionalGroup A.G (A.Point base))
    (s t : B.Sorts) : Prop :=
  prefixSupport P (originalRelation A base hOne (fun x y => h.val x = y)) s t

/-- The one-original-sort equivalence preserves the complete tagged old
colour, including the true logical diagonal. -/
theorem original_tagged_colour_one_sort
    (x y : Sigma A.Point) :
    taggedColour A.source x y =
      (⟨base,base,A.source.colour (originalPointEquiv A base hOne x)
        (originalPointEquiv A base hOne y)⟩ :
          Σ i : A.Sorts, Σ j : A.Sorts, Option (A.source.Atom i j)) := by
  rcases x with ⟨i,x⟩
  rcases y with ⟨j,y⟩
  cases hOne i
  cases hOne j
  rfl

/-- Original one-sort colour equality read through the literal unary
reduct, for arbitrary current endpoint sorts. -/
theorem original_reduct_pair_colour_eq
    (s t : B.Sorts) (x x' : B.Point s) (y y' : B.Point t)
    (hcol : B.source.colour x y = B.source.colour x' y') :
    A.source.colour
        (originalPointEquiv A base hOne (P.project ⟨s,x⟩))
        (originalPointEquiv A base hOne (P.project ⟨t,y⟩)) =
      A.source.colour
        (originalPointEquiv A base hOne (P.project ⟨s,x'⟩))
        (originalPointEquiv A base hOne (P.project ⟨t,y'⟩)) := by
  have hTagged : taggedColour A.source (P.project ⟨s,x⟩) (P.project ⟨t,y⟩) =
      taggedColour A.source (P.project ⟨s,x'⟩) (P.project ⟨t,y'⟩) := by
    change (⟨P.parent s,P.parent t,A.source.colour (P.point s x) (P.point t y)⟩ :
      Σ i : A.Sorts, Σ j : A.Sorts, Option (A.source.Atom i j)) =
        ⟨P.parent s,P.parent t,A.source.colour (P.point s x') (P.point t y')⟩
    rw [P.colour,P.colour,hcol]
  rw [original_tagged_colour_one_sort A base hOne,
    original_tagged_colour_one_sort A base hOne] at hTagged
  simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hTagged

/-- Current invariance of an original functional graph is derived from
old pair homogeneity and the actual fine-colour reduct equation. No
section from current automorphisms to original automorphisms is assumed. -/
theorem original_functional_prefix_invariant
    (h : OriginalFunctionalGroup A.G (A.Point base)) :
    PrefixInvariant (K := B.G) P
      (originalRelation A base hOne (fun x y => h.val x = y)) := by
  intro s t g x y hxy
  obtain ⟨x₀⟩ := A.source.nonemptySort base
  apply (original_functional_colour_iff A.source A.homogeneous h x₀ _ _).mp
  have hcol := original_reduct_pair_colour_eq A B P base hOne s t
    x (g • x) y (g • y)
    ((B.source.colourInvariant_of_homogeneous B.homogeneous g x y).symm)
  rw [← hcol]
  exact (original_functional_colour_iff A.source A.homogeneous h x₀ _ _).mpr hxy

/-- Every REALIZED prefix type has a functional-graph image. The image
point is lifted through the actual total-carrier bijection. -/
theorem original_functional_support_total
    (h : OriginalFunctionalGroup A.G (A.Point base)) (s : B.Sorts) :
    ∃ t, originalFunctionalSupport A B P base hOne h s t := by
  obtain ⟨x⟩ := B.source.nonemptySort s
  let e := prefixOriginalPointEquiv A B P base hOne
  let y := e.symm (h.val (e ⟨s,x⟩))
  refine ⟨y.1,x,y.2,?_⟩
  exact (e.apply_symm_apply (h.val (e ⟨s,x⟩))).symm

/-- The same original involution makes its actual prefix support symmetric. -/
theorem original_functional_support_symmetric
    (h : OriginalFunctionalGroup A.G (A.Point base))
    {s t : B.Sorts} (hst : originalFunctionalSupport A B P base hOne h s t) :
    originalFunctionalSupport A B P base hOne h t s := by
  obtain ⟨x,y,hxy⟩ := hst
  refine ⟨y,x,?_⟩
  change h.val (originalPointEquiv A base hOne (P.project ⟨t,y⟩)) = _
  rw [← hxy]
  exact original_functional_involutive A.source A.homogeneous h _

/-- The original graph composed with itself is literal real equality. -/
theorem original_functional_real_square
    (h : OriginalFunctionalGroup A.G (A.Point base)) :
    RawSymmetric.compose
        (originalRelation A base hOne (fun x y => h.val x = y))
        (originalRelation A base hOne (fun x y => h.val x = y)) = Eq := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    apply (originalPointEquiv A base hOne).injective
    calc
      originalPointEquiv A base hOne x =
          h.val (h.val (originalPointEquiv A base hOne x)) :=
        (original_functional_involutive A.source A.homogeneous h _).symm
      _ = h.val (originalPointEquiv A base hOne z) := congrArg h.val hxz
      _ = originalPointEquiv A base hOne y := hzy
  · rintro rfl
    refine ⟨(originalPointEquiv A base hOne).symm
      (h.val (originalPointEquiv A base hOne x)),?_,?_⟩
    · exact (Equiv.apply_symm_apply _ _).symm
    · change h.val (originalPointEquiv A base hOne
        ((originalPointEquiv A base hOne).symm _)) = _
      rw [Equiv.apply_symm_apply]
      exact original_functional_involutive A.source A.homogeneous h _

/-- C14: Phi preserves the actual represented square, with current
middle-point alignment discharged by proved graph invariance. -/
theorem original_functional_support_square
    (h : OriginalFunctionalGroup A.G (A.Point base)) (s t : B.Sorts) :
    (∃ q, originalFunctionalSupport A B P base hOne h s q ∧
      originalFunctionalSupport A B P base hOne h q t) ↔ s = t := by
  unfold originalFunctionalSupport
  rw [← prefixSupport_comp P B.homogeneous _ _
    (original_functional_prefix_invariant A B P base hOne h)]
  rw [original_functional_real_square A base hOne h]
  exact prefixSupport_identity P s t

/-- C15: totality, symmetry and literal square-identity force exactly
one supported type image, including in the zero-step and finite cases. -/
theorem original_functional_support_unique
    (h : OriginalFunctionalGroup A.G (A.Point base))
    {s t q : B.Sorts}
    (hst : originalFunctionalSupport A B P base hOne h s t)
    (hsq : originalFunctionalSupport A B P base hOne h s q) : t = q :=
  (original_functional_support_square A B P base hOne h t q).mp
    ⟨s,original_functional_support_symmetric A B P base hOne h hst,hsq⟩

/-- The unique actual type image, with the same map as its inverse. -/
def originalFunctionalTypePerm
    (h : OriginalFunctionalGroup A.G (A.Point base)) : Equiv.Perm B.Sorts where
  toFun s := (original_functional_support_total A B P base hOne h s).choose
  invFun s := (original_functional_support_total A B P base hOne h s).choose
  left_inv s := by
    let f := fun s => (original_functional_support_total A B P base hOne h s).choose
    have hs : originalFunctionalSupport A B P base hOne h s (f s) :=
      (original_functional_support_total A B P base hOne h s).choose_spec
    have ht : originalFunctionalSupport A B P base hOne h (f s) (f (f s)) :=
      (original_functional_support_total A B P base hOne h (f s)).choose_spec
    exact ((original_functional_support_square A B P base hOne h s (f (f s))).mp
      ⟨f s,hs,ht⟩).symm
  right_inv s := by
    let f := fun s => (original_functional_support_total A B P base hOne h s).choose
    have hs := (original_functional_support_total A B P base hOne h s).choose_spec
    have ht := (original_functional_support_total A B P base hOne h (f s)).choose_spec
    exact ((original_functional_support_square A B P base hOne h s (f (f s))).mp
      ⟨f s,hs,ht⟩).symm

/-- The permutation has EXACTLY the actual old-graph support relation. -/
theorem original_functional_type_perm_iff
    (h : OriginalFunctionalGroup A.G (A.Point base)) (s t : B.Sorts) :
    originalFunctionalTypePerm A B P base hOne h s = t ↔
      originalFunctionalSupport A B P base hOne h s t := by
  have hs := (original_functional_support_total A B P base hOne h s).choose_spec
  constructor
  · intro heq
    exact heq ▸ hs
  · intro hst
    exact original_functional_support_unique A B P base hOne h hs hst

/-- Every actual real point witnesses the SAME unique type image. This
retains all original point data, without asserting marked equivariance. -/
theorem original_functional_type_perm_point
    (h : OriginalFunctionalGroup A.G (A.Point base)) (x : Sigma B.Point) :
    originalFunctionalTypePerm A B P base hOne h x.1 =
      ((prefixOriginalPointEquiv A B P base hOne).symm
        (h.val (prefixOriginalPointEquiv A B P base hOne x))).1 := by
  apply (original_functional_type_perm_iff A B P base hOne h _ _).mpr
  let e := prefixOriginalPointEquiv A B P base hOne
  let y := e.symm (h.val (e x))
  refine ⟨x.2,y.2,?_⟩
  exact (e.apply_symm_apply (h.val (e x))).symm

/-- C15's literal involution on every realized prefix-type set. -/
theorem original_functional_type_perm_involutive
    (h : OriginalFunctionalGroup A.G (A.Point base)) :
    Function.Involutive (originalFunctionalTypePerm A B P base hOne h) :=
  (originalFunctionalTypePerm A B P base hOne h).left_inv

/-- Identity acts as identity on types, including true equality only. -/
theorem original_functional_type_perm_one :
    originalFunctionalTypePerm A B P base hOne 1 = 1 := by
  apply Equiv.ext
  intro s
  apply (original_functional_type_perm_iff A B P base hOne 1 s s).mpr
  obtain ⟨x⟩ := B.source.nonemptySort s
  exact ⟨x,x,rfl⟩

/-- C16: the actual original graph action respects the original group
multiplication, rather than choosing independent type involutions. -/
theorem original_functional_type_perm_mul
    (h k : OriginalFunctionalGroup A.G (A.Point base)) :
    originalFunctionalTypePerm A B P base hOne (h * k) =
      originalFunctionalTypePerm A B P base hOne h *
        originalFunctionalTypePerm A B P base hOne k := by
  apply Equiv.ext
  intro s
  obtain ⟨x⟩ := B.source.nonemptySort s
  let e := prefixOriginalPointEquiv A B P base hOne
  let y := e.symm (k.val (e ⟨s,x⟩))
  change originalFunctionalTypePerm A B P base hOne (h * k) s =
    originalFunctionalTypePerm A B P base hOne h
      (originalFunctionalTypePerm A B P base hOne k s)
  calc
    _ = (e.symm (h.val (k.val (e ⟨s,x⟩)))).1 :=
      original_functional_type_perm_point A B P base hOne (h * k) ⟨s,x⟩
    _ = (e.symm (h.val (e y))).1 := by rw [Equiv.apply_symm_apply]
    _ = originalFunctionalTypePerm A B P base hOne h y.1 :=
      (original_functional_type_perm_point A B P base hOne h y).symm
    _ = originalFunctionalTypePerm A B P base hOne h
        (originalFunctionalTypePerm A B P base hOne k s) := by
      rw [original_functional_type_perm_point A B P base hOne k ⟨s,x⟩]

/-- The actual group homomorphism to all prefix-type permutations. -/
def originalFunctionalTypeAction :
    OriginalFunctionalGroup A.G (A.Point base) →* Equiv.Perm B.Sorts where
  toFun := originalFunctionalTypePerm A B P base hOne
  map_one' := original_functional_type_perm_one A B P base hOne
  map_mul' := original_functional_type_perm_mul A B P base hOne

/-- Explicit type action; it is not an action by marked-source automorphisms. -/
@[instance_reducible] def originalFunctionalTypeMulAction :
    MulAction (OriginalFunctionalGroup A.G (A.Point base)) B.Sorts where
  smul h s := originalFunctionalTypePerm A B P base hOne h s
  one_smul s := congrArg (fun f : Equiv.Perm B.Sorts => f s)
    (original_functional_type_perm_one A B P base hOne)
  mul_smul h k s := congrArg (fun f : Equiv.Perm B.Sorts => f s)
    (original_functional_type_perm_mul A B P base hOne h k)

/-- C19: the ACTUAL forgetful parent map commutes with every original
functional type permutation. No section or marked automorphism is used. -/
theorem original_functional_type_perm_parent
    (C : CurrentSource.{u,v,w,r}) (Q : UnaryReduct B.source C.source)
    (h : OriginalFunctionalGroup A.G (A.Point base)) (s : C.Sorts) :
    Q.parent (originalFunctionalTypePerm A C (P.compose Q) base hOne h s) =
      originalFunctionalTypePerm A B P base hOne h (Q.parent s) := by
  symm
  apply (original_functional_type_perm_iff A B P base hOne h _ _).mpr
  obtain ⟨x,y,hxy⟩ :=
    (original_functional_type_perm_iff A C (P.compose Q) base hOne h s _).mp rfl
  exact ⟨Q.point s x,Q.point _ y,hxy⟩

/-- C17/C20: every nonidentity original functional element acts freely
on terminal realized types, by its ORIGINAL bipartite orbital graph. -/
theorem original_functional_terminal_free
    (terminal : ∀ s : B.Sorts, FullCoverTerminal B.source s)
    (h : OriginalFunctionalGroup A.G (A.Point base)) (hne : h ≠ 1)
    (s : B.Sorts) : originalFunctionalTypePerm A B P base hOne h s ≠ s := by
  intro hfix
  obtain ⟨a,ha,hBP⟩ :=
    original_functional_bipartite_atom A.source A.homogeneous h hne
  have hSupport := (original_functional_type_perm_iff A B P base hOne h s s).mp hfix
  obtain ⟨x,y,hxy⟩ := hSupport
  apply original_bipartite_table_loopless A B P base hOne terminal a hBP s
  exact ⟨x,y,(ha _ _).mpr hxy⟩

end
end CCO.AutomaticEPCore
