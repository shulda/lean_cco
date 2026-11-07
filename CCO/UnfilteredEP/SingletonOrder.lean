import CCO.APRamseyReadout.SmallerLanguage

/-!
# Uniqueness of the full block order on one generated root

The structural step is explicit: when a generated support has at most one
point of each hidden target sort, the fixed priority determines its entire
block order. This applies to every term value, not only the displayed
selected coordinates. The actual terminal source supplies this injectivity
separately from the independent symmetric-coordinate argument.
-/

universe u v w r l k
namespace CCO.UnfilteredEP
open CCO.FullCode CCO.APRamseyReadout
noncomputable section

/-- A block order on a support with no repeated hidden sort has no free
comparison. The statement concerns the whole support. -/
theorem blockOrder_unique_of_sort_injective
    {I : Type u} {V : Type v} (sort : V → I)
    (priority : LinearOrder I) (injective : Function.Injective sort)
    (a b : LinearOrder V)
    (ha : sortBlockOrder sort priority a = a)
    (hb : sortBlockOrder sort priority b = b) : a = b := by
  apply LinearOrder.ext_lt
  intro x y
  by_cases hxy : x = y
  · subst y
    exact ⟨fun h => False.elim (@lt_irrefl V a.toPreorder x h),
      fun h => False.elim (@lt_irrefl V b.toPreorder x h)⟩
  · have hs : sort x ≠ sort y := fun h => hxy (injective h)
    have hA := sortBlockOrder_different sort priority a hs
    have hB := sortBlockOrder_different sort priority b hs
    rw [ha] at hA
    rw [hb] at hB
    exact hA.trans hB.symm

section Readout
variable {ι : Type u} {X : ι → Type v}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {L : Language.{l}} {V : Type k} {C : Structure L V}
variable {scheme : RootScheme L} {S : CCO.AtomicSource.{u,v,w} ι X}
variable (D : TupleInterpretation (G := G) S C scheme)
variable (priority : LinearOrder L.Sorts)

/-- The full readout of a singleton is unique after the actual
same-target term-value uniqueness has been established. No Ramsey or EP
premise occurs in this elementary implication. -/
theorem blockReadout_subsingleton_of_sort_injective
    (A : CCO.FiniteInduced (X := X))
    (injective : Function.Injective (D.supportStructure A).sort) :
    Subsingleton (D.BlockReadoutOn priority A) := by
  constructor
  intro a b
  apply Subtype.ext
  apply TupleInterpretation.ReadoutOn.ext
  exact blockOrder_unique_of_sort_injective (D.supportStructure A).sort
    priority injective a.val.order b.val.order a.property b.property

/-- Existence is independent of the uniqueness argument: take any
finite support order and concatenate its sort blocks. -/
@[instance_reducible] def blockReadout_unique_of_sort_injective
    (A : CCO.FiniteInduced (X := X))
    (injective : Function.Injective (D.supportStructure A).sort) :
    Unique (D.BlockReadoutOn priority A) := by
  letI := blockReadout_subsingleton_of_sort_injective D priority A injective
  exact { default := Classical.choice (D.block_readout_nonempty priority A),
          uniq := fun _ => Subsingleton.elim _ _ }

end Readout
end
end CCO.UnfilteredEP
