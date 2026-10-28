import CCO.RealHull.Geometry.Supports

/-! Least generated ORIGINAL global equivalence support, by intersection of
all genuine globally composition-closed supports. Finite original palettes
make every support finite; no RAW word-exactness is involved. -/
universe v w
namespace CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def generatedSet (U : Set (Atom S)) : Set (Atom S) :=
  {a | ∀ R : Support S, U ⊆ R.val → a ∈ R.val}

theorem generated_plus_le (U : Set (Atom S)) (R : Support S) (hUR : U ⊆ R.val) :
    plus S (generatedSet S U) ⊆ plus S R.val := by
  intro c hc
  cases c with
  | none => exact none_mem_plus S _
  | some a => exact (some_mem_plus S _ _).mpr (((some_mem_plus S _ _).mp hc) R hUR)

def generatedSupport (U : Set (Atom S)) : Support S :=
  ⟨generatedSet S U,by
    intro c hc
    cases c with
    | none => exact none_mem_plus S _
    | some a =>
      apply (some_mem_plus S _ _).mpr
      intro R hUR
      exact (some_mem_plus S _ _).mp
        (R.property (prod_mono S (generated_plus_le S U R hUR) (generated_plus_le S U R hUR) hc))⟩

theorem subset_generated (U : Set (Atom S)) : U ⊆ (generatedSupport S U).val :=
  fun _ ha _ hUR => hUR ha

theorem generated_le (U : Set (Atom S)) (R : Support S) (hUR : U ⊆ R.val) :
    (generatedSupport S U).val ⊆ R.val := fun _ ha => ha R hUR

theorem generated_eq_of_support (R : Support S) : generatedSupport S R.val = R := by
  apply Subtype.ext
  exact Set.Subset.antisymm (generated_le S R.val R Set.Subset.rfl) (subset_generated S R.val)

theorem generated_mono {U V : Set (Atom S)} (hUV : U ⊆ V) :
    (generatedSupport S U).val ⊆ (generatedSupport S V).val :=
  generated_le S U _ (Set.Subset.trans hUV (subset_generated S V))

theorem finite_support (R : Support S) : R.val.Finite := by
  letI := S.finiteAtom () ()
  exact Set.toFinite _

end CCO.RealHull.Geometry
