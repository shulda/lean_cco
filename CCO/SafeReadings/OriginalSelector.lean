import CCO.SafeReadings.NoReturn

/-! The original-H consumer uses the accepted original gate engine, after
identifying its genuine generation graph with the original instance of Q. -/
universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t} (A : PureTagAction S Λ N)

/-- Exact ORIGINAL multipliers, rather than an augmented safe menu, are
precisely the multipliers in the accepted original ActionGenerated type. -/
theorem original_generated_iff {seed D : TaggedMenu S} :
    ActionGenerated S A seed D ↔ Generated S (originalFamily S) A seed D := by
  constructor
  · intro h
    induction h with
    | seed => exact .seed
    | opposite h ih => exact .opposite ih
    | left P hP h ih => exact .left P hP ih
    | right P hP h ih => exact .right P hP ih
    | action g h ih => exact .action g ih
  · intro h
    induction h with
    | seed => exact .seed
    | opposite h ih => exact .opposite ih
    | left P hP h ih => exact .left P hP ih
    | right P hP h ih => exact .right P hP ih
    | action g h ih => exact .action g ih

theorem original_generatedFamily (seed : TaggedMenu S) :
    Selectors.generatedFamily S A seed = generatedFamily S (originalFamily S) A seed := by
  ext D
  exact original_generated_iff S A

/-- Explicitly discharge the old conditional engine's PureNoReturn
premise by the new proved separation on the ORIGINAL instance. -/
theorem pureNoReturn_of_original_noReturn
    (h : NoReturn S (originalFamily S) A) : PureNoReturn S A := by
  intro seed hs D E hD hE hp he
  apply h seed hs D E
  · rwa [← original_generatedFamily S A]
  · rwa [← original_generatedFamily S A]
  · exact hp
  · simpa only [← original_generatedFamily S A] using he

/-- The engine is applied only to ORIGINAL H. The actual source no-return
lemma supplies h; augmented K uses the separately proved Q gate engine. -/
theorem original_selector_of_noReturn
    {G : Type*} [Group G] [∀ i, MulAction G (X i)] [Fintype Λ]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,0,w} S)
    (h : NoReturn S (originalFamily S) A) :
    ∃ selector : HereditarySelector S, selector.Covariant S A :=
  exists_covariant_selector_of_pure_noReturn S H sap cco A
    (pureNoReturn_of_original_noReturn S A h)

end CCO.SafeReadings
