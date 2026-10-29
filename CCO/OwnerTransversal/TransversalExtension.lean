import CCO.OwnerTransversal.TransversalInstance

/-! Actual origin-level extension over an already prescribed finite
embedding.  The age and homogeneity used here are the internally
constructed providers, not additional source hypotheses. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe v w t
namespace CCO.OwnerTransversal.TransversalAge
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds CountableColour

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

/-- Arbitrary finite index universes can be used as actual origin charts. -/
theorem embed_origins {I : Type*} [Finite I] (a : I → NamedCarrier S H R B)
    (hs : ∀ i j, i ≠ j → ¬ finitePacket S H (a i).val (a j).val) :
    ∃ f : I ↪ U S H R B,
      (∀ i, (limitTable S H R B).owner (f i) = ownerLabel S H R B (a i)) ∧
      ∀ i j, (limitTable S H R B).colour (f i) (f j) = col S (a i).val (a j).val := by
  classical
  let : Fintype I := Fintype.ofFinite _
  let Q := Chart.ofPoints a hs
  obtain ⟨f,ho,hc⟩ := embed_chart S H R B Q
  let e := Fintype.equivFin I
  refine ⟨e.toEmbedding.trans f,?_,?_⟩
  · intro i
    exact (ho (e i)).trans (by
      change ownerLabel S H R B (a (e.symm (e i))) = _
      rw [Equiv.symm_apply_apply])
  · intro i j
    exact (hc (e i) (e j)).trans (by
      change col S (a (e.symm (e i))).val (a (e.symm (e j))).val = _
      rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply])

/-- A supplied old origin embedding extends over every actual larger
finite origin chart. All old points, literal owners and fine pairs remain. -/
theorem extend_origins {I J : Type*} [Finite I] [Finite J] (e : I ↪ J)
    (a : J → NamedCarrier S H R B)
    (hs : ∀ i j, i ≠ j → ¬ finitePacket S H (a i).val (a j).val)
    (f : I ↪ U S H R B)
    (ho : ∀ i, (limitTable S H R B).owner (f i) = ownerLabel S H R B (a (e i)))
    (hc : ∀ i j, (limitTable S H R B).colour (f i) (f j) =
      col S (a (e i)).val (a (e j)).val) :
    ∃ g : J ↪ U S H R B,
      (∀ i, g (e i) = f i) ∧
      (∀ j, (limitTable S H R B).owner (g j) = ownerLabel S H R B (a j)) ∧
      ∀ i j, (limitTable S H R B).colour (g i) (g j) = col S (a i).val (a j).val := by
  obtain ⟨h,hOwner,hColour⟩ := embed_origins S H R B a hs
  obtain ⟨k,hk⟩ := tuple_homogeneous S H R B (fun i => h (e i)) f
    (fun i => (hOwner (e i)).trans (ho i).symm)
    (fun i j => (hColour (e i) (e j)).trans (hc i j).symm)
  have hp := (limitCoding S H R B).embedding_preserves (limitCoding S H R B) k.toEmbedding
  let g : J ↪ U S H R B := h.trans ⟨k,k.injective⟩
  refine ⟨g,hk,?_,?_⟩
  · intro j
    exact (hp.1 (h j)).trans (hOwner j)
  · intro i j
    exact (hp.2 (h i) (h j)).trans (hColour i j)

end
end CCO.OwnerTransversal.TransversalAge
