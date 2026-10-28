import CCO.RealHull.Geometry.FibreIntervals
import CCO.RealHull.Geometry.Boundaries
import CCO.RealHull.Geometry.GeneratedSupport
import CCO.RealHull.Geometry.RamseySource

/-! B009 source headline and meaningful downstream finite-fibre consumers.
All original and inherited providers are proved; there is no SAP, exact-word,
imaginary-CCO, globalisation or interval-lifting premise. -/
universe v w z t
namespace CCO.RealHull.Geometry
open ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable (A : Finset M) (q : ↥A → Atom S)
variable [Nonempty (FibreSet S A q)]
variable {G : Type t} [Group G] [MulAction G M]

/-- C15's FULL internal cover theorem, without globalisation or exactness. -/
theorem actual_fibre_cover_index_two (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite (FibreSet S A q)]
    (E F : ColourEq (fibreSource S A q) ()) (hEF : E ⋖ F) (x : FibreSet S A q) :
    relativeIndex E.val F.val x = 2 := by
  letI : Finite (RelativeClass E.val F.val x) := by unfold RelativeClass; infer_instance
  exact full_relative_hasse (fibreSource S A q) (fibre_homogeneous S A q H)
    (fibre_semanticCCO S A q H cco) E F hEF x

/-- One finite ACTUAL realised fibre carries the inherited source BEFORE
globalisation, is then one original E_T-class, has two-power size, and ONLY
AFTER this existence result has the full original interval of all internal
full-Aut equivalences. The target is the actual fibre, not a substitute model.
-/
theorem actual_finite_fibre_package (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite (FibreSet S A q)] :
    HomogeneousSource (fibreSource S A q) (inducedAut S () (FibreSet S A q)) ∧
    SemanticCCO.{0,v,z,w} (fibreSource S A q) ∧
    ({c : Atom S | ∀ a : ↥A, c ∈ square S (q a)} = (fibreSpokeFixer S A q H).val) ∧
    (∀ x : FibreSet S A q, ∀ y : M,
      y ∈ FibreSet S A q ↔ supportEquiv S (finiteFibrePaletteSupport S H cco A q) x.val y) ∧
    (∃ n : Nat, Nat.card (FibreSet S A q) = 2^n ∧ n ≤ Nat.card (Atom S)) ∧
    (∀ x : FibreSet S A q,
      Nonempty (Set.Iic (supportEquiv S (fibreSpokeFixer S A q H)) ≃o
        InducedFullEq S () (FibreSet S A q))) := by
  exact ⟨fibre_homogeneous S A q H,fibre_semanticCCO S A q H cco,
    finite_fibre_palette_eq S A q H cco,finite_fibre_actual_ET_class S H cco A q,
    finite_fibre_size_power_two S A q H cco,
    fun x => ⟨finiteFibreFullIntervalIso S A q H cco x⟩⟩

/-- The actual source's empty-base case is finite precisely when the original
carrier is finite, with the SAME two-power/old-palette bound. -/
theorem finite_empty_anchor_size (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (r : ↥(∅ : Finset M) → Atom S) [Finite M] :
    ∃ n : Nat, Nat.card M = 2^n ∧ n ≤ Nat.card (Atom S) := by
  letI : Nonempty (FibreSet S ∅ r) := fibre_empty_nonempty S r
  letI : Finite (FibreSet S ∅ r) := (empty_fibre_finite_iff S r).mpr inferInstance
  obtain ⟨n,hn,hbound⟩ := finite_fibre_size_power_two S ∅ r H cco
  exact ⟨n,(Nat.card_congr (emptyFibreEquiv S r)).symm.trans hn,hbound⟩

end CCO.RealHull.Geometry
