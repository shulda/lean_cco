import CCO.FinitePackets.Geometry.PacketCore
import CCO.FinitePackets.Geometry.CutCrossing
import CCO.RawExact.CanonicalQuotientInheritance

/-! C12 and the SEPARATE C13 actual quotient-source instance. The kernel is
the exact core proved here, not an arbitrary invariant or finite-index kernel.
Only source inheritance retains the accepted provider's countability premise. -/
universe v w t z
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
include H cco

theorem minimal_cut_eq_core {E : ColourEq S ()} (hE : MinimalInfiniteCut S E) :
    E = core S E := by
  by_contra he
  have hlt : core S E < E := lt_of_le_of_ne (core_le S E) (fun h => he h.symm)
  exact hE.1 (finiteIndex_trans S ⊥ (core S E) E bot_le (core_le S E)
    (hE.2 (core S E) hlt) (finiteIndex_core S H cco E))

theorem minimal_cut_positive_word {E : ColourEq S ()} (hE : MinimalInfiniteCut S E) :
    ∃ word : PositiveWord S () (), PositiveWord.represented S word = E.val.r := by
  have hc : core S E ≠ ⊥ := by
    rw [← minimal_cut_eq_core S H cco hE]
    exact cut_nonidentity S hE
  obtain ⟨word,hw⟩ := nonidentity_core_positive S H E hc
  exact ⟨word,hw.trans (congrArg (fun F : ColourEq S () => F.val.r)
    (minimal_cut_eq_core S H cco hE).symm)⟩

theorem minimal_cut_exact_represents {E : ColourEq S ()} (hE : MinimalInfiniteCut S E) :
    RawExact.evaluate S (coreExact S H E).words = E.val.r := by
  rw [coreExact_represents,← minimal_cut_eq_core S H cco hE]

noncomputable def minimalCutQuotientData (E : ColourEq S ()) (hE : MinimalInfiniteCut S E) :
    RawExact.CanonicalQuotients.ExactData S ({E.val} : Finset (Setoid M)) :=
  RawExact.CanonicalQuotients.singletonData S E.val (coreExact S H E)
    (minimal_cut_exact_represents S H cco hE)

/-- The constructed language is the language of ACTUAL original-action
quotient pair orbitals. Its sole carrier is definitionally Quotient E. -/
noncomputable def minimalCutQuotientSource (E : ColourEq S ()) (hE : MinimalInfiniteCut S E) :=
  RawExact.CanonicalQuotients.source S H (minimalCutQuotientData S H cco E hE)

theorem minimal_cut_actual_quotient_source [Countable M]
    (E : ColourEq S ()) (hE : MinimalInfiniteCut S E) :
    RawExact.CanonicalQuotients.SourceProperties.{v,w,t,z} S H
      (minimalCutQuotientData S H cco E hE) := by
  have cv : SemanticCCO.{0,v,v,w} S := semanticCCO_change_universe S cco
  exact RawExact.CanonicalQuotients.singleton_source_properties S H cv E.val
    (coreExact S H E) (minimal_cut_exact_represents S H cco hE)

omit H cco in
theorem minimal_cut_quotient_carrier (E : ColourEq S ()) :
    RawExact.CanonicalQuotients.Carrier
      (RawExact.CanonicalQuotients.singletonIndex E.val) = Quotient E.val := rfl

omit H cco in
theorem minimal_cut_quotient_one_sort (E : ColourEq S ())
    (k : RawExact.CanonicalQuotients.Index ({E.val} : Finset (Setoid M))) :
    k = RawExact.CanonicalQuotients.singletonIndex E.val :=
  RawExact.CanonicalQuotients.singletonIndex_unique E.val k

end CCO.FinitePackets.Geometry
