import CCO.GuardedOldSeams.Envelope
import CCO.GuardedOldSeams.IdempotentMonolith
import CCO.RealClosure.Bounds.TerminalNR2
import CCO.TerminalProfiles.OriginalEquivalenceReproduction
import CCO.TransitionClosure.OriginalEquivalenceJoinStrong

/-! The CCO-free lattice is the FULL original invariant lattice with
identity removed. Only its final distributive specialization assumes CCO. -/

universe u v w t
namespace CCO.GuardedOldSeams
open CCO.ParityHasse.Original CCO.TerminalLattice CCO.RealClosure.Bounds
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- Actual nonempty positive STRONG word profiles, with strong idempotence. -/
abbrev StrongIdempotent (i : ι) :=
  {e : S.Menu i i // e.Nonempty ∧
    (∃ word : PositiveWord S i i, PositiveWord.profile S word = e) ∧ S.product e e = e}

abbrev NonidentityEquivalence (i : ι) := {E : ColourEq S i // ⊥ < E}

instance strongIdempotentFinite (i : ι) : Finite (StrongIdempotent S i) := by
  letI := S.finiteAtom i i
  infer_instance

def idempotentEnvelope {i : ι} (e : StrongIdempotent S i) : NonidentityEquivalence S i :=
  ⟨envelope S e.val e.property.2.2,envelope_gt_bot S e.val e.property.2.2 e.property.1⟩

theorem equivalence_diversity_nonempty {i : ι} (E : ColourEq S i) (hE : ⊥ < E) :
    (originalEquivDiversityPalette S E).Nonempty := by
  obtain ⟨x,y,hxy,hne⟩ := actual_nontrivial_equiv_pair S E hE
  obtain ⟨a,ha⟩ := S.some_colour_of_ne x y (by
    intro h; exact hne (eq_of_heq (Sigma.mk.inj h).2))
  exact ⟨a,x,y,hxy,ha⟩

theorem envelope_equivalence_diversity {i : ι} (E : ColourEq S i)
    (he : S.product (originalEquivDiversityPalette S E)
      (originalEquivDiversityPalette S E) = originalEquivDiversityPalette S E) :
    envelope S (originalEquivDiversityPalette S E) he = E := by
  classical
  apply ColourEq.ext
  intro x y
  change (x = y ∨ S.menuRel (originalEquivDiversityPalette S E) x y) ↔ E x y
  rw [originalEquivDiversityPalette_semantics]
  exact ⟨fun h => h.elim (fun h => h ▸ E.val.refl x) And.right,
    fun h => if heq : x = y then Or.inl heq else Or.inr ⟨heq,h⟩⟩

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (nr2 : Selectors.OriginalNR2 S)
include H sap nr2

/-- FULL original NR2 first supplies a RAW word. Its nonidentity diversity
forces the positive branch of the accepted identity/positive normalization. -/
theorem equivalence_diversity_positive {i : ι} (E : ColourEq S i) (hE : ⊥ < E) :
    ∃ word : PositiveWord S i i,
      PositiveWord.profile S word = originalEquivDiversityPalette S E := by
  obtain ⟨word,hw⟩ := terminal_raw_word_of_originalNR2 S H nr2 E
  have hn := equivalence_diversity_nonempty S E hE
  have h := PositiveWord.raw_guard_empty_or_positive_profile_of_SAP S H sap word
  rw [hw] at h
  rcases h with hempty | ⟨p,hp⟩
  · obtain ⟨a,ha⟩ := hn
    have hf : a ∈ (∅ : S.Menu i i) := hempty ▸ ha
    exact False.elim hf
  · exact ⟨p,hp.symm⟩

/-- Every FULL original nonidentity invariant equivalence supplies an
actual positive reachable strong idempotent, without CCO. -/
def equivalenceIdempotent {i : ι} (E : NonidentityEquivalence S i) : StrongIdempotent S i :=
  ⟨originalEquivDiversityPalette S E.val,
    equivalence_diversity_nonempty S E.val E.property,
    equivalence_diversity_positive S H sap nr2 E.val E.property,
    (TerminalProfiles.original_equiv_diversity_reproduction S H sap E.val E.property
      _ (equivalence_diversity_nonempty S E.val E.property) (by intro a ha; exact ha)).2.2⟩

/-- C31--C33: actual order-preserving BIJECTION onto ALL nonidentity
original invariant equivalences. No exactness or CCO premise. -/
def idempotentEnvelopeIso (i : ι) :
    StrongIdempotent S i ≃o NonidentityEquivalence S i where
  toFun := idempotentEnvelope S
  invFun := equivalenceIdempotent S H sap nr2
  left_inv e := by
    apply Subtype.ext
    exact envelope_diversity S e.val e.property.2.2
  right_inv E := by
    apply Subtype.ext
    exact envelope_equivalence_diversity S E.val
      (equivalenceIdempotent S H sap nr2 E).property.2.2
  map_rel_iff' := by
    intro e f
    exact envelope_le_iff S e.val f.val e.property.2.2 f.property.2.2

@[instance_reducible] def nonidentityEquivalenceLattice (i : ι) :
    Lattice (NonidentityEquivalence S i) := by
  letI := ColourEq.lattice S H (i := i)
  exact Subtype.lattice
    (fun {_ _} hE _hF => lt_of_lt_of_le hE le_sup_left)
    (fun {_ _} hE hF => nonidentity_inf_gt_bot S H sap _ _ hE hF)

/-- The operations are transported through the ACTUAL envelope order
isomorphism while retaining the inherited menu inclusion order. -/
@[instance_reducible] def idempotentLattice (i : ι) : Lattice (StrongIdempotent S i) := by
  letI := nonidentityEquivalenceLattice S H sap i
  let Φ := idempotentEnvelopeIso S H sap nr2 i
  exact {
    sup := fun e f => Φ.symm (Φ e ⊔ Φ f)
    inf := fun e f => Φ.symm (Φ e ⊓ Φ f)
    le_sup_left := fun e f => Φ.le_iff_le.mp (by simp only [OrderIso.apply_symm_apply]; exact le_sup_left)
    le_sup_right := fun e f => Φ.le_iff_le.mp (by simp only [OrderIso.apply_symm_apply]; exact le_sup_right)
    sup_le := fun e f k he hf => Φ.le_iff_le.mp (by
      simp only [OrderIso.apply_symm_apply]
      exact sup_le (Φ.monotone he) (Φ.monotone hf))
    inf_le_left := fun e f => Φ.le_iff_le.mp (by simp only [OrderIso.apply_symm_apply]; exact inf_le_left)
    inf_le_right := fun e f => Φ.le_iff_le.mp (by simp only [OrderIso.apply_symm_apply]; exact inf_le_right)
    le_inf := fun e f k he hf => Φ.le_iff_le.mp (by
      simp only [OrderIso.apply_symm_apply]
      exact le_inf (Φ.monotone he) (Φ.monotone hf)) }

omit H sap nr2 in
/-- Diversity commutes with the literal full equivalence intersection. -/
theorem equivalence_diversity_inf {i : ι} (E F : ColourEq S i) :
    originalEquivDiversityPalette S (E ⊓ F) =
      originalEquivDiversityPalette S E ∩ originalEquivDiversityPalette S F := by
  ext a
  constructor
  · rintro ⟨x,y,⟨hE,hF⟩,hcol⟩
    exact ⟨⟨x,y,hE,hcol⟩,⟨x,y,hF,hcol⟩⟩
  · rintro ⟨⟨x,y,hE,hcol⟩,⟨p,q,hF,hcol'⟩⟩
    exact ⟨x,y,⟨hE,(F.property p q x y (hcol'.trans hcol.symm)).mp hF⟩,hcol⟩

/-- IL meet is actual palette intersection, and is genuinely NONEMPTY. -/
theorem idempotent_inf_palette {i : ι} (e f : StrongIdempotent S i) :
    letI := idempotentLattice S H sap nr2 i
    (e ⊓ f).val = e.val ∩ f.val := by
  letI := idempotentLattice S H sap nr2 i
  change originalEquivDiversityPalette S
    ((idempotentEnvelope S e).val ⊓ (idempotentEnvelope S f).val) = _
  rw [equivalence_diversity_inf]
  simp only [idempotentEnvelope,envelope_diversity]

theorem idempotent_intersection_nonempty {i : ι} (e f : StrongIdempotent S i) :
    (e.val ∩ f.val).Nonempty := by
  letI := idempotentLattice S H sap nr2 i
  rw [← idempotent_inf_palette S H sap nr2 e f]
  exact (e ⊓ f).property.1

/-- IL join is the genuine STRONG triangle product, without CCO. -/
theorem idempotent_sup_palette {i : ι} (e f : StrongIdempotent S i) :
    letI := idempotentLattice S H sap nr2 i
    (e ⊔ f).val = S.product e.val f.val := by
  letI := idempotentLattice S H sap nr2 i
  change originalEquivDiversityPalette S
    (ColourEq.join S H (idempotentEnvelope S e).val (idempotentEnvelope S f).val) = _
  rw [TransitionClosure.original_raw_equiv_join_guard_eq_strong S H sap
    _ _ (idempotentEnvelope S e).property (idempotentEnvelope S f).property]
  simp only [idempotentEnvelope,envelope_diversity]

/-- The actual SAP-monolith's diversity, inside the positive idempotents. -/
def leastIdempotent (i : ι) : StrongIdempotent S i :=
  equivalenceIdempotent S H sap nr2
    ⟨originalMonolith S H sap i,originalMonolith_gt_bot S H sap i⟩

theorem leastIdempotent_le {i : ι} (e : StrongIdempotent S i) :
    leastIdempotent S H sap nr2 i ≤ e := by
  apply (idempotentEnvelopeIso S H sap nr2 i).le_iff_le.mp
  have hL : (idempotentEnvelopeIso S H sap nr2 i) (leastIdempotent S H sap nr2 i) =
      ⟨originalMonolith S H sap i,originalMonolith_gt_bot S H sap i⟩ :=
    (idempotentEnvelopeIso S H sap nr2 i).apply_symm_apply _
  rw [hL]
  exact originalMonolith_le S H sap _ (idempotentEnvelope S e).property

theorem leastIdempotent_unique {i : ι} (e : StrongIdempotent S i)
    (least : ∀ f : StrongIdempotent S i, e ≤ f) : e = leastIdempotent S H sap nr2 i :=
  le_antisymm (least _) (leastIdempotent_le S H sap nr2 e)

/-- e0 is a two-sided unit HERE: its quantified input is a strong
IDEMPOTENT, rather than an arbitrary positive reachable profile. -/
theorem leastIdempotent_product {i : ι} (e : StrongIdempotent S i) :
    S.product (leastIdempotent S H sap nr2 i).val e.val = e.val ∧
    S.product e.val (leastIdempotent S H sap nr2 i).val = e.val := by
  letI := idempotentLattice S H sap nr2 i
  constructor
  · rw [← idempotent_sup_palette S H sap nr2]
    exact congrArg Subtype.val (sup_eq_right.mpr (leastIdempotent_le S H sap nr2 e))
  · rw [← idempotent_sup_palette S H sap nr2]
    exact congrArg Subtype.val (sup_eq_left.mpr (leastIdempotent_le S H sap nr2 e))

/-- Only this final specialization invokes original semantic CCO.
Terminal FULL exactness discharges its actual original-NR2 provider. -/
@[instance_reducible] def idempotentDistribLattice
    (cco : SemanticCCO.{u,v,max u v,w} S) (i : ι) :
    letI := idempotentLattice S H sap nr2 i
    DistribLattice (StrongIdempotent S i) := by
  letI := idempotentLattice S H sap nr2 i
  letI := terminalDistribLattice S H cco (sortNR2_of_originalNR2 S H nr2 (i := i))
  letI : DistribLattice (NonidentityEquivalence S i) :=
    Subtype.distribLattice
      (fun {_ _} hE _hF => lt_of_lt_of_le hE le_sup_left)
      (fun {_ _} hE hF => nonidentity_inf_gt_bot S H sap _ _ hE hF)
  let Φ := idempotentEnvelopeIso S H sap nr2 i
  apply DistribLattice.ofInfSupLe
  intro e f k
  apply Φ.le_iff_le.mp
  change Φ (e ⊓ (f ⊔ k)) ≤ Φ ((e ⊓ f) ⊔ (e ⊓ k))
  simpa only [map_inf,map_sup] using
    (le_of_eq (inf_sup_left (Φ e) (Φ f) (Φ k)))

end
end CCO.GuardedOldSeams
