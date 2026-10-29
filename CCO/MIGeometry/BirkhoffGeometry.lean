import CCO.MIGeometry.Pseudocomplements
import CCO.MIGeometry.Ancestors

/-! The exhaustive finite-poset ancestor theorem instantiated in the
ACTUAL exact lattice of the original source. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners
open ExactCRT.FiniteOrder

section Order
variable {L : Type*} [DistribLattice L] [OrderBot L]
theorem atom_supIrred {a : L} (ha : IsAtom a) : SupIrred a := by
  refine ⟨?_,?_⟩
  · intro h
    exact ha.ne_bot (le_antisymm (h bot_le) bot_le)
  · intro b c hbc
    by_cases hb : b = a
    · exact Or.inl hb
    · right
      have hba : b ≤ a := hbc ▸ le_sup_left
      have hbz : b = ⊥ := ha.2 b (lt_of_le_of_ne hba hb)
      simpa [hbz] using hbc

theorem atom_joinIrreducible_isMin {a : L} (ha : IsAtom a) :
    IsMin (⟨a,atom_supIrred ha⟩ : JoinIrreducible L) := by
  intro q hq
  have hqa : q.val = a := by
    by_contra hn
    exact q.property.ne_bot (ha.2 q.val (lt_of_le_of_ne hq hn))
  exact hqa.ge

theorem joinIrreducible_min_isAtom [Finite L] (p : JoinIrreducible L) (hp : IsMin p) :
    IsAtom p.val := by
  obtain hz | ⟨a,ha,hap⟩ := eq_bot_or_exists_atom_le p.val
  · exact False.elim (p.property.ne_bot hz)
  · have hpa : p.val ≤ a := hp (show (⟨a,atom_supIrred ha⟩ : JoinIrreducible L) ≤ p from hap)
    have he := le_antisymm hap hpa
    exact he ▸ ha
end Order

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

noncomputable def directionPoint (normalized : NoFiniteExactKernel S) (D : Direction S) :
    JoinIrreducible (ExactL S H cco) := by
  letI := ExactCRT.exactDistribLattice S H (semanticCCO_change_universe S cco) ()
  exact ⟨⟨D.val.val,direction_exact S H cco D⟩,
    atom_supIrred (direction_exact_atom S H cco normalized D)⟩

/-- ALL minimal irreducibles correspond to the ALL original directions. -/
noncomputable def sourceMinima (normalized : NoFiniteExactKernel S) :
    Ancestors.Minima (Direction S) (JoinIrreducible (ExactL S H cco)) := by
  letI := ExactCRT.exactDistribLattice S H (semanticCCO_change_universe S cco) ()
  refine ⟨directionPoint S H cco normalized,?_,?_,?_⟩
  · intro D E he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun p : JoinIrreducible (ExactL S H cco) => p.val.val) he
  · intro D
    exact atom_joinIrreducible_isMin (direction_exact_atom S H cco normalized D)
  · intro p hp
    have ha := joinIrreducible_min_isAtom p hp
    let D : Direction S := ⟨exactColour S H cco p.val,exact_atom_isDirection S H cco normalized p.val ha⟩
    exact ⟨D,Subtype.ext (Subtype.ext rfl)⟩

/-- The actual maximal exact pseudocomplement is precisely P minus the
upset of its corresponding minimum, rather than an arbitrary selected core. -/
theorem hat_birkhoff_core (normalized : NoFiniteExactKernel S) (D : Direction S) :
    ExactCRT.exactBirkhoff S H (semanticCCO_change_universe S cco) () (hatExact S H cco D) =
      (sourceMinima S H cco normalized).core D := by
  letI := ExactCRT.exactDistribLattice S H (semanticCCO_change_universe S cco) ()
  apply SetLike.ext
  intro p
  change p.val ≤ hatExact S H cco D ↔ ¬ (⟨D.val.val,direction_exact S H cco D⟩ : ExactL S H cco) ≤ p.val
  have ha := direction_exact_atom S H cco normalized D
  have hcrit := le_hat_iff S H cco normalized D (exactColour S H cco p.val) p.val.property
  change p.val ≤ hatExact S H cco D ↔
    exactColour S H cco p.val ⊓ D.val = ⊥ at hcrit
  rw [hcrit]
  constructor
  · intro hz hle
    have he : D.val = ⊥ := by
      rw [← hz]
      have hc : D.val ≤ exactColour S H cco p.val := hle
      exact (inf_eq_right.mpr hc).symm
    exact D.property.1 (he ▸ finiteClasses_bot S)
  · intro hn
    have hlt : p.val ⊓ (⟨D.val.val,direction_exact S H cco D⟩ : ExactL S H cco) <
        (⟨D.val.val,direction_exact S H cco D⟩ : ExactL S H cco) :=
      lt_of_le_of_ne inf_le_right (by
        intro he
        exact hn (by rw [← he]; exact inf_le_left))
    exact Subtype.ext (congrArg (fun e : ExactL S H cco => e.val) (ha.2 _ hlt))

/-- Actual exact joint-owner relations obtained through the proved source
Birkhoff equivalence. The pointwise ancestor formulas remain available by
applying the literal order isomorphism. -/
noncomputable def ownerExact (normalized : NoFiniteExactKernel S) (D : Direction S) : ExactL S H cco :=
  (ExactCRT.exactBirkhoff S H (semanticCCO_change_universe S cco) ()).symm
    ((sourceMinima S H cco normalized).owner D)

noncomputable def jointOwnerExact (normalized : NoFiniteExactKernel S) : ExactL S H cco :=
  (ExactCRT.exactBirkhoff S H (semanticCCO_change_universe S cco) ()).symm
    (sourceMinima S H cco normalized).jointOwner

noncomputable def jointOwner (normalized : NoFiniteExactKernel S) : ColourEq S () :=
  exactColour S H cco (jointOwnerExact S H cco normalized)

/-- C26 permits Hstar=Top and its actual singleton owner quotient. -/
theorem jointOwner_ne_bot (normalized : NoFiniteExactKernel S) [Nonempty (Direction S)] :
    jointOwner S H cco normalized ≠ ⊥ := by
  intro hz
  have he : jointOwnerExact S H cco normalized = ⊥ :=
    Subtype.ext (congrArg (fun E : ColourEq S () => E.val) hz)
  have hm := (sourceMinima S H cco normalized).jointOwner_gt_bot
  have hb : (sourceMinima S H cco normalized).jointOwner = ⊥ := by
    have hh := congrArg (ExactCRT.exactBirkhoff S H (semanticCCO_change_universe S cco) ()) he
    simpa only [jointOwnerExact,OrderIso.apply_symm_apply,OrderIso.map_bot] using hh
  exact hm.ne' hb

theorem ownerExact_birkhoff (normalized : NoFiniteExactKernel S) (D : Direction S) :
    ExactCRT.exactBirkhoff S H (semanticCCO_change_universe S cco) ()
      (ownerExact S H cco normalized D) = (sourceMinima S H cco normalized).owner D :=
  (ExactCRT.exactBirkhoff S H (semanticCCO_change_universe S cco) ()).apply_symm_apply _

/-- The source JOG equality is literal equality of ACTUAL exact equivalences. -/
theorem ownerExact_JOG (normalized : NoFiniteExactKernel S)
    (D E : Direction S) (hne : D ≠ E) :
    ownerExact S H cco normalized D ⊔ ownerExact S H cco normalized E =
      hatExact S H cco D ⊔ hatExact S H cco E := by
  let e := ExactCRT.exactBirkhoff S H (semanticCCO_change_universe S cco) ()
  apply e.injective
  rw [e.map_sup,e.map_sup]
  rw [ownerExact_birkhoff,ownerExact_birkhoff,hat_birkhoff_core,hat_birkhoff_core]
  exact (sourceMinima S H cco normalized).owner_sup_owner D E hne

theorem owners_meet_jointOwner (normalized : NoFiniteExactKernel S) :
    colourFamilyMeet S (fun D => exactColour S H cco (ownerExact S H cco normalized D)) =
      jointOwner S H cco normalized := by
  let e := ExactCRT.exactBirkhoff S H (semanticCCO_change_universe S cco) ()
  let A : ExactL S H cco :=
    ⟨(colourFamilyMeet S (fun D => exactColour S H cco (ownerExact S H cco normalized D))).val,
      colourFamilyMeet_exact S (fun D => exactColour S H cco (ownerExact S H cco normalized D))
        (fun D => (ownerExact S H cco normalized D).property)⟩
  have hh : e A = (sourceMinima S H cco normalized).jointOwner := by
    rw [← (sourceMinima S H cco normalized).inf_owner_eq_jointOwner]
    apply SetLike.ext
    intro p
    simp only [LowerSet.mem_iInf_iff]
    have hp (D : Direction S) : p ∈ (sourceMinima S H cco normalized).owner D ↔
        p.val ≤ ownerExact S H cco normalized D := by
      rw [← ownerExact_birkhoff S H cco normalized D]
      exact ExactCRT.mem_exactBirkhoff S H (semanticCCO_change_universe S cco) () _ p
    simp_rw [hp]
    change (∀ ⦃x y⦄, p.val.val x y → ∀ D, (ownerExact S H cco normalized D).val x y) ↔
      ∀ D ⦃x y⦄, p.val.val x y → (ownerExact S H cco normalized D).val x y
    exact ⟨fun h D _ _ hxy => h hxy D,fun h _ _ hxy D => h D hxy⟩
  have he : A = jointOwnerExact S H cco normalized := by
    apply e.injective
    exact hh.trans (e.apply_symm_apply _).symm
  exact Subtype.ext (congrArg (fun z : ExactL S H cco => z.val) he)

theorem jointOwner_exact (normalized : NoFiniteExactKernel S) :
    ExactCRT.IsExactEq S (i := ()) (jointOwner S H cco normalized).val :=
  (jointOwnerExact S H cco normalized).property

/-- Strict counting is local orbital-block counting and also covers Top. -/
theorem jointOwner_quotient_rank_drop (normalized : NoFiniteExactKernel S)
    [Nonempty (Direction S)] :
    Nat.card ((actualQuotientSource S H (jointOwner S H cco normalized)).Atom () ()) <
      Nat.card (S.Atom () ()) := by
  letI := S.finiteAtom () ()
  letI := (actualQuotientSource S H (jointOwner S H cco normalized)).finiteAtom () ()
  simpa only [Nat.card_eq_fintype_card] using quotient_palette_strictly_drops S H
    (jointOwner S H cco normalized) (jointOwner_ne_bot S H cco normalized)

end CCO.MIGeometry
