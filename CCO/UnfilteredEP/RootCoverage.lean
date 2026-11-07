import CCO.UnfilteredEP.RootMeetCofinality
import CCO.APRamseyReadout.ProperHiddenAge
import CCO.TypedOrbitFrames.ActualNamedTerms
import CCO.FullCode.CofinalAge

/-!
# B064 C75--C77: every proper hidden point belongs to one whole root

No selected-chart restriction is imposed on hidden vertices. A point of
an arbitrary proper quotient has one actual representative; the FULL
meet-prime argument finds a selected coordinate below its kernel. The
existing named upward map then recovers this point from the complete
valid tuple of that representative's owner. In particular orphan-only
finite hosts are covered. Finite unary term forms subsequently give an
actual finite root-generated cofinal extension on the same chosen carrier.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p z
namespace CCO.UnfilteredEP
open CCO.ParityHasse.Original CCO.CloneTupleGeometry CCO.CloneTupleGeometry.OwnerStage
open CCO.APRamseyReadout CCO.TypedOrbitFrames CCO.UnaryTermsReturn
open CCO.FullCode
noncomputable section

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)

/-- The full binary-code target restricted to ALL actual proper sorts.
The language, every named partial function and every cylinder is retained. -/
abbrev properCoordinateCarrier :=
  {x : Values B // ProperSort B ht ((CoordinateTarget B ht).sort x)}

abbrev properCoordinateTarget :
    Structure (CoordinateLanguage B ht) (properCoordinateCarrier B ht) :=
  (CoordinateTarget B ht).induce _ (proper_set_closed B ht (Target B ht))

abbrev properCoordinateInclusion :
    Structure.Embedding (properCoordinateTarget B ht) (CoordinateTarget B ht) :=
  (CoordinateTarget B ht).inclusion _ (proper_set_closed B ht (Target B ht))

/-- Every actual proper hidden point is a value in one of the literal
named quotient sorts, with its existing quotient class unchanged. -/
theorem proper_value_named (x : properCoordinateCarrier B ht) :
    ∃ i : B.Sorts, ∃ D : NamedCoordinate B i,
      ∃ q : Quotient D.val.val, x.val = namedNode B D q := by
  rcases x with ⟨x,hx⟩
  cases x with
  | inl x => change False at hx; exact hx.elim
  | inr x =>
    rcases x with ⟨⟨i,J,q⟩,hNamed⟩
    let D : NamedCoordinate B i := ⟨J,by
      obtain ⟨E,hE⟩ := hNamed
      change E.val = J at hE
      rw [← hE]
      exact E.property⟩
    exact ⟨i,D,q,rfl⟩

/-- Removing the arbitrary clone index does not change ANY proper named
quotient value, because every such kernel contains the actual clone K. -/
theorem named_class_owner {i : B.Sorts} (D : NamedCoordinate B i)
    (q : Quotient D.val.val) :
    Quotient.mk D.val.val (q.out.1,0) = q := by
  have hKD : fullCloneKernel B.source i ≤ D.val := named_kernel_contains_clone B D
  exact (Quotient.sound (hKD (show fullCloneKernel B.source i (q.out.1,0) q.out from rfl))).trans
    (Quotient.out_eq q)

/-- The literal old-language upward term from one selected coordinate.
Its target need not be a member of the selected chart. -/
def selectedUpwardTerm {i : B.Sorts} (D : NamedCoordinate B i)
    (k : Fin (chartArity F i)) (hKD : (chartSymbol F i k).val ≤ D.val) :
    Term (CoordinateLanguage B ht) (chartSort B ht F i k) (coordinateSort B ht D) :=
  CCO.TerminalHiddenHN.freshTermToFull (Lang B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))
    (originalNamedWordAsTerm (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
      (CCO.UnaryTermsReturn.originalNamedUpTerm (cloneSource B) (HF B) (cloneSAP B)
        (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
        (chartCoordinate B ht F i k) D hKD))

theorem selectedUpwardTerm_eval {i : B.Sorts} (D : NamedCoordinate B i)
    (k : Fin (chartArity F i)) (hKD : (chartSymbol F i k).val ≤ D.val)
    (x : B.Point i) :
    namedNode B D (Quotient.mk D.val.val (x,0)) ∈
      (selectedUpwardTerm B ht F D k hKD).eval (CoordinateTarget B ht)
        ((ownerRoot B ht F ⟨i,x⟩).coordinate k) := by
  apply (CCO.TerminalHiddenHN.freshTermToFull_eval (Lang B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))
    (Hidden B ht) _ _ _ ((ownerRoot B ht F ⟨i,x⟩).sorted k)).mpr
  rw [ownerRoot_coordinate]
  change originalCompletedNamedHiddenNode (cloneSource B) (HF B) D
      (Quotient.mk D.val.val (x,0)) =
    (originalCompletedStructure (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))).eval
      (originalNamedWordAsTerm (cloneSource B) (HF B) (cloneSAP B)
        (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
        (originalNamedUpTerm (cloneSource B) (HF B) (cloneSAP B)
          (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
          (chartCoordinate B ht F i k) D hKD))
      (originalCompletedNamedHiddenNode (cloneSource B) (HF B)
        (chartCoordinate B ht F i k)
        (Quotient.mk (chartCoordinate B ht F i k).val.val (x,0)))
  exact (original_named_word_as_term_eval (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
    (originalNamedUpTerm (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
      (chartCoordinate B ht F i k) D hKD)
    (Quotient.mk (chartCoordinate B ht F i k).val.val (x,0))).symm

/-- C75--C76. Every proper ambient point is an actual old term value of
one WHOLE valid visible root. No root or packet partner is required in the
finite hidden object which happened to contain that point. -/
theorem proper_point_covered_in_full (x : properCoordinateCarrier B ht) :
    ∃ (r : Root (CoordinateTarget B ht) (tupleScheme B ht F))
      (j : Fin ((tupleScheme B ht F).arity r.tag))
      (t : Term (CoordinateLanguage B ht) ((tupleScheme B ht F).coordinateSort r.tag j)
        ((CoordinateTarget B ht).sort x.val)),
      x.val ∈ t.eval (CoordinateTarget B ht) (r.coordinate j) := by
  rcases x with ⟨x,hproper⟩
  obtain ⟨i,D,q,hx⟩ := proper_value_named B ht ⟨x,hproper⟩
  change x = namedNode B D q at hx
  subst x
  obtain ⟨k,hk⟩ := selected_coordinate_below_named B ht F D
  refine ⟨ownerRoot B ht F ⟨i,q.out.1⟩,k,selectedUpwardTerm B ht F D k hk,?_⟩
  have hq := named_class_owner B D q
  exact Eq.mp (congrArg (fun y =>
    namedNode B D y ∈ (selectedUpwardTerm B ht F D k hk).eval (CoordinateTarget B ht)
      ((ownerRoot B ht F ⟨i,q.out.1⟩).coordinate k)) hq)
    (selectedUpwardTerm_eval B ht F D k hk q.out.1)

/-- Restriction keeps every coordinate of every valid root: selected
coordinates are proper named sorts, independently of their values. -/
theorem root_coordinates_proper (r : Root (CoordinateTarget B ht) (tupleScheme B ht F))
    (j : Fin ((tupleScheme B ht F).arity r.tag)) :
    ProperSort B ht ((CoordinateTarget B ht).sort (r.coordinate j)) := by
  rw [r.sorted j]
  trivial

/-- C76. The exact accepted FullCode root-coverage predicate holds on
ALL proper hidden values, rather than a root-generated subage. -/
theorem actual_proper_root_covered :
    RootCovered (properCoordinateTarget B ht) (tupleScheme B ht F) := by
  intro x
  obtain ⟨r,j,t,htx⟩ := proper_point_covered_in_full B ht F x
  let r' := r.restrict (C := CoordinateTarget B ht) (proper_set_closed B ht (Target B ht))
    (root_coordinates_proper B ht F r)
  refine ⟨r',j,t,?_⟩
  exact (t.map_iff (properCoordinateInclusion B ht) (r'.coordinate j) x).mp htx

/-- Finite actual normal term FUNCTIONS remain valid on every proper
input, including values which came from orphan-only finite hosts. -/
theorem proper_coordinate_normal :
    (CCO.TerminalHiddenHN.binaryNormalForms (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)).Valid (properCoordinateTarget B ht) :=
  NormalForms.valid_of_embedding _ (properCoordinateInclusion B ht)
    (CCO.TerminalHiddenHN.binaryNormalForms_valid (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))


/-- The actual finite proper hidden age in the faithful binary language.
Membership preserves ALL original function graphs and named cylinders. -/
def ProperFiniteCodeAge
    (D : FiniteHidden.{max u v w,max u v} (CoordinateLanguage B ht)) : Prop :=
  ActualAge B ht (CCO.TerminalHiddenHN.binaryDecode (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) D.model) ∧
    ∀ x, ProperSort B ht (D.model.sort x)

/-- The entire finite proper age is the age of the literal proper ambient
restriction. Both directions retain arbitrary finite carrier presentations. -/
theorem proper_coordinate_ambient :
    IsAmbientAge (ProperFiniteCodeAge B ht) (properCoordinateTarget B ht) := by
  intro D
  let hbin := CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
    (cloneSAP B) (fullCovers B ht)
  constructor
  · rintro ⟨hD,hproper⟩
    obtain ⟨e⟩ := hD.2
    have f := CCO.TerminalHiddenHN.binaryEmbedding (Sig B ht) hbin e
    rw [CCO.TerminalHiddenHN.binaryStructure_binaryDecode] at f
    refine ⟨f.factor (properCoordinateInclusion B ht) ?_⟩
    rintro _ ⟨x,rfl⟩
    refine ⟨⟨f.point x,?_⟩,rfl⟩
    change ProperSort B ht ((CoordinateTarget B ht).sort (f.point x))
    rw [f.sort_eq]
    exact hproper x
  · rintro ⟨e⟩
    let f := (properCoordinateInclusion B ht).comp e
    have raw := CCO.TerminalHiddenHN.binaryDecodeEmbedding (Sig B ht) hbin f
    rw [CCO.TerminalHiddenHN.binaryDecode_binaryStructure] at raw
    refine ⟨⟨D.finite,⟨raw⟩⟩,?_⟩
    intro x
    rw [← e.sort_eq x]
    exact (e.point x).property

/-- C77. One actual finite closed root-generated extension of EVERY finite
proper hidden object. The chosen old carrier precedes any eventual order
or full-code competitor, and empty/orphan-only inputs are allowed. -/
theorem actual_proper_cofinal_root_hosts :
    CofinalRootHosts (ProperFiniteCodeAge B ht) (tupleScheme B ht F) :=
  root_cover_cofinal (properCoordinateTarget B ht) (tupleScheme B ht F)
    (CCO.TerminalHiddenHN.binaryNormalForms (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))
    (proper_coordinate_normal B ht) (proper_coordinate_ambient B ht)
    (actual_proper_root_covered B ht F)

end
end CCO.UnfilteredEP
