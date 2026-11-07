import CCO.UnfilteredEP.HierarchyPaths

/-!
# B064 C44: every actual RAW transition has its named inverse chart

The full RAW transition menu of the actual hidden signature is included.
The inverse is the existing converse RAW symbol, whose genuine target is
proved equal to the original source. All casts retain the same actual
quotient class and completed hidden vertex.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnaryTermsReturn
open CCO.TransitionClosure CCO.TypedOrbitFrames CCO.QuotientTransport
noncomputable section

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

abbrev rawCutSource {i j : B.Sorts}
    (a : OriginalNamedRawTransitionSymbol (cloneSource B) (HF B) i j) : HiddenCut B :=
  ⟨i,a.val.1⟩

abbrev rawCutTarget {i j : B.Sorts}
    (a : OriginalNamedRawTransitionSymbol (cloneSource B) (HF B) i j) : HiddenCut B :=
  ⟨j,originalNamedRawTransitionSymbol_target (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a⟩

private theorem namedWord_cast_target_node {i j : B.Sorts}
    {D : NamedCoordinate B i} {E F : NamedCoordinate B j} (h : E = F)
    (t : OriginalNamedRawUnaryTerm (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) D E)
    (q : Quotient D.val.val) :
    namedNode B F (OriginalNamedRawUnaryTerm.eval (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) (h ▸ t) q) =
    namedNode B E (OriginalNamedRawUnaryTerm.eval (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) t q) := by
  cases h
  rfl

/-- Converse transport returns to the literal old completed vertex,
not just to an isomorphic quotient type. -/
theorem raw_converse_returns_node {i j : B.Sorts}
    (a : OriginalNamedRawTransitionSymbol (cloneSource B) (HF B) i j)
    (q : Quotient a.val.1.val.val) :
    let inv := originalNamedRawTransitionSymbol_converse (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a
    namedNode B (rawCutTarget B ht inv).2
      ((originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) inv).quotientEquiv
        ((originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) a).quotientEquiv q)) =
      namedNode B a.val.1 q := by
  let inv := originalNamedRawTransitionSymbol_converse (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a
  let T := originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) a
  let U := originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) inv
  change namedNode B (rawCutTarget B ht inv).2 (U.quotientEquiv (T.quotientEquiv q)) = _
  induction q using Quotient.inductionOn with | _ x =>
    obtain ⟨y,hxy⟩ := T.serial x
    have hyx : inv.val.2.val.val y x := hxy
    refine (congrArg (fun z => namedNode B (rawCutTarget B ht inv).2 (U.quotientEquiv z))
      (T.quotientEquiv_edge hxy)).trans ?_
    refine (congrArg (namedNode B (rawCutTarget B ht inv).2)
      (U.quotientEquiv_edge hyx)).trans ?_
    exact congrArg (fun D : NamedCoordinate B i =>
      namedNode B D (Quotient.mk D.val.val x))
      (originalNamedRawTransitionSymbol_converse_target_name (cloneSource B) (HF B) (cloneSAP B)
        (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a)

/-- The casted inverse syntax has the literal inverse quotient value. -/
theorem raw_inverse_word_returns_node {i j : B.Sorts}
    (a : OriginalNamedRawTransitionSymbol (cloneSource B) (HF B) i j)
    (q : Quotient a.val.1.val.val) :
    namedNode B a.val.1
      (OriginalNamedRawUnaryTerm.eval (cloneSource B) (HF B) (cloneSAP B)
        (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
        (originalNamedRawUnaryTerm_inverse_symbol (cloneSource B) (HF B) (cloneSAP B)
          (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a)
        ((originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) a).quotientEquiv q)) =
      namedNode B a.val.1 q := by
  let inv := originalNamedRawTransitionSymbol_converse (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a
  let t : OriginalNamedRawUnaryTerm (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
      (rawCutTarget B ht a).2 (rawCutTarget B ht inv).2 :=
    .transition inv (.ident (rawCutTarget B ht a).2)
  let h := originalNamedRawTransitionSymbol_converse_target_name (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a
  have hc := namedWord_cast_target_node B ht h t
    ((originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) a).quotientEquiv q)
  exact hc.trans (raw_converse_returns_node B ht a q)

/-- Every actual named RAW primitive is a path in the SAME actual unary
signature. Its semantic inverse is realized by the genuine named converse. -/
def rawNamedCutPath {i j : B.Sorts}
    (a : OriginalNamedRawTransitionSymbol (cloneSource B) (HF B) i j) :
    NamedCutPath B ht (rawCutSource B a) (rawCutTarget B ht a) where
  quotientEquiv := (originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) a).quotientEquiv
  equivariant g q :=
    (originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) a).quotientEquiv_equivariant g q
  forward := originalNamedWordAsTerm (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) (.transition a (.ident a.val.1))
  backward := originalNamedWordAsTerm (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
    (originalNamedRawUnaryTerm_inverse_symbol (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a)
  forward_value q :=
    original_named_word_as_term_eval (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) (.transition a (.ident a.val.1)) q
  backward_value q := by
    let T := originalNamedRawTransitionSymbol_transport (cloneSource B) (HF B) a
    obtain ⟨r,rfl⟩ := T.quotientEquiv.surjective q
    exact (original_named_word_as_term_eval (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
      (originalNamedRawUnaryTerm_inverse_symbol (cloneSource B) (HF B) (cloneSAP B)
        (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a)
      (T.quotientEquiv r)).trans ((raw_inverse_word_returns_node B ht a r).trans
        (congrArg (namedNode B a.val.1) (T.quotientEquiv.symm_apply_apply r).symm))

end
end CCO.UnfilteredEP
