import CCO.UnfilteredEP.HierarchyRawPaths
import CCO.TypedOrbitFrames.RealTermNormalForms
import CCO.UnaryTermsReturn.LiteralRealFactorization

/-! B064 C57/C62: every bijective ACTUAL quotient-start unary term has
an inverse in the existing named language. Named-word normal forms retain
the actual input kernel; injectivity removes every strict upward factor.
No arbitrary semantic inverse is declared a new function symbol. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnaryTermsReturn
open CCO.TransitionClosure CCO.TypedOrbitFrames CCO.QuotientTransport
open CCO.UnaryFreshFrames CCO.ParityHasse.Original
noncomputable section

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
local notation "S" => cloneSource B
local notation "H" => HF B
local notation "sap" => cloneSAP B
local notation "nr2" => CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)

private theorem named_word_surjective {i j : B.Sorts}
    {D : NamedCoordinate B i} {E : NamedCoordinate B j}
    (word : OriginalNamedRawUnaryTerm (S) (H) (sap) (nr2) D E) :
    Function.Surjective (OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) word) := by
  induction word with
  | ident D => exact Function.surjective_id
  | @up j D E F word above ih =>
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      obtain ⟨p,hp⟩ := ih (Quotient.mk E.val.val x)
      refine ⟨p,?_⟩
      change Quot.mapRight above
        (OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) word p) = _
      rw [hp]
      rfl
  | @transition j k D a word ih =>
    exact (originalNamedRawTransitionSymbol_transport (S) (H) a).quotientEquiv.surjective.comp ih

/-- Every injective genuine named word has its actual named inverse.
The only potentially collapsing constructor is an upward quotient map;
its injectivity forces equality of its FULL source and target kernels. -/
private theorem path_of_injective_named_word {i j : B.Sorts}
    {D : NamedCoordinate B i} {E : NamedCoordinate B j}
    (word : OriginalNamedRawUnaryTerm (S) (H) (sap) (nr2) D E)
    (injective : Function.Injective
      (OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) word)) :
    ∃ p : NamedCutPath B ht ⟨i,D⟩ ⟨j,E⟩,
      p.forward = originalNamedWordAsTerm (S) (H) (sap) (nr2) word := by
  induction word with
  | ident D => exact ⟨NamedCutPath.identity _,rfl⟩
  | @up j D E F word above ih =>
    have prefixInj : Function.Injective
        (OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) word) := by
      intro p q hpq
      apply injective
      exact congrArg (Quot.mapRight above) hpq
    obtain ⟨path,hpath⟩ := ih prefixInj
    have upInj : Function.Injective (Quot.mapRight above) := by
      intro p q hpq
      obtain ⟨x,rfl⟩ := named_word_surjective B ht word p
      obtain ⟨y,rfl⟩ := named_word_surjective B ht word q
      exact congrArg (OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) word)
        (injective hpq)
    have below : F.val ≤ E.val := by
      intro x y hxy
      have hq : Quot.mapRight above (Quotient.mk E.val.val x) =
          Quot.mapRight above (Quotient.mk E.val.val y) := Quotient.sound hxy
      exact Quotient.exact (upInj hq)
    have names : F = E := Subtype.ext (le_antisymm below above)
    subst F
    let full := originalNamedWordAsTerm (S) (H) (sap) (nr2) (.up word above)
    have values (q : Quotient D.val.val) :
        (Hidden B ht).eval full (namedNode B D q) =
          namedNode B E (path.quotientEquiv q) := by
      have hword := original_named_word_as_term_eval (S) (H) (sap) (nr2) word q
      have same : OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) (.up word above) q =
          OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) word q := by
        change Quot.mapRight above _ = _
        have upId (r : Quotient E.val.val) : Quot.mapRight above r = r := by
          induction r using Quotient.inductionOn with | _ x => rfl
        exact upId _
      exact (original_named_word_as_term_eval (S) (H) (sap) (nr2) (.up word above) q).trans
        ((congrArg (namedNode B E) same).trans
          (hword.symm.trans (by rw [← hpath]; exact path.forward_value q)))
    exact ⟨{path with forward := full,forward_value := values},rfl⟩
  | @transition j k D a word ih =>
    have prefixInj : Function.Injective
        (OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) word) := by
      intro p q hpq
      apply injective
      exact congrArg (originalNamedRawTransitionSymbol_transport (S) (H) a).quotientEquiv hpq
    obtain ⟨path,hpath⟩ := ih prefixInj
    refine ⟨path.compose (rawNamedCutPath B ht a),?_⟩
    change (rawNamedCutPath B ht a).forward.comp path.forward = _
    rw [hpath]
    rfl

/-- Every arbitrary bijective quotient-start term is the forward term
of an actual named path, with an existing inverse term. This includes
terms mixing upward maps and all RAW transitions, not just raw letters. -/
theorem namedCutPath_of_bijective_term (D E : HiddenCut B)
    (term : Term (Lang B ht) (hiddenCutSort B ht D) (hiddenCutSort B ht E))
    (bijective : Function.Bijective ((Hidden B ht).typedEval term)) :
    ∃ path : NamedCutPath B ht D E, path.forward = term := by
  rcases D with ⟨i,D⟩
  rcases E with ⟨j,E⟩
  let projection := originalProjectionAsTerm (S) (H) (sap) (nr2) D
  let real := term.comp projection
  rcases original_real_term_literal_named_form (S) (H) (sap) (nr2) real with
    ⟨impossible,_⟩ | ⟨k,U,F,word,output,hReal⟩
  · cases impossible
  · have hj : j = k := congrArg (fun s : (Lang B ht).Sorts => s.down.1) output
    subst k
    have names : E = F := by
      change (⟨⟨j,.inr E⟩⟩ : (Lang B ht).Sorts) = ⟨⟨j,.inr F⟩⟩ at output
      simpa only [ULift.ext_iff,Sigma.mk.injEq,heq_eq_eq,true_and,Sum.inr.injEq] using output
    subst F
    have realValue (x : (B.cloneCurrent.Point i)) :
        (Hidden B ht).eval term (namedNode B D (Quotient.mk D.val.val x)) =
        namedNode B E (OriginalNamedRawUnaryTerm.eval (S) (H) (sap) (nr2) word
          (Quotient.mk U.val.val x)) := by
      have h := hReal x
      change (Hidden B ht).eval (term.comp projection) (.inl ⟨i,x⟩) = _ at h
      rw [Structure.eval_comp] at h
      have hp : (Hidden B ht).eval projection (.inl ⟨i,x⟩) =
          namedNode B D (Quotient.mk D.val.val x) :=
        original_projection_as_term_eval (S) (H) (sap) (nr2) D x
      exact (congrArg ((Hidden B ht).eval term) hp).symm.trans h
    obtain ⟨K,_,theta,thetaInj,hPoint,hKernel⟩ :=
      original_real_named_term_literal_QTNF (S) (H) (sap) (nr2) U E word
    have kernel : K.val = D.val := by
      apply ColourEq.ext
      intro x y
      constructor
      · intro hK
        have hw := (hKernel x y).mpr hK
        have heval : (Hidden B ht).eval term (namedNode B D (Quotient.mk D.val.val x)) =
            (Hidden B ht).eval term (namedNode B D (Quotient.mk D.val.val y)) :=
          (realValue x).trans ((congrArg (namedNode B E) hw).trans (realValue y).symm)
        have typed : (Hidden B ht).typedEval term
            ⟨namedNode B D (Quotient.mk D.val.val x),rfl⟩ =
            (Hidden B ht).typedEval term ⟨namedNode B D (Quotient.mk D.val.val y),rfl⟩ :=
          Subtype.ext heval
        exact Quotient.exact (namedNode_injective B D (congrArg Subtype.val (bijective.1 typed)))
      · intro hD
        have heval := congrArg ((Hidden B ht).eval term)
          (congrArg (namedNode B D) (Quotient.sound hD))
        have nodes := (realValue x).symm.trans (heval.trans (realValue y))
        exact (hKernel x y).mp (namedNode_injective B E nodes)
    have names : K = D := Subtype.ext kernel
    subst K
    obtain ⟨path,hPath⟩ := path_of_injective_named_word B ht theta thetaInj
    have values (q : Quotient D.val.val) :
        (Hidden B ht).eval term (namedNode B D q) =
          namedNode B E (path.quotientEquiv q) := by
      induction q using Quotient.inductionOn with
      | _ x =>
        have hTheta := original_named_word_as_term_eval (S) (H) (sap) (nr2) theta
          (Quotient.mk D.val.val x)
        rw [← hPath] at hTheta
        exact (realValue x).trans ((congrArg (namedNode B E) (hPoint x)).trans
          (hTheta.symm.trans (path.forward_value _)))
    exact ⟨{path with forward := term,forward_value := values},rfl⟩

end
end CCO.UnfilteredEP
