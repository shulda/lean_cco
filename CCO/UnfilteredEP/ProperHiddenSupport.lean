import CCO.APRamseyReadout.ProperHiddenAge
import CCO.TerminalHiddenHN.NormalForms

/-! The entire actual proper hidden age used by B064. Restriction keeps
every proper sort, including orphan points and unnamed chart partners.
The SAP statement below uses only the actual unordered SAP theorem;
it makes no assertion about ordered amalgamation or reset midpoints. -/

universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnarySupport
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- Any induced map from a proper-only member factors through the entire
proper restriction, on exactly the same points. -/
def properEmbeddingFactor {V W : Type z}
    {A : Structure (Sig B ht) V} {D : Structure (Sig B ht) W}
    (hA : ∀ x, ProperSort B ht (A.sort x)) (e : A.Embedding D) :
    A.Embedding (D.induce {x | ProperSort B ht (D.sort x)}
      (proper_set_closed B ht D)) where
  point x := ⟨e.point x,by
    change ProperSort B ht (D.sort (e.point x))
    rw [e.sort_eq]
    exact hA x⟩
  sort_eq := e.sort_eq
  map_func F x y h := e.map_func F x y h
  map_rel R xs h := e.map_rel R xs h
  injective _ _ h := e.injective (congrArg Subtype.val h)
  reflect_func F x y h := by
    obtain ⟨a,ha,he⟩ := e.reflect_func F x y.val h
    exact ⟨a,ha,Subtype.ext he⟩
  reflect_rel R xs h := e.reflect_rel R xs h

/-- C27: genuine hereditary SAP on ALL finite proper-only members.
The strong intersection is inherited after deleting only real sorts. -/
theorem proper_hidden_age_sap :
    CCO.UnaryHN.Raw.FiniteHereditarySAP (ProperAge.{u,v,w,z} B ht) where
  finite C hC := hC.1.1
  hereditary := by
    intro V W A D hD e
    refine ⟨(whole_age_sap B ht).hereditary hD.1 e,?_⟩
    intro x
    rw [← e.sort_eq x]
    exact hD.2 _
  strong := by
    intro H V W Root Left Right hL hR sL sR
    obtain ⟨X,hX,D,hD,jL,jR,hcomm,hstrong⟩ :=
      (whole_age_sap B ht).strong hL.1 hR.1 sL sR
    let T := D.induce {x | ProperSort B ht (D.sort x)} (proper_set_closed B ht D)
    let f := properEmbeddingFactor B ht hL.2 jL
    let g := properEmbeddingFactor B ht hR.2 jR
    refine ⟨_,Finite.of_injective Subtype.val Subtype.val_injective,T,
      proper_restriction_mem B ht hD,f,g,?_,?_⟩
    · intro p
      exact Subtype.ext (hcomm p)
    · intro x y hxy
      exact hstrong x y (congrArg Subtype.val hxy)

/-- C28-C29: one finite family of actual term FUNCTIONS works at every
proper input, not just at roots selected by a visible coordinate chart. -/
theorem proper_hidden_term_functions_finite (s : (Lang B ht).Sorts) :
    ((Hidden B ht).NamedFunctions s).Finite :=
  CCO.TerminalHiddenHN.hidden_named_functions_finite
    (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht) s

theorem proper_hidden_normal_forms {V : Type z}
    (C : Structure (Sig B ht) V) (hC : ProperAge B ht C) :
    (CCO.TerminalHiddenHN.binaryNormalForms
      (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)).Valid
        (CCO.TerminalHiddenHN.binaryStructure (Sig B ht)
          (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
            (cloneSAP B) (fullCovers B ht)) C) :=
  CCO.TerminalHiddenHN.binaryNormalForms_valid_of_actualAge
    (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht) C hC.1

end
end CCO.UnfilteredEP
