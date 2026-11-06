import CCO.ExactEPGeometry.TraceProductForward
import CCO.ExactEPGeometry.PeirceChoices

/-!
# B062 C20–C22: ACTUAL AP-only one-stage exact trace-product equality

Both source input traces must be nonempty.  The proof derives their real
phase-mask witnesses and validates the fixed output mask in the genuine
marked age; the two Peirce choices then produce an actual old triple.
The accepted seed theorem gives one legal marking of that triple, the
actual marked age embeds it with the true equality pattern, and its
established two-point homogeneity aligns BOTH fixed output endpoints.

The result is equality of ACTUAL marked pair relations on the displayed
child sorts.  No SAP, new quotient action, arbitrary seed orbit or extra
conditional provider is hidden in the statement.  Iteration over a finite
tower is a later separate obligation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase
open scoped FirstOrder
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- The source-strength one-character-step (TP). The two input trace
nonemptiness witnesses are existential REAL marked pairs, exactly as in
the source. For each fixed actual output pair, its old represented product
trace is equivalent to existence of a middle point in the actual
DISPLAYED marked type.  No extra validity or SAP premise is inserted. -/
theorem marked_trace_product
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : APCharacter.SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j k : ι} (D : RawExact.NonemptyExact S i j)
    (E : RawExact.NonemptyExact S j k)
    (ε η θ : Bit)
    (hD : ∃ a b : APCharacter.Age.Limit S H (P.completion_property cco),
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S D.words) ε η a b)
    (hE : ∃ b c : APCharacter.Age.Limit S H (P.completion_property cco),
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S E.words) η θ b c)
    (a c : APCharacter.Age.Limit S H (P.completion_property cco)) :
    (∃ b : APCharacter.Age.Limit S H (P.completion_property cco),
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S D.words) ε η a b ∧
      markedTrace S H (P.completion_property cco)
        (RawExact.evaluate S E.words) η θ b c) ↔
      markedTrace S H (P.completion_property cco)
        (TRel.comp (RawExact.evaluate S D.words)
          (RawExact.evaluate S E.words)) ε θ a c := by
  constructor
  · rintro ⟨b, hAB, hBC⟩
    exact marked_trace_comp_forward S H (P.completion_property cco)
      D E ε η θ a b c hAB hBC
  · intro hAC
    obtain ⟨hOwnerA,hOwnerC,x,z,hOldXZ,hCodeAC⟩ := hAC
    obtain ⟨u,v,hMarkedD⟩ := hD
    obtain ⟨v',w',hMarkedE⟩ := hE
    obtain ⟨hu,hv,xD,yD,hRealD,hCodeD⟩ := hMarkedD
    obtain ⟨hv',hw',yE,zE,hRealE,hCodeE⟩ := hMarkedE
    have hAllowedD : P.allows (S.colour xD yD) ε η :=
      limit_pair_colour_allowed S H (P.completion_property cco)
        u v ε η (S.colour xD yD) hu hv hCodeD
    have hAllowedE : P.allows (S.colour yE zE) η θ :=
      limit_pair_colour_allowed S H (P.completion_property cco)
        v' w' η θ (S.colour yE zE) hv' hw' hCodeE
    have hAllowedOut : P.allows (S.colour x z) ε θ :=
      limit_pair_colour_allowed S H (P.completion_property cco)
        a c ε θ (S.colour x z) hOwnerA hOwnerC hCodeAC
    have hValidI : P.validBit i ε := hAllowedD.1
    have hValidJ : P.validBit j η := hAllowedD.2.1
    have hValidK : P.validBit k θ := hAllowedE.2.1
    obtain ⟨x₀,y₀,z₀,hD₀,hE₀,hOutOld,hMaskAB,hMaskBC,hMaskAC⟩ :=
      peirce_old_masked_triangle S H P cco D E x z hOldXZ ε η θ
        hValidI hValidJ hValidK
        ⟨xD,yD,hRealD,hAllowedD⟩
        ⟨yE,zE,hRealE,hAllowedE⟩ hAllowedOut
    obtain ⟨a₀,b₀,c₀,hOwnerA₀,hOwnerB₀,hOwnerC₀,
        hCodeAB₀,hCodeBC₀,hCodeAC₀,_⟩ :=
      masked_three_point_in_limit (S := S) (H := H) P cco
        x₀ y₀ z₀ ε η θ hValidI hValidJ hValidK
        hMaskAB hMaskBC hMaskAC
    have hTags : taggedColour S (⟨i,x₀⟩ : Sigma X) ⟨k,z₀⟩ =
        taggedColour S (⟨i,x⟩ : Sigma X) ⟨k,z⟩ := by
      change (⟨i,k,S.colour x₀ z₀⟩ : APCharacter.Age.Colour S) =
        (⟨i,k,S.colour x z⟩ : APCharacter.Age.Colour S)
      exact congrArg (fun col : Option (S.Atom i k) =>
        (⟨i,k,col⟩ : APCharacter.Age.Colour S)) hOutOld
    have hOwnerAlignA :
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.owner a₀ =
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.owner a :=
      hOwnerA₀.trans hOwnerA.symm
    have hOwnerAlignC :
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.owner c₀ =
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.owner c :=
      hOwnerC₀.trans hOwnerC.symm
    have hCodeAlign :
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour a₀ c₀ =
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour a c := by
      calc
        _ = APCharacter.Age.colourEquiv S
          (taggedColour S (⟨i,x₀⟩ : Sigma X) ⟨k,z₀⟩) := hCodeAC₀
        _ = APCharacter.Age.colourEquiv S
          (taggedColour S (⟨i,x⟩ : Sigma X) ⟨k,z⟩) :=
            congrArg (APCharacter.Age.colourEquiv S) hTags
        _ = (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour a c :=
            hCodeAC.symm
    obtain ⟨g,hga,hgc⟩ :=
      marked_align_endpoints S H (P.completion_property cco)
        a₀ c₀ a c hOwnerAlignA hOwnerAlignC hCodeAlign
    have hPres :=
      (APCharacter.Age.limitCoding S H (P.completion_property cco)).embedding_preserves
        (APCharacter.Age.limitCoding S H (P.completion_property cco)) g.toEmbedding
    have hMidOwner :
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.owner (g b₀) =
          APCharacter.Age.ownerEquiv S (j,η) :=
      (hPres.1 b₀).trans hOwnerB₀
    have hABCode :
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour a (g b₀) =
          APCharacter.Age.colourEquiv S
            (taggedColour S (⟨i,x₀⟩ : Sigma X) ⟨j,y₀⟩) := by
      calc
        _ = (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour
          (g a₀) (g b₀) := by rw [hga]
        _ = (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour
          a₀ b₀ := hPres.2 a₀ b₀
        _ = APCharacter.Age.colourEquiv S
          (taggedColour S (⟨i,x₀⟩ : Sigma X) ⟨j,y₀⟩) := hCodeAB₀
    have hBCCode :
        (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour (g b₀) c =
          APCharacter.Age.colourEquiv S
            (taggedColour S (⟨j,y₀⟩ : Sigma X) ⟨k,z₀⟩) := by
      calc
        _ = (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour
          (g b₀) (g c₀) := by rw [hgc]
        _ = (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour
          b₀ c₀ := hPres.2 b₀ c₀
        _ = APCharacter.Age.colourEquiv S
          (taggedColour S (⟨j,y₀⟩ : Sigma X) ⟨k,z₀⟩) := hCodeBC₀
    exact ⟨g b₀,
      ⟨hOwnerA,hMidOwner,x₀,y₀,hD₀,hABCode⟩,
      ⟨hMidOwner,hOwnerC,y₀,z₀,hE₀,hBCCode⟩⟩

end
end CCO.ExactEPGeometry
