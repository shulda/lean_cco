import CCO.ExactEPGeometry.PeirceEndpoints
import CCO.ExactEPGeometry.MarkedPair
import CCO.APCharacter.Totality

/-!
# B062 C14/C17: the TWO actual AP-only fork applications

Fork totality is taken from the established maximal-character source,
not from a hypothetical colouring table. An allowed first leg is turned
into a real point of `{c};Eᵒᵖ`, and the selected first a-leg then gives a
real point of `{a}ᵒᵖ;{c}`. All relations and colour converses preserve
the optional diagonal. These are the nonempty-mask inputs to the two
successive source RAW exact-primality applications in C22.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : APCharacter.SourcePhase S H C A)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- The exact first auxiliary factor meets the actual allowed (ε,η) mask.
The fixed output orbital is the ACTUAL c colour of x,z. The E-pair may
be witnessed elsewhere; old pair homogeneity transfers E to the chosen
(T)-witness and no extra finite identity edge is introduced. -/
theorem first_peirce_auxiliary_meets_mask
    {i j k : ι}
    (E : RawExact.NonemptyExact S j k)
    (x : X i) (z : X k) (y₀ : X j) (z₀ : X k)
    (hE : RawExact.evaluate S E.words y₀ z₀)
    (ε η θ : APCharacter.Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η) (hz : P.validBit k θ)
    (hc : P.allows (S.colour x z) ε θ)
    (hb : P.allows (S.colour y₀ z₀) η θ) :
    ∃ x' y', TRel.comp (S.rawAtomRel (S.colour x z))
        (TRel.converse (RawExact.evaluate S E.words)) x' y' ∧
      P.allows (S.colour x' y') ε η := by
  have hbReverse : P.allows (S.colour z₀ y₀) θ η :=
    allowed_reverse_real S (M := P.masks) y₀ z₀ η θ hb
  have hcNonempty : TRel.Nonempty (S.rawAtomRel (S.colour x z)) :=
    ⟨x, z, rfl⟩
  have hbNonempty : TRel.Nonempty (S.rawAtomRel (S.colour z₀ y₀)) :=
    ⟨z₀, y₀, rfl⟩
  obtain ⟨x', y', ⟨w, hxw, hwy⟩, hAllowed⟩ :=
    P.fork_totality cco (S.colour x z) (S.colour z₀ y₀)
      ε θ η hv hz hw hc hbReverse hcNonempty hbNonempty
  have hReverseColour : S.colour y' w = S.colour y₀ z₀ := by
    calc
      S.colour y' w =
          (S.colour w y').map (fun a => S.conv a) :=
        S.colour_reverse w y'
      _ = (S.colour z₀ y₀).map (fun a => S.conv a) :=
        congrArg (fun c => c.map (fun a => S.conv a)) hwy
      _ = S.colour y₀ z₀ := (S.colour_reverse z₀ y₀).symm
  have hE' : RawExact.evaluate S E.words y' w :=
    exact_of_same_actual_colour S H E y₀ z₀ hE y' w hReverseColour
  exact ⟨x', y', ⟨w, hxw, hE'⟩, hAllowed⟩

/-- The other actual fork applies to a reversed selected a-leg and the
same old output c. Its allowed result meets `{a}ᵒᵖ;{c}` with the correct
second child phase. This is INDEPENDENT of choosing any b from E. -/
theorem second_peirce_auxiliary_meets_mask
    {i j k : ι}
    (x : X i) (y : X j) (z : X k)
    (ε η θ : APCharacter.Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η) (hz : P.validBit k θ)
    (ha : P.allows (S.colour x y) ε η)
    (hc : P.allows (S.colour x z) ε θ) :
    ∃ y' z', TRel.comp (TRel.converse (S.rawAtomRel (S.colour x y)))
        (S.rawAtomRel (S.colour x z)) y' z' ∧
      P.allows (S.colour y' z') η θ := by
  have haReverse : P.allows (S.colour y x) η ε :=
    allowed_reverse_real S (M := P.masks) x y ε η ha
  have haNonempty : TRel.Nonempty (S.rawAtomRel (S.colour y x)) :=
    ⟨y, x, rfl⟩
  have hcNonempty : TRel.Nonempty (S.rawAtomRel (S.colour x z)) :=
    ⟨x, z, rfl⟩
  obtain ⟨y', z', ⟨w, hyw, hwz⟩, hAllowed⟩ :=
    P.fork_totality cco (S.colour y x) (S.colour x z)
      η ε θ hw hv hz haReverse hc haNonempty hcNonempty
  have hForwardColour : S.colour w y' = S.colour x y := by
    calc
      S.colour w y' =
          (S.colour y' w).map (fun a => S.conv a) :=
        S.colour_reverse y' w
      _ = (S.colour y x).map (fun a => S.conv a) :=
        congrArg (fun c => c.map (fun a => S.conv a)) hyw
      _ = S.colour x y := (S.colour_reverse y x).symm
  exact ⟨y', z', ⟨w, hForwardColour, hwz⟩, hAllowed⟩

end
end CCO.ExactEPGeometry
