import CCO.ExactEPGeometry.PeirceMasks
import CCO.ExactEPGeometry.TracePrimality

/-!
# B062: two genuinely represented Peircean mask choices (C15/C18/C19)

The source has one actual homogeneous original orbital colouring, its RAW
equality-inclusive exact calculus and an ACTUAL AP+HOM CCO maximal character
step. The two independent (T) fork witnesses feed two NONEMPTY exact-meet
applications of the accepted (P) provider. Neither phase is chosen merely
from a formal colour algebra. All optional `none` diagonals remain real.

This constructs an actual OLD colour-labelled triangle with three correct
phase masks. Global marked-age realization and alignment with arbitrary
prescribed marked output endpoints are the subsequent C20–C22 obligations.
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
include cco

/-- Two accepted AP-only exact domains, whose ACTUAL intersection is
nonempty and which separately meet the SAME genuine character mask,
have a common real masked pair. Empty old intersections are not covered. -/
theorem mask_two_exact
    {i j : ι} (D F : RawExact.NonemptyExact S i j)
    (ε η : Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η)
    (hMeet : TRel.Nonempty (fun x y =>
      RawExact.evaluate S D.words x y ∧ RawExact.evaluate S F.words x y))
    (hD : TRel.Nonempty (fun x y =>
      RawExact.evaluate S D.words x y ∧ P.allows (S.colour x y) ε η))
    (hF : TRel.Nonempty (fun x y =>
      RawExact.evaluate S F.words x y ∧ P.allows (S.colour x y) ε η)) :
    TRel.Nonempty (fun x y =>
      RawExact.evaluate S D.words x y ∧
      RawExact.evaluate S F.words x y ∧
      P.allows (S.colour x y) ε η) := by
  have hm : TRel.Nonempty (rawExactFamily S [D, F]) := by
    obtain ⟨x, y, hd, hf⟩ := hMeet
    refine ⟨x, y, ?_⟩
    intro d hdMem
    have hor : d = D ∨ d = F := by simpa using hdMem
    rcases hor with h | h
    · subst d; exact hd
    · subst d; exact hf
  have he : ∀ d ∈ ([D, F] : List (RawExact.NonemptyExact S i j)), ∃ x y,
      RawExact.evaluate S d.words x y ∧ P.allows (S.colour x y) ε η := by
    intro d hdMem
    have hor : d = D ∨ d = F := by simpa using hdMem
    rcases hor with h | h
    · subst d; exact hD
    · subst d; exact hF
  obtain ⟨x, y, hAll, hAllow⟩ :=
    rawExactFamily_mask_primality (S := S) P cco [D, F] ε η hv hw hm he
  exact ⟨x, y, hAll D (by simp), hAll F (by simp), hAllow⟩

/-- Both actual Peirce choices, with no synthetic triangles. The output is
an OLD realized triple carrying the original c optional orbital and all
three TRUE phase masks simultaneously. Equal vertices are permitted only
when the corresponding actual optional colour is logical equality. -/
theorem peirce_old_masked_triangle
    {i j k : ι} (D : RawExact.NonemptyExact S i j)
    (E : RawExact.NonemptyExact S j k)
    (x : X i) (z : X k)
    (hDE : TRel.comp (RawExact.evaluate S D.words)
      (RawExact.evaluate S E.words) x z)
    (ε η θ : Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η) (hz : P.validBit k θ)
    (hDmask : TRel.Nonempty (fun a b =>
      RawExact.evaluate S D.words a b ∧ P.allows (S.colour a b) ε η))
    (hEmask : TRel.Nonempty (fun b c =>
      RawExact.evaluate S E.words b c ∧ P.allows (S.colour b c) η θ))
    (hOut : P.allows (S.colour x z) ε θ) :
    ∃ (a : X i) (b : X j) (c : X k),
      RawExact.evaluate S D.words a b ∧
      RawExact.evaluate S E.words b c ∧
      S.colour a c = S.colour x z ∧
      P.allows (S.colour a b) ε η ∧
      P.allows (S.colour b c) η θ ∧
      P.allows (S.colour a c) ε θ := by
  obtain ⟨y₀, z₀, hE₀, hMaskE₀⟩ := hEmask
  obtain ⟨F, hF⟩ := first_peirce_auxiliary_exact S C E x z
  have hMeet1 : TRel.Nonempty (fun a b =>
      RawExact.evaluate S D.words a b ∧ RawExact.evaluate S F.words a b) := by
    obtain ⟨a, b, hDab, haux⟩ :=
      first_peirce_intersection_nonempty S D E x z hDE
    refine ⟨a, b, hDab, ?_⟩
    rw [hF]
    exact haux
  have hFmask : TRel.Nonempty (fun a b =>
      RawExact.evaluate S F.words a b ∧ P.allows (S.colour a b) ε η) := by
    obtain ⟨a, b, haux, hAllowed⟩ :=
      first_peirce_auxiliary_meets_mask S H P cco E x z
        y₀ z₀ hE₀ ε η θ hv hw hz hOut hMaskE₀
    refine ⟨a, b, ?_, hAllowed⟩
    rw [hF]
    exact haux
  obtain ⟨a, b, hDab, hFab, hMaskAB⟩ :=
    mask_two_exact S H P cco D F ε η hv hw hMeet1 hDmask hFmask
  rw [hF] at hFab
  obtain ⟨z₁, hAC, hEbz₁⟩ := hFab
  have hOut1 : P.allows (S.colour a z₁) ε θ := by
    rw [hAC]
    exact hOut
  obtain ⟨K, hK⟩ := second_peirce_auxiliary_exact S C a b z₁
  have hMeet2 : TRel.Nonempty (fun b' c' =>
      RawExact.evaluate S E.words b' c' ∧ RawExact.evaluate S K.words b' c') := by
    obtain ⟨b', c', hEb'c', haux⟩ :=
      second_peirce_intersection_nonempty S E a b z₁ hEbz₁
    refine ⟨b', c', hEb'c', ?_⟩
    rw [hK]
    exact haux
  have hKmask : TRel.Nonempty (fun b' c' =>
      RawExact.evaluate S K.words b' c' ∧ P.allows (S.colour b' c') η θ) := by
    obtain ⟨b', c', haux, hAllowed⟩ :=
      second_peirce_auxiliary_meets_mask S H P cco a b z₁
        ε η θ hv hw hz hMaskAB hOut1
    refine ⟨b', c', ?_, hAllowed⟩
    rw [hK]
    exact haux
  obtain ⟨b₂, c₂, hEb₂c₂, hKb₂c₂, hMaskBC⟩ :=
    mask_two_exact S H P cco E K η θ hw hz hMeet2 hEmask hKmask
  rw [hK] at hKb₂c₂
  obtain ⟨a₂, hColourAB, hColourAC⟩ := hKb₂c₂
  have hDa₂b₂ : RawExact.evaluate S D.words a₂ b₂ :=
    exact_of_same_actual_colour S H D a b hDab a₂ b₂ hColourAB
  have hMaskA₂B₂ : P.allows (S.colour a₂ b₂) ε η := by
    rw [hColourAB]
    exact hMaskAB
  have hOutput : S.colour a₂ c₂ = S.colour x z := hColourAC.trans hAC
  have hMaskA₂C₂ : P.allows (S.colour a₂ c₂) ε θ := by
    rw [hOutput]
    exact hOut
  exact ⟨a₂, b₂, c₂, hDa₂b₂, hEb₂c₂, hOutput,
    hMaskA₂B₂, hMaskBC, hMaskA₂C₂⟩

end
end CCO.ExactEPGeometry
