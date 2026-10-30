import CCO.APCharacter.ActualMasks
import CCO.RigidGroupoid.Phase.AffineSlice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The original maximal gate collapses an exact constant-character slice
to ONE whole bridge. No bridge is identified with a fine old atom. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
namespace SourcePhase
variable (P : SourcePhase S H C A)

theorem bit_eq_of_ne (a b δ : Bit) (ha : a ≠ δ) (hb : b ≠ δ) : a = b := by
  fin_cases a <;> fin_cases b <;> fin_cases δ <;> norm_num at *

variable {P}
/-- A subgroup with genuinely exact represented union and zero character
is trivial, by ORIGINAL maximality of the reached gate. -/
theorem subgroup_trivial (b : Reached S A)
    (U : Subgroup (Isotropy S C (Reached.kernel H C b)))
    (hU : FullExact S (isotropyUnion S C U))
    (hz : letI := Reached.groupoid H C (A := A)
      ∀ u ∈ U, P.character.value u = 0) :
    ∀ u ∈ U, u = 1 := by
  letI := Reached.groupoid H C (A := A)
  intro u hu
  by_contra hne
  let K := Reached.kernel H C b
  let Z := isotropyKernel S C U hU
  have hle : K ≤ Z := isotropyKernel_contains_gate S H C U hU
  have hlt : K < Z := by
    refine lt_iff_le_and_ne.mpr ⟨hle,?_⟩
    intro he
    apply hne
    obtain ⟨x,y,hxy⟩ := u.exact.nonempty S
    have hZ : Z.rel x y := ⟨u,hu,hxy⟩
    have hK : K.rel x y := by rw [he]; exact hZ
    exact u.eq_of_common_real_pair H (Arrow.id K) hxy hK
  let odd := P.atSort b
  obtain ⟨x,y,hxy⟩ := odd.exact.nonempty S
  have hZ : Z.rel x y := P.atSort_dominant b Z hlt x y hxy
  obtain ⟨v,hv,hvxy⟩ := hZ
  have heq : v = odd := v.eq_of_common_real_pair H odd hvxy hxy
  have ho : P.character.value odd = 0 := by rw [← heq]; exact hz v hv
  have hh := P.atSort_detects b
  change P.character.value odd = 1 at hh
  exact zero_ne_one (ho.symm.trans hh)

variable (P)
def WrongSheet (b c : Reached S A) (δ : Bit) (D : TRel X b.val c.val) : Prop :=
  ∀ x y, D x y → ∃ R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c),
    R.rel x y ∧ (letI := Reached.groupoid H C (A := A); P.character.value R ≠ δ)

/-- The affine subgroup is killed using its ACTUAL exact represented
union. This conclusion contains the original real relation equality. -/
theorem wrong_exact_single_bridge (cco : SemanticCCO.{u,v,max u v,w} S)
    (b c : Reached S A) (δ : Bit) (D : TRel X b.val c.val)
    (hD : FullExact S D)
    (hLeft : TRel.comp (Reached.kernel H C b).rel D = D)
    (hRight : TRel.comp D (Reached.kernel H C c).rel = D)
    (hWrong : P.WrongSheet b c δ D) :
    ∃ R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c), D = R.rel := by
  letI := Reached.groupoid H C (A := A)
  obtain ⟨x,y,hxy⟩ := hD.nonempty S
  obtain ⟨d,hd,_⟩ := hWrong x y hxy
  obtain ⟨d',U,hRep,_,hU⟩ := exact_rigid_coset S H C cco d hD hLeft hRight
    (fun x y h => by obtain ⟨R,hR,_⟩ := hWrong x y h; exact ⟨R,hR⟩)
  have allWrong : ∀ u ∈ U, P.character.value (d'.comp C u) ≠ δ := by
    intro u hu he
    obtain ⟨a,z,haz⟩ := (d'.comp C u).exact.nonempty S
    have hDz : D a z := by rw [hRep]; exact ⟨u,hu,haz⟩
    obtain ⟨R,hR,hχ⟩ := hWrong a z hDz
    have hh : R = d'.comp C u := R.eq_of_common_real_pair H _ hR haz
    exact hχ (hh ▸ he)
  have baseWrong : P.character.value d' ≠ δ := by
    have hh := allWrong 1 U.one_mem
    change P.character.value (d'.comp C (Arrow.id _)) ≠ δ at hh
    simpa only [Arrow.comp_id] using hh
  have hz : ∀ u ∈ U, P.character.value u = 0 := by
    intro u hu
    have hc := bit_eq_of_ne (P.character.value (d'.comp C u))
      (P.character.value d') δ (allWrong u hu) baseWrong
    have he : P.character.value d' + P.character.value u = P.character.value d' := by
      rw [← P.character.map_comp]; exact hc
    exact (add_left_cancel (he.trans (add_zero _).symm))
  have trivial := subgroup_trivial (P := P) c U hU hz
  refine ⟨d',?_⟩
  rw [hRep]
  funext x y
  apply propext
  constructor
  · rintro ⟨u,hu,hxy⟩
    rw [trivial u hu] at hxy
    change (d'.comp C (Arrow.id _)).rel x y at hxy
    rw [Arrow.comp_id] at hxy
    exact hxy
  · intro hxy
    refine ⟨1,U.one_mem,?_⟩
    change (d'.comp C (Arrow.id _)).rel x y
    rw [Arrow.comp_id]
    exact hxy

end SourcePhase
end
end CCO.APCharacter
