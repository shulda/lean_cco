import CCO.ExactEPGeometry.PeirceChoices
import CCO.ExactEPGeometry.MarkedTrace
import Mathlib.Tactic.FinCases

/-!
# B062 C20: one ACTUAL globally marked triangle and its marked-limit image

All three old vertices are real.  Repeated old vertices are identified
BEFORE the actual finite marked diagram is embedded, using the kernel
quotient of the three-position map.  The embedding is injective on these
distinct old vertices and retains every old pair colour and each phase
name.  No fake equality-coloured diversity edge or arbitrary seed orbit.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) {M : APCharacter.MaskData S}
variable (completion : APCharacter.Age.CompletionProperty S M)

/-- A finite tuple of actual old points, possibly with repetitions, in ONE
global legal character marking has an image in the genuine marked limit.
The equality pattern is exactly the old tuple equality pattern: the quotient
by the kernel is formed BEFORE applying an injective age embedding. -/
theorem marked_finite_tuple_realized
    {I : Type} [Finite I]
    (point : I → Sigma X) (mark : Sigma X → Bit)
    (hm : M.GlobalMarking mark) :
    ∃ image : I → APCharacter.Age.Limit S H completion,
      (∀ a b, image a = image b ↔ point a = point b) ∧
      (∀ a, (APCharacter.Age.limitCoding S H completion).table.owner (image a) =
        APCharacter.Age.ownerEquiv S ((point a).1, mark (point a))) ∧
      ∀ a b, (APCharacter.Age.limitCoding S H completion).table.colour (image a) (image b) =
        APCharacter.Age.colourEquiv S (taggedColour S (point a) (point b)) := by
  classical
  let Q := Quotient (Setoid.ker point)
  letI : Finite Q :=
    Finite.of_surjective (fun a : I => (Quotient.mk _ a : Q)) Quotient.mk_surjective
  let real : Q → Sigma X := Quotient.lift point (by
    intro a b h
    exact h)
  have realInj : Function.Injective real := by
    intro a b h
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
        exact Quotient.sound h
  let bits : Q → Bit := fun z => mark (real z)
  have legal : APCharacter.Age.Legal S M real bits := by
    constructor
    · exact fun z => hm.1 (real z)
    · exact fun a b => hm.2 (real a) (real b)
  obtain ⟨f, ho, hc⟩ :=
    APCharacter.Age.embed_realized S H completion real bits realInj legal
  let image : I → APCharacter.Age.Limit S H completion :=
    fun a => f (Quotient.mk _ a)
  refine ⟨image, ?_, ?_, ?_⟩
  · intro a b
    constructor
    · intro h
      have he : (Quotient.mk _ a : Q) = Quotient.mk _ b := f.injective h
      exact Quotient.exact he
    · intro he
      exact congrArg f (Quotient.sound he)
  · intro a
    simpa [image, real, bits] using ho (Quotient.mk _ a)
  · intro a b
    simpa [image, real] using hc (Quotient.mk _ a) (Quotient.mk _ b)

variable {S H completion}

/-- An actual OLD compatible triple carries all nine pair tests. The three
off-diagonal masks are exactly the given ones and their real converses;
the true diagonal masks are derived from the identity source law. -/
theorem masked_three_point_legal
    {i j k : ι} (a : X i) (b : X j) (c : X k)
    (ε η θ : Bit)
    (hv : M.validBit i ε) (hw : M.validBit j η) (hz : M.validBit k θ)
    (hab : M.allowed (S.colour a b) ε η)
    (hbc : M.allowed (S.colour b c) η θ)
    (hac : M.allowed (S.colour a c) ε θ) :
    APCharacter.Age.Legal S M
      (fun n : Fin 3 => ![(⟨i,a⟩ : Sigma X), ⟨j,b⟩, ⟨k,c⟩] n)
      (fun n : Fin 3 => ![ε,η,θ] n) := by
  constructor
  · intro n
    fin_cases n
    · simpa using hv
    · simpa using hw
    · simpa using hz
  · intro n m
    fin_cases n <;> fin_cases m
    · have hd : S.colour a a = none := (S.colour_none_iff a a).mpr rfl
      simpa [hd] using (M.identity i ε ε).mpr ⟨rfl, hv⟩
    · simpa using hab
    · simpa using hac
    · simpa using allowed_reverse_real S a b ε η hab
    · have hd : S.colour b b = none := (S.colour_none_iff b b).mpr rfl
      simpa [hd] using (M.identity j η η).mpr ⟨rfl, hw⟩
    · simpa using hbc
    · simpa using allowed_reverse_real S a c ε θ hac
    · simpa using allowed_reverse_real S b c η θ hbc
    · have hd : S.colour c c = none := (S.colour_none_iff c c).mpr rfl
      simpa [hd] using (M.identity k θ θ).mpr ⟨rfl, hz⟩

/-- Full C20: one globally markable actual old triangle becomes a literal
marked-limit triangle, with all colours and all phase names retained, and
endpoint equality reflected exactly.  No three-distinct-points hypothesis
is added: the kernel quotient handles all repeated positions. -/
theorem masked_three_point_in_limit
    {C : ExactCalculus S} {r : ι} {A : Kernel S r}
    (P : APCharacter.SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i j k : ι} (a : X i) (b : X j) (c : X k)
    (ε η θ : Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η) (hz : P.validBit k θ)
    (hab : P.allows (S.colour a b) ε η)
    (hbc : P.allows (S.colour b c) η θ)
    (hac : P.allows (S.colour a c) ε θ) :
    ∃ (A' B' C' : APCharacter.Age.Limit S H (P.completion_property cco)),
      (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.owner A' =
        APCharacter.Age.ownerEquiv S (i,ε) ∧
      (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.owner B' =
        APCharacter.Age.ownerEquiv S (j,η) ∧
      (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.owner C' =
        APCharacter.Age.ownerEquiv S (k,θ) ∧
      (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour A' B' =
        APCharacter.Age.colourEquiv S
          (taggedColour S (⟨i,a⟩ : Sigma X) ⟨j,b⟩) ∧
      (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour B' C' =
        APCharacter.Age.colourEquiv S
          (taggedColour S (⟨j,b⟩ : Sigma X) ⟨k,c⟩) ∧
      (APCharacter.Age.limitCoding S H (P.completion_property cco)).table.colour A' C' =
        APCharacter.Age.colourEquiv S
          (taggedColour S (⟨i,a⟩ : Sigma X) ⟨k,c⟩) ∧
      (A' = C' ↔ (⟨i,a⟩ : Sigma X) = ⟨k,c⟩) := by
  let old : Fin 3 → Sigma X := ![⟨i,a⟩,⟨j,b⟩,⟨k,c⟩]
  let bits : Fin 3 → Bit := ![ε,η,θ]
  have legal : APCharacter.Age.Legal S P.masks old bits :=
    masked_three_point_legal (S := S) (M := P.masks) a b c ε η θ hv hw hz hab hbc hac
  obtain ⟨mark, hm, prescribed⟩ :=
    APCharacter.Age.finite_seed_small S P.masks P.finite_seed_extension old bits legal
  obtain ⟨f, heq, ho, hc⟩ :=
    marked_finite_tuple_realized S H (P.completion_property cco) old mark hm
  refine ⟨f 0, f 1, f 2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [old,bits,prescribed 0] using ho 0
  · simpa [old,bits,prescribed 1] using ho 1
  · simpa [old,bits,prescribed 2] using ho 2
  · simpa [old] using hc 0 1
  · simpa [old] using hc 1 2
  · simpa [old] using hc 0 2
  · simpa [old] using heq 0 2

end
end CCO.ExactEPGeometry
