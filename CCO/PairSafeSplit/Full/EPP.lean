import CCO.APCharacter.Calculus
import Mathlib.Tactic.FinCases

/-! B047 C15–C21. FULL represented deterministic sheets and typed EPP.
The original AP-character proof uses RAW nonempty saturation, never the
separate STRONG saturation result. Logical identity remains in every domain. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.PairSafeSplit.Full
open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}

/-- An entire represented rigid sheet, including possible diagonal pairs. -/
def Sheet (P : SourcePhase S H C A) (b c : Reached S A) (δ : Bit)
    (x : X b.val) (y : X c.val) : Prop :=
  ∃ R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c),
    R.rel x y ∧ (letI := Reached.groupoid H C (A := A); P.character.value R = δ)

theorem bit_ne_iff_eq_add_one (x y : Bit) : x ≠ y ↔ x = y + 1 := by
  fin_cases x <;> fin_cases y
  · exact ⟨fun h => False.elim (h rfl), fun h => False.elim (zero_ne_one h)⟩
  · exact ⟨fun _ => rfl, fun _ => zero_ne_one⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩
  · exact ⟨fun h => False.elim (h rfl), fun h => False.elim (one_ne_zero h)⟩

/-- Opposite endpoint bits allow exactly the complement of a deterministic
sheet. Nonrigid actual atoms remain allowed in both phases. -/
theorem allows_opposite_iff (P : SourcePhase S H C A) (b c : Reached S A)
    (δ : Bit) (x : X b.val) (y : X c.val) :
    P.allows (S.colour x y) 0 (δ + 1) ↔ ¬ Sheet P b c δ x y := by
  letI := Reached.groupoid H C (A := A)
  rw [P.allows_actual_iff]
  constructor
  · rintro ⟨_,_,h⟩ ⟨R,hR,hχ⟩
    have he := h b.property c.property R hR
    have heq : δ + 1 = δ := calc
      δ + 1 = 0 + P.character.value R := he
      _ = P.character.value R := zero_add _
      _ = δ := hχ
    have h1 : (1 : Bit) = 0 := add_left_cancel (a := δ) (heq.trans (add_zero δ).symm)
    exact one_ne_zero h1
  · intro h
    refine ⟨fun hn => False.elim (hn b.property),
      fun hn => False.elim (hn c.property),?_⟩
    intro hb hc R hR
    have hne : P.character.value R ≠ δ := fun hχ => h ⟨R,hR,hχ⟩
    have hχ := (bit_ne_iff_eq_add_one _ _).mp hne
    simpa only [zero_add] using hχ.symm

/-- Source `thm:typed-epp` in its FULL represented reading. Every exact
domain and its meet includes the original logical diagonal when present.
The finite family may be empty: the conclusion then proves its premise
cannot hold, rather than selecting a nonexistent member. -/
theorem typed_epp (P : SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S) (b c : Reached S A)
    (D : List (RawExact.NonemptyExact S b.val c.val)) (δ : Bit)
    (hne : TRel.Nonempty (fun x y => ∀ d ∈ D, RawExact.evaluate S d.words x y))
    (hsheet : ∀ x y, (∀ d ∈ D, RawExact.evaluate S d.words x y) → Sheet P b c δ x y) :
    ∃ d ∈ D, ∀ x y, RawExact.evaluate S d.words x y → Sheet P b c δ x y := by
  classical
  by_contra hn
  have each : ∀ d ∈ D, ∃ x y, RawExact.evaluate S d.words x y ∧
      P.allows (S.colour x y) 0 (δ+1) := by
    intro d hd
    have ex : ∃ x y, RawExact.evaluate S d.words x y ∧ ¬ Sheet P b c δ x y := by
      by_contra hbad
      apply hn
      refine ⟨d,hd,fun x y hxy => ?_⟩
      exact Classical.byContradiction (fun hs => hbad ⟨x,y,hxy,hs⟩)
    obtain ⟨x,y,hxy,hnot⟩ := ex
    exact ⟨x,y,hxy,(allows_opposite_iff P b c δ x y).mpr hnot⟩
  obtain ⟨x,y,hxy,hallow⟩ := P.phase_primality cco D 0 (δ+1)
    (fun hh => False.elim (hh b.property)) (fun hh => False.elim (hh c.property)) hne each
  exact (allows_opposite_iff P b c δ x y).mp hallow (hsheet x y hxy)

theorem top_not_one_sheet (P : SourcePhase S H C A)
    (cco : SemanticCCO.{u,v,max u v,w} S) (b c : Reached S A) (δ : Bit) :
    ¬ (∀ x y, Sheet P b c δ x y) := by
  intro h
  obtain ⟨x⟩ := S.nonemptySort b.val
  obtain ⟨y⟩ := S.nonemptySort c.val
  obtain ⟨d,hd,_⟩ := typed_epp P cco b c [] δ ⟨x,y,by simp⟩ (by
    intro a b _; exact h a b)
  exact List.not_mem_nil hd

end
end CCO.PairSafeSplit.Full
