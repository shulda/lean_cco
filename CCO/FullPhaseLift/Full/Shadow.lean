import CCO.FullPhaseLift.Full.Reindex
import CCO.FullPhaseLift.Canonical.Source
import CCO.StrongExact.CycleCompletion

/-! The source A03 receives a genuine atomic canonical pair shadow with
simple-cycle certificates. Every signed low literal is interpreted LOCALLY
in its ambient nullary type, unary name, or specified two-point atom.
A merely colliding low realization is deliberately not this interface. -/

universe v w
namespace CCO.FullPhaseLift.Full.Shadow
open Canonical
noncomputable section
variable {L : Signature} {M : Type w} {V : Type v}
variable (U : BoolTable L M) (hsym : SameSortSymmetric U)

/-- A finite local certificate for one signed old literal. Both Boolean
values and all repeated-coordinate/nullary tests are retained. -/
inductive LowCertificate (P : CCO.PartialDiagram (source U hsym) V)
    (r : Fin L.size) (xs : Fin (L.arity r) → V) (b : Bool) : Prop
  | nullary (slots : Fin (L.arity r) → Fin 0)
      (read : nullaryType U ⟨r,slots⟩ = b) : LowCertificate P r xs b
  | unary (x : V) (slots : Fin (L.arity r) → Fin 1)
      (tuple : xs = (fun _ : Fin 1 => x) ∘ slots)
      (read : (P.vertexSort x).val ⟨r,slots⟩ = b) : LowCertificate P r xs b
  | pair (x y : V) (hne : x ≠ y) (slots : Fin (L.arity r) → Fin 2)
      (tuple : xs = ![x,y] ∘ slots)
      (a : (source U hsym).Atom (P.vertexSort x) (P.vertexSort y))
      (edge : P.edge x y hne = some a)
      (read : a.val ⟨r,slots⟩ = b) : LowCertificate P r xs b

def LowRefines (P : CCO.PartialDiagram (source U hsym) V)
    (D : Partial L V) : Prop :=
  ∀ r xs b, SmallSupport xs → D r xs = some b → LowCertificate U hsym P r xs b

/-- Frozen factors retain their ENTIRE unary and two-point atomic profiles,
not just positive names or a selected relation from their complete tables. -/
def FactorRefines (P : CCO.PartialDiagram (source U hsym) V)
    {D : Partial L V} {m : ℕ} (F : Fin m → FrozenFactor U D) : Prop :=
  (∀ j x, (P.vertexSort ((F j).inclusion x)).val = unaryProfile (F j).table x) ∧
  ∀ j x y (hne : x ≠ y),
    ∃ a, P.edge ((F j).inclusion x) ((F j).inclusion y)
      (fun h => hne ((F j).inclusion.injective h)) = some a ∧
      a.val = pairProfile (F j).table x y

structure CertifiedPairCompletion (D : Partial L V) {m : ℕ}
    (F : Fin m → FrozenFactor U D) where
  diagram : CCO.PartialDiagram (source U hsym) V
  low : LowRefines U hsym diagram D
  frozen : FactorRefines U hsym diagram F
  cycles : ∀ C : SimpleCycle diagram, CycleHom C

theorem LowCertificate.interpret
    {P : CCO.PartialDiagram (source U hsym) V} {r xs b}
    (h : LowCertificate U hsym P r xs b) (f : DiagramHom P) :
    U r (((pack U).symm ∘ f.image) ∘ xs) = b := by
  cases h with
  | nullary slots read =>
    have he : ((pack U).symm ∘ f.image) ∘ xs = Fin.elim0 ∘ slots := by
      funext i
      exact Fin.elim0 (slots i)
    rw [he]
    exact read
  | unary x slots tuple read =>
    rw [tuple]
    have he : ((pack U).symm ∘ f.image) ∘ ((fun _ : Fin 1 => x) ∘ slots) =
        (fun _ : Fin 1 => (f.point x).val) ∘ slots := rfl
    rw [he]
    have hp := congrFun (f.point x).property ⟨r,slots⟩
    exact hp.trans read
  | pair x y hne slots tuple a edge read =>
    have hp := (colour_some_iff U (f.point x) (f.point y) a).mp
      (f.preserves_edge x y hne a edge)
    rw [tuple]
    have he : ((pack U).symm ∘ f.image) ∘ (![x,y] ∘ slots) =
        ![(f.point x).val,(f.point y).val] ∘ slots := by
      funext i
      change (f.point (![x,y] (slots i))).val =
        ![(f.point x).val,(f.point y).val] (slots i)
      generalize slots i = j
      fin_cases j <;> rfl
    rw [he]
    exact (congrFun hp.2 ⟨r,slots⟩).trans read

theorem LowRefines.interpret {P : CCO.PartialDiagram (source U hsym) V}
    {D : Partial L V} (h : LowRefines U hsym P D) (f : DiagramHom P) :
    LowRealizes U D ((pack U).symm ∘ f.image) :=
  fun r xs b hs hd => (h r xs b hs hd).interpret U hsym f

/-- The RAW source A03. Its completion premise contains local signed
canonical refinement plus actual CycleHom certificates, not a chosen full
completion, an SAP callback, or a negative-menu injectivization callback. -/
def SupportNormal : Prop :=
  ∀ (n : ℕ) (D : Partial L (Fin n)) (m : ℕ) (F : Fin m → FrozenFactor U D),
    Consistent U D → HigherCovered F →
    Nonempty (CertifiedPairCompletion U hsym D F) →
    ∃ f : Fin n → M, Realizes U D f ∧ ∀ j, (F j).FixedBy f

end
end CCO.FullPhaseLift.Full.Shadow
