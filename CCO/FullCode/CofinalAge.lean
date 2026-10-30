import CCO.FullCode.FiniteHidden
import CCO.FullCode.Cofinality

/-! Ambient root coverage discharges the actual cofinal-host contract. -/

universe u v
namespace CCO.FullCode
variable {L : Language.{u}}

def CofinalRootHosts (H : FiniteHidden.{u,v} L → Prop) (S : RootScheme L) : Prop :=
  ∀ D : FiniteHidden.{u,v} L, H D →
    ∃ E : FiniteHidden.{u,v} L, H E ∧ RootGenerated E.model S ∧
      Nonempty (Structure.Embedding D.model E.model)

def IsAmbientAge (H : FiniteHidden.{u,v} L → Prop)
    {V : Type v} (P : Structure L V) : Prop :=
  ∀ D : FiniteHidden.{u,v} L, H D ↔ Nonempty (Structure.Embedding D.model P)

/-- RC supplies a finite cofinal root-generated member of the SAME ambient
age, using only old functions, finite normal forms and actual root coverage.
No hidden Ramsey, EP, CCO, SAP or ambient homogeneity is involved. -/
theorem root_cover_cofinal {H : FiniteHidden.{u,v} L → Prop}
    {V : Type v} (P : Structure L V) (S : RootScheme L)
    (N : NormalForms L) (valid : N.Valid P)
    (ambient : IsAmbientAge H P) (cover : RootCovered P S) :
    CofinalRootHosts H S := by
  intro D hD
  obtain ⟨f⟩ := (ambient D).mp hD
  let C := cofinalExtension P S N valid cover D.model f
  let E : FiniteHidden.{u,v} L :=
    ⟨C.carrier, P.induce C.carrier C.closed, C.finite.to_subtype⟩
  have hE : H E := (ambient E).mpr ⟨P.inclusion C.carrier C.closed⟩
  exact ⟨E, hE, C.generated, ⟨C.embedding⟩⟩

end CCO.FullCode
