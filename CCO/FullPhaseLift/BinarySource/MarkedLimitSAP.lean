import CCO.FullPhaseLift.Marked.Model

/-! Actual FULL marked model SAP from the proved finite marked class SAP.
Native finite-age isomorphisms transport arbitrary finite full spans to
charts; a class amalgam embeds back into the SAME constructed model. -/
set_option backward.isDefEq.respectTransparency.types false
open scoped FirstOrder
universe u v w m
namespace CCO.FullPhaseLift.BinarySource.MarkedLimitSAP
open Canonical APCharacter
noncomputable section

private def normalizedEmbedding {K : Signature} {V W : Type}
    {A : Canonical.R.Structure K.language V} {B : Canonical.R.Structure K.language W}
    (f : A.Embedding B) : Canonical.Embedding (ofRelational A) (ofRelational B) := by
  classical
  apply embeddingOf f.point f.injective
  intro r xs
  change decide (B.rel ⟨r,rfl⟩ (f.point ∘ xs)) = decide (A.rel ⟨r,rfl⟩ xs)
  exact congrArg (fun p : Prop => decide p) (propext (f.rel_iff ⟨r,rfl⟩ xs))

private def originalEmbedding {K : Signature} {V W : Type}
    {A : Canonical.R.Structure K.language V} {T : BoolTable K W}
    (f : Canonical.Embedding (ofRelational A) T) : A.Embedding (toRelational T) where
  point := f.point
  injective := f.injective
  rel_iff := by
    intro n R xs
    simpa only [toRelational_ofRelational] using f.rel_iff R xs

variable {L : Signature} {M : Type m} (U : BoolTable L M)
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (pack : M ≃ Sigma X) (mask : MaskData S)
variable (sap : Marked.StrongAmalgamation U S pack mask)

private theorem chart_iso_of_embedding {V : Type} [Finite V]
    {T : BoolTable (Marked.addBit L) V}
    (e : Canonical.Embedding T (FullReduct.expandedTable U S pack mask sap)) :
    ∃ C : Marked.Chart U S pack mask,
      Nonempty (Canonical.Iso T (Marked.table C.old.full C.bits)) := by
  letI := toFirstOrder T
  obtain ⟨C,⟨iso⟩⟩ := ((Marked.data U S pack mask sap).finite_age V).mp
    ⟨FullReduct.intoLimit U S pack mask sap e⟩
  exact ⟨C,⟨isoOfFirstOrder iso⟩⟩

/-- Full relational SAP of the ACTUAL marked Fraisse model. The finite
class SAP parameter is exactly the one used to CONSTRUCT this model,
and the final source consumer instantiates it by `Marked.strongAmalgamation`.
No full-model SAP, homogeneity or finite-age callback is a hypothesis. -/
theorem ageSAP :
    (toRelational (FullReduct.expandedTable U S pack mask sap)).AgeSAP := by
  classical
  intro V0 V1 V2 _ _ _ A0 A1 A2 h0 h1 h2 s t
  obtain ⟨e0⟩ := h0
  obtain ⟨e1⟩ := h1
  obtain ⟨e2⟩ := h2
  let T0 := ofRelational A0
  let T1 := ofRelational A1
  let T2 := ofRelational A2
  let E := FullReduct.expandedTable U S pack mask sap
  have f0 : Canonical.Embedding T0 E := by
    simpa only [ofRelational_toRelational] using normalizedEmbedding e0
  have f1 : Canonical.Embedding T1 E := by
    simpa only [ofRelational_toRelational] using normalizedEmbedding e1
  have f2 : Canonical.Embedding T2 E := by
    simpa only [ofRelational_toRelational] using normalizedEmbedding e2
  obtain ⟨C0,⟨c0⟩⟩ := chart_iso_of_embedding U S pack mask sap f0
  obtain ⟨C1,⟨c1⟩⟩ := chart_iso_of_embedding U S pack mask sap f1
  obtain ⟨C2,⟨c2⟩⟩ := chart_iso_of_embedding U S pack mask sap f2
  let a : C0 ⟶ C1 := c1.toEmbedding.comp ((normalizedEmbedding s).comp c0.symm.toEmbedding)
  let b : C0 ⟶ C2 := c2.toEmbedding.comp ((normalizedEmbedding t).comp c0.symm.toEmbedding)
  obtain ⟨Z,l,r,comm,inter⟩ := sap C0 C1 C2 a b
  let D := toRelational (Marked.table Z.old.full Z.bits)
  let le : A1.Embedding D := originalEmbedding (l.comp c1.toEmbedding)
  let re : A2.Embedding D := originalEmbedding (r.comp c2.toEmbedding)
  have hd : Nonempty (D.Embedding (toRelational E)) :=
    ⟨Marked.classEmbedding U S pack mask sap Z.old.full Z.bits Z.legal⟩
  refine ⟨Fin Z.old.size,inferInstance,D,hd,le,re,?_,?_⟩
  · intro x
    change l.point (c1.point (s.point x)) = r.point (c2.point (t.point x))
    have h := comm (c0.point x)
    change l.point (c1.point (s.point (c0.point.symm (c0.point x)))) =
      r.point (c2.point (t.point (c0.point.symm (c0.point x)))) at h
    simpa only [Equiv.symm_apply_apply] using h
  · intro x y h
    obtain ⟨z,hz,hz'⟩ := inter (c1.point x) (c2.point y) h
    refine ⟨c0.point.symm z,?_,?_⟩
    · apply c1.point.injective
      exact hz
    · apply c2.point.injective
      exact hz'

end
end CCO.FullPhaseLift.BinarySource.MarkedLimitSAP
