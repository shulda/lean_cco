import CCO.RelationalCompletion.Relational.Homogeneous

universe u v
namespace CCO.RelationalCompletion.Relational.Structure
variable {L : Language.{u}} {W : Type v}

/-- C06--C08: SAP over the FULL deletion base followed by actual homogeneity
constructs a full induced replacement clone fresh outside ALL old points. -/
theorem exists_induced_clone (U : Structure L W) (hom : U.Homogeneous)
    (sap : U.AgeSAP) (S : Set W) [Finite S] (v : S) :
    ∃ e : Embedding (U.induce S) U,
      (∀ x : S, x ≠ v → e.point x = x.val) ∧ e.point v ∉ S := by
  let B := U.induce S
  let root : Set S := {x | x ≠ v}
  let A := B.induce root
  let s : Embedding A B := B.inclusion root
  have hB : U.Age B := U.induced_mem_age S
  have hA : U.Age A := ⟨(U.inclusion S).comp s⟩
  obtain ⟨X, hX, D, hD, l, r, hcomm, hinter⟩ :=
    sap root S S A B B hA hB hB s s
  letI : Finite X := hX
  obtain ⟨d⟩ := hD
  obtain ⟨a, ha⟩ := hom S B (d.comp l) (U.inclusion S)
  let e : Embedding B U := a.toEmbedding.comp (d.comp r)
  have he : ∀ x : S, x ≠ v → e.point x = x.val := by
    intro x hx
    have hc := hcomm ⟨x, hx⟩
    change l.point x = r.point x at hc
    change a.point (d.point (r.point x)) = x.val
    rw [← hc]
    exact ha x
  refine ⟨e, he, ?_⟩
  intro hv
  let x : S := ⟨e.point v, hv⟩
  have hh : a.point (d.point (l.point x)) = a.point (d.point (r.point v)) := ha x
  have hlr : l.point x = r.point v := d.injective (a.point.injective hh)
  obtain ⟨c, _, hc⟩ := hinter x v hlr
  exact c.property hc

end CCO.RelationalCompletion.Relational.Structure
