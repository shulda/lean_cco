import CCO.UnarySupport.BoundaryLanguages

namespace CCO.UnarySupport.Boundaries
open Structure

def nullarySource : Structure (relationalSignature (fun _ : Unit => 0)) Empty :=
  relational _ (fun _ _ => False)

def nullaryTarget : Structure (relationalSignature (fun _ : Unit => 0)) Unit :=
  relational _ (fun _ _ => True)

def nullaryMap : Hom nullarySource nullaryTarget where
  point := Empty.elim
  sort_eq x := Empty.elim x
  map_func F := Empty.elim F
  map_rel _ _ h := False.elim h

theorem nullary_local : nullaryMap.LocallyInduced := by
  intro S hS
  cases hS with
  | singleton x => exact Empty.elim x
  | binary R hR xs hr hd => exact False.elim (by cases hR)

theorem nullary_not_embedding : ¬ nullaryMap.HomEmbedding := by
  intro hf
  let S : Set Empty := ∅
  have hS : nullarySource.IsClosed S := relational_closed _ _ S
  have h := hf S hS (empty_irreducible _)
  have hr := (h.2.1 () (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).1 trivial
  exact hr

/-- With an empty source, all local tests and nonempty-HE conclusions hold,
but a false nullary fact cannot be reflected from a true target fact. -/
theorem nullary_counterexample :
    nullarySource.Total ∧ nullaryMap.LocallyInduced ∧
    nullaryMap.NonemptyHomEmbedding ∧ ¬ nullaryMap.HomEmbedding := by
  refine ⟨relational_total _ _, nullary_local, ?_, nullary_not_embedding⟩
  exact nullaryMap.locallyInduced_nonempty (relational_total _ _) (by intro R; exact Nat.zero_le 2) nullary_local

end CCO.UnarySupport.Boundaries
