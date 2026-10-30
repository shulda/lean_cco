import CCO.SimultaneousQuotients.CCOBranch.TypedCycles

/-!
# Every actual raw expansion cycle has a source homomorphism

The two-mark case uses one actual quotient edge witness. The multi-mark
case uses the genuine specified typed simple cycle obtained by compression.
Real representatives then satisfy EVERY used exact menu, so the previously
proved private-walk realization gives the entire raw cycle homomorphism.
-/

universe u v w q r
namespace CCO.SimultaneousQuotients.CCOBranch

open CCO.RawExact CCO.RawExact.QuotientExpansion

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {Q : ι → Type q} (T : AtomicSource.{u,q,r} ι Q)
variable {n : Nat} (Dq : PartialDiagram T (Fin n))
variable (P : Menus S Dq.vertexSort)
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))

/-- Merged direct occurrences give exactly the same literal used-edge
set as the canonical initial labelling chosen for compression. -/
theorem cycleUsesEdge_iff_initial_label
    (C : SimpleCycle (diagram S Dq.vertexSort P hNonempty)) (e : Edge n) :
    CycleUsesEdge S Dq.vertexSort P hNonempty C e ↔
      CyclicSuppression.LabelOn (initialCycle S Dq.vertexSort P hNonempty C) e := by
  constructor
  · rintro ⟨k, o, p, q, hpq, hv, hw, ho⟩
    exact ⟨k, (initial_label_of_path_witness S Dq.vertexSort P hNonempty C k o p q hpq hv hw).trans ho⟩
  · rintro ⟨k, hk⟩
    obtain ⟨p, q, hpq, hv, hw⟩ := cycleOccurrence_spec S Dq.vertexSort P hNonempty C k
    exact ⟨k, cycleOccurrence S Dq.vertexSort P hNonempty C k, p, q, hpq, hv, hw, hk⟩

variable (π : ∀ i : ι, X i → Q i) (ontoπ : ∀ k, Function.Surjective (π k))
variable (hSpecified : ∀ o : Occurrence S Dq.vertexSort P,
  ∃ a : T.Atom (Dq.vertexSort (left o.1)) (Dq.vertexSort (right o.1)),
    Dq.edge (left o.1) (right o.1) (left_ne_right o.1) = some a)
variable (hRepresents : ∀ (e : Edge n)
  (a : T.Atom (Dq.vertexSort (left e)) (Dq.vertexSort (right e))),
  Dq.edge (left e) (right e) (left_ne_right e) = some a →
    evaluate S (P e) = GroupActions.pullback (π (Dq.vertexSort (left e)))
      (π (Dq.vertexSort (right e))) (T.atomRel a))

include hSpecified hRepresents ontoπ

/-- One actual edge orbital realizes all used menus in the two-mark case. -/
theorem menus_realised_of_single_label
    (C : SimpleCycle (diagram S Dq.vertexSort P hNonempty)) (e : Edge n)
    (he : CyclicSuppression.LabelOn (initialCycle S Dq.vertexSort P hNonempty C) e)
    (hAll : ∀ f, CyclicSuppression.LabelOn (initialCycle S Dq.vertexSort P hNonempty C) f → f = e) :
    ∃ b : ∀ m : Fin n, X (Dq.vertexSort m), ∀ f, CycleUsesEdge S Dq.vertexSort P hNonempty C f →
      evaluate S (P f) (b (left f)) (b (right f)) := by
  classical
  obtain ⟨a, ha⟩ := specified_of_initial_label S T Dq P hNonempty hSpecified C e he
  obtain ⟨x, y, hColour⟩ := T.realized a
  obtain ⟨u, hu⟩ := ontoπ (Dq.vertexSort (left e)) x
  obtain ⟨v, hv⟩ := ontoπ (Dq.vertexSort (right e)) y
  let fallback : ∀ m : Fin n, X (Dq.vertexSort m) :=
    fun m => Classical.choice (S.nonemptySort (Dq.vertexSort m))
  let b : ∀ m : Fin n, X (Dq.vertexSort m) :=
    Function.update (Function.update fallback (left e) u) (right e) v
  have hLeft : b (left e) = u := by simp [b, left_ne_right e]
  have hRight : b (right e) = v := by simp [b]
  have hMenu : evaluate S (P e) u v := by
    rw [hRepresents e a ha]
    change T.colour (π (Dq.vertexSort (left e)) u) (π (Dq.vertexSort (right e)) v) = some a
    rw [hu, hv]
    exact hColour
  refine ⟨b, ?_⟩
  intro f hf
  have hLabel := (cycleUsesEdge_iff_initial_label S T Dq P hNonempty C f).mp hf
  have hfe : f = e := hAll f hLabel
  subst f
  simpa only [hLeft, hRight] using hMenu

/-- A genuine typed simple-cycle homomorphism simultaneously realizes
all used edge menus after choosing arbitrary real representatives. -/
theorem menus_realised_of_marked_projection
    (hCycles : ∀ C : SimpleCycle Dq, CycleHom C)
    (C : SimpleCycle (diagram S Dq.vertexSort P hNonempty))
    (B : MarkedProjection S Dq.vertexSort P hNonempty C) :
    ∃ b : ∀ m : Fin n, X (Dq.vertexSort m), ∀ e, CycleUsesEdge S Dq.vertexSort P hNonempty C e →
      evaluate S (P e) (b (left e)) (b (right e)) := by
  classical
  let Cq := projected_typed_cycle S T Dq P hNonempty hSpecified C B
  obtain ⟨point, hPreserve⟩ := hCycles Cq
  let fallback : ∀ m : Fin n, X (Dq.vertexSort m) :=
    fun m => Classical.choice (S.nonemptySort (Dq.vertexSort m))
  let b := cycleRealRepresentatives T Dq π ontoπ Cq point fallback
  have hProject : ∀ k : Fin Cq.length,
      π (Dq.vertexSort (Cq.vertices k)) (b (Cq.vertices k)) = point k :=
    cycleRealRepresentatives_project T Dq π ontoπ Cq point fallback
  let qpoint : ∀ m, Q (Dq.vertexSort m) := fun m => π (Dq.vertexSort m) (b m)
  have hPointPreserve : ∀ p a,
      Dq.edge (Cq.vertices p) (Cq.vertices (cyclicNext Cq.length_pos p)) (Cq.next_ne p) = some a →
      T.colour (qpoint (Cq.vertices p)) (qpoint (Cq.vertices (cyclicNext Cq.length_pos p))) = some a := by
    intro p a ha
    change T.colour (π (Dq.vertexSort (Cq.vertices p)) (b (Cq.vertices p)))
      (π (Dq.vertexSort (Cq.vertices (cyclicNext Cq.length_pos p)))
        (b (Cq.vertices (cyclicNext Cq.length_pos p)))) = some a
    rw [hProject p, hProject (cyclicNext Cq.length_pos p)]
    exact hPreserve p a ha
  refine ⟨b, ?_⟩
  intro e he
  have hLabel := (cycleUsesEdge_iff_initial_label S T Dq P hNonempty C e).mp he
  obtain ⟨k, hk⟩ := (B.labels_iff e).mp hLabel
  obtain ⟨a, ha⟩ := specified_of_initial_label S T Dq P hNonempty hSpecified C e hLabel
  rw [hRepresents e a ha]
  change T.colour (qpoint (left e)) (qpoint (right e)) = some a
  have hEndpoints := B.endpoints k
  rw [hk] at hEndpoints
  rcases hEndpoints with h | h
  · exact preserve_at_equal_endpoints T Dq Cq qpoint hPointPreserve k
      (left e) (right e) (left_ne_right e) h.1 h.2 a ha
  · have hReverse : Dq.edge (right e) (left e) (left_ne_right e).symm = some (T.conv a) :=
      (Dq.edge_reverse (left e) (right e) (left_ne_right e) a).mp ha
    have hColour := preserve_at_equal_endpoints T Dq Cq qpoint hPointPreserve k
      (right e) (left e) (left_ne_right e).symm h.1 h.2 (T.conv a) hReverse
    exact (T.colour_swap (qpoint (left e)) (qpoint (right e)) a).mpr hColour

/-- B041 C33-C36: the genuine all-cycle bridge for the constructed actual private
word expansion. Marker compression and both witness cases are proved;
there is no assumed raw cycle or expansion-classification provider. -/
theorem all_raw_cycles_of_typed_cycles
    (hPositive : ∀ o, 0 < diversityLength S (word S Dq.vertexSort P o))
    (hCycles : ∀ C : SimpleCycle Dq, CycleHom C) :
    ∀ C : SimpleCycle (diagram S Dq.vertexSort P hNonempty), CycleHom C := by
  intro C
  rcases cycle_marked_cases S Dq.vertexSort P hNonempty C with hOne | hMany
  · obtain ⟨e, he, _, hAll⟩ := hOne
    obtain ⟨b, hb⟩ := menus_realised_of_single_label S T Dq P hNonempty π ontoπ
      hSpecified hRepresents C e he hAll
    exact cycleHom_of_marked_edge_realization S Dq.vertexSort P hNonempty C b hb hPositive
  · obtain ⟨B⟩ := hMany
    obtain ⟨b, hb⟩ := menus_realised_of_marked_projection S T Dq P hNonempty π ontoπ
      hSpecified hRepresents hCycles C B
    exact cycleHom_of_marked_edge_realization S Dq.vertexSort P hNonempty C b hb hPositive

end CCO.SimultaneousQuotients.CCOBranch
