import CCO.RawExact.QuotientExpansionCycleCases
import CCO.RawExact.QuotientExpansionCycleRealization
import CCO.GroupActions

/-!
# Actual typed cycle witnesses for compressed quotient expansions

The compressed marked enumeration is injective and every one of its
canonical edges was used by the original raw cycle. A word can occur
only on an actually specified quotient edge. Hence the projected object
is an actual typed SimpleCycle, to which the quotient cycle hypothesis
applies. Arbitrary real representatives then realize every used menu.
-/

universe v w z q r
namespace CCO.RawExact.QuotientExpansion

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {K : Type z} {Q : K → Type q} (T : AtomicSource.{z,q,r} K Q)
variable {n : Nat} (Dq : PartialDiagram T (Fin n))
variable (P : Menus S (fun _ : Fin n => ()))
variable (hNonempty : ∀ e, TRel.Nonempty (evaluate S (P e)))

/-- Equality elimination transports the WHOLE specified atomic label. -/
theorem specified_at_equal_endpoints
    (v w v' w' : Fin n) (hvw : v ≠ w) (hv'w' : v' ≠ w')
    (hv : v' = v) (hw : w' = w)
    (h : ∃ a : T.Atom (Dq.vertexSort v) (Dq.vertexSort w), Dq.edge v w hvw = some a) :
    ∃ a : T.Atom (Dq.vertexSort v') (Dq.vertexSort w'), Dq.edge v' w' hv'w' = some a := by
  cases hv
  cases hw
  exact h

variable (hSpecified : ∀ o : Occurrence S (fun _ : Fin n => ()) P,
  ∃ a : T.Atom (Dq.vertexSort (left o.1)) (Dq.vertexSort (right o.1)),
    Dq.edge (left o.1) (right o.1) (left_ne_right o.1) = some a)

include hSpecified

/-- A used initial label has an actual specified quotient atom. -/
theorem specified_of_initial_label
    (C : SimpleCycle (diagram S (fun _ : Fin n => ()) P hNonempty)) (e : Edge n)
    (he : CyclicSuppression.LabelOn (initialCycle S (fun _ => ()) P hNonempty C) e) :
    ∃ a : T.Atom (Dq.vertexSort (left e)) (Dq.vertexSort (right e)),
      Dq.edge (left e) (right e) (left_ne_right e) = some a := by
  obtain ⟨k, hk⟩ := he
  change (cycleOccurrence S (fun _ => ()) P hNonempty C k).1 = e at hk
  have h := hSpecified (cycleOccurrence S (fun _ => ()) P hNonempty C k)
  cases hk
  exact h

/-- The compressed marked object is a genuine specified typed cycle,
not a closed walk with repeated quotient vertices. -/
noncomputable def projected_typed_cycle
    (C : SimpleCycle (diagram S (fun _ : Fin n => ()) P hNonempty))
    (B : MarkedProjection S (fun _ => ()) P hNonempty C) : SimpleCycle Dq where
  length := B.length
  length_ge_three := B.length_ge_three
  length_pos := B.length_pos
  vertices := B.vertices
  next_ne := by
    intro k
    have hThree := B.length_ge_three
    exact B.vertices.injective.ne
      (cyclicNext_ne_self_of_two_le B.length_pos (by omega) k).symm
  specified := by
    intro k
    let e := B.edges k
    have he : CyclicSuppression.LabelOn (initialCycle S (fun _ => ()) P hNonempty C) e :=
      (B.labels_iff e).mpr ⟨k, rfl⟩
    obtain ⟨a, ha⟩ := specified_of_initial_label S T Dq P hNonempty hSpecified C e he
    have hThree := B.length_ge_three
    have hDifferent : B.vertices k ≠ B.vertices (cyclicNext B.length_pos k) :=
      B.vertices.injective.ne (cyclicNext_ne_self_of_two_le B.length_pos (by omega) k).symm
    rcases B.endpoints k with h | h
    · exact specified_at_equal_endpoints T Dq (left e) (right e) _ _
        (left_ne_right e) hDifferent h.1 h.2 ⟨a, ha⟩
    · have hReverse : Dq.edge (right e) (left e) (left_ne_right e).symm = some (T.conv a) :=
        (Dq.edge_reverse (left e) (right e) (left_ne_right e) a).mp ha
      exact specified_at_equal_endpoints T Dq (right e) (left e) _ _
        (left_ne_right e).symm hDifferent h.1 h.2 ⟨T.conv a, hReverse⟩

omit hSpecified

variable (π : ∀ k : K, A → Q k) (ontoπ : ∀ k, Function.Surjective (π k))

/-- One named real representative function keeps choice-proof terms
out of dependent cycle-index rewriting. -/
noncomputable def pointRepresentative (C : SimpleCycle Dq)
    (point : ∀ p : Fin C.length, Q (Dq.vertexSort (C.vertices p)))
    (k : Fin C.length) : A :=
  (ontoπ (Dq.vertexSort (C.vertices k)) (point k)).choose

theorem pointRepresentative_project (C : SimpleCycle Dq)
    (point : ∀ p : Fin C.length, Q (Dq.vertexSort (C.vertices p)))
    (k : Fin C.length) :
    π (Dq.vertexSort (C.vertices k)) (pointRepresentative T Dq π ontoπ C point k) = point k :=
  (ontoπ (Dq.vertexSort (C.vertices k)) (point k)).choose_spec

/-- Real representatives selected only for the displayed cycle points.
The chosen values all lie in the ONE original real sort. -/
noncomputable def cycleRealRepresentatives (C : SimpleCycle Dq)
    (point : ∀ p : Fin C.length, Q (Dq.vertexSort (C.vertices p))) (fallback : A)
    (m : Fin n) : A := by
  classical
  exact if h : ∃ p, C.vertices p = m then
    pointRepresentative T Dq π ontoπ C point h.choose
  else fallback

/-- At every actual cycle position, the chosen real point projects to
EXACTLY the point of its given typed cycle homomorphism. -/
theorem cycleRealRepresentatives_project (C : SimpleCycle Dq)
    (point : ∀ p : Fin C.length, Q (Dq.vertexSort (C.vertices p))) (fallback : A)
    (k : Fin C.length) :
    π (Dq.vertexSort (C.vertices k))
      (cycleRealRepresentatives T Dq π ontoπ C point fallback (C.vertices k)) = point k := by
  classical
  have hExists : ∃ p, C.vertices p = C.vertices k := ⟨k, rfl⟩
  unfold cycleRealRepresentatives
  rw [dite_eq_left hExists]
  have hIndex : hExists.choose = k := C.vertices.injective hExists.choose_spec
  rw [hIndex]
  exact pointRepresentative_project T Dq π ontoπ C point k

/-- Transport a preserved cyclic edge to explicitly named endpoints. -/
theorem preserve_at_equal_endpoints
    (C : SimpleCycle Dq)
    (point : ∀ m, Q (Dq.vertexSort m))
    (hPreserve : ∀ p a, Dq.edge (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
      (C.next_ne p) = some a → T.colour (point (C.vertices p))
        (point (C.vertices (cyclicNext C.length_pos p))) = some a)
    (p : Fin C.length) (v w : Fin n) (hvw : v ≠ w)
    (hv : C.vertices p = v) (hw : C.vertices (cyclicNext C.length_pos p) = w)
    (a : T.Atom (Dq.vertexSort v) (Dq.vertexSort w))
    (ha : Dq.edge v w hvw = some a) : T.colour (point v) (point w) = some a := by
  cases hv
  cases hw
  exact hPreserve p a ha

end CCO.RawExact.QuotientExpansion
