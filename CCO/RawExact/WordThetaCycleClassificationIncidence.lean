import CCO.RawExact.WordThetaCycleClassificationSupport

/-!
# Root incidence and existence of private interiors on a RAW theta cycle

These are literal finite-cycle facts. A cycle in the one-centre fan has
at least three distinct vertices, so it must meet a private interior.
The actual incoming and outgoing root edges exhaust all cycle edges at
the root. Duplicate direct occurrences do not create a third neighbour.
-/

universe u v w
namespace CCO.RawExact
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I] {sort : I → ι}
variable (menus : ∀ t : I, NonemptyExact S root (sort t)) (centres : ∀ t : I, X (sort t))
variable {E : PartialDiagram S (PrivateFanVertex S menus centres)} (C : SimpleCycle E)

/-- The literal two cycle neighbours exhaust every edge at the displayed root. -/
theorem privateFan_cycle_root_neighbours
    (hOn : CycleVertex C (privateFanRoot S menus centres)) :
    ∃ a b : PrivateFanVertex S menus centres,
      a ≠ b ∧ CycleEdge C (privateFanRoot S menus centres) a ∧
      CycleEdge C (privateFanRoot S menus centres) b ∧
      ∀ v, CycleEdge C (privateFanRoot S menus centres) v → v = a ∨ v = b := by
  obtain ⟨p, hp⟩ := hOn
  obtain ⟨prev, hprev, hUnique, hPrevUnique⟩ :=
    cycle_root_incidences C (privateFanRoot S menus centres) p hp
  refine ⟨C.vertices prev, C.vertices (cyclicNext C.length_pos p), ?_, ?_, ?_, ?_⟩
  · intro h
    have hIndex := C.vertices.injective h
    exact cyclicNext_no_two_cycle C.length_pos C.length_ge_three p prev hIndex.symm hprev
  · exact ⟨prev, Or.inr ⟨rfl, (congrArg C.vertices hprev).trans hp⟩⟩
  · exact ⟨p, Or.inl ⟨hp, rfl⟩⟩
  · intro v hv
    obtain ⟨q, h | h⟩ := hv
    · have hq := hUnique q h.1
      subst q
      exact Or.inr h.2.symm
    · have hq := hPrevUnique q h.2
      subst q
      exact Or.inl h.1.symm

/-- With only one actual marked centre, a genuine simple cycle cannot
be supported by the two terminals alone. Some private occurrence is met. -/
theorem privateFan_one_centre_cycle_has_interior
    (hCentres : ∀ c d : DistinctCentres sort centres, c = d) :
    ∃ (o : WordOccurrence S menus) (p : PrivateInteriorPosition S menus o),
      CycleVertex C (privateFanInterior S menus centres o p) := by
  classical
  by_contra hNone
  have hLeft (k : Fin C.length) : ∃ c : Option (DistinctCentres sort centres),
      C.vertices k = .inl c := by
    cases hval : C.vertices k with
    | inl c => exact ⟨c, rfl⟩
    | inr p =>
        rcases p with ⟨o, p⟩
        exact False.elim (hNone ⟨o, p, k, hval⟩)
  have hn := C.length_ge_three
  let p0 : Fin C.length := ⟨0, by omega⟩
  let p1 : Fin C.length := ⟨1, by omega⟩
  let p2 : Fin C.length := ⟨2, by omega⟩
  have h01 : C.vertices p0 ≠ C.vertices p1 := by
    intro h
    have hh := congrArg Fin.val (C.vertices.injective h)
    change (0 : Nat) = 1 at hh
    omega
  have h02 : C.vertices p0 ≠ C.vertices p2 := by
    intro h
    have hh := congrArg Fin.val (C.vertices.injective h)
    change (0 : Nat) = 2 at hh
    omega
  have h12 : C.vertices p1 ≠ C.vertices p2 := by
    intro h
    have hh := congrArg Fin.val (C.vertices.injective h)
    change (1 : Nat) = 2 at hh
    omega
  obtain ⟨c0, hc0⟩ := hLeft p0
  obtain ⟨c1, hc1⟩ := hLeft p1
  obtain ⟨c2, hc2⟩ := hLeft p2
  cases c0 with
  | none =>
      cases c1 with
      | none => exact h01 (hc0.trans hc1.symm)
      | some c1 =>
          cases c2 with
          | none => exact h02 (hc0.trans hc2.symm)
          | some c2 =>
              have h := hCentres c1 c2
              subst c2
              exact h12 (hc1.trans hc2.symm)
  | some c0 =>
      cases c1 with
      | none =>
          cases c2 with
          | none => exact h12 (hc1.trans hc2.symm)
          | some c2 =>
              have h := hCentres c0 c2
              subst c2
              exact h02 (hc0.trans hc2.symm)
      | some c1 =>
          have h := hCentres c0 c1
          subst c1
          exact h01 (hc0.trans hc1.symm)

end CCO.RawExact
