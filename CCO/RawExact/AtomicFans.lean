import CCO.RawExact.Balls
import CCO.PairHomogeneity

/-!
# RAW C12/C13: actual anchored fan and alignment after CCO

This is an actual finite typed fan: one formal target root, finitely many
distinct actual centres, all the literal complete centre pair colours,
and specified diversity edges from root to each centre. The last step
of the source's exact-ball Helly proof is unconditional GIVEN the
semantic-CCO cycle checks for the fan. The cycle checks themselves
remain an explicit and currently unproved C12 obligation; this module
does not assume a fictitious source-level CCO instance.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Actual finite complete centre diagrams can be aligned by ONE
original-source automorphism, not independently chosen transports.
Repeated sorts and diagonal pairs are included. -/
theorem align_actual_centres
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {I : Type (max u v)} [Finite I]
    (sort : I → ι)
    (from to : ∀ t : I, X (sort t))
    (hColour : ∀ p q : I,
      S.colour (from p) (from q) = S.colour (to p) (to q)) :
    ∃ g : G, ∀ t : I, g • from t = to t := by
  let f : I → Sigma X := fun p => ⟨sort p, from p⟩
  let h : I → Sigma X := fun p => ⟨sort p, to p⟩
  have hPairs : ∀ p q : I,
      taggedColour S (f p) (f q) = taggedColour S (h p) (h q) := by
    intro p q
    change
      (⟨sort p, sort q, S.colour (from p) (from q)⟩ :
        Σ a : ι, Σ b : ι, Option (S.Atom a b)) =
      (⟨sort p, sort q, S.colour (to p) (to q)⟩ :
        Σ a : ι, Σ b : ι, Option (S.Atom a b))
    rw [hColour p q]
  obtain ⟨g, hg⟩ := H.extends_finite_diagram f h hPairs
  refine ⟨g, ?_⟩
  intro p
  have hp : (⟨sort p, g • from p⟩ : Sigma X) = ⟨sort p, to p⟩ := by
    simpa [f, h] using hg p
  simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hp

/-- The anchored fan is a TRUE finite typed partial diagram. The
centre-centre edges retain the original full optional colour, so
genuinely coincident centres are not treated as diversity edges.
The distinct-centre hypothesis is imposed only on the theorem
that consumes this fan below. -/
def atomicFan {I : Type (max u v)} [Finite I]
    (root : ι)
    (centreSort : I → ι)
    (centres : ∀ t : I, X (centreSort t))
    (atoms : ∀ t : I, S.Atom root (centreSort t)) :
    PartialDiagram S (Option I) where
  finite_type := inferInstance
  vertexSort := fun t => match t with
    | none => root
    | some i => centreSort i
  edge := fun p q _ => match p, q with
    | none, none => none
    | none, some i => some (atoms i)
    | some i, none => some (S.conv (atoms i))
    | some i, some j => S.colour (centres i) (centres j)
  edge_reverse := by
    intro p q hneq c
    cases p with
    | none =>
        cases q with
        | none =>
            exact False.elim (hneq rfl)
        | some t =>
            change some (atoms t) = some c ↔
              some (S.conv (atoms t)) = some (S.conv c)
            constructor
            · intro h
              have ha : atoms t = c := Option.some.inj h
              rw [ha]
            · intro h
              have ha : S.conv (atoms t) = S.conv c := Option.some.inj h
              have hconv := congrArg (fun a => S.conv a) ha
              simpa only [S.conv_invol] using hconv
    | some t =>
        cases q with
        | none =>
            change some (S.conv (atoms t)) = some c ↔
              some (atoms t) = some (S.conv c)
            constructor
            · intro h
              have ha : S.conv (atoms t) = c := Option.some.inj h
              have hconv := congrArg (fun a => S.conv a) ha
              simpa only [S.conv_invol] using hconv
            · intro h
              have ha : atoms t = S.conv c := Option.some.inj h
              have hconv := congrArg (fun a => S.conv a) ha
              simpa only [S.conv_invol] using hconv
        | some z =>
            change S.colour (centres t) (centres z) = some c ↔
              S.colour (centres z) (centres t) = some (S.conv c)
            exact S.colour_swap (centres t) (centres z) c

/-- C13's FINAL step after C12 supplies its real cycle witnesses.
A semantic-CCO solution is moved by ONE original automorphism
so that every named centre is restored to its literal original
real value. In particular its fresh root satisfies ALL atom balls,
including arbitrary repeated original sort labels. -/
theorem atomic_fan_helly_of_cycle_checks
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {I : Type (max u v)} [Finite I]
    (root : ι)
    (centreSort : I → ι)
    (centres : ∀ t : I, X (centreSort t))
    (atoms : ∀ t : I, S.Atom root (centreSort t))
    (hDistinct : Function.Injective
      (fun t : I => (⟨centreSort t, centres t⟩ : Sigma X)))
    (hCycles : ∀ C : SimpleCycle (atomicFan S root centreSort centres atoms),
      CycleHom C) :
    ∃ x : X root, ∀ t : I, S.atomRel (atoms t) x (centres t) := by
  let D := atomicFan S root centreSort centres atoms
  obtain ⟨f⟩ := cco (Option I) D hCycles
  have hCentreColour : ∀ p q : I,
      S.colour (f.point (some p)) (f.point (some q)) =
        S.colour (centres p) (centres q) := by
    intro p q
    by_cases hpq : p = q
    · subst q
      calc
        S.colour (f.point (some p)) (f.point (some p)) = none :=
          (S.colour_none_iff _ _).mpr rfl
        _ = S.colour (centres p) (centres p) :=
          ((S.colour_none_iff _ _).mpr rfl).symm
    · have hDifferent : (⟨centreSort p, centres p⟩ : Sigma X) ≠
          ⟨centreSort q, centres q⟩ := by
        intro h
        exact hpq (hDistinct h)
      cases hAtom : S.colour (centres p) (centres q) with
      | none =>
          exact False.elim (hDifferent ((S.colour_none_iff _ _).mp hAtom))
      | some c =>
          have hSome : (some p : Option I) ≠ some q := by
            intro h
            exact hpq (Option.some.inj h)
          have hEdge : D.edge (some p) (some q) hSome = some c := by
            change S.colour (centres p) (centres q) = some c
            exact hAtom
          have hImage := f.preserves_edge (some p) (some q) hSome c hEdge
          exact hImage.trans hAtom.symm
  obtain ⟨g, hg⟩ :=
    align_actual_centres S H centreSort
      (fun t => f.point (some t)) centres hCentreColour
  refine ⟨g • f.point none, ?_⟩
  intro t
  have hNe : (none : Option I) ≠ some t := by simp
  have hEdge : D.edge none (some t) hNe = some (atoms t) := rfl
  have hRoot : S.colour (f.point none) (f.point (some t)) =
      some (atoms t) := f.preserves_edge none (some t) hNe (atoms t) hEdge
  have hInv := S.colourInvariant_of_homogeneous H g
    (f.point none) (f.point (some t))
  rw [hg t] at hInv
  exact hInv.trans hRoot

end CCO.RawExact
