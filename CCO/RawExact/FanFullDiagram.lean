import CCO.RawExact.FanRootSpokeChoice
import CCO.RawExact.FanPuncturedDiagram
import Mathlib.Tactic

/-!
# B002 C12: one actual original-atom labelled private fan

The full finite fan is coloured by two compatible ingredients:
the genuinely realized punctured diagram off the one formal root,
and the unique old source-atom candidate on each root incident spoke.
Every edge uses the source's real dependent atom palette. Reverse
root spokes carry the original typed converse.

Crucially the chosen arbitrary real placeholder at the formal root
is NOT claimed to realize its incident edges. Those are merely valid
atomic constraints in an actual finite partial diagram. Their
simultaneous satisfaction is the future CCO/Helly conclusion.

The diagram structure is independent of a global Helly witness.
Pairwise ball compatibility is used separately to show that all
listed RAW occurrences have their proper root-spoke labels.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- A source typed converse is an injection, so selection of the
old atom on an unoriented direct spoke is orientation-independent. -/
theorem option_map_actual_converse_some_iff
    {i j : ι} (o : Option (S.Atom i j)) (a : S.Atom i j) :
    o = some a ↔ o.map S.conv = some (S.conv a) := by
  cases o with
  | none =>
      simp
  | some b =>
      change b = a ↔ S.conv b = S.conv a
      constructor
      · rintro rfl
        rfl
      · intro h
        have hReverse := congrArg (fun x => S.conv x) h
        simpa only [S.conv_invol] using hReverse

/-- A fixed old atom choice on each root spoke and the original
colours on all other edges give one source-typed partial edge map.
The `p ≠ q` proof prevents an artificial diagonal edge. -/
noncomputable def privateFanFullEdge
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (p q : PrivateFanVertex S D centres) (hpq : p ≠ q) :
    Option (S.Atom (privateFanSort S D centres p)
      (privateFanSort S D centres q)) :=
  match p, q with
  | .inl none, .inl none => False.elim (hpq rfl)
  | .inl none, q => privateFanRootSelectedAtom S H D centres q
  | p, .inl none =>
      (privateFanRootSelectedAtom S H D centres p).map S.conv
  | p, q => (privateFanPuncturedDiagram S H D centres).edge p q hpq

/-- All ROOT spokes and all actual nonroot private-path/centre
edges are combined into a single genuine finite old-colour diagram.
No `sorry`, synthetic equality colour, SAP or full C13 is used. -/
noncomputable def privateFanFullDiagram
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    PartialDiagram S (PrivateFanVertex S D centres) where
  finite_type := privateFanVertex_finite S D centres
  vertexSort := privateFanSort S D centres
  edge := privateFanFullEdge S H D centres
  edge_reverse := by
    intro p q hpq a
    cases p with
    | inl pp =>
      cases pp with
      | none =>
        cases q with
        | inl qq =>
          cases qq with
          | none =>
            exact False.elim (hpq rfl)
          | some c =>
            exact option_map_actual_converse_some_iff S
              (privateFanRootSelectedAtom S H D centres (.inl (some c))) a
        | inr qq =>
          exact option_map_actual_converse_some_iff S
            (privateFanRootSelectedAtom S H D centres (.inr qq)) a
      | some c =>
        cases q with
        | inl qq =>
          cases qq with
          | none =>
            have h :=
              (option_map_actual_converse_some_iff S
                (privateFanRootSelectedAtom S H D centres (.inl (some c)))
                (S.conv a)).symm
            simpa only [S.conv_invol] using h
          | some d =>
            exact (privateFanPuncturedDiagram S H D centres).edge_reverse
              (.inl (some c)) (.inl (some d)) hpq a
        | inr qq =>
          exact (privateFanPuncturedDiagram S H D centres).edge_reverse
            (.inl (some c)) (.inr qq) hpq a
    | inr pp =>
      cases q with
      | inl qq =>
        cases qq with
        | none =>
          have h :=
            (option_map_actual_converse_some_iff S
              (privateFanRootSelectedAtom S H D centres (.inr pp))
              (S.conv a)).symm
          simpa only [S.conv_invol] using h
        | some c =>
          exact (privateFanPuncturedDiagram S H D centres).edge_reverse
            (.inr pp) (.inl (some c)) hpq a
      | inr qq =>
        exact (privateFanPuncturedDiagram S H D centres).edge_reverse
          (.inr pp) (.inr qq) hpq a

end CCO.RawExact
