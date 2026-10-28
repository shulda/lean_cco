import CCO.RawExact.FanFullDiagram
import CCO.RawExact.FanPuncturedSupport

/-!
# B002 C12: exact root/nonroot edge semantics of the FULL private fan

The complete source-typed fan diagram is assembled from its punctured
(old-colour-realized) graph plus the unique actual source atom on each
root-incident spoke. These reduction lemmas make its true Lean edge
predicate explicit and prevent an accidental extra constraint.

All root-edge label uniqueness is derived only from pairwise actual
exact-ball compatibility, never from a source Helly conclusion.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- On every REAL formal root spoke, the full diagram has precisely
the atom witnessed by the original source reference occurrence. -/
theorem privateFanFull_root_edge_iff_candidate
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (v : PrivateFanVertex S D centres)
    (hv : privateFanRoot S D centres ≠ v)
    (a : S.Atom root (privateFanSort S D centres v)) :
    (privateFanFullDiagram S H D centres).edge
      (privateFanRoot S D centres) v hv = some a ↔
        privateFanRootSpokeCandidate S H D centres v a := by
  cases v with
  | inl ov =>
      cases ov with
      | none =>
          exact False.elim (hv rfl)
      | some c =>
          change privateFanRootSelectedAtom S H D centres (.inl (some c)) =
              some a ↔
            privateFanRootSpokeCandidate S H D centres (.inl (some c)) a
          exact privateFanRootSelectedAtom_some_iff
            S H D centres hPair (.inl (some c)) a
  | inr op =>
      change privateFanRootSelectedAtom S H D centres (.inr op) =
          some a ↔
        privateFanRootSpokeCandidate S H D centres (.inr op) a
      exact privateFanRootSelectedAtom_some_iff
        S H D centres hPair (.inr op) a

/-- The reverse of every root spoke carries exactly the TRUE
typed atomic converse, not a fabricated diagonal atom. -/
theorem privateFanFull_reverse_root_edge_iff_candidate
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (v : PrivateFanVertex S D centres)
    (hv : v ≠ privateFanRoot S D centres)
    (a : S.Atom root (privateFanSort S D centres v)) :
    (privateFanFullDiagram S H D centres).edge v
      (privateFanRoot S D centres) hv = some (S.conv a) ↔
        privateFanRootSpokeCandidate S H D centres v a := by
  have hReverse := (privateFanFullDiagram S H D centres).edge_reverse
    (privateFanRoot S D centres) v hv.symm a
  exact hReverse.symm.trans
    (privateFanFull_root_edge_iff_candidate S H D centres hPair
      v hv.symm a)

/-- For any two vertices different from the root, the FULL
diagram has EXACTLY the punctured diagram's original source
colour. The global root placeholder is irrelevant. -/
theorem privateFanFull_nonroot_edge_eq
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres)
    (hv : v ≠ privateFanRoot S D centres)
    (hw : w ≠ privateFanRoot S D centres)
    (hvw : v ≠ w) :
    (privateFanFullDiagram S H D centres).edge v w hvw =
      (privateFanPuncturedDiagram S H D centres).edge v w hvw := by
  cases v with
  | inl vv =>
      cases vv with
      | none => exact False.elim (hv rfl)
      | some c =>
          cases w with
          | inl ww =>
              cases ww with
              | none => exact False.elim (hw rfl)
              | some d => rfl
          | inr ww => rfl
  | inr vv =>
      cases w with
      | inl ww =>
          cases ww with
          | none => exact False.elim (hw rfl)
          | some d => rfl
      | inr ww => rfl

end CCO.RawExact
