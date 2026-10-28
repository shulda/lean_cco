import CCO.RawExact.FanVariableRootSpoke
import CCO.RawExact.FanFullEdgeSemantics
import CCO.RawExact.FanTwoWalkReplacement

/-!
# B002 C12: simultaneous realization of ANY TWO old root-spoke atoms

Two given root-incident edges of the full private fan have actual
reference-word occurrences certifying their precise original atoms.
Pairwise intersections of the relevant exact balls let us replace
just THOSE TWO occurrences by real RAW walks with one shared old root.

No hypothesis requires all occurrences to share one root, so this is
not a disguised use of the desired heterogeneous exact-ball Helly.
Repeated original centres, duplicate direct spokes and equal word
occurrences are allowed. All other word walks remain independently
chosen and may start at different points.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The TWO root-spoke edges prescribed by the same full finite
original-coloured fan can be realized together at ONE actual root,
without making any assertion about other root spokes. -/
theorem privateFan_two_root_spokes_realizable
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (v w : PrivateFanVertex S D centres)
    (hv : privateFanRoot S D centres ≠ v)
    (hw : privateFanRoot S D centres ≠ w)
    (a : S.Atom root (privateFanSort S D centres v))
    (b : S.Atom root (privateFanSort S D centres w))
    (ha : (privateFanFullDiagram S H D centres).edge
      (privateFanRoot S D centres) v hv = some a)
    (hb : (privateFanFullDiagram S H D centres).edge
      (privateFanRoot S D centres) w hw = some b) :
    ∃ (x : X root) (choice : FanWalkChoices S D centres),
      S.colour
        (privateFanVariableTypedPoint S D centres choice x
          (privateFanRoot S D centres))
        (privateFanVariableTypedPoint S D centres choice x v) =
          some a ∧
      S.colour
        (privateFanVariableTypedPoint S D centres choice x
          (privateFanRoot S D centres))
        (privateFanVariableTypedPoint S D centres choice x w) =
          some b := by
  have hCandidateV :=
    (privateFanFull_root_edge_iff_candidate S H D centres hPair v hv a).mp ha
  have hCandidateW :=
    (privateFanFull_root_edge_iff_candidate S H D centres hPair w hw b).mp hb
  obtain ⟨ov, pv, hpv, hvPos, hvRef⟩ := hCandidateV
  obtain ⟨ow, pw, hpw, hwPos, hwRef⟩ := hCandidateW
  obtain ⟨x, choice, hxv, hxw⟩ :=
    choose_fan_walks_with_two_common_roots S H D centres hPair ov ow
  refine ⟨x, choice, ?_, ?_⟩
  · exact privateFanVariable_root_spoke_atom_of_occurrence
      S H D centres choice x v a ov pv hpv hvPos hxv hvRef
  · exact privateFanVariable_root_spoke_atom_of_occurrence
      S H D centres choice x w b ow pw hpw hwPos hxw hwRef

end CCO.RawExact
