import CCO.StrongExact.ThetaArcUnique
import CCO.StrongExact.ThetaReduction

/-!
# C07: construct a genuinely single-valued typed theta edge function

In the hard theta case every positive word has at least two letters.
The proved ordered-endpoint uniqueness of the finite candidate arcs
then makes the literal old atomic edge label unambiguous.

Choose the UNIQUE candidate when one exists and otherwise leave the
edge unspecified. Reverse closure of the candidate list, together
with uniqueness, supplies the exact original atomic converse law.
This produces a real B001 `ThetaEdges`, not a multigraph or a
silent extra fixed-point/completion hypothesis. Cycle witnesses
and word readout are separate obligations.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- A literal candidate arc with fixed ordered endpoints. -/
structure ThetaArcAt (ws : List (PositiveWord S i j))
    (x y : thetaVertices S ws) where
  arc : ThetaArc S ws
  mem : arc ∈ thetaArcs S ws
  src_eq : arc.src = x
  dst_eq : arc.dst = y

/-- The old atom of an arc transported onto its fixed formal
endpoint types. This changes ONLY definitional sort tags. -/
def ThetaArcAt.atom {ws : List (PositiveWord S i j)}
    {x y : thetaVertices S ws} (a : ThetaArcAt S ws x y) :
    S.Atom (thetaVertexSort S ws x) (thetaVertexSort S ws y) := by
  cases a with
  | mk arc hm hx hy =>
      cases hx
      cases hy
      exact arc.atom

/-- Every candidate has its genuinely conversed companion, with
the ordered formal endpoints exchanged. -/
def ThetaArcAt.reverse {ws : List (PositiveWord S i j)}
    {x y : thetaVertices S ws} (a : ThetaArcAt S ws x y) :
    ThetaArcAt S ws y x :=
  ⟨a.arc.reverse,
    thetaArcs_reverse_closed S ws a.arc a.mem,
    by simpa only [ThetaArc.reverse] using a.dst_eq,
    by simpa only [ThetaArc.reverse] using a.src_eq⟩

theorem ThetaArcAt.atom_reverse
    {ws : List (PositiveWord S i j)}
    {x y : thetaVertices S ws} (a : ThetaArcAt S ws x y) :
    a.reverse.atom = S.conv a.atom := by
  cases a with
  | mk arc hm hx hy =>
      cases hx
      cases hy
      rfl

/-- Existence plus no parallel arcs gives a Subsingleton of candidate
edge records, even though the colour palette itself may be large. -/
theorem thetaArcAt_subsingleton
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (x y : thetaVertices S ws) :
    Subsingleton (ThetaArcAt S ws x y) := by
  constructor
  intro a b
  rcases a with ⟨arcA, ha, hax, hay⟩
  rcases b with ⟨arcB, hb, hbx, hby⟩
  have heq := thetaArcs_unique_of_endpoints S ws hLong
    arcA arcB ha hb (hax.trans hbx.symm) (hay.trans hby.symm)
  cases heq
  rfl

/-- The optional unique old candidate for each ordered formal
vertex pair; no atomic value is fabricated for absent edges. -/
noncomputable def thetaArcAtChoice
    (ws : List (PositiveWord S i j))
    (x y : thetaVertices S ws) :
    Option (ThetaArcAt S ws x y) := by
  classical
  exact if h : Nonempty (ThetaArcAt S ws x y)
    then some (Classical.choice h)
    else none

theorem thetaArcAtChoice_eq_some
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    {x y : thetaVertices S ws} (a : ThetaArcAt S ws x y) :
    thetaArcAtChoice S ws x y = some a := by
  haveI : Subsingleton (ThetaArcAt S ws x y) :=
    thetaArcAt_subsingleton S ws hLong x y
  unfold thetaArcAtChoice
  have h : Nonempty (ThetaArcAt S ws x y) := ⟨a⟩
  rw [dif_pos h]
  exact congrArg Option.some (Subsingleton.elim _ _)

/-- Literal optional original colour, selected only from genuine
forward/reverse word arcs. It has the B001 distinct-endpoints API. -/
noncomputable def thetaEdge
    (ws : List (PositiveWord S i j))
    (x y : thetaVertices S ws) (_hxy : x ≠ y) :
    Option (S.Atom (thetaVertexSort S ws x)
      (thetaVertexSort S ws y)) :=
  (thetaArcAtChoice S ws x y).map (ThetaArcAt.atom S)

/-- A chosen genuine atomic edge automatically entails its literally
reversed old atom at the opposite ordered pair. -/
private theorem thetaEdge_flip
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (x y : thetaVertices S ws) (hxy : x ≠ y)
    (a : S.Atom (thetaVertexSort S ws x)
      (thetaVertexSort S ws y))
    (ha : thetaEdge S ws x y hxy = some a) :
    thetaEdge S ws y x hxy.symm = some (S.conv a) := by
  unfold thetaEdge at ha ⊢
  cases hChoice : thetaArcAtChoice S ws x y with
  | none =>
      simp [hChoice] at ha
  | some candidate =>
      have hAtom : candidate.atom = a := by
        simpa only [hChoice, Option.map_some, Option.some.injEq] using ha
      have hRev : thetaArcAtChoice S ws y x =
          some (candidate.reverse) :=
        thetaArcAtChoice_eq_some S ws hLong candidate.reverse
      simp only [hRev, Option.map_some, Option.some.injEq]
      rw [ThetaArcAt.atom_reverse S candidate]
      exact congrArg (fun v => S.conv v) hAtom

theorem thetaEdge_reverse
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (x y : thetaVertices S ws) (hxy : x ≠ y)
    (a : S.Atom (thetaVertexSort S ws x)
      (thetaVertexSort S ws y)) :
    thetaEdge S ws x y hxy = some a ↔
    thetaEdge S ws y x hxy.symm = some (S.conv a) := by
  constructor
  · exact thetaEdge_flip S ws hLong x y hxy a
  · intro h
    have hh := thetaEdge_flip S ws hLong y x hxy.symm
      (S.conv a) h
    simpa only [S.conv_invol] using hh

/-- The genuinely typed, simple B001 partial theta edge API:
candidate uniqueness and actual original converse are PROVED from
the source word-line geometry, not postulated as a provider. -/
noncomputable def thetaEdgesOfLong
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws) :
    ThetaEdges S ws where
  edge := thetaEdge S ws
  edge_reverse := by
    intro x y hxy a
    exact thetaEdge_reverse S ws hLong x y hxy a

/-- Every original letter from every private word is a **literal**
specified edge of the newly constructed single-valued diagram. -/
theorem thetaEdgesOfLong_preserves_forward
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (b : Fin ws.length) (e : wordEdgeIndex S (ws.get b)) :
    (thetaEdgesOfLong S ws hLong).edge
        (thetaBranchEdgeSource S ws b e)
        (thetaBranchEdgeTarget S ws b e)
        (thetaBranchEdge_distinct S ws b e) =
      some (thetaBranchEdgeAtom S ws b e) := by
  let a : ThetaArcAt S ws
      (thetaBranchEdgeSource S ws b e)
      (thetaBranchEdgeTarget S ws b e) :=
    ⟨thetaForwardArc S ws b e,
      thetaForwardArc_mem_theta S ws b e, rfl, rfl⟩
  have hChoose := thetaArcAtChoice_eq_some S ws hLong a
  simp only [thetaEdgesOfLong, thetaEdge, hChoose, Option.map_some]
  rfl

end CCO.StrongExact
