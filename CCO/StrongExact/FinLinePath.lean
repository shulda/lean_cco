import CCO.StrongExact.CycleCutPath
import CCO.StrongExact.ProfileSemantics
import Mathlib.Data.List.FinRange

/-!
# Genuine finite simple paths and their literal original-sort realization

An injectively enumerated specified line gives an actual `SpecifiedPath`
whose vertex list is EXACTLY that line and is nodup. A selected positive
word-profile atom yields real points preserving EVERY original adjacent
label and that same endpoint diversity atom. No stable-network premise,
all-walk substitution, or conditional completion provider is used.
-/

universe u v w z
namespace CCO.StrongPC
variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X} {V : Type z}
variable (D : PartialDiagram S V)

/-- All formal vertices of an endpoint-separated specified walk,
including both endpoints, in their actual traversal order. -/
def SpecifiedPath.vertexList {x y : V} : SpecifiedPath D x y → List V
  | .edge (x := x) (y := y) _ _ _ => [x,y]
  | .cons (x := x) _ _ _ _ tail => x :: tail.vertexList

/-- A genuine simple specified path, rather than an arbitrary
endpoint-separated walk: no formal vertex repeats anywhere. -/
def SimpleSpecifiedPath (x y : V) :=
  {p : SpecifiedPath D x y // p.vertexList.Nodup}

/-- Build the actual positive path from every literal old edge of an
injectively enumerated finite line. -/
noncomputable def specifiedLinePath :
    (n : Nat) → (vertices : Fin (n + 2) ↪ V) →
    (atoms : ∀ p : Fin (n + 1),
      S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ))) →
    (∀ p : Fin (n + 1), D.edge (vertices p.castSucc) (vertices p.succ)
      (lineStepPair vertices p).ne = some (atoms p)) →
    SpecifiedPath D (vertices 0) (vertices (Fin.last (n + 1)))
  | 0, vertices, atoms, hEdges =>
      .edge (lineEndpointPair vertices).ne (atoms 0) (hEdges 0)
  | n + 1, vertices, atoms, hEdges =>
      .cons (lineStepPair vertices 0).ne (lineEndpointPair vertices).ne
        (atoms 0) (hEdges 0)
        (specifiedLinePath n
          ⟨fun p => vertices p.succ,
            fun _ _ h => (Fin.succ_injective _) (vertices.injective h)⟩
          (fun p => atoms p.succ) (fun p => hEdges p.succ))

/-- The constructed path retains every original formal vertex exactly
once in its traversal order; no endpoint-separated walk is substituted. -/
theorem specifiedLinePath_vertexList :
    ∀ (n : Nat) (vertices : Fin (n + 2) ↪ V)
      (atoms : ∀ p : Fin (n + 1),
        S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ)))
      (hEdges : ∀ p : Fin (n + 1), D.edge (vertices p.castSucc) (vertices p.succ)
        (lineStepPair vertices p).ne = some (atoms p)),
      (specifiedLinePath D n vertices atoms hEdges).vertexList = List.ofFn vertices := by
  intro n
  induction n with
  | zero =>
      intro vertices atoms hEdges
      simp [specifiedLinePath,SpecifiedPath.vertexList,List.ofFn_succ]
  | succ n ih =>
      intro vertices atoms hEdges
      change vertices 0 ::
        (specifiedLinePath D n
          ⟨fun p => vertices p.succ,
            fun _ _ h => (Fin.succ_injective _) (vertices.injective h)⟩
          (fun p => atoms p.succ) (fun p => hEdges p.succ)).vertexList = _
      rw [ih]
      exact (List.ofFn_succ (f := fun p => vertices p)).symm

theorem specifiedLinePath_nodup (n : Nat) (vertices : Fin (n + 2) ↪ V)
    (atoms : ∀ p : Fin (n + 1),
      S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ)))
    (hEdges : ∀ p : Fin (n + 1), D.edge (vertices p.castSucc) (vertices p.succ)
      (lineStepPair vertices p).ne = some (atoms p)) :
    (specifiedLinePath D n vertices atoms hEdges).vertexList.Nodup := by
  rw [specifiedLinePath_vertexList D n vertices atoms hEdges]
  exact List.nodup_ofFn_ofInjective vertices.injective

noncomputable def simpleSpecifiedLine (n : Nat) (vertices : Fin (n + 2) ↪ V)
    (atoms : ∀ p : Fin (n + 1),
      S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ)))
    (hEdges : ∀ p : Fin (n + 1), D.edge (vertices p.castSucc) (vertices p.succ)
      (lineStepPair vertices p).ne = some (atoms p)) :
    SimpleSpecifiedPath D (vertices 0) (vertices (Fin.last (n + 1))) :=
  ⟨specifiedLinePath D n vertices atoms hEdges,
    specifiedLinePath_nodup D n vertices atoms hEdges⟩

/-- Read an actual represented word witness onto the EXACT original
finite line, retaining the two literal real endpoint values. -/
theorem specifiedLinePath_represented_readout :
    ∀ (n : Nat) (vertices : Fin (n + 2) ↪ V)
      (atoms : ∀ p : Fin (n + 1),
        S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ)))
      (hEdges : ∀ p : Fin (n + 1), D.edge (vertices p.castSucc) (vertices p.succ)
        (lineStepPair vertices p).ne = some (atoms p))
      (x : X (D.vertexSort (vertices 0)))
      (y : X (D.vertexSort (vertices (Fin.last (n + 1))))),
      PositiveWord.represented S (specifiedLinePath D n vertices atoms hEdges).word x y →
      ∃ point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)),
        point 0 = x ∧ point (Fin.last (n + 1)) = y ∧
        ∀ p : Fin (n + 1), S.colour (point p.castSucc) (point p.succ) = some (atoms p) := by
  intro n
  induction n with
  | zero =>
      intro vertices atoms hEdges x y hWord
      let point : ∀ p : Fin 2, X (D.vertexSort (vertices p)) :=
        Fin.cases x (Fin.cases y (fun p => Fin.elim0 p))
      refine ⟨point,rfl,rfl,?_⟩
      intro p
      have hp : p = 0 := Fin.eq_zero p
      subst p
      exact hWord
  | succ n ih =>
      intro vertices atoms hEdges x y hWord
      let tailVertices : Fin (n + 2) ↪ V :=
        ⟨fun p => vertices p.succ,
          fun _ _ h => (Fin.succ_injective _) (vertices.injective h)⟩
      let tailAtoms := fun p : Fin (n + 1) => atoms p.succ
      have tailEdges : ∀ p : Fin (n + 1),
          D.edge (tailVertices p.castSucc) (tailVertices p.succ)
            (lineStepPair tailVertices p).ne = some (tailAtoms p) :=
        fun p => hEdges p.succ
      change ∃ mid : X (D.vertexSort (vertices (1 : Fin (n + 3)))),
        S.colour x mid = some (atoms 0) ∧
        PositiveWord.represented S
          (specifiedLinePath D n tailVertices tailAtoms tailEdges).word mid y at hWord
      obtain ⟨mid,hFirst,hTail⟩ := hWord
      obtain ⟨tailPoint,hSource,hTarget,hTailEdges⟩ :=
        ih tailVertices tailAtoms tailEdges mid y hTail
      let point : ∀ p : Fin (n + 3), X (D.vertexSort (vertices p)) :=
        Fin.cases x tailPoint
      refine ⟨point,rfl,hTarget,?_⟩
      intro p
      refine Fin.cases ?_ (fun q => ?_) p
      · change S.colour x (tailPoint 0) = some (atoms 0)
        rw [hSource]
        exact hFirst
      · exact hTailEdges q

/-- Any atom in the genuine simple line's strong word profile has a
literal real line realization preserving EVERY old specified atom and
that same actual endpoint diversity atom. No stable network is assumed. -/
theorem specifiedLine_realizable_of_profile
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (n : Nat) (vertices : Fin (n + 2) ↪ V)
    (atoms : ∀ p : Fin (n + 1),
      S.Atom (D.vertexSort (vertices p.castSucc)) (D.vertexSort (vertices p.succ)))
    (hEdges : ∀ p : Fin (n + 1), D.edge (vertices p.castSucc) (vertices p.succ)
      (lineStepPair vertices p).ne = some (atoms p))
    (a : S.Atom (D.vertexSort (vertices 0))
      (D.vertexSort (vertices (Fin.last (n + 1)))))
    (ha : a ∈ PositiveWord.profile S (specifiedLinePath D n vertices atoms hEdges).word) :
    ∃ point : ∀ p : Fin (n + 2), X (D.vertexSort (vertices p)),
      (∀ p : Fin (n + 1), S.colour (point p.castSucc) (point p.succ) = some (atoms p)) ∧
      S.colour (point 0) (point (Fin.last (n + 1))) = some a := by
  obtain ⟨x,y,hWord,hxy⟩ :=
    (StrongExact.positive_profile_iff_represented S H sap
      (specifiedLinePath D n vertices atoms hEdges).word a).mp ha
  obtain ⟨point,hSource,hTarget,hLetters⟩ :=
    specifiedLinePath_represented_readout D n vertices atoms hEdges x y hWord
  exact ⟨point,hLetters,by rw [hSource,hTarget]; exact hxy⟩

end CCO.StrongPC
