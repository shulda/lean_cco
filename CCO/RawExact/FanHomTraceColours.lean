import CCO.RawExact.FanHomWordTrace
import CCO.RawExact.FanFullEdgeSemantics
import CCO.RawExact.FanPuncturedSupport
import CCO.RawExact.WalkColourAtAllIndices
import Lean.Elab.Tactic.Omega

/-!
# Original edge colours along a completed private word

A homomorphism of the full private fan preserves the actual atomic
colour of every diversity step of each RAW word occurrence. Root spokes
use their proved unique reference label; all other steps use the
punctured diagram's actual old reference map.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Every forward step of a completed private word has precisely
its original reference walk's full typed pair colour. -/
theorem privateFanHom_forward_colour
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D)
    (p q : PathPosition S (occurrenceWord S D o))
    (hpq : p.val + 1 = q.val) :
    taggedColour S
      (⟨privateFanSort S D centres (privateFanAtWordPosition S D centres o p),
        f.point (privateFanAtWordPosition S D centres o p)⟩ : Sigma X)
      (⟨privateFanSort S D centres (privateFanAtWordPosition S D centres o q),
        f.point (privateFanAtWordPosition S D centres o q)⟩ : Sigma X) =
      taggedColour S (referencePointAt S H D centres o p)
        (referencePointAt S H D centres o q) := by
  have hq0 : q.val ≠ 0 := by omega
  have hw : privateFanAtWordPosition S D centres o q ≠
      privateFanRoot S D centres := by
    intro h
    have hStart := (privateFanAt_is_root_iff_start S D centres o q).mp h
    have hVal := congrArg Fin.val hStart
    exact hq0 hVal
  have hPosition : p ≠ q := by
    intro h
    have hVal := congrArg Fin.val h
    omega
  have hvw : privateFanAtWordPosition S D centres o p ≠
      privateFanAtWordPosition S D centres o q :=
    (privateFanAtWordPosition_injective S D centres o).ne hPosition
  by_cases hp0 : p.val = 0
  · have hpStart : p = pathStart S (occurrenceWord S D o) := Fin.ext hp0
    subst p
    rw [privateFanAt_start S D centres o]
    obtain ⟨a, ha⟩ := genuineEdge_tagged_some_at_sorts S
      (referencePointAt S H D centres o (pathStart S (occurrenceWord S D o)))
      (referencePointAt S H D centres o q)
      root (privateFanSort S D centres (privateFanAtWordPosition S D centres o q))
      ((referencePointAt_sort S H D centres o _).trans
        (pathSortAt_start S (occurrenceWord S D o)))
      (privateFan_referencePoint_sort S H D centres o q).symm
      (referencePointAt_genuine_forward S H D centres o _ q hpq)
    have hFirst : q.val = 1 := by
      change 0 + 1 = q.val at hpq
      omega
    have hEdge := (privateFanFull_root_edge_iff_candidate S H D centres hPair
      (privateFanAtWordPosition S D centres o q) hw.symm a).mpr
        ⟨o, q, hFirst, rfl, ha⟩
    have hColour := f.preserves_edge
      (privateFanRoot S D centres) (privateFanAtWordPosition S D centres o q)
      hw.symm a hEdge
    calc
      _ = (⟨root,
          privateFanSort S D centres (privateFanAtWordPosition S D centres o q),
          some a⟩ : Σ i : ι, Σ j : ι, Option (S.Atom i j)) := by
        exact congrArg (fun c : Option (S.Atom root
            (privateFanSort S D centres (privateFanAtWordPosition S D centres o q))) =>
          (⟨root, privateFanSort S D centres (privateFanAtWordPosition S D centres o q), c⟩ :
            Σ i : ι, Σ j : ι, Option (S.Atom i j))) hColour
      _ = _ := ha.symm
  · have hv : privateFanAtWordPosition S D centres o p ≠
        privateFanRoot S D centres := by
      intro h
      have hStart := (privateFanAt_is_root_iff_start S D centres o p).mp h
      exact hp0 (congrArg Fin.val hStart)
    have hAdj := privateFan_path_edge S D centres o p q
      ((pathAdjacent_iff_step S (occurrenceWord S D o) p q).mpr (Or.inl hpq))
    obtain ⟨a, ha⟩ :=
      (privateFanPuncturedDiagram_support_iff S H D centres _ _ hvw).mpr
        ⟨hv, hw, hAdj⟩
    have hFull : (privateFanFullDiagram S H D centres).edge
        (privateFanAtWordPosition S D centres o p)
        (privateFanAtWordPosition S D centres o q) hvw = some a := by
      rw [privateFanFull_nonroot_edge_eq S H D centres _ _ hv hw hvw]
      exact ha
    have hColour := f.preserves_edge _ _ hvw a hFull
    have hOld := (privateFanPuncturedDiagram_realization S H D centres).preserves_edge
      _ _ hvw a ha
    have hTagged : taggedColour S
        (⟨privateFanSort S D centres (privateFanAtWordPosition S D centres o p),
          f.point (privateFanAtWordPosition S D centres o p)⟩ : Sigma X)
        (⟨privateFanSort S D centres (privateFanAtWordPosition S D centres o q),
          f.point (privateFanAtWordPosition S D centres o q)⟩ : Sigma X) =
        taggedColour S
          (⟨privateFanSort S D centres (privateFanAtWordPosition S D centres o p),
            privateFanNonrootTypedPoint S H D centres
              (privateFanAtWordPosition S D centres o p)⟩ : Sigma X)
          (⟨privateFanSort S D centres (privateFanAtWordPosition S D centres o q),
            privateFanNonrootTypedPoint S H D centres
              (privateFanAtWordPosition S D centres o q)⟩ : Sigma X) := by
      change S.colour
        (privateFanNonrootTypedPoint S H D centres (privateFanAtWordPosition S D centres o p))
        (privateFanNonrootTypedPoint S H D centres (privateFanAtWordPosition S D centres o q)) =
          some a at hOld
      exact congrArg (fun c : Option (S.Atom
          (privateFanSort S D centres (privateFanAtWordPosition S D centres o p))
          (privateFanSort S D centres (privateFanAtWordPosition S D centres o q))) =>
        (⟨privateFanSort S D centres (privateFanAtWordPosition S D centres o p),
          privateFanSort S D centres (privateFanAtWordPosition S D centres o q), c⟩ :
            Σ i : ι, Σ j : ι, Option (S.Atom i j))) (hColour.trans hOld.symm)
    rw [privateFanNonrootTypedPoint_tag S H D centres _,
      privateFanNonrootTypedPoint_tag S H D centres _,
      privateFanNonrootReference_at_nonroot S H D centres o p hp0,
      privateFanNonrootReference_at_nonroot S H D centres o q hq0] at hTagged
    exact hTagged

/-- The completed finite trace retains the whole reference
RAW word's atomic edge certificate, without requiring injectivity. -/
theorem privateFanHomWordTrace_colours
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (hPair : ∀ p q : I,
      (ball (evaluate S (D p).words) (centres p) ∩
        ball (evaluate S (D q).words) (centres q)).Nonempty)
    (f : DiagramHom (privateFanFullDiagram S H D centres))
    (o : WordOccurrence S D) :
    SameEdgeColours S
      (realWalkTrace S (referenceOccurrenceWalk S H D centres o).2)
      (privateFanHomWordTrace S H D centres f o) := by
  have hlen :
      (realWalkTrace S (referenceOccurrenceWalk S H D centres o).2).length =
        (privateFanHomWordTrace S H D centres f o).length :=
    (realWalkTrace_length S _).trans (privateFanHomWordTrace_length S H D centres f o).symm
  apply sameEdgeColours_of_indexed S _ _ hlen
  intro k hk hk'
  have hkPath : k + 1 < diversityLength S (occurrenceWord S D o) + 1 := by
      rwa [realWalkTrace_length S] at hk
  let p : PathPosition S (occurrenceWord S D o) := ⟨k, by omega⟩
  let q : PathPosition S (occurrenceWord S D o) := ⟨k + 1, hkPath⟩
  have h := privateFanHom_forward_colour S H D centres hPair f o p q rfl
  simpa only [referencePointAt, List.get_eq_getElem, p, q,
      privateFanHomWordTrace, List.getElem_ofFn] using h.symm

end CCO.RawExact
