import CCO.StrongExact.AgeAP
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Independent triangle fullness from ordinary AP and semantic homomorphic CCO

For a COMPLETE finite typed diversity diagram, actual realizability of every
restriction on at most three vertices implies an injective realization in the
original source. The proof uses the complete input's actual chord colours:
ordinary AP realizes each rooted triangle fan homomorphically, including its
closing edge; CCO realizes the whole diagram; completeness makes that map
injective. No SAP, strong product, NR2 or assumed triangle-completion provider
occurs. The original homogeneous-source wrapper discharges AP separately.

This proves `sections/triangle_fullness.tex`, lemma `lem:cco-triangle-fullness`,
in the accepted actual-age `AtomicSource` model; it does not assert completion
of partial triangle-consistent diagrams or a new arbitrary-class framework.
-/

universe u v w z
namespace CCO
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}

namespace PartialDiagram
variable {V : Type z}
def restrict (D : PartialDiagram S V) (F : Finset V) : PartialDiagram S ↥F where
  finite_type := inferInstance
  vertexSort x := D.vertexSort x.val
  edge x y h := D.edge x.val y.val (fun he => h (Subtype.ext he))
  edge_reverse x y _h a := D.edge_reverse x.val y.val _ a
end PartialDiagram

def CompleteDiagram.SmallRealizable {V : Type z} (A : CompleteDiagram (S := S) V) : Prop :=
  ∀ (F : Finset V), F.card ≤ 3 → Nonempty (DiagramHom (A.diagram.restrict F))

/-- A full homomorphism of a complete diversity diagram is injective, without SAP. -/
theorem DiagramHom.injective_of_complete {V : Type z} {D : PartialDiagram S V}
    (hComplete : D.IsComplete) (f : DiagramHom D) : f.IsInjective := by
  intro x y hxy
  by_contra hn
  obtain ⟨a, ha⟩ := hComplete x y hn
  exact S.atomRel_ne (f.preserves_edge x y hn a ha) hxy

namespace CompleteDiagram
variable {V : Type z} (A : CompleteDiagram (S := S) V)

/-- The actual triangles of the complete input, never triangles in a partial reduct. -/
def TrianglesRealizable : Prop :=
  ∀ (x y z : V) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
      (a : S.Atom (A.diagram.vertexSort x) (A.diagram.vertexSort y))
      (b : S.Atom (A.diagram.vertexSort y) (A.diagram.vertexSort z))
      (c : S.Atom (A.diagram.vertexSort x) (A.diagram.vertexSort z)),
    A.diagram.edge x y hxy = some a → A.diagram.edge y z hyz = some b →
    A.diagram.edge x z hxz = some c → S.Triangle a b c

theorem trianglesRealizable_of_small (hsmall : A.SmallRealizable) : A.TrianglesRealizable := by
  classical
  intro x y z hxy hyz hxz a b c ha hb hc
  let F : Finset V := {x, y, z}
  have hcard : F.card ≤ 3 := by simp [F, hxy, hxz, hyz]
  obtain ⟨f⟩ := hsmall F hcard
  let xx : ↥F := ⟨x, by simp [F]⟩
  let yy : ↥F := ⟨y, by simp [F]⟩
  let zz : ↥F := ⟨z, by simp [F]⟩
  refine ⟨f.point xx, f.point yy, f.point zz, ?_, ?_, ?_⟩
  · exact f.preserves_edge xx yy (fun h => hxy (congrArg Subtype.val h)) a ha
  · exact f.preserves_edge yy zz (fun h => hyz (congrArg Subtype.val h)) b hb
  · exact f.preserves_edge xx zz (fun h => hxz (congrArg Subtype.val h)) c hc
end CompleteDiagram

namespace PartialDiagram
variable {V : Type z} (D : PartialDiagram S V)
def taggedEdge (x y : V) (h : x ≠ y) : Σ i : ι, Σ j : ι, Option (S.Atom i j) :=
  ⟨D.vertexSort x, D.vertexSort y, D.edge x y h⟩
end PartialDiagram

theorem taggedColour_ne_of_some {i j : ι} {a : S.Atom i j} {p q : Sigma X}
    (h : taggedColour S p q = ⟨i, j, some a⟩) : p ≠ q := by
  intro heq
  have hh := congrArg (fun c : Σ i : ι, Σ j : ι, Option (S.Atom i j) => c.2.2.isSome) h
  subst q
  have hn : S.colour p.2 p.2 = none := (S.colour_none_iff p.2 p.2).mpr rfl
  simp [taggedColour, hn] at hh

namespace CompleteDiagram
variable {V : Type z} (A : CompleteDiagram (S := S) V)

def prefixEmbedding {n : Nat} (vertices : Fin n ↪ V) {k : Nat} (hk : k < n) : Fin (k+1) ↪ V where
  toFun p := vertices ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_of_lt hk)⟩
  inj' := by
    intro p q h
    exact Fin.ext (congrArg (fun p : Fin n => p.val) (vertices.injective h))

def FanRealized {n : Nat} (vertices : Fin n ↪ V) {k : Nat} (hk : k < n) (hkpos : 1 ≤ k) : Prop :=
  let e := prefixEmbedding vertices hk
  ∃ point : Fin (k+1) → Sigma X,
    (∀ p, (point p).1 = A.diagram.vertexSort (e p)) ∧
    (∀ p : Fin k, taggedColour S (point p.castSucc) (point p.succ) =
      A.diagram.taggedEdge (e p.castSucc) (e p.succ)
        (e.injective.ne (by intro h; have := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_succ] at this; omega))) ∧
    taggedColour S (point 0) (point (Fin.last k)) =
      A.diagram.taggedEdge (e 0) (e (Fin.last k))
        (e.injective.ne (by intro h; have := congrArg Fin.val h; simp only [Fin.val_zero, Fin.val_last] at this; omega))

/-- A rooted fan of the actual chord colours of a complete input has an ordinary homomorphic realization. -/
theorem fanRealized_of_AP (ap : AgeAP S) (htri : A.TrianglesRealizable)
    {n : Nat} (vertices : Fin n ↪ V) :
    ∀ {k : Nat} (hk : k < n) (hkpos : 1 ≤ k), A.FanRealized vertices hk hkpos := by
  intro k
  induction k with
  | zero => intro hk hp; omega
  | succ k ih =>
    intro hk hp
    by_cases hzero : k = 0
    · subst k
      let e := prefixEmbedding vertices hk
      have hne : e 0 ≠ e (Fin.last 1) := e.injective.ne (by decide)
      obtain ⟨a, ha⟩ := A.complete (e 0) (e (Fin.last 1)) hne
      obtain ⟨x, y, hxy⟩ := S.realized a
      let point : Fin 2 → Sigma X := fun p => if p.val = 0 then
        ⟨A.diagram.vertexSort (e 0), x⟩ else ⟨A.diagram.vertexSort (e (Fin.last 1)), y⟩
      refine ⟨point, ?_, ?_, ?_⟩
      · intro p
        fin_cases p <;> rfl
      · intro p
        fin_cases p
        change taggedColour S ⟨_, x⟩ ⟨_, y⟩ = A.diagram.taggedEdge (e 0) (e (Fin.last 1)) _
        unfold taggedColour PartialDiagram.taggedEdge
        rw [ha, hxy]
      · change taggedColour S ⟨_, x⟩ ⟨_, y⟩ = A.diagram.taggedEdge (e 0) (e (Fin.last 1)) _
        unfold taggedColour PartialDiagram.taggedEdge
        rw [ha, hxy]
    · have hkpos : 1 ≤ k := by omega
      have hkold : k < n := by omega
      obtain ⟨point, hsort, hpath, hchord⟩ := ih hkold hkpos
      let e := prefixEmbedding vertices hkold
      let e' := prefixEmbedding vertices hk
      have hrLast : e 0 ≠ e (Fin.last k) := e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this; omega)
      have hlastNext : e (Fin.last k) ≠ e' (Fin.last (k+1)) := by
        intro h
        have hh := congrArg Fin.val (vertices.injective h)
        simp at hh
      have hrNext : e 0 ≠ e' (Fin.last (k+1)) := by
        intro h
        have hh := congrArg Fin.val (vertices.injective h)
        simp at hh
      obtain ⟨a, ha⟩ := A.complete (e 0) (e (Fin.last k)) hrLast
      obtain ⟨b, hb⟩ := A.complete (e (Fin.last k)) (e' (Fin.last (k+1))) hlastNext
      obtain ⟨c, hc⟩ := A.complete (e 0) (e' (Fin.last (k+1))) hrNext
      obtain ⟨x, y, z, hxy, hyz, hxz⟩ := htri _ _ _ hrLast hlastNext hrNext a b c ha hb hc
      change S.colour x y = some a at hxy
      change S.colour y z = some b at hyz
      change S.colour x z = some c at hxz
      change taggedColour S (point 0) (point (Fin.last k)) = A.diagram.taggedEdge (e 0) (e (Fin.last k)) _ at hchord
      have hcol : taggedColour S (point 0) (point (Fin.last k)) =
          taggedColour S ⟨_, x⟩ ⟨_, y⟩ := by
        calc
          _ = A.diagram.taggedEdge (e 0) (e (Fin.last k)) _ := hchord
          _ = _ := by unfold PartialDiagram.taggedEdge taggedColour; rw [ha, hxy]
      have hne : point 0 ≠ point (Fin.last k) := by
        apply taggedColour_ne_of_some (a := a)
        simpa [PartialDiagram.taggedEdge, ha] using hchord
      obtain ⟨out, next, houtsort, hnextsort, houtcol, hrootnext, hlastnext⟩ :=
        ap.extend_tuple_triangle point 0 (Fin.last k) ⟨_, x⟩ ⟨_, y⟩ ⟨_, z⟩ hne (S.atomRel_ne hxy) hcol
      let point' : Fin (k+2) → Sigma X := fun p =>
        if h : p.val < k+1 then out ⟨p.val, h⟩ else next
      have hsort' : ∀ p, (point' p).1 = A.diagram.vertexSort (e' p) := by
        intro p
        by_cases h : p.val < k+1
        · simp only [point', dite_eq_left h]
          exact (houtsort _).trans (hsort _)
        · have hpLast : p = Fin.last (k+1) := by apply Fin.ext; simp; omega
          subst p
          simpa [point'] using hnextsort
      have hpath' : ∀ p : Fin (k+1), taggedColour S (point' p.castSucc) (point' p.succ) =
          A.diagram.taggedEdge (e' p.castSucc) (e' p.succ)
            (e'.injective.ne (by intro h; have := congrArg Fin.val h; simp at this)) := by
        intro p
        by_cases h : p.val < k
        · have h1 : p.val < k+1 := by omega
          have h2 : p.val+1 < k+1 := by omega
          simp only [point', Fin.val_castSucc, Fin.val_succ, dite_eq_left h1, dite_eq_left h2]
          exact (houtcol ⟨p.val, h1⟩ ⟨p.val+1, h2⟩).trans (hpath ⟨p.val, h⟩)
        · have hpLast : p = Fin.last k := by apply Fin.ext; simp; omega
          subst p
          simp only [point', Fin.val_castSucc, Fin.val_succ, Fin.val_last,
            dite_eq_left (Nat.lt_succ_self k), dite_eq_right (Nat.lt_irrefl (k+1))]
          calc
            _ = taggedColour S ⟨_, y⟩ ⟨_, z⟩ := hlastnext
            _ = _ := by
              change taggedColour S ⟨_, y⟩ ⟨_, z⟩ =
                A.diagram.taggedEdge (e (Fin.last k)) (e' (Fin.last (k+1))) hlastNext
              unfold taggedColour PartialDiagram.taggedEdge
              rw [hb, hyz]
      have hchord' : taggedColour S (point' 0) (point' (Fin.last (k+1))) =
          A.diagram.taggedEdge (e' 0) (e' (Fin.last (k+1))) hrNext := by
        simp only [point', Fin.val_zero, Fin.val_last,
          dite_eq_right (Nat.lt_irrefl (k+1))]
        calc
          _ = taggedColour S ⟨_, x⟩ ⟨_, z⟩ := hrootnext
          _ = _ := by
            change taggedColour S ⟨_, x⟩ ⟨_, z⟩ =
              A.diagram.taggedEdge (e 0) (e' (Fin.last (k+1))) hrNext
            unfold taggedColour PartialDiagram.taggedEdge
            rw [hc, hxz]
      exact ⟨point', hsort', hpath', hchord'⟩
end CompleteDiagram

theorem PartialDiagram.taggedEdge_reverse {V : Type z} (D : PartialDiagram S V)
    (x y : V) (h : x ≠ y) :
    D.taggedEdge y x h.symm = reverseTagged S (D.taggedEdge x y h) := by
  cases hxy : D.edge x y h with
  | none =>
      cases hyx : D.edge y x h.symm with
      | none => simp only [PartialDiagram.taggedEdge, reverseTagged, hxy, hyx, Option.map_none]
      | some b =>
          have hh := (D.edge_reverse y x h.symm b).mp hyx
          rw [hxy] at hh
          contradiction
  | some a =>
      have hyx := (D.edge_reverse x y h a).mp hxy
      simp only [PartialDiagram.taggedEdge, reverseTagged, hxy, hyx, Option.map_some]

namespace CompleteDiagram
variable {V : Type z} (A : CompleteDiagram (S := S) V)

/-- Every simple cycle of a complete input is homomorphically realized by its legal rooted triangle fan. -/
theorem cycleHom_of_AP_triangles (ap : AgeAP S) (htri : A.TrianglesRealizable)
    (C : SimpleCycle A.diagram) : CycleHom C := by
  classical
  letI : NeZero C.length := ⟨Nat.ne_of_gt C.length_pos⟩
  have hk : C.length - 1 < C.length := by have := C.length_pos; omega
  have hpos : 1 ≤ C.length - 1 := by have := C.length_ge_three; omega
  have hlen : C.length - 1 + 1 = C.length := by have := C.length_pos; omega
  obtain ⟨point, hsort, hpath, hchord⟩ := A.fanRealized_of_AP ap htri C.vertices hk hpos
  let pointN : Fin C.length → Sigma X := fun p => point (Fin.cast hlen.symm p)
  have hsortN : ∀ p, (pointN p).1 = A.diagram.vertexSort (C.vertices p) := by
    intro p
    exact hsort (Fin.cast hlen.symm p)
  have htag_all : ∀ p : Fin C.length,
      taggedColour S (pointN p) (pointN (cyclicNext C.length_pos p)) =
        A.diagram.taggedEdge (C.vertices p) (C.vertices (cyclicNext C.length_pos p)) (C.next_ne p) := by
    intro p
    by_cases hlast : p.val = C.length - 1
    · have hp : p = ⟨C.length - 1, hk⟩ := Fin.ext hlast
      have hn : cyclicNext C.length_pos p = 0 := by
        apply Fin.ext
        simp only [cyclicNext, Fin.val_zero]
        rw [hlast, hlen, Nat.mod_self]
      have hrev := congrArg (reverseTagged S) hchord
      have hback : taggedColour S (pointN ⟨C.length - 1, hk⟩) (pointN 0) =
          A.diagram.taggedEdge (C.vertices ⟨C.length - 1, hk⟩) (C.vertices 0)
            (C.vertices.injective.ne (by intro he; have hh := congrArg Fin.val he; simp at hh; omega)) := by
        calc
          _ = reverseTagged S (taggedColour S (point 0) (point (Fin.last (C.length-1)))) :=
            taggedColour_reverse S _ _
          _ = _ := hrev
          _ = _ := (A.diagram.taggedEdge_reverse _ _ _).symm
      simpa only [← hp, hn] using hback
    · have hlt : p.val < C.length - 1 := by omega
      have hn : cyclicNext C.length_pos p = ⟨p.val+1, by omega⟩ := by
        apply Fin.ext
        simp only [cyclicNext]
        exact Nat.mod_eq_of_lt (by omega)
      simp only [hn]
      change taggedColour S (point ⟨p.val, by omega⟩) (point ⟨p.val+1, by omega⟩) =
        A.diagram.taggedEdge (C.vertices p) (C.vertices ⟨p.val+1, by omega⟩) _
      exact hpath ⟨p.val, hlt⟩
  have htyped : ∀ p, ∃ x : X (A.diagram.vertexSort (C.vertices p)), pointN p = ⟨_, x⟩ := by
    intro p
    generalize hp : pointN p = q
    have hs : q.1 = A.diagram.vertexSort (C.vertices p) :=
      (congrArg Sigma.fst hp).symm.trans (hsortN p)
    rcases q with ⟨j, x⟩
    cases hs
    exact ⟨x, rfl⟩
  choose typedPoint htyped using htyped
  refine ⟨typedPoint, ?_⟩
  intro p a ha
  have htag := htag_all p
  rw [htyped p, htyped (cyclicNext C.length_pos p)] at htag
  simpa only [taggedColour, PartialDiagram.taggedEdge, ha,
    Sigma.mk.injEq, heq_eq_eq, true_and] using htag

/-- The independent AP+semantic-CCO triangle-fullness theorem for the actual induced age.
Only the complete input's actual chords are used. No SAP or homogeneity is needed. -/
theorem triangleFullness_of_AP_CCO (ap : AgeAP S) (cco : SemanticCCO.{u,v,z,w} S)
    (hsmall : A.SmallRealizable) : ∃ f : DiagramHom A.diagram, f.IsInjective := by
  obtain ⟨f⟩ := cco V A.diagram (A.cycleHom_of_AP_triangles ap (A.trianglesRealizable_of_small hsmall))
  exact ⟨f, f.injective_of_complete A.complete⟩

/-- The full complete input colouring, retaining `none` only for its real logical diagonal. -/
noncomputable def fullColour (x y : V) : Σ i : ι, Σ j : ι, Option (S.Atom i j) := by
  classical
  exact if h : x = y then ⟨A.diagram.vertexSort x, A.diagram.vertexSort y, none⟩
    else A.diagram.taggedEdge x y h

/-- Readout into one actual finite INDUCED source structure, with the entire complete
input colouring retained, including its genuine logical diagonal. This is the
hereditary-age membership consumer of triangle fullness. -/
theorem induced_realization_of_AP_CCO (ap : AgeAP S) (cco : SemanticCCO.{u,v,z,w} S)
    (hsmall : A.SmallRealizable) :
    ∃ (T : FiniteInduced (X := X)) (e : V ↪ ↥T.vertices),
      (∀ x, (e x).val.1 = A.diagram.vertexSort x) ∧
      (∀ x y, taggedColour S (e x).val (e y).val = A.fullColour x y) := by
  classical
  obtain ⟨f, hf⟩ := A.triangleFullness_of_AP_CCO ap cco hsmall
  letI : Finite V := A.diagram.finite_type
  let T : FiniteInduced (X := X) := ⟨Set.range f.image, Set.finite_range f.image⟩
  let e : V ↪ ↥T.vertices := {
    toFun := fun x => ⟨f.image x, ⟨x, rfl⟩⟩
    inj' := fun _ _ h => hf (congrArg Subtype.val h) }
  refine ⟨T, e, fun _ => rfl, ?_⟩
  intro x y
  by_cases h : x = y
  · subst y
    simp only [fullColour]
    change taggedColour S ⟨_, f.point x⟩ ⟨_, f.point x⟩ = _
    simp [taggedColour, (S.colour_none_iff (f.point x) (f.point x)).mpr rfl]
  · simp only [fullColour, dite_eq_right h]
    obtain ⟨a, ha⟩ := A.complete x y h
    have hc := f.preserves_edge x y h a ha
    change taggedColour S ⟨_, f.point x⟩ ⟨_, f.point y⟩ = _
    simp only [taggedColour, PartialDiagram.taggedEdge, ha, hc]

/-- The ordinary-AP source wrapper, derived from the actual original homogeneous source independently of SAP. -/
theorem triangleFullness_of_homogeneous_CCO
    {G : Type*} [Group G] [∀ q : ι, MulAction G (X q)]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,z,w} S)
    (hsmall : A.SmallRealizable) : ∃ f : DiagramHom A.diagram, f.IsInjective :=
  A.triangleFullness_of_AP_CCO (AtomicSource.ageAP_of_homogeneous H) cco hsmall
end CompleteDiagram

end CCO
