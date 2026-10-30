import CCO.RelationalCompletion.Atomic.Fan
import Mathlib.Tactic.Tauto

/-! The literal partial star/path fan. Unlike the complete restriction of A,
it records no other chords, so a realization may identify nonadjacent points. -/
universe u v
namespace CCO.RelationalCompletion.Atomic
variable {P : Palette.{u,v}}

/-- The root star and the consecutive path, in both orientations. -/
def FanRecorded {k : Nat} (x y : Fin (k+1)) : Prop :=
  x.val = 0 ∨ y.val = 0 ∨ x.val + 1 = y.val ∨ y.val + 1 = x.val

theorem fanRecorded_symm {k : Nat} {x y : Fin (k+1)} :
    FanRecorded x y ↔ FanRecorded y x := by
  simp only [FanRecorded]
  tauto

noncomputable def fanDiagram (A : Model P) {n : Nat}
    (vertices : Fin n ↪ Fin A.size) {k : Nat} (hk : k < n) : Diagram P (k+1) := by
  classical
  let e := prefixEmbedding vertices hk
  exact {
    tag := fun p => A.tag (e p)
    edge := fun x y => if FanRecorded x y then A.edge (e x) (e y) else none
    edge_self := by
      intro x
      split
      · exact A.diagram.edge_self (e x)
      · rfl
    edge_reverse := by
      intro x y
      by_cases h : FanRecorded x y
      · simp only [ite_eq_left h, ite_eq_left (fanRecorded_symm.mp h)]
        exact A.diagram.edge_reverse (e x) (e y)
      · simp only [ite_eq_right h, ite_eq_right (fun h' => h (fanRecorded_symm.mp h')), Option.map_none]
    typed := by
      intro x y a h
      split at h
      · exact A.diagram.typed (e x) (e y) a h
      · contradiction }

/-- All recorded star/path pairs, including their converses, are preserved by
the actual fan realization. No assertion is made about other chords. -/
theorem fanRealized_colour {A : Model P} {n k : Nat}
    {vertices : Fin n ↪ Fin A.size} {hk : k < n}
    {B : Model P} {point : Fin (k+1) → Fin B.size}
    (hpath : ∀ p : Fin k, B.colour (point p.castSucc) (point p.succ) =
      A.colour ((prefixEmbedding vertices hk) p.castSucc) ((prefixEmbedding vertices hk) p.succ))
    (hstar : ∀ p, B.colour (point 0) (point p) =
      A.colour ((prefixEmbedding vertices hk) 0) ((prefixEmbedding vertices hk) p))
    (x y : Fin (k+1)) (h : FanRecorded x y) :
    B.colour (point x) (point y) =
      A.colour ((prefixEmbedding vertices hk) x) ((prefixEmbedding vertices hk) y) := by
  rcases h with hx | hy | hxy | hyx
  · have he : x = 0 := Fin.ext hx
    subst x; exact hstar y
  · have he : y = 0 := Fin.ext hy
    subst y
    rw [B.colour_reverse, A.colour_reverse, hstar x]
  · have hlt : x.val < k := by have := y.isLt; omega
    have h1 : (⟨x.val, hlt⟩ : Fin k).castSucc = x := Fin.ext rfl
    have h2 : (⟨x.val, hlt⟩ : Fin k).succ = y := Fin.ext hxy
    simpa only [h1, h2] using hpath ⟨x.val, hlt⟩
  · have hlt : y.val < k := by have := x.isLt; omega
    have h1 : (⟨y.val, hlt⟩ : Fin k).castSucc = y := Fin.ext rfl
    have h2 : (⟨y.val, hlt⟩ : Fin k).succ = x := Fin.ext hyx
    rw [B.colour_reverse, A.colour_reverse]
    exact congrArg (Model.reverseTagged P) (by simpa only [h1, h2] using hpath ⟨y.val, hlt⟩)

/-- The fan induction supplies a homomorphism of its literal partial diagram. -/
theorem fanDiagram_hom (K : Model P → Prop) (A : Model P)
    (ap : AP K) (small : SmallSubmodels K A)
    {n k : Nat} (vertices : Fin n ↪ Fin A.size) (hk : k < n) (hp : 1 ≤ k) :
    ∃ B : Model P, K B ∧ Nonempty (Hom (fanDiagram A vertices hk) B) := by
  classical
  obtain ⟨B, hKB, point, htag, hpath, hstar⟩ := fanRealized K A ap small vertices hk hp
  refine ⟨B, hKB, ⟨{ vertex := point, tag_eq := htag, edge_eq := ?_ }⟩⟩
  intro x y a ha
  change (if FanRecorded x y then A.edge ((prefixEmbedding vertices hk) x)
    ((prefixEmbedding vertices hk) y) else none) = some a at ha
  split at ha
  next h =>
    have hc := fanRealized_colour hpath hstar x y h
    exact (congrArg (fun c : Σ _i : P.Sorts, Σ _j : P.Sorts, Option P.Atom => c.2.2) hc).trans ha
  next => contradiction

end CCO.RelationalCompletion.Atomic
