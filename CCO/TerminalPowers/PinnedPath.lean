import CCO.TerminalPowers.GraphSource
import CCO.GuardedEndpoints
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

/-! Separate formal occurrences in a finite path. The represented walk may
repeat points; SAP injectivizes ALL occurrences while fixing BOTH endpoints. -/
universe u v w t
namespace CCO.TerminalPowers
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X) {i : ι}

def pathGraph (n : Nat) : SimpleGraph (Fin (n+1)) where
  Adj p q := p.val+1 = q.val ∨ q.val+1 = p.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro p h; rcases h with h | h <;> omega⟩

noncomputable def pathDiagram (t : S.Atom i i) (n : Nat) : PartialDiagram S (Fin (n+1)) :=
  monochromaticDiagram S (pathGraph n) t

noncomputable def walkHom (t : S.Atom i i) {n : Nat} {x y : X i}
    (p : (atomGraph S t).Walk x y) (hp : p.length = n) : DiagramHom (pathDiagram S t n) where
  point v := p.getVert v.val
  preserves_edge := by
    intro a b hab c hc
    obtain ⟨hedge,hc⟩ := (monochromaticDiagram_edge_iff S (pathGraph n) t hab c).mp hc
    subst c
    change S.colour (p.getVert a.val) (p.getVert b.val) = some t
    rcases hedge with he | he
    · have h := p.adj_getVert_succ (i := a.val) (by omega)
      change S.atomRel t (p.getVert a.val) (p.getVert (a.val+1)) at h
      simpa only [he,AtomicSource.atomRel] using h
    · have h := p.adj_getVert_succ (i := b.val) (by omega)
      have hr := h.symm
      change S.atomRel t (p.getVert (b.val+1)) (p.getVert b.val) at hr
      simpa only [he,AtomicSource.atomRel] using hr

theorem walkHom_first (t : S.Atom i i) {n : Nat} {x y : X i}
    (p : (atomGraph S t).Walk x y) (hp : p.length = n) :
    (walkHom S t p hp).point 0 = x := p.getVert_zero

theorem walkHom_last (t : S.Atom i i) {n : Nat} {x y : X i}
    (p : (atomGraph S t).Walk x y) (hp : p.length = n) :
    (walkHom S t p hp).point (Fin.last n) = y := by
  change p.getVert n = y
  rw [← hp]
  exact p.getVert_length

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)] (H : HomogeneousSource S G)

include H in
/-- C14--C16: no injectivity of the represented walk beyond its designated
distinct literal endpoints is assumed. The forbidden set is empty. -/
theorem injective_path_fixed_endpoints (sap : AgeSAP S) (t : S.Atom i i)
    {n : Nat} (_hn : 0 < n) {x y : X i} (hxy : x ≠ y)
    (hwalk : relPow (S.atomRel t) n x y) :
    ∃ f : DiagramHom (pathDiagram S t n), f.IsInjective ∧
      f.point 0 = x ∧ f.point (Fin.last n) = y ∧
      ∀ p : Fin n, S.colour (f.point p.castSucc) (f.point p.succ) = some t := by
  obtain ⟨p,hp⟩ := (relPow_atom_iff_walk S t n x y).mp hwalk
  let f := walkHom S t p hp
  let T : Set (Fin (n+1)) := {0,Fin.last n}
  have hpin : ∀ a ∈ T, ∀ b ∈ T, f.image a = f.image b → a = b := by
    intro a ha b hb he
    have hfirst : f.point 0 = x := walkHom_first S t p hp
    have hlast : f.point (Fin.last n) = y := walkHom_last S t p hp
    have hne : f.image 0 ≠ f.image (Fin.last n) := by
      intro he
      have he' := eq_of_heq (Sigma.mk.inj he).2
      exact hxy (hfirst.symm.trans (he'.trans hlast))
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · subst b; exact False.elim (hne he)
    · subst a; exact False.elim (hne he.symm)
    · exact ha.trans hb.symm
  obtain ⟨g,hg,hfix,_⟩ := DiagramHom.injectivize_of_SAP H sap f T hpin
    (∅ : Set (Sigma X)) Set.finite_empty
  have hfirst : g.point 0 = x := by
    have he := eq_of_heq (Sigma.mk.inj (hfix 0 (Or.inl rfl))).2
    exact he.trans (walkHom_first S t p hp)
  have hlast : g.point (Fin.last n) = y := by
    have he := eq_of_heq (Sigma.mk.inj (hfix (Fin.last n) (Or.inr rfl))).2
    exact he.trans (walkHom_last S t p hp)
  refine ⟨g,hg,hfirst,hlast,?_⟩
  intro q
  apply g.preserves_edge q.castSucc q.succ (by intro h; have := congrArg Fin.val h; simp at this) t
  exact (monochromaticDiagram_edge_iff S (pathGraph n) t _ t).mpr ⟨Or.inl rfl,rfl⟩

end CCO.TerminalPowers
