import CCO.Finite

/-! Literal gluing of finite old-coloured diagram pieces. Distinct pieces
may share vertices, but never a pair of distinct vertices. Thus the union
has exactly one old optional atom on every ordered pair, and no edge is
dropped or invented when private theta packages share old roots. -/

universe u v a p k q

namespace CCO.GuardedOldSeams

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,a} ι X)

structure DiagramGluing (V : Type p) (K : Type k) where
  sort : V → ι
  piece : K → Type q
  embed : ∀ k, piece k → V
  embed_injective : ∀ k, Function.Injective (embed k)
  overlap_unique : ∀ k l (x y : piece k) (x' y' : piece l),
    embed k x = embed l x' → embed k y = embed l y' → x ≠ y → k = l
  edge : ∀ k (x y : piece k), x ≠ y →
    Option (S.Atom (sort (embed k x)) (sort (embed k y)))
  edge_reverse : ∀ k (x y : piece k) (h : x ≠ y)
    (b : S.Atom (sort (embed k x)) (sort (embed k y))),
    edge k x y h = some b ↔ edge k y x h.symm = some (S.conv b)

namespace DiagramGluing

variable {S} {V : Type p} {K : Type k} (D : DiagramGluing.{u,v,a,p,k,q} S V K)

structure PairWitness (x y : V) where
  index : K
  source : D.piece index
  target : D.piece index
  source_eq : D.embed index source = x
  target_eq : D.embed index target = y

theorem PairWitness.unique {x y : V} (hxy : x ≠ y)
    (w w' : D.PairWitness x y) : w = w' := by
  rcases w with ⟨k,s,t,hs,ht⟩
  rcases w' with ⟨l,s',t',hs',ht'⟩
  have hst : s ≠ t := fun he => hxy (hs.symm.trans ((congrArg (D.embed k) he).trans ht))
  have hkl := D.overlap_unique k l s t s' t'
    (hs.trans hs'.symm) (ht.trans ht'.symm) hst
  subst l
  have hss := D.embed_injective k (hs.trans hs'.symm)
  have htt := D.embed_injective k (ht.trans ht'.symm)
  subst s'
  subst t'
  rfl

def PairWitness.edge {x y : V} (w : D.PairWitness x y) (hxy : x ≠ y) :
    Option (S.Atom (D.sort x) (D.sort y)) := by
  rcases w with ⟨k,s,t,hs,ht⟩
  subst x
  subst y
  exact D.edge k s t (fun he => hxy (congrArg (D.embed k) he))

noncomputable def unionEdge (x y : V) (hxy : x ≠ y) :
    Option (S.Atom (D.sort x) (D.sort y)) := by
  classical
  exact if h : Nonempty (D.PairWitness x y) then
    PairWitness.edge D (Classical.choice h) hxy else none

theorem unionEdge_on_piece (k : K) (x y : D.piece k)
    (hxy : D.embed k x ≠ D.embed k y) :
    D.unionEdge (D.embed k x) (D.embed k y) hxy =
      D.edge k x y (fun he => hxy (congrArg (D.embed k) he)) := by
  classical
  let witness : D.PairWitness (D.embed k x) (D.embed k y) := ⟨k,x,y,rfl,rfl⟩
  have hw : Nonempty (D.PairWitness (D.embed k x) (D.embed k y)) := ⟨witness⟩
  rw [unionEdge, dite_eq_left hw, PairWitness.unique D hxy (Classical.choice hw) witness]
  rfl

theorem unionEdge_reverse (x y : V) (hxy : x ≠ y)
    (b : S.Atom (D.sort x) (D.sort y)) :
    D.unionEdge x y hxy = some b ↔
      D.unionEdge y x hxy.symm = some (S.conv b) := by
  classical
  by_cases hw : Nonempty (D.PairWitness x y)
  · obtain ⟨k,s,t,hs,ht⟩ := Classical.choice hw
    subst x
    subst y
    rw [unionEdge_on_piece, unionEdge_on_piece]
    exact D.edge_reverse k s t _ b
  · have hrev : ¬ Nonempty (D.PairWitness y x) := by
      rintro ⟨k,s,t,hs,ht⟩
      exact hw ⟨k,t,s,ht,hs⟩
    simp only [unionEdge, dite_eq_right hw, dite_eq_right hrev, reduceCtorEq]

noncomputable def toDiagram [Finite V] : PartialDiagram S V where
  finite_type := inferInstance
  vertexSort := D.sort
  edge := D.unionEdge
  edge_reverse := D.unionEdge_reverse

noncomputable def homOfPieces [Finite V]
    (point : ∀ x : V, X (D.sort x))
    (preserves : ∀ k (x y : D.piece k) (h : x ≠ y)
      (b : S.Atom (D.sort (D.embed k x)) (D.sort (D.embed k y))),
      D.edge k x y h = some b →
      S.colour (point (D.embed k x)) (point (D.embed k y)) = some b) :
    DiagramHom D.toDiagram where
  point := point
  preserves_edge := by
    classical
    intro x y hxy b hb
    change D.unionEdge x y hxy = some b at hb
    by_cases hw : Nonempty (D.PairWitness x y)
    · obtain ⟨k,s,t,hs,ht⟩ := Classical.choice hw
      subst x
      subst y
      rw [unionEdge_on_piece] at hb
      exact preserves k s t _ b hb
    · simp only [unionEdge, dite_eq_right hw] at hb
      cases hb

theorem hom_preserves_piece [Finite V] (f : DiagramHom D.toDiagram)
    (k : K) (x y : D.piece k) (h : x ≠ y)
    (b : S.Atom (D.sort (D.embed k x)) (D.sort (D.embed k y)))
    (hb : D.edge k x y h = some b) :
    S.colour (f.point (D.embed k x)) (f.point (D.embed k y)) = some b := by
  have hxy : D.embed k x ≠ D.embed k y := fun he => h (D.embed_injective k he)
  exact f.preserves_edge _ _ hxy b ((D.unionEdge_on_piece k x y hxy).trans hb)

end DiagramGluing
end CCO.GuardedOldSeams
