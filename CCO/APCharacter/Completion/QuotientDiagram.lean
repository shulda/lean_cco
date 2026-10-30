import CCO.APCharacter.Completion.Walks

/-! Actual finite pushforward diagrams. An old homomorphism is used only to
read the original atom on each lifted edge, never to assume a simultaneous
realization after identification. Atomic compatibility is a separate finite
old-cycle consequence for the two-vertex fold. -/
universe u v w z z'
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} {W : Type z'} (D : PartialDiagram S V)
variable (f : DiagramHom D) (q : V → W) (sort : W → ι)
variable (typed : ∀ a, D.vertexSort a = sort (q a))

def pushedPoint (a : V) (u : W) (ha : q a = u) : X (sort u) :=
  (typed a |>.trans (congrArg sort ha)) ▸ f.point a

private theorem sigma_cast {i j : ι} (h : i = j) (a : X i) :
    (⟨j,h ▸ a⟩ : Sigma X) = ⟨i,a⟩ := by
  cases h
  rfl

theorem pushedPoint_sigma (a : V) (u : W) (ha : q a = u) :
    (⟨sort u,pushedPoint D f q sort typed a u ha⟩ : Sigma X) = f.image a :=
  sigma_cast ((typed a).trans (congrArg sort ha)) (f.point a)

def PushedEdge (u v : W) (c : S.Atom (sort u) (sort v)) : Prop :=
  ∃ (a b : V) (ha : q a = u) (hb : q b = v),
    (graph D).Adj a b ∧
    S.colour (pushedPoint D f q sort typed a u ha)
      (pushedPoint D f q sort typed b v hb) = some c

def PushCompatible : Prop := ∀ u v c d,
  PushedEdge D f q sort typed u v c → PushedEdge D f q sort typed u v d → c = d

theorem pushedEdge_reverse (u v : W) (c : S.Atom (sort u) (sort v)) :
    PushedEdge D f q sort typed u v c ↔
    PushedEdge D f q sort typed v u (S.conv c) := by
  constructor
  · rintro ⟨a,b,ha,hb,hab,hc⟩
    exact ⟨b,a,hb,ha,(graph D).symm.symm a b hab,
      (S.colour_swap _ _ c).mp hc⟩
  · rintro ⟨b,a,hb,ha,hba,hc⟩
    exact ⟨a,b,ha,hb,(graph D).symm.symm b a hba,
      (S.colour_swap _ _ c).mpr hc⟩

noncomputable def pushedEdge (u v : W) : Option (S.Atom (sort u) (sort v)) := by
  classical
  exact if h : ∃ c, PushedEdge D f q sort typed u v c then some h.choose else none

theorem pushedEdge_eq_iff (compatible : PushCompatible D f q sort typed)
    (u v : W) (c : S.Atom (sort u) (sort v)) :
    pushedEdge D f q sort typed u v = some c ↔ PushedEdge D f q sort typed u v c := by
  classical
  unfold pushedEdge
  split_ifs with h
  · constructor
    · intro hc
      have he : h.choose = c := Option.some.inj hc
      exact he ▸ h.choose_spec
    · intro hc
      rw [compatible u v _ _ h.choose_spec hc]
  · constructor
    · intro hc; cases hc
    · intro hc; exact False.elim (h ⟨c,hc⟩)

noncomputable def pushDiagram [Finite W]
    (compatible : PushCompatible D f q sort typed) : PartialDiagram S W where
  finite_type := inferInstance
  vertexSort := sort
  edge u v _ := pushedEdge D f q sort typed u v
  edge_reverse u v _ c := by
    rw [pushedEdge_eq_iff D f q sort typed compatible,
      pushedEdge_eq_iff D f q sort typed compatible]
    exact pushedEdge_reverse D f q sort typed u v c

/-- Every new specified edge carries an actual old specified-edge lift,
including its exact original atomic name read through the sorting equalities. -/
theorem pushDiagram_lift [Finite W] (compatible : PushCompatible D f q sort typed)
    (u v : W) (huv : u ≠ v) (c : S.Atom (sort u) (sort v))
    (hc : (pushDiagram D f q sort typed compatible).edge u v huv = some c) :
    ∃ (a b : V) (ha : q a = u) (hb : q b = v),
      (graph D).Adj a b ∧
      S.colour (pushedPoint D f q sort typed a u ha)
        (pushedPoint D f q sort typed b v hb) = some c :=
  (pushedEdge_eq_iff D f q sort typed compatible u v c).mp hc

/-- Every old specified edge supplies a real atom in the pushed diagram,
provided its two formal images remain distinct. -/
theorem pushDiagram_old_edge [Finite W] (compatible : PushCompatible D f q sort typed)
    {a b : V} (hab : (graph D).Adj a b) (hne : q a ≠ q b) :
    ∃ c, (pushDiagram D f q sort typed compatible).edge (q a) (q b) hne = some c ∧
      S.colour (pushedPoint D f q sort typed a (q a) rfl)
        (pushedPoint D f q sort typed b (q b) rfl) = some c := by
  have hn : S.colour (pushedPoint D f q sort typed a (q a) rfl)
      (pushedPoint D f q sort typed b (q b) rfl) ≠ none := by
    intro hc
    have he := (S.colour_none_iff _ _).mp hc
    have he' : f.image a = f.image b :=
      (pushedPoint_sigma D f q sort typed a (q a) rfl).symm.trans
        (he.trans (pushedPoint_sigma D f q sort typed b (q b) rfl))
    obtain ⟨h,c,hc⟩ := hab
    exact S.atomRel_ne (f.preserves_edge a b h c hc) he'
  cases hc : S.colour (pushedPoint D f q sort typed a (q a) rfl)
      (pushedPoint D f q sort typed b (q b) rfl) with
  | none => exact False.elim (hn hc)
  | some c =>
    exact ⟨c,(pushedEdge_eq_iff D f q sort typed compatible _ _ c).mpr
      ⟨a,b,rfl,rfl,hab,hc⟩,rfl⟩

private theorem uncast_colour {i j i' j' : ι} (hi : i = i') (hj : j = j')
    (a : X i) (b : X j) (a' : X i') (b' : X j')
    (h : S.colour (hi ▸ a) (hj ▸ b) = S.colour a' b') :
    S.colour a b = S.colour (hi.symm ▸ a') (hj.symm ▸ b') := by
  cases hi
  cases hj
  exact h

/-- A realization of the actual quotient diagram composes back to a
homomorphism of the old diagram. The map may identify the selected pair. -/
def pullPushHom [Finite W] (compatible : PushCompatible D f q sort typed)
    (noCollapse : ∀ a b, (graph D).Adj a b → q a ≠ q b)
    (g : DiagramHom (pushDiagram D f q sort typed compatible)) : DiagramHom D where
  point a := (typed a).symm ▸ g.point (q a)
  preserves_edge a b hab c hc := by
    have ha : (graph D).Adj a b := ⟨hab,c,hc⟩
    obtain ⟨d,hd,hColour⟩ := pushDiagram_old_edge D f q sort typed compatible ha (noCollapse a b ha)
    have hg := g.preserves_edge (q a) (q b) (noCollapse a b ha) d hd
    have hh : S.colour (pushedPoint D f q sort typed a (q a) rfl)
        (pushedPoint D f q sort typed b (q b) rfl) = S.colour (g.point (q a)) (g.point (q b)) :=
      hColour.trans hg.symm
    have hOrig := uncast_colour (typed a) (typed b) (f.point a) (f.point b)
      (g.point (q a)) (g.point (q b)) hh
    exact hOrig.symm.trans (f.preserves_edge a b hab c hc)

/-- Lift compatibility can be checked entirely on literal OLD tagged pair
colours, before any quotient realization is constructed. -/
def EdgeCoherent : Prop := ∀ a b a' b',
  (graph D).Adj a b → (graph D).Adj a' b' → q a = q a' → q b = q b' →
  taggedColour S (f.image a) (f.image b) = taggedColour S (f.image a') (f.image b')

theorem pushedEdge_tag (u v : W) (c : S.Atom (sort u) (sort v))
    (a b : V) (ha : q a = u) (hb : q b = v)
    (hc : S.colour (pushedPoint D f q sort typed a u ha)
      (pushedPoint D f q sort typed b v hb) = some c) :
    taggedColour S (f.image a) (f.image b) = ⟨sort u,sort v,some c⟩ := by
  have he := congrArg₂ (taggedColour S)
    (pushedPoint_sigma D f q sort typed a u ha)
    (pushedPoint_sigma D f q sort typed b v hb)
  rw [← he]
  change (⟨sort u,sort v,S.colour _ _⟩ : Σ i, Σ j, Option (S.Atom i j)) = _
  rw [hc]

theorem pushCompatible_of_edgeCoherent (coherent : EdgeCoherent D f q) :
    PushCompatible D f q sort typed := by
  rintro u v c d ⟨a,b,ha,hb,hab,hc⟩ ⟨a',b',ha',hb',ha'b',hd⟩
  have he := coherent a b a' b' hab ha'b' (ha.trans ha'.symm) (hb.trans hb'.symm)
  rw [pushedEdge_tag D f q sort typed u v c a b ha hb hc,
    pushedEdge_tag D f q sort typed u v d a' b' ha' hb' hd] at he
  have he' := eq_of_heq (Sigma.mk.inj he).2
  have he'' := eq_of_heq (Sigma.mk.inj he').2
  exact Option.some.inj he''

end CCO.APCharacter.Completion
