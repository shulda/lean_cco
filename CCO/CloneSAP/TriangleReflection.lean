import CCO.CloneSAP.Triangles

universe u v w z
namespace CCO.CloneSAP
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def includeFull : FullCode S → FullCode (source S) :=
  fun c => ⟨c.1,c.2.1,c.2.2.map Sum.inl⟩

@[simp] theorem eraseFull_include (c : FullCode S) :
    eraseFull S (includeFull S c) = c := by
  rcases c with ⟨i,j,c⟩
  cases c <;> rfl

/-- Old colours lift literally when owners differ; a true logical diagonal
also lifts literally. No old equality is turned into clone diversity. -/
theorem includeFull_colour (p q : Sigma (Carrier X))
    (h : owner p ≠ owner q ∨ p = q) :
    taggedColour (source S) p q = includeFull S (taggedColour S (owner p) (owner q)) := by
  classical
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  apply congrArg (fun c => (⟨i,j,c⟩ : FullCode (source S)))
  change colour S x y = (S.colour x.1 y.1).map Sum.inl
  by_cases hn : S.colour x.1 y.1 = none
  · have he : (⟨i,x⟩ : Sigma (Carrier X)) = ⟨j,y⟩ :=
      h.resolve_left (not_not.mpr ((S.colour_none_iff _ _).mp hn))
    rw [hn,Option.map_none]
    exact (colour_none_iff S x y).mpr he
  · simp [colour,hn]

/-- C10: triangle-definedness reflects to the original source, using only
old diversity atoms in the clone language. -/
theorem triangle_defined_reflects
    (triangles : TriangleDefined.{u,v,w,z} (source S)) : TriangleDefined.{u,v,w,z} S := by
  classical
  intro V _ c small
  let up : V → V → FullCode (source S) := fun x y => includeFull S (c x y)
  have up_small : SmallEmbeddings (source S) up := by
    intro F hF
    obtain ⟨f,hf⟩ := small F hF
    obtain ⟨g,hg⟩ := fresh_lift (fun a : F => f a)
    refine ⟨g,?_⟩
    intro a b
    have he : owner (g a) ≠ owner (g b) ∨ g a = g b := by
      by_cases hab : a = b
      · exact Or.inr (congrArg g hab)
      · refine Or.inl (fun h => hab ?_)
        rw [hg,hg] at h
        exact f.injective h
    rw [includeFull_colour S _ _ he,hg,hg,hf]
  obtain ⟨g,hg⟩ := triangles V up up_small
  let f : V → Sigma X := fun x => owner (g x)
  have hf (x y : V) : taggedColour S (f x) (f y) = c x y := by
    have he := congrArg (eraseFull S) (hg x y)
    simpa only [up,eraseFull_colour,eraseFull_include] using he
  have f_inj : Function.Injective f := by
    intro x y he
    let F : Finset V := {x,y}
    have hF : F.card ≤ 3 := (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((by simp : ( {y} : Finset V).card ≤ 2)))
    obtain ⟨l,hl⟩ := small F hF
    let a : F := ⟨x,by simp [F]⟩
    let b : F := ⟨y,by simp [F]⟩
    have hh : taggedColour S (l a) (l b) = taggedColour S (f x) (f y) := (hl a b).trans (hf x y).symm
    have hl' : l a = l b := (tagged_diagonal S hh).mpr he
    exact congrArg Subtype.val (l.injective hl')
  exact ⟨⟨f,f_inj⟩,hf⟩

theorem triangle_defined_iff : TriangleDefined.{u,v,w,z} (source S) ↔ TriangleDefined.{u,v,w,z} S :=
  ⟨triangle_defined_reflects S,triangle_defined S⟩

end CCO.CloneSAP
