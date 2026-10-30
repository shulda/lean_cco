import CCO.SimultaneousQuotients.Towers.SourceIso
import CCO.Finite

/-! Actual typed source isomorphisms recovered from the equality partition
of all realized tagged optional colours. Sorts, fibres and atoms are rebuilt
from real points; no palette correspondence is a premise. -/

universe u v w u' v' w' u'' v'' w''
namespace CCO.FullPhaseLift.Full

structure SourceIso {κ : Type u} {Y : κ → Type v} {ι : Type u'} {X : ι → Type v'}
    (T : AtomicSource.{u,v,w} κ Y) (S : AtomicSource.{u',v',w'} ι X) where
  sort : κ ≃ ι
  point : ∀ k, Y k ≃ X (sort k)
  atom : ∀ k l, T.Atom k l ≃ S.Atom (sort k) (sort l)
  colours : ∀ k l (x : Y k) (y : Y l),
    (T.colour x y).map (atom k l) = S.colour (point k x) (point l y)

namespace SourceIso
variable {κ : Type u} {Y : κ → Type v} {ι : Type u'} {X : ι → Type v'}
variable {T : AtomicSource.{u,v,w} κ Y} {S : AtomicSource.{u',v',w'} ι X}

def whole (F : SourceIso T S) : Sigma Y ≃ Sigma X := Equiv.sigmaCongr F.sort F.point

@[simp] theorem whole_apply (F : SourceIso T S) (p : Sigma Y) :
    F.whole p = ⟨F.sort p.1,F.point p.1 p.2⟩ := rfl

@[simp] theorem whole_sort (F : SourceIso T S) (p : Sigma Y) :
    (F.whole p).1 = F.sort p.1 := rfl

def mapColour (F : SourceIso T S) (c : Σ k, Σ l, Option (T.Atom k l)) :
    Σ i, Σ j, Option (S.Atom i j) :=
  ⟨F.sort c.1,F.sort c.2.1,c.2.2.map (F.atom c.1 c.2.1)⟩

theorem mapColour_injective (F : SourceIso T S) : Function.Injective F.mapColour := by
  rintro ⟨k,l,a⟩ ⟨k',l',b⟩ h
  have hk : k = k' := F.sort.injective (congrArg Sigma.fst h)
  subst k'
  have ht : (⟨F.sort l,a.map (F.atom k l)⟩ : Σ j,Option (S.Atom (F.sort k) j)) =
      ⟨F.sort l',b.map (F.atom k l')⟩ := eq_of_heq (Sigma.mk.inj h).2
  have hl : l = l' := F.sort.injective (congrArg Sigma.fst ht)
  subst l'
  have ha : a.map (F.atom k l) = b.map (F.atom k l) := eq_of_heq (Sigma.mk.inj ht).2
  have hab := Option.map_injective (F.atom k l).injective ha
  subst b
  rfl

theorem map_tagged (F : SourceIso T S) (p q : Sigma Y) :
    F.mapColour (taggedColour T p q) = taggedColour S (F.whole p) (F.whole q) := by
  rcases p with ⟨k,x⟩
  rcases q with ⟨l,y⟩
  exact congrArg (fun c => (⟨F.sort k,F.sort l,c⟩ : Σ i,Σ j,Option (S.Atom i j)))
    (F.colours k l x y)

theorem whole_tagged_iff (F : SourceIso T S) (p q r s : Sigma Y) :
    taggedColour T p q = taggedColour T r s ↔
      taggedColour S (F.whole p) (F.whole q) = taggedColour S (F.whole r) (F.whole s) := by
  rw [← F.map_tagged,← F.map_tagged]
  exact F.mapColour_injective.eq_iff.symm

theorem atom_conv (F : SourceIso T S) (k l : κ) (a : T.Atom k l) :
    F.atom l k (T.conv a) = S.conv (F.atom k l a) := by
  obtain ⟨x,y,hxy⟩ := T.realized a
  have ht : T.colour y x = some (T.conv a) := (T.colour_swap x y a).mp hxy
  have hs : S.colour (F.point k x) (F.point l y) = some (F.atom k l a) := by
    have h := F.colours k l x y
    simpa only [hxy,Option.map_some] using h.symm
  have hsw := (S.colour_swap (F.point k x) (F.point l y) (F.atom k l a)).mp hs
  have hm := F.colours l k y x
  rw [ht,Option.map_some,hsw] at hm
  exact Option.some.inj hm

private theorem diagonal_tagged_iff {J : Type*} {Z : J → Type*}
    (U : AtomicSource J Z) (p q : Sigma Z) :
    taggedColour U p p = taggedColour U q q ↔ p.1 = q.1 := by
  constructor
  · exact congrArg Sigma.fst
  · intro h
    rcases p with ⟨i,x⟩
    rcases q with ⟨j,y⟩
    change i = j at h
    subst j
    have hx : U.colour x x = none := (U.colour_none_iff _ _).mpr rfl
    have hy : U.colour y y = none := (U.colour_none_iff _ _).mpr rfl
    simp only [taggedColour,hx,hy]

private theorem sigma_cast {J : Type*} {Z : J → Type*} {a b : J}
    (h : a = b) (x : Z a) :
    (⟨b,cast (congrArg Z h) x⟩ : Sigma Z) = ⟨a,x⟩ := by cases h; rfl

section Pattern
variable (T S)
variable (e : Sigma Y ≃ Sigma X)
variable (h : ∀ p q r s, taggedColour T p q = taggedColour T r s ↔
  taggedColour S (e p) (e q) = taggedColour S (e r) (e s))

private noncomputable def patternSort (k : κ) : ι :=
  (e ⟨k,Classical.choice (T.nonemptySort k)⟩).1

include h

private theorem pattern_sort_point (p : Sigma Y) :
    (e p).1 = patternSort T e p.1 := by
  apply (diagonal_tagged_iff S _ _).mp
  apply (h p p _ _).mp
  exact (diagonal_tagged_iff T _ _).mpr rfl

private theorem patternSort_bijective : Function.Bijective (patternSort T e) := by
  constructor
  · intro k l he
    have ht : taggedColour S (e ⟨k,Classical.choice (T.nonemptySort k)⟩)
        (e ⟨k,Classical.choice (T.nonemptySort k)⟩) =
        taggedColour S (e ⟨l,Classical.choice (T.nonemptySort l)⟩)
        (e ⟨l,Classical.choice (T.nonemptySort l)⟩) :=
      (diagonal_tagged_iff S _ _).mpr he
    exact (diagonal_tagged_iff T _ _).mp ((h _ _ _ _).mpr ht)
  · intro i
    let x := Classical.choice (S.nonemptySort i)
    let p := e.symm ⟨i,x⟩
    refine ⟨p.1,?_⟩
    exact (pattern_sort_point T S e h p).symm.trans (congrArg Sigma.fst (e.apply_symm_apply ⟨i,x⟩))

private noncomputable def patternSortEquiv : κ ≃ ι :=
  Equiv.ofBijective (patternSort T e) (patternSort_bijective T S e h)

private noncomputable def patternPoint (k : κ) (y : Y k) : X (patternSortEquiv T S e h k) :=
  cast (congrArg X (pattern_sort_point T S e h ⟨k,y⟩)) (e ⟨k,y⟩).2

private theorem patternPoint_whole (k : κ) (y : Y k) :
    (⟨patternSortEquiv T S e h k,patternPoint T S e h k y⟩ : Sigma X) = e ⟨k,y⟩ :=
  sigma_cast (pattern_sort_point T S e h ⟨k,y⟩) (e ⟨k,y⟩).2

private theorem patternPoint_bijective (k : κ) :
    Function.Bijective (patternPoint T S e h k) := by
  constructor
  · intro x y hxy
    have ht : e ⟨k,x⟩ = e ⟨k,y⟩ := (patternPoint_whole T S e h k x).symm.trans
      ((congrArg (Sigma.mk (patternSortEquiv T S e h k)) hxy).trans
        (patternPoint_whole T S e h k y))
    exact eq_of_heq (Sigma.mk.inj (e.injective ht)).2
  · intro x
    let p := e.symm ⟨patternSortEquiv T S e h k,x⟩
    have hep : e p = ⟨patternSortEquiv T S e h k,x⟩ := e.apply_symm_apply _
    have hs0 : (e p).1 = patternSortEquiv T S e h p.1 := pattern_sort_point T S e h p
    have hs1 := congrArg (fun q : Sigma X => q.1) hep
    have hsort : patternSortEquiv T S e h p.1 = patternSortEquiv T S e h k := hs0.symm.trans hs1
    have hpk := (patternSortEquiv T S e h).injective hsort
    rcases p with ⟨l,y⟩
    change l = k at hpk
    subst l
    exact ⟨y,eq_of_heq (Sigma.mk.inj ((patternPoint_whole T S e h k y).trans hep)).2⟩

private noncomputable def patternPointEquiv (k : κ) : Y k ≃ X (patternSortEquiv T S e h k) :=
  Equiv.ofBijective _ (patternPoint_bijective T S e h k)

end Pattern

private noncomputable def renamedSource (S : AtomicSource.{u',v',w'} ι X) (σ : κ ≃ ι) :
    AtomicSource κ (fun k => X (σ k)) where
  Atom k l := S.Atom (σ k) (σ l)
  finiteSort := by
    letI := S.finiteSort
    exact Fintype.ofEquiv ι σ.symm
  finiteAtom k l := S.finiteAtom _ _
  nonemptySort k := S.nonemptySort _
  conv := S.conv
  conv_invol := S.conv_invol
  symmetricLoop := S.symmetricLoop
  colour := S.colour
  colour_none_iff := by
    intro i j x y
    let E : Sigma (fun k => X (σ k)) ≃ Sigma X :=
      Equiv.sigmaCongr σ (fun k => Equiv.refl (X (σ k)))
    have he : E (⟨i,x⟩ : Sigma (fun k => X (σ k))) = E ⟨j,y⟩ ↔
        (⟨i,x⟩ : Sigma (fun k => X (σ k))) = ⟨j,y⟩ := E.injective.eq_iff
    exact (S.colour_none_iff x y).trans he
  colour_swap := S.colour_swap
  realized := S.realized

/-- Recover the actual typed source isomorphism from a bijection which
identifies precisely the equality classes of all tagged optional colours. -/
noncomputable def of_pattern (e : Sigma Y ≃ Sigma X)
    (h : ∀ p q r s, taggedColour T p q = taggedColour T r s ↔
      taggedColour S (e p) (e q) = taggedColour S (e r) (e s)) : SourceIso T S := by
  let σ := patternSortEquiv T S e h
  let f := patternPointEquiv T S e h
  let U := renamedSource S σ
  have hp : ∀ {k l} (x x' : Y k) (y y' : Y l),
      T.colour x y = T.colour x' y' ↔ U.colour (f k x) (f l y) = U.colour (f k x') (f l y') := by
    intro k l x x' y y'
    change T.colour x y = T.colour x' y' ↔
      S.colour (patternPoint T S e h k x) (patternPoint T S e h l y) =
        S.colour (patternPoint T S e h k x') (patternPoint T S e h l y')
    have hh := h ⟨k,x⟩ ⟨l,y⟩ ⟨k,x'⟩ ⟨l,y'⟩
    rw [← patternPoint_whole T S e h k x,← patternPoint_whole T S e h l y,
      ← patternPoint_whole T S e h k x',← patternPoint_whole T S e h l y'] at hh
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  let F := SimultaneousQuotients.Towers.atomicIso T U f hp
  exact ⟨σ,f,F.atom,F.colours⟩

@[simp] theorem of_pattern_whole (e : Sigma Y ≃ Sigma X)
    (h : ∀ p q r s, taggedColour T p q = taggedColour T r s ↔
      taggedColour S (e p) (e q) = taggedColour S (e r) (e s)) :
    (of_pattern e h).whole = e := by
  apply Equiv.ext
  rintro ⟨k,y⟩
  exact patternPoint_whole T S e h k y

/-- Reverse the actual source isomorphism through its whole carrier map.
The constructor recovers the dependent typed data without manual casts. -/
noncomputable def symm (F : SourceIso T S) : SourceIso S T :=
  of_pattern F.whole.symm (by
    intro p q r s
    have h := F.whole_tagged_iff (F.whole.symm p) (F.whole.symm q)
      (F.whole.symm r) (F.whole.symm s)
    simpa only [Equiv.apply_symm_apply] using h.symm)

@[simp] theorem symm_whole (F : SourceIso T S) : F.symm.whole = F.whole.symm :=
  of_pattern_whole _ _

/-- Compose actual whole source isomorphisms, then reconstruct the exact
typed correspondence. No prefix-history coherence callback is required. -/
noncomputable def trans {ζ : Type u''} {Z : ζ → Type v''}
    {U : AtomicSource.{u'',v'',w''} ζ Z} (F : SourceIso T S) (G : SourceIso S U) :
    SourceIso T U :=
  of_pattern (F.whole.trans G.whole) (by
    intro p q r s
    exact (F.whole_tagged_iff p q r s).trans
      (G.whole_tagged_iff (F.whole p) (F.whole q) (F.whole r) (F.whole s)))

@[simp] theorem trans_whole {ζ : Type u''} {Z : ζ → Type v''}
    {U : AtomicSource.{u'',v'',w''} ζ Z} (F : SourceIso T S) (G : SourceIso S U) :
    (F.trans G).whole = F.whole.trans G.whole := of_pattern_whole _ _

noncomputable abbrev compose {ζ : Type u''} {Z : ζ → Type v''}
    {U : AtomicSource.{u'',v'',w''} ζ Z} (G : SourceIso S U) (F : SourceIso T S) :
    SourceIso T U := F.trans G

@[simp] theorem compose_whole {ζ : Type u''} {Z : ζ → Type v''}
    {U : AtomicSource.{u'',v'',w''} ζ Z} (G : SourceIso S U) (F : SourceIso T S) :
    (G.compose F).whole = F.whole.trans G.whole := trans_whole F G

end SourceIso
end CCO.FullPhaseLift.Full
