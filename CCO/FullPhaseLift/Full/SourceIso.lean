import CCO.SimultaneousQuotients.Towers.SourceIso
import CCO.Finite

/-! Actual typed source isomorphisms recovered from the equality partition
of all realized tagged optional colours. Sorts, fibres and atoms are rebuilt
from real points; no palette correspondence is a premise. -/

universe u v w u' v' w'
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

end SourceIso
end CCO.FullPhaseLift.Full
