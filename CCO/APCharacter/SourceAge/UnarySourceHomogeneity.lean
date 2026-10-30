import CCO.APCharacter.SourceAge.UnarySourceAction

/-! Whole finite-diagram homogeneity of the actual child source follows
from homogeneity of the ENTIRE marked Fraïssé limit, with literal names. -/
universe u v w t
namespace CCO.APCharacter.SourceAge.UnarySource
open OwnerTransversal.CountableColour
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {M : MaskData S}
variable {completion : Age.CompletionProperty S M}
noncomputable section
variable (I : Identification S H completion)

/-- Forget child names but retain every literal original optional atom. -/
def eraseColour (a : Σ c, Σ d, Option ((source I).Atom c d)) : Age.Colour S :=
  ⟨a.1.1,a.2.1.1,a.2.2.map Subtype.val⟩

theorem erase_tagged (p q : NewPoint I) :
    eraseColour I (taggedColour (source I) p q) = taggedColour S (oldEquiv I p) (oldEquiv I q) := by
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  change (⟨c.1,d.1,(Rank.colour S (β I) (tag I) x y).map Subtype.val⟩ : Age.Colour S) =
    ⟨c.1,d.1,S.colour x.val y.val⟩
  rw [Rank.colour_map]

theorem new_colour (p q : NewPoint I) :
    (Age.limitCoding S H completion).table.colour (newEquiv I p) (newEquiv I q) =
      Age.colourEquiv S (eraseColour I (taggedColour (source I) p q)) := by
  rw [erase_tagged]
  exact colour_eq I (oldEquiv I p) (oldEquiv I q)

theorem action_colours (g : FullGroup I) (p q : NewPoint I) :
    taggedColour (source I) (g • p) (g • q) = taggedColour (source I) p q := by
  have he := full_colour I g (newEquiv I p) (newEquiv I q)
  rw [← smul_image,← smul_image,new_colour,new_colour] at he
  have ho := (Age.colourEquiv S).injective he
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  have hOld : S.colour (g • x).val (g • y).val = S.colour x.val y.val := by
    rw [erase_tagged,erase_tagged] at ho
    change taggedColour S ⟨c.1,(g • x).val⟩ ⟨d.1,(g • y).val⟩ =
      taggedColour S ⟨c.1,x.val⟩ ⟨d.1,y.val⟩ at ho
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using ho
  have hn : (source I).colour (g • x) (g • y) = (source I).colour x y := by
    apply Option.map_injective Subtype.val_injective
    change (Rank.colour S (β I) (tag I) (g • x) (g • y)).map Subtype.val =
      (Rank.colour S (β I) (tag I) x y).map Subtype.val
    rw [Rank.colour_map,Rank.colour_map,hOld]
  exact congrArg (fun a => (⟨c,d,a⟩ : Σ c, Σ d, Option ((source I).Atom c d))) hn

/-- Equality recognition from the actual logical diagonal of a tagged atom. -/
theorem equality_iff {J : Type*} {P : J → Type*} (T : AtomicSource J P)
    (p q r s : Sigma P) (h : taggedColour T p q = taggedColour T r s) :
    p=q ↔ r=s := by
  have hh := congrArg (fun a : Σ i, Σ j, Option (T.Atom i j) => a.2.2 = none) h
  exact (T.colour_none_iff p.2 q.2).symm.trans (hh.to_iff.trans (T.colour_none_iff r.2 s.2))

/-- The SAME actual whole-structure automorphism simultaneously extends
every finite complete new-source partial isomorphism, not merely each child. -/
theorem homogeneous : HomogeneousSource (source I) (FullGroup I) := by
  classical
  refine ⟨fun _ _ => rfl,action_colours I,?_⟩
  intro V _ f h hpairs
  let p : V → Age.Limit S H completion := newEquiv I ∘ f
  let q : V → Age.Limit S H completion := newEquiv I ∘ h
  have hEq (i j : V) : p i = p j ↔ q i = q j := by
    change newEquiv I (f i) = newEquiv I (f j) ↔ newEquiv I (h i) = newEquiv I (h j)
    rw [(newEquiv I).injective.eq_iff,(newEquiv I).injective.eq_iff]
    exact equality_iff (source I) _ _ _ _ (hpairs i j)
  have hOwner (i : V) : (Age.limitCoding S H completion).table.owner (p i) =
      (Age.limitCoding S H completion).table.owner (q i) := by
    have hs : (f i).1 = (h i).1 := congrArg (fun a : Σ c, Σ d, Option ((source I).Atom c d) => a.1) (hpairs i i)
    exact (new_owner I (f i)).trans ((congrArg (fun c => Age.ownerEquiv S (childLabel I c)) hs).trans
      (new_owner I (h i)).symm)
  have hColour (i j : V) : (Age.limitCoding S H completion).table.colour (p i) (p j) =
      (Age.limitCoding S H completion).table.colour (q i) (q j) := by
    change (Age.limitCoding S H completion).table.colour (newEquiv I (f i)) (newEquiv I (f j)) =
      (Age.limitCoding S H completion).table.colour (newEquiv I (h i)) (newEquiv I (h j))
    rw [new_colour,new_colour,hpairs]
  obtain ⟨g,hg⟩ := Age.tuple_homogeneous S H completion p q hEq hOwner hColour
  refine ⟨ULift.up g,?_⟩
  intro i
  apply (newEquiv I).injective
  rw [smul_image]
  exact hg i

end
end CCO.APCharacter.SourceAge.UnarySource
