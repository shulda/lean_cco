import CCO.APCharacter.SourceAge.UnarySourceHomogeneity
import CCO.StabilizerHomogeneity

/-! Literal complete finite types in the canonical actual unary source.
Old point maps are bijections and child atoms are occurring OLD colours,
so equal old complete types and equal actual bits reflect all new names. -/

universe u v w t
namespace CCO.PairSafeSplit.SAP
open APCharacter APCharacter.SourceAge APCharacter.SourceAge.UnarySource
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {M : MaskData S}
variable {completion : Age.CompletionProperty S M}
noncomputable section
variable (I : Identification S H completion)

def oldBase (B : FiniteInduced (X := Rank.Point (β I) (tag I))) :
    FiniteInduced (X := X) where
  vertices := (oldEquiv I) '' B.vertices
  finite_vertices := B.finite_vertices.image _

theorem mark_oldEquiv (x : NewPoint I) : mark I (oldEquiv I x) = x.1.2.val := by
  rcases x with ⟨c,⟨x,hx⟩⟩
  exact congrArg Subtype.val hx

theorem child_eq_of_old_and_mark (x y : NewPoint I)
    (hs : (oldEquiv I x).1 = (oldEquiv I y).1)
    (hm : mark I (oldEquiv I x) = mark I (oldEquiv I y)) : x.1 = y.1 := by
  apply childLabel_injective I
  apply Prod.ext
  · exact hs
  · exact (mark_oldEquiv I x).symm.trans (hm.trans (mark_oldEquiv I y))

/-- On FIXED child sorts the old complete optional colour determines
the new complete optional colour, retaining equality and both directions. -/
theorem tagged_colour_of_old (p q r s : NewPoint I)
    (hp : p.1 = r.1) (hq : q.1 = s.1)
    (hold : taggedColour S (oldEquiv I p) (oldEquiv I q) =
      taggedColour S (oldEquiv I r) (oldEquiv I s)) :
    taggedColour (UnarySource.source I) p q = taggedColour (UnarySource.source I) r s := by
  rcases p with ⟨c,x⟩
  rcases q with ⟨d,y⟩
  rcases r with ⟨c',x'⟩
  rcases s with ⟨d',y'⟩
  change c = c' at hp
  change d = d' at hq
  subst c'
  subst d'
  have hc : S.colour x.val y.val = S.colour x'.val y'.val := by
    change taggedColour S ⟨c.1,x.val⟩ ⟨d.1,y.val⟩ =
      taggedColour S ⟨c.1,x'.val⟩ ⟨d.1,y'.val⟩ at hold
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hold
  have hn : (UnarySource.source I).colour x y = (UnarySource.source I).colour x' y' := by
    apply Option.map_injective Subtype.val_injective
    change (Rank.colour S (β I) (tag I) x y).map Subtype.val =
      (Rank.colour S (β I) (tag I) x' y').map Subtype.val
    rw [Rank.colour_map,Rank.colour_map,hc]
  exact congrArg (fun a => (⟨c,d,a⟩ : Σ c, Σ d, Option ((UnarySource.source I).Atom c d))) hn

/-- Exact complete-type reflection with the literal child sorts fixed. -/
theorem sameType_of_old
    (B : FiniteInduced (X := Rank.Point (β I) (tag I))) (x y : NewPoint I)
    (hc : x.1 = y.1)
    (hold : RealAction.SameTypeOver S (oldBase I B) (oldEquiv I x) (oldEquiv I y)) :
    RealAction.SameTypeOver (UnarySource.source I) B x y := by
  refine ⟨tagged_colour_of_old I x x y y hc hc hold.1,?_,?_⟩
  · intro b hb
    exact tagged_colour_of_old I x b y b hc rfl
      (hold.2.1 (oldEquiv I b) ⟨b,hb,rfl⟩)
  · intro b hb
    exact tagged_colour_of_old I b x b y rfl hc
      (hold.2.2 (oldEquiv I b) ⟨b,hb,rfl⟩)

/-- Direct old-to-new type reflection in the SAME canonical actual source.
No new limit embedding, arbitrary homogeneous marking or SAP is assumed. -/
theorem sameTypeOver_of_old_and_mark
    (B : FiniteInduced (X := Rank.Point (β I) (tag I))) (x y : NewPoint I)
    (hold : RealAction.SameTypeOver S (oldBase I B) (oldEquiv I x) (oldEquiv I y))
    (hm : mark I (oldEquiv I x) = mark I (oldEquiv I y)) :
    RealAction.SameTypeOver (UnarySource.source I) B x y := by
  have hs : (oldEquiv I x).1 = (oldEquiv I y).1 :=
    congrArg (fun c : Age.Colour S => c.1) hold.1
  exact sameType_of_old I B x y (child_eq_of_old_and_mark I x y hs hm) hold

end
end CCO.PairSafeSplit.SAP
