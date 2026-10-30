import CCO.FullPhaseLift.BinarySource.MarkedComparisonTarget

/-! Equality of actual new tagged colours is exactly equality of the
literal old pair code and the two endpoint bits. This is the concrete
whole-pattern input for typed source-isomorphism construction. -/

universe m t v
namespace CCO.FullPhaseLift.BinarySource.MarkedComparison
open Canonical APCharacter OwnerTransversal.CountableColour RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section

theorem canonical_pattern_iff {L : Signature} {V : Type v}
    (E : BoolTable (Marked.addBit L) V) (hsym : SameSortSymmetric E) (x y z s : V) :
    taggedColour (Canonical.source E hsym) (Canonical.pack E x) (Canonical.pack E y) =
      taggedColour (Canonical.source E hsym) (Canonical.pack E z) (Canonical.pack E s) ↔
    (codeTable (Marked.oldTable E) (Marked.bits E)).owner x =
        (codeTable (Marked.oldTable E) (Marked.bits E)).owner z ∧
    (codeTable (Marked.oldTable E) (Marked.bits E)).owner y =
        (codeTable (Marked.oldTable E) (Marked.bits E)).owner s ∧
    (codeTable (Marked.oldTable E) (Marked.bits E)).colour x y =
        (codeTable (Marked.oldTable E) (Marked.bits E)).colour z s := by
  have hcode :
      taggedColour (Canonical.source E hsym) (Canonical.pack E x) (Canonical.pack E y) =
        taggedColour (Canonical.source E hsym) (Canonical.pack E z) (Canonical.pack E s) ↔
      pairNameCode E x y = pairNameCode E z s := by
    constructor
    · intro h
      simpa only [tagCode_pack_eq_pairNameCode] using congrArg (tagCode E) h
    · intro h
      apply tagCode_injective E
      simpa only [tagCode_pack_eq_pairNameCode] using h
  rw [hcode]
  have h := marked_pairNameCode_eq_iff (Marked.oldTable E) (Marked.oldTable E)
    (Marked.bits E) (Marked.bits E) x y z s
  rw [Marked.table_oldTable_bits] at h
  rw [h]
  constructor
  · rintro ⟨hc,hx,hy⟩
    refine ⟨?_,?_,hc⟩
    · change (unaryProfile (Marked.oldTable E) x,Marked.bits E x) =
        (unaryProfile (Marked.oldTable E) z,Marked.bits E z)
      exact Prod.ext (congrArg (fun c : Profile L 1 × Profile L 1 × Option (Profile L 2) => c.1) hc) hx
    · change (unaryProfile (Marked.oldTable E) y,Marked.bits E y) =
        (unaryProfile (Marked.oldTable E) s,Marked.bits E s)
      exact Prod.ext (congrArg (fun c : Profile L 1 × Profile L 1 × Option (Profile L 2) => c.2.1) hc) hy
  · rintro ⟨hx,hy,hc⟩
    exact ⟨hc,congrArg Prod.snd hx,congrArg Prod.snd hy⟩

variable {L : Signature} {M : Type m} (U : BoolTable L M) (hsym : SameSortSymmetric U)
variable {G : Type t} [Group G] [∀ i, MulAction G (Canonical.Carrier U i)]
variable {H : HomogeneousSource (Canonical.source U hsym) G}
variable {C : ExactCalculus (Canonical.source U hsym)} {a : UnaryName U}
variable {K : Kernel (Canonical.source U hsym) a}
variable (P : SourcePhase (Canonical.source U hsym) H C K)
variable (cco : SemanticCCO.{0,m,m,0} (Canonical.source U hsym))
variable (I : Identification (Canonical.source U hsym) H (P.completion_property cco))

theorem target_pattern_iff (p q r s : NewPoint I) :
    taggedColour (APCharacter.SourceAge.UnarySource.source I) p q =
      taggedColour (APCharacter.SourceAge.UnarySource.source I) r s ↔
    (targetTable U hsym P cco I).owner p = (targetTable U hsym P cco I).owner r ∧
    (targetTable U hsym P cco I).owner q = (targetTable U hsym P cco I).owner s ∧
    (targetTable U hsym P cco I).colour p q = (targetTable U hsym P cco I).colour r s := by
  constructor
  · intro h
    have hp := congrArg (fun c : Σ i, Σ j, Option ((APCharacter.SourceAge.UnarySource.source I).Atom i j) => c.1) h
    have hq := congrArg (fun c : Σ i, Σ j, Option ((APCharacter.SourceAge.UnarySource.source I).Atom i j) => c.2.1) h
    change p.1 = r.1 at hp
    change q.1 = s.1 at hq
    refine ⟨?_,?_,?_⟩
    · rw [target_owner,target_owner,hp]
    · rw [target_owner,target_owner,hq]
    · have old := congrArg (eraseColour I) h
      rw [erase_tagged,erase_tagged] at old
      rw [target_colour,target_colour,old]
  · rintro ⟨hp,hq,hc⟩
    have hs1 := childLabel_injective I (childLabel_of_target_owner U hsym P cco I hp)
    have hs2 := childLabel_injective I (childLabel_of_target_owner U hsym P cco I hq)
    have hold := oldColours_of_target_colour U hsym P cco I hc
    rcases p with ⟨c,x⟩
    rcases q with ⟨d,y⟩
    rcases r with ⟨e,z⟩
    rcases s with ⟨f,s⟩
    change c = e at hs1
    change d = f at hs2
    subst e
    subst f
    change taggedColour (Canonical.source U hsym) ⟨c.1,x.val⟩ ⟨d.1,y.val⟩ =
      taggedColour (Canonical.source U hsym) ⟨c.1,z.val⟩ ⟨d.1,s.val⟩ at hold
    have hcol : (Canonical.source U hsym).colour x.val y.val =
        (Canonical.source U hsym).colour z.val s.val := by
      simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hold
    have hnew : (APCharacter.SourceAge.UnarySource.source I).colour x y =
        (APCharacter.SourceAge.UnarySource.source I).colour z s := by
      apply Option.map_injective Subtype.val_injective
      change (Rank.colour (Canonical.source U hsym) (β I) (tag I) x y).map Subtype.val =
        (Rank.colour (Canonical.source U hsym) (β I) (tag I) z s).map Subtype.val
      rw [Rank.colour_map,Rank.colour_map,hcol]
    exact congrArg (fun a => (⟨c,d,a⟩ : Σ c, Σ d,
      Option ((APCharacter.SourceAge.UnarySource.source I).Atom c d))) hnew

end
end CCO.FullPhaseLift.BinarySource.MarkedComparison
