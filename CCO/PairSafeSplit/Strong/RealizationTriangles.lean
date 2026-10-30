import CCO.PairSafeSplit.Strong.Realization

/-! Actual old triple readout over fixed endpoints in the whole child source.
All three optional pair colours, including equality, are retained. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong.Realization
open APCharacter RigidGroupoid.Geometry
open APCharacter.SourceAge.UnarySource
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (I : Identification S H (P.completion_property cco))

theorem allows_pair_reverse (p q : Sigma X) (ε η : Bit)
    (h : P.allows (S.colour p.2 q.2) ε η) :
    P.allows (S.colour q.2 p.2) η ε := by
  cases hc : S.colour p.2 q.2 with
  | none =>
    have he : p = q := (S.colour_none_iff p.2 q.2).mp hc
    subst q
    rw [hc] at h ⊢
    obtain ⟨he,hε⟩ := (P.allows_identity p.1 ε η).mp h
    subst η
    exact h
  | some a =>
    rw [(S.colour_swap p.2 q.2 a).mp hc]
    exact (P.allows_reverse a ε η).mp (by rwa [hc] at h)

/-- Every legal old two-step witness has an actual midpoint of the
specified child sort over these SAME actual endpoints. There is no
distinctness assumption and no old or new SAP hypothesis. -/
theorem midpoint_readout {c d e : Rank.Child (β I)}
    (x : Rank.Point (β I) (tag I) c) (z : Rank.Point (β I) (tag I) e)
    (y : X d.1)
    (hxy : P.allows (S.colour x.val y) c.2.val d.2.val)
    (hyz : P.allows (S.colour y z.val) d.2.val e.2.val) :
    ∃ y' : Rank.Point (β I) (tag I) d,
      S.colour x.val y'.val = S.colour x.val y ∧
      S.colour y'.val z.val = S.colour y z.val := by
  classical
  have hxz : P.allows (S.colour x.val z.val) c.2.val e.2.val := by
    have h := (global_marking I).2 (⟨c.1,x.val⟩ : Sigma X) ⟨e.1,z.val⟩
    have hx : mark I ⟨c.1,x.val⟩ = c.2.val := congrArg Subtype.val x.property
    have hz : mark I ⟨e.1,z.val⟩ = e.2.val := congrArg Subtype.val z.property
    rwa [hx,hz] at h
  let point : Fin 3 → Sigma X := ![⟨c.1,x.val⟩,⟨d.1,y⟩,⟨e.1,z.val⟩]
  let bits : Fin 3 → Bit := ![c.2.val,d.2.val,e.2.val]
  have legal : Age.Legal S P.masks point bits := by
    constructor
    · intro i
      fin_cases i
      · exact c.2.property
      · exact d.2.property
      · exact e.2.property
    · intro i j
      fin_cases i <;> fin_cases j
      · change P.allows (S.colour x.val x.val) c.2.val c.2.val
        rw [(S.colour_none_iff x.val x.val).mpr rfl]
        exact (P.allows_identity c.1 _ _).mpr ⟨rfl,c.2.property⟩
      · exact hxy
      · exact hxz
      · exact allows_pair_reverse P ⟨c.1,x.val⟩ ⟨d.1,y⟩ _ _ hxy
      · change P.allows (S.colour y y) d.2.val d.2.val
        rw [(S.colour_none_iff y y).mpr rfl]
        exact (P.allows_identity d.1 _ _).mpr ⟨rfl,d.2.property⟩
      · exact hyz
      · exact allows_pair_reverse P ⟨c.1,x.val⟩ ⟨e.1,z.val⟩ _ _ hxz
      · exact allows_pair_reverse P ⟨d.1,y⟩ ⟨e.1,z.val⟩ _ _ hyz
      · change P.allows (S.colour z.val z.val) e.2.val e.2.val
        rw [(S.colour_none_iff z.val z.val).mpr rfl]
        exact (P.allows_identity e.1 _ _).mpr ⟨rfl,e.2.property⟩
  let j : Fin 2 → Fin 3 := ![0,2]
  let p : Fin 2 → NewPoint I := ![⟨c,x⟩,⟨e,z⟩]
  have hpOwner : ∀ i, childLabel I (p i).1 = ((point (j i)).1,bits (j i)) := by
    intro i
    fin_cases i <;> rfl
  have hpColour : ∀ i k, taggedColour S (oldEquiv I (p i)) (oldEquiv I (p k)) =
      taggedColour S (point (j i)) (point (j k)) := by
    intro i k
    fin_cases i <;> fin_cases k <;> rfl
  obtain ⟨f,ho,hc,he⟩ := align_legal_tuple P cco I point bits legal j p hpOwner hpColour
  have hs : (f 1).1 = d := childLabel_injective I (ho 1)
  let y' : Rank.Point (β I) (tag I) d := cast
    (congrArg (Rank.Point (β I) (tag I)) hs) (f 1).2
  have hy' : (⟨d,y'⟩ : NewPoint I) = f 1 := sigma_cast hs (f 1).2
  have he0 : f 0 = (⟨c,x⟩ : NewPoint I) := he 0
  have he2 : f 2 = (⟨e,z⟩ : NewPoint I) := he 1
  refine ⟨y',?_,?_⟩
  · have hh := hc 0 1
    rw [he0,← hy'] at hh
    change taggedColour S ⟨c.1,x.val⟩ ⟨d.1,y'.val⟩ =
      taggedColour S ⟨c.1,x.val⟩ ⟨d.1,y⟩ at hh
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hh
  · have hh := hc 1 2
    rw [← hy',he2] at hh
    change taggedColour S ⟨d.1,y'.val⟩ ⟨e.1,z.val⟩ =
      taggedColour S ⟨d.1,y⟩ ⟨e.1,z.val⟩ at hh
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hh

end
end CCO.PairSafeSplit.Strong.Realization
