import CCO.PairSafeSplit.Strong.Realization

/-! Actual occurring child atoms are exactly the original atoms permitted
by their endpoint-bit mask. This is a source construction, without SAP. -/

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

theorem occurring_atom_allowed {c d : Rank.Child (β I)} (a : (source I).Atom c d) :
    P.allows (some a.val) c.2.val d.2.val := by
  obtain ⟨x,y,hxy⟩ := a.property
  have hm := (global_marking I).2 (⟨c.1,x.val⟩ : Sigma X) ⟨d.1,y.val⟩
  have hx : mark I ⟨c.1,x.val⟩ = c.2.val := congrArg Subtype.val x.property
  have hy : mark I ⟨d.1,y.val⟩ = d.2.val := congrArg Subtype.val y.property
  rw [hxy,hx,hy] at hm
  exact hm

theorem atom_exists_of_allowed {c d : Rank.Child (β I)} (a : S.Atom c.1 d.1)
    (ha : P.allows (some a) c.2.val d.2.val) :
    ∃ b : (source I).Atom c d, b.val = a := by
  classical
  obtain ⟨x,y,hxy⟩ := S.realized a
  let point : Fin 2 → Sigma X := ![⟨c.1,x⟩,⟨d.1,y⟩]
  let bits : Fin 2 → Bit := ![c.2.val,d.2.val]
  have legal : Age.Legal S P.masks point bits := by
    constructor
    · intro i
      fin_cases i
      · exact c.2.property
      · exact d.2.property
    · intro i j
      fin_cases i <;> fin_cases j
      · change P.allows (S.colour x x) c.2.val c.2.val
        rw [(S.colour_none_iff x x).mpr rfl]
        exact (P.allows_identity c.1 _ _).mpr ⟨rfl,c.2.property⟩
      · change P.allows (S.colour x y) c.2.val d.2.val
        rw [hxy]
        exact ha
      · change P.allows (S.colour y x) d.2.val c.2.val
        rw [(S.colour_swap x y a).mp hxy]
        exact (P.allows_reverse a _ _).mp ha
      · change P.allows (S.colour y y) d.2.val d.2.val
        rw [(S.colour_none_iff y y).mpr rfl]
        exact (P.allows_identity d.1 _ _).mpr ⟨rfl,d.2.property⟩
  obtain ⟨f,ho,hc⟩ := embed_legal_tuple P cco I point bits legal
  have hs0 : (f 0).1 = c := childLabel_injective I (ho 0)
  have hs1 : (f 1).1 = d := childLabel_injective I (ho 1)
  let p : Rank.Point (β I) (tag I) c := cast
    (congrArg (Rank.Point (β I) (tag I)) hs0) (f 0).2
  let q : Rank.Point (β I) (tag I) d := cast
    (congrArg (Rank.Point (β I) (tag I)) hs1) (f 1).2
  have hp : (⟨c,p⟩ : NewPoint I) = f 0 := sigma_cast hs0 (f 0).2
  have hq : (⟨d,q⟩ : NewPoint I) = f 1 := sigma_cast hs1 (f 1).2
  have colour : taggedColour S (oldEquiv I (f 0)) (oldEquiv I (f 1)) =
      ⟨c.1,d.1,some a⟩ := by
    rw [hc]
    exact congrArg (fun a => (⟨c.1,d.1,a⟩ : Σ i, Σ j, Option (S.Atom i j))) hxy
  rw [← hp,← hq] at colour
  have hcol : S.colour p.val q.val = some a := by
    change taggedColour S ⟨c.1,p.val⟩ ⟨d.1,q.val⟩ = ⟨c.1,d.1,some a⟩ at colour
    simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using colour
  exact ⟨⟨a,p,q,hcol⟩,rfl⟩

theorem atom_exists_iff_allowed {c d : Rank.Child (β I)} (a : S.Atom c.1 d.1) :
    (∃ b : (source I).Atom c d, b.val = a) ↔ P.allows (some a) c.2.val d.2.val := by
  constructor
  · rintro ⟨b,rfl⟩
    exact occurring_atom_allowed P cco I b
  · exact atom_exists_of_allowed P cco I a

end
end CCO.PairSafeSplit.Strong.Realization
