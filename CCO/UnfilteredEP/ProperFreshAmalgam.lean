import CCO.UnfilteredEP.ProperFiniteClosure

/-! C61, unordered stage: genuine proper hidden SAP glues over the
ENTIRE specified closed base, and its intersection clause makes any
off-base witness point fresh over the whole original member. Ordered
shuffle compatibility remains a separate source obligation. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnarySupport
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

def properClosedInclusion {P D : Set (Values B)}
    (hP : (Target B ht).IsClosed P) (hD : (Target B ht).IsClosed D)
    (hPD : P ⊆ D) :
    ((Target B ht).induce P hP).Embedding ((Target B ht).induce D hD) where
  point x := ⟨x.val,hPD x.property⟩
  sort_eq _ := rfl
  map_func _ _ _ h := h
  map_rel _ _ h := h
  injective x y h := by
    apply Subtype.ext
    exact congrArg (fun p : D => p.val) h
  reflect_func F x y hy := ⟨⟨y.val,hP F x.val x.property hy⟩,hy,rfl⟩
  reflect_rel _ _ h := h

/-- The point is fresh over ALL of D, not merely different from the
two distinguished endpoints or from a selected chart subset. -/
theorem proper_hidden_fresh_amalgam
    (P D T : Set (Values B))
    (hP : (Target B ht).IsClosed P) (hD : (Target B ht).IsClosed D)
    (hT : (Target B ht).IsClosed T) (hPD : P ⊆ D) (hPT : P ⊆ T)
    (finiteD : D.Finite) (finiteT : T.Finite)
    (properD : ∀ x ∈ D, ProperSort B ht ((Target B ht).sort x))
    (properT : ∀ x ∈ T, ProperSort B ht ((Target B ht).sort x))
    (z : T) (hz : z.val ∉ P) :
    ∃ (V : Type (max u v)) (_ : Finite V)
      (C : Structure (Sig B ht) V), ProperAge B ht C ∧
      ∃ (f : ((Target B ht).induce D hD).Embedding C)
        (g : ((Target B ht).induce T hT).Embedding C),
        (∀ p : P, f.point ⟨p.val,hPD p.property⟩ = g.point ⟨p.val,hPT p.property⟩) ∧
        g.point z ∉ Set.range f.point := by
  have hAD : ProperAge B ht ((Target B ht).induce D hD) :=
    ⟨CCO.TerminalHiddenHN.actualAge_of_closed
      (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht) D finiteD hD,
      fun x => properD x.val x.property⟩
  have hAT : ProperAge B ht ((Target B ht).induce T hT) :=
    ⟨CCO.TerminalHiddenHN.actualAge_of_closed
      (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht) T finiteT hT,
      fun x => properT x.val x.property⟩
  obtain ⟨V,hV,C,hC,f,g,hcomm,hstrong⟩ := (proper_hidden_age_sap B ht).strong hAD hAT
    (properClosedInclusion B ht hP hD hPD) (properClosedInclusion B ht hP hT hPT)
  refine ⟨V,hV,C,hC,f,g,hcomm,?_⟩
  rintro ⟨d,hd⟩
  obtain ⟨p,_,hp⟩ := hstrong d z hd
  exact hz ((congrArg Subtype.val hp) ▸ p.property)

end
end CCO.UnfilteredEP
