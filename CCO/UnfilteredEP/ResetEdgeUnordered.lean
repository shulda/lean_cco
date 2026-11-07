import CCO.UnfilteredEP.ResetPairWitness
import CCO.UnaryFreshFrames.ClosureActions

/-! The unordered part of C37-C42: one complete quotient orbital fixes
the ENTIRE pointed generated diagram. The two distinguished endpoints
are retained. Normalized order comparisons are a separate conclusion. -/

universe u v w a b
namespace CCO.UnfilteredEP
noncomputable section

section General
open CCO.UnaryFreshFrames CCO.HiddenSAPReadings
variable {L : Language.{a}} [Finite L.Sorts] [Finite L.Func] [Finite L.Rel]
variable {V : Type b} (M : Structure L V)

def partialAutIso (g : M.Aut) :
    CCO.UnarySupport.Structure.DiagramIso (partialTarget M) (partialTarget M) where
  equiv := g.val
  sort_eq x := M.aut_sort g x
  func_iff F x y := by
    classical
    change ((g • y) ∈ if M.sort (g • x) = L.input F then {M.func F (g • x)} else ∅) ↔
      (y ∈ if M.sort x = L.input F then {M.func F x} else ∅)
    rw [M.aut_sort g x]
    by_cases hs : M.sort x = L.input F
    · simp only [hs,if_pos,Set.mem_singleton_iff]
      rw [← M.aut_func g F x]
      exact g.val.injective.eq_iff
    · simp only [hs,ite_false,Set.mem_empty_iff_false]
  rel_iff R xs := M.aut_rel g R xs

def partialPairClosure (x y : V) :=
  (partialTarget M).induce (M.closure {x,y})
    ((partialTarget_closed_iff M _).mpr (M.closure_closed _))

def partialPairClosureIso (g : M.Aut) (x y x' y' : V)
    (hx : g • x = x') (hy : g • y = y') :
    CCO.UnarySupport.Structure.DiagramIso
      (partialPairClosure M x y) (partialPairClosure M x' y') where
  equiv := {
    toFun z := ⟨g • z.val,by
      have h := M.aut_mem_closure g z.property
      simpa only [Set.image_insert_eq,Set.image_singleton,hx,hy] using h⟩
    invFun z := ⟨g⁻¹ • z.val,by
      have hx' : g⁻¹ • x' = x := by rw [← hx,inv_smul_smul]
      have hy' : g⁻¹ • y' = y := by rw [← hy,inv_smul_smul]
      have h := M.aut_mem_closure g⁻¹ z.property
      simpa only [Set.image_insert_eq,Set.image_singleton,hx',hy'] using h⟩
    left_inv z := Subtype.ext (inv_smul_smul g z.val)
    right_inv z := Subtype.ext (smul_inv_smul g z.val) }
  sort_eq z := M.aut_sort g z.val
  func_iff F z t := (partialAutIso M g).func_iff F z.val t.val
  rel_iff R xs := (partialAutIso M g).rel_iff R (Subtype.val ∘ xs)

@[simp] theorem partialPairClosureIso_point (g : M.Aut) (x y x' y' : V)
    (hx : g • x = x') (hy : g • y = y') (z) :
    ((partialPairClosureIso M g x y x' y' hx hy).equiv z).val = g • z.val := rfl

end General

section Actual
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.UnaryTermsReturn CCO.TerminalLattice
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

theorem actual_reset_pairs_move {i : B.Sorts} (J : FullCloneProperMI B.source i)
    (m : ActualResetMenu B J) (q t q' t' : Quotient J.val.val)
    (hqt : m.relation q t) (hq't' : m.relation q' t') :
    letI : MulAction (ResetGroup B) (Quotient J.val.val) :=
      originalQuotientAction (cloneSource B) (cloneHomogeneous B) J.val
    ∃ g : ResetGroup B, g • q = q' ∧ g • t = t' := by
  letI : MulAction (ResetGroup B) (Quotient J.val.val) :=
    originalQuotientAction (cloneSource B) (cloneHomogeneous B) J.val
  obtain ⟨g,hgq,hgt⟩ := hqt
  obtain ⟨h,hhq,hht⟩ := hq't'
  have hgq' : g • Quotient.mk J.val.val m.first = q := hgq
  have hgt' : g • Quotient.mk J.val.val m.second = t := hgt
  have hhq' : h • Quotient.mk J.val.val m.first = q' := hhq
  have hht' : h • Quotient.mk J.val.val m.second = t' := hht
  refine ⟨h*g⁻¹,?_,?_⟩
  · rw [mul_smul,← hgq',inv_smul_smul]
    exact hhq'
  · rw [mul_smul,← hgt',inv_smul_smul]
    exact hht'

theorem actual_reset_hidden_pairs_move {i : B.Sorts} (J : FullCloneProperMI B.source i)
    (m : ActualResetMenu B J) (q t q' t' : Quotient J.val.val)
    (hqt : m.relation q t) (hq't' : m.relation q' t') :
    ∃ g : (Hidden B ht).Aut,
      g • coordinateNode B ht J q = coordinateNode B ht J q' ∧
      g • coordinateNode B ht J t = coordinateNode B ht J t' := by
  letI : MulAction (ResetGroup B) (Quotient J.val.val) :=
    originalQuotientAction (cloneSource B) (cloneHomogeneous B) J.val
  obtain ⟨g,hgq,hgt⟩ := actual_reset_pairs_move B J m q t q' t' hqt hq't'
  let motion := CCO.TypedOrbitFrames.originalCompletedMotionHom (cloneSource B) (HF B)
    (cloneSAP B) (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) g
  have hn (a : Quotient J.val.val) :
      motion • coordinateNode B ht J a = coordinateNode B ht J (g • a) := by
    induction a using Quotient.inductionOn with | _ x => rfl
  exact ⟨motion,(hn q).trans (congrArg (coordinateNode B ht J) hgq),
    (hn t).trans (congrArg (coordinateNode B ht J) hgt)⟩

/-- One complete m orbital gives isomorphic WHOLE unexpanded pair
closures, by a single actual source automorphism fixing the two marks. -/
theorem actual_reset_unordered_pointed_type {i : B.Sorts} (J : FullCloneProperMI B.source i)
    (m : ActualResetMenu B J) (q t q' t' : Quotient J.val.val)
    (hqt : m.relation q t) (hq't' : m.relation q' t') :
    ∃ g : (Hidden B ht).Aut,
      ∃ e : CCO.UnarySupport.Structure.DiagramIso
        (partialPairClosure (Hidden B ht) (coordinateNode B ht J q) (coordinateNode B ht J t))
        (partialPairClosure (Hidden B ht) (coordinateNode B ht J q') (coordinateNode B ht J t')),
        (∀ z, (e.equiv z).val = g • z.val) ∧
        g • coordinateNode B ht J q = coordinateNode B ht J q' ∧
        g • coordinateNode B ht J t = coordinateNode B ht J t' := by
  obtain ⟨g,hgq,hgt⟩ := actual_reset_hidden_pairs_move B ht J m q t q' t' hqt hq't'
  exact ⟨g,partialPairClosureIso (Hidden B ht) g _ _ _ _ hgq hgt,fun _ => rfl,hgq,hgt⟩

end Actual
end
end CCO.UnfilteredEP
