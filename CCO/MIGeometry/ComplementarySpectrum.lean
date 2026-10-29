import CCO.MIGeometry.Spectrum
import CCO.ExactCRT.FineColourReadout

/-! Actual CRT realization of every fine lift. Pair-orbital readout is
proved independently from the set-theoretic CRT used for the vertices. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
open RawExact ExactCRT FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{0,v,0,w} S)
variable (C K : ColourEq S ())
include H cco

/-- Two actual quotient pair colours determine the literal original fine
colour when the exact kernels have trivial intersection. -/
theorem complementary_pair_readout (hC : IsExactEq S (i := ()) C.val)
    (hK : IsExactEq S (i := ()) K.val) (hCK : C.val ⊓ K.val = ⊥)
    (a b x y : M)
    (hY : col (actualQuotientSource S H C) (Quotient.mk'' a) (Quotient.mk'' b) =
      col (actualQuotientSource S H C) (Quotient.mk'' x) (Quotient.mk'' y))
    (hX : col (actualQuotientSource S H K) (Quotient.mk'' a) (Quotient.mk'' b) =
      col (actualQuotientSource S H K) (Quotient.mk'' x) (Quotient.mk'' y)) :
    col S a b = col S x y := by
  letI := originalQuotientAction S H C
  letI := originalQuotientAction S H K
  let E : Bool → ExactEq S H (semanticCCO_change_universe S cco) ()
    | false => ⟨C.val,hC⟩ | true => ⟨K.val,hK⟩
  have read := two_factor_saturated_colour_readout S H (semanticCCO_change_universe S cco)
    (E false) (E true) (col S a b)
  have sat (F : ColourEq S ())
      (hh : col (actualQuotientSource S H F) (Quotient.mk'' a) (Quotient.mk'' b) =
        col (actualQuotientSource S H F) (Quotient.mk'' x) (Quotient.mk'' y)) :
      saturate F.val.r (S.rawAtomRel (col S a b)) F.val.r x y := by
    letI := originalQuotientAction S H F
    obtain ⟨g,hgx,hgy⟩ := (actualQuotientSource_colour_orbital S H F _ _ _ _).mp hh
    have hx : F x (g • a) := Quotient.exact hgx.symm
    have hy : F (g • b) y := Quotient.exact hgy
    exact ⟨g • b,⟨g • a,hx,col_invariant S H g a b⟩,hy⟩
  have hs := (Iff.of_eq (congrFun (congrFun read x) y)).mpr ⟨sat C hY,sat K hX⟩
  change saturate (C.val ⊓ K.val).r (S.rawAtomRel (col S a b)) (C.val ⊓ K.val).r x y at hs
  rw [hCK] at hs
  rcases hs with ⟨v,⟨u,hu,hcol⟩,hv⟩
  cases hu
  cases hv
  exact hcol.symm

/-- C11: EVERY old fine pair above the recipient orbital is realized in
the single full helper. The two helper points may coincide. -/
theorem complementary_spectrum (hC : IsExactEq S (i := ()) C.val)
    (hK : IsExactEq S (i := ()) K.val) (hCK : C.val ⊓ K.val = ⊥)
    (B : Finset (Quotient (C.val ⊔ K.val))) (P : Finset (Quotient K.val))
    (spectrum : OwnerSpectrum (actualQuotientSource S H K)
      (Abstract.quotientMap (show K.val ≤ C.val ⊔ K.val from le_sup_right)) B P)
    (y y' : Quotient C.val)
    (hy : Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) y ∈ B)
    (hy' : Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) y' ∈ B)
    (u v : M)
    (hcol : col (actualQuotientSource S H C) (Quotient.mk'' u) (Quotient.mk'' v) =
      col (actualQuotientSource S H C) y y') :
    ∃ x x' : M, (Quotient.mk'' x : Quotient C.val) = y ∧
      (Quotient.mk'' x' : Quotient C.val) = y' ∧
      (Quotient.mk'' x : Quotient K.val) ∈ P ∧
      (Quotient.mk'' x' : Quotient K.val) ∈ P ∧ col S x x' = col S u v := by
  letI := originalQuotientAction S H C
  letI := originalQuotientAction S H K
  obtain ⟨g,hgu,hgv⟩ := (actualQuotientSource_colour_orbital S H C _ _ _ _).mp hcol
  change (Quotient.mk'' (g • u) : Quotient C.val) = y at hgu
  change (Quotient.mk'' (g • v) : Quotient C.val) = y' at hgv
  let t := Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) y
  let t' := Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left) y'
  have hu : Abstract.quotientMap (show K.val ≤ C.val ⊔ K.val from le_sup_right)
      (Quotient.mk'' (g • u)) = t := congrArg
    (Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left)) hgu
  have hv : Abstract.quotientMap (show K.val ≤ C.val ⊔ K.val from le_sup_right)
      (Quotient.mk'' (g • v)) = t' := congrArg
    (Abstract.quotientMap (show C.val ≤ C.val ⊔ K.val from le_sup_left)) hgv
  obtain ⟨p,hp,p',hp',hpt,hpt',hpair⟩ := spectrum.2.2 t hy t' hy'
    (Quotient.mk'' (g • u)) (Quotient.mk'' (g • v)) hu hv
  let a : Abstract.FibreProduct C.val K.val := ⟨(y,p),hpt.symm⟩
  let b : Abstract.FibreProduct C.val K.val := ⟨(y',p'),hpt'.symm⟩
  let x := (realFibreProductEquiv S H C K hCK).symm a
  let x' := (realFibreProductEquiv S H C K hCK).symm b
  have hx := congrArg Subtype.val ((realFibreProductEquiv S H C K hCK).apply_symm_apply a)
  have hx' := congrArg Subtype.val ((realFibreProductEquiv S H C K hCK).apply_symm_apply b)
  have hxC : (Quotient.mk'' x : Quotient C.val) = y := congrArg Prod.fst hx
  have hxK : (Quotient.mk'' x : Quotient K.val) = p := congrArg Prod.snd hx
  have hxC' : (Quotient.mk'' x' : Quotient C.val) = y' := congrArg Prod.fst hx'
  have hxK' : (Quotient.mk'' x' : Quotient K.val) = p' := congrArg Prod.snd hx'
  refine ⟨x,x',hxC,hxC',hxK.symm ▸ hp,hxK'.symm ▸ hp',?_⟩
  have hyPair : col (actualQuotientSource S H C) (Quotient.mk'' (g • u))
      (Quotient.mk'' (g • v)) = col (actualQuotientSource S H C) (Quotient.mk'' x) (Quotient.mk'' x') := by
    rw [hgu,hgv,hxC,hxC']
  have hxPair : col (actualQuotientSource S H K) (Quotient.mk'' (g • u))
      (Quotient.mk'' (g • v)) = col (actualQuotientSource S H K) (Quotient.mk'' x) (Quotient.mk'' x') := by
    rw [hxK,hxK']
    exact hpair.symm
  exact (complementary_pair_readout S H cco C K hC hK hCK _ _ _ _ hyPair hxPair).symm.trans
    (col_invariant S H g u v)

end CCO.MIGeometry
