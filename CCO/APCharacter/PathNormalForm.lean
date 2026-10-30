import CCO.APCharacter.Calculus

/-! Exact formal endpoint supports, using typed converse rotation. These
are OLD represented relations intersected with masks, not an assumed marked
age product or a pre-existing homogeneous marked source. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
namespace MaskData
variable (M : MaskData S) (laws : M.Calculus)

def masked {i j : ι} (R : TRel X i j) (ε η : Bit) : TRel X i j :=
  fun x y => R x y ∧ M.allowed (S.colour x y) ε η

include H C laws in
theorem masked_step {i j k : ι} (R : TRel X i j) (hR : FullExact S R)
    (b : S.Atom j k) (ε η θ : Bit)
    (hv : M.validBit i ε) (hw : M.validBit j η) (hz : M.validBit k θ)
    (hb : M.allowed (some b) η θ)
    (hAllowedR : ∃ x y, R x y ∧ M.allowed (S.colour x y) ε η) :
    M.masked (TRel.comp (M.masked R ε η) (S.atomRel b)) ε θ =
      M.masked (TRel.comp R (S.atomRel b)) ε θ := by
  funext x z
  apply propext
  constructor
  · rintro ⟨⟨y,hxy,hyz⟩,hc⟩
    exact ⟨⟨y,hxy.1,hyz⟩,hc⟩
  · rintro ⟨⟨y,hxy,hyz⟩,hc⟩
    let c := S.colour x z
    let T := TRel.comp (S.rawAtomRel c) (S.atomRel (S.conv b))
    have hB : FullExact S (S.atomRel (S.conv b)) := by
      obtain ⟨p,q,hpq⟩ := S.realized (S.conv b)
      have h := fullExact_actual_atom S p q
      rw [hpq] at h
      exact h
    have hT : FullExact S T := C.comp (fullExact_actual_atom S x z) hB
    have hyb : S.atomRel (S.conv b) z y := (S.colour_swap y z b).mp hyz
    obtain ⟨DR,hDR⟩ := hR
    obtain ⟨DT,hDT⟩ := hT
    have hab : TRel.Nonempty (fun a d => ∀ e ∈ [DR,DT], RawExact.evaluate S e.words a d) := by
      refine ⟨x,y,?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rw [hDR]; exact hxy
      · have he' : e = DT := by simpa using he
        subst e
        rw [hDT]
        exact ⟨z,rfl,hyb⟩
    have htMask : ∃ a d, T a d ∧ M.allowed (S.colour a d) ε η := by
      obtain ⟨p,q,hpq⟩ := S.realized (S.conv b)
      exact laws.totality c (some (S.conv b)) ε θ η hv hz hw hc
        ((M.reverse b η θ).mp hb) ⟨x,z,rfl⟩ ⟨p,q,hpq⟩
    obtain ⟨a,d,hAll,hMask⟩ := laws.primality [DR,DT] ε η hv hw hab (by
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · simpa only [hDR] using hAllowedR
      · have he' : e = DT := by simpa using he
        subst e
        simpa only [hDT] using htMask)
    have hRa : R a d := by rw [← hDR]; exact hAll DR (by simp)
    have hTa : T a d := by rw [← hDT]; exact hAll DT (by simp)
    obtain ⟨z',haz',hdz'⟩ := hTa
    have hcol : S.colour a z' = S.colour x z := haz'
    obtain ⟨g,hga,hgz⟩ := (S.pair_homogeneous_of_homogeneous H) a x z' z hcol
    have hRd : R x (g • d) := by
      simpa only [hga] using (FullExact.invariant S H ⟨DR,hDR⟩) g a d hRa
    have hMask' : M.allowed (S.colour x (g • d)) ε η := by
      have he : S.colour x (g • d) = S.colour a d := by
        rw [← hga]
        exact S.colourInvariant_of_homogeneous H g a d
      rw [he]
      exact hMask
    have hbd : S.atomRel b (g • d) z := by
      have he : S.colour z' d = some (S.conv b) := hdz'
      have hdb : S.colour d z' = some b := by
        have hh := (S.colour_swap z' d (S.conv b)).mp he
        simpa only [S.conv_invol] using hh
      have hh := (S.colourInvariant_of_homogeneous H g d z').trans hdb
      simpa only [AtomicSource.atomRel,hgz] using hh
    exact ⟨⟨g • d,⟨hRd,hMask'⟩,hbd⟩,hc⟩

include H C laws in
theorem masked_step_nonempty {i j k : ι} (R : TRel X i j) (hR : FullExact S R)
    (b : S.Atom j k) (ε η θ : Bit)
    (hv : M.validBit i ε) (hw : M.validBit j η) (hz : M.validBit k θ)
    (hb : M.allowed (some b) η θ)
    (hAllowedR : ∃ x y, R x y ∧ M.allowed (S.colour x y) ε η) :
    TRel.Nonempty (M.masked (TRel.comp (M.masked R ε η) (S.atomRel b)) ε θ) := by
  obtain ⟨x,y,hxy,hc⟩ := hAllowedR
  obtain ⟨a,d,had⟩ := S.realized b
  obtain ⟨x',z,⟨y',hx'y',hy'z⟩,ho⟩ := laws.totality (S.colour x y) (some b)
    ε η θ hv hw hz hc hb ⟨x,y,rfl⟩ ⟨a,d,had⟩
  obtain ⟨g,hgx,hgy⟩ := (S.pair_homogeneous_of_homogeneous H) x x' y y' hx'y'.symm
  have hR' : R x' y' := by simpa only [hgx,hgy] using hR.invariant S H g x y hxy
  have hc' : M.allowed (S.colour x' y') ε η := by rw [hx'y']; exact hc
  exact ⟨x',z,⟨⟨y',⟨hR',hc'⟩,hy'z⟩,ho⟩⟩

inductive Prefix : {i j : ι} → Bit → Bit → Type (max u w) where
  | edge {i j : ι} {ε η : Bit} (a : S.Atom i j)
      (start : M.validBit i ε) (finish : M.validBit j η)
      (allowed : M.allowed (some a) ε η) : Prefix (i := i) (j := j) ε η
  | snoc {i j k : ι} {ε η θ : Bit} (p : Prefix (i := i) (j := j) ε η)
      (a : S.Atom j k) (finish : M.validBit k θ)
      (allowed : M.allowed (some a) η θ) : Prefix (i := i) (j := k) ε θ

namespace Prefix
variable {M}
def word {i j : ι} {ε η : Bit} : M.Prefix (i := i) (j := j) ε η → RawWord S i j
  | .edge a _ _ _ => .atom a (.nil _)
  | .snoc p a _ _ => RawWord.append S p.word (.atom a (.nil _))

def support {i j : ι} {ε η : Bit} : M.Prefix (i := i) (j := j) ε η → TRel X i j
  | .edge a _ _ _ => S.atomRel a
  | .snoc p a _ _ => M.masked (TRel.comp p.support (S.atomRel a)) ε η

theorem valid_start {i j : ι} {ε η : Bit} (p : M.Prefix (i := i) (j := j) ε η) : M.validBit i ε := by
  induction p with
  | edge _ h _ _ => exact h
  | snoc _ _ _ _ ih => exact ih

theorem valid_end {i j : ι} {ε η : Bit} (p : M.Prefix (i := i) (j := j) ε η) : M.validBit j η := by
  cases p with
  | edge _ _ h _ => exact h
  | snoc _ _ h _ => exact h

include C in
theorem word_exact {i j : ι} {ε η : Bit} (p : M.Prefix (i := i) (j := j) ε η) :
    FullExact S (RawWord.relation S p.word) := by
  induction p with
  | edge a _ _ _ =>
    obtain ⟨x,y,hxy⟩ := S.realized a
    have h := fullExact_actual_atom S x y
    rw [hxy] at h
    change FullExact S (S.atomRel a) at h
    simpa only [word,RawWord.relation,TRel.comp_ident] using h
  | snoc p a _ _ ih =>
    obtain ⟨x,y,hxy⟩ := S.realized a
    have h := fullExact_actual_atom S x y
    rw [hxy] at h
    change FullExact S (S.atomRel a) at h
    simpa only [word,RawWord.relation_append,RawWord.relation,TRel.comp_ident] using C.comp ih h

include H C laws in
theorem normal_form {i j : ι} {ε η : Bit} (p : M.Prefix (i := i) (j := j) ε η) :
    p.support = M.masked (RawWord.relation S p.word) ε η ∧ TRel.Nonempty p.support := by
  induction p with
  | @edge j ε η a hv hw ha =>
    constructor
    · funext x y
      apply propext
      constructor
      · intro hxy
        refine ⟨by simpa only [support,word,RawWord.relation,TRel.comp_ident] using hxy,?_⟩
        change S.colour x y = some a at hxy
        rw [hxy]
        exact ha
      · intro hxy
        simpa only [support,word,RawWord.relation,TRel.comp_ident] using hxy.1
    · exact S.realized a
  | @snoc j k ε η θ p a hz ha ih =>
    have hSome : ∃ x y, RawWord.relation S p.word x y ∧ M.allowed (S.colour x y) ε η := by
      obtain ⟨x,y,hxy⟩ := ih.2
      rw [ih.1] at hxy
      exact ⟨x,y,hxy⟩
    constructor
    · change M.masked (TRel.comp p.support (S.atomRel a)) ε θ = _
      rw [ih.1,M.masked_step H C laws _ (p.word_exact C) a ε η θ p.valid_start p.valid_end hz ha hSome]
      simp only [word,RawWord.relation_append,RawWord.relation,TRel.comp_ident]
    · change TRel.Nonempty (M.masked (TRel.comp p.support (S.atomRel a)) ε θ)
      rw [ih.1]
      exact M.masked_step_nonempty H C laws _ (p.word_exact C) a ε η θ
        p.valid_start p.valid_end hz ha hSome

end Prefix

end MaskData
end
end CCO.APCharacter
