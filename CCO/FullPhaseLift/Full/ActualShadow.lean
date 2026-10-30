import CCO.FullPhaseLift.Full.Shadow

/-! An actual strict low target supplies a complete canonical shadow,
including every signed low literal and every complete frozen pair profile.
This direction uses neither pair homogeneity, SAP, nor CCO. -/

universe v w
namespace CCO.FullPhaseLift.Full.Shadow
open Canonical
noncomputable section
variable {L : Signature} {M : Type w} {V : Type v}
variable (U : BoolTable L M) (hsym : SameSortSymmetric U)

/-- The complete canonical pair diagram induced by the chosen distinct
actual vertices. This does not assert any higher-arity completion. -/
def actualDiagram [Finite V] (p : V ↪ M) : CCO.PartialDiagram (source U hsym) V where
  finite_type := inferInstance
  vertexSort x := (pack U (p x)).1
  edge x y _ := (source U hsym).colour (pack U (p x)).2 (pack U (p y)).2
  edge_reverse x y _ a := (source U hsym).colour_swap _ _ a

def actualHom [Finite V] (p : V ↪ M) : DiagramHom (actualDiagram U hsym p) where
  point x := (pack U (p x)).2
  preserves_edge _ _ _ _ h := h

theorem actualDiagram_complete [Finite V] (p : V ↪ M) :
    (actualDiagram U hsym p).IsComplete := by
  intro x y hne
  have hxy : p x ≠ p y := p.injective.ne hne
  let a : (source U hsym).Atom (pack U (p x)).1 (pack U (p y)).1 :=
    ⟨pairProfile U (p x) (p y),⟨(pack U (p x)).2,(pack U (p y)).2,hxy,rfl⟩⟩
  exact ⟨a,(colour_some_iff U _ _ a).mpr ⟨hxy,rfl⟩⟩

theorem actual_low_certificate [Finite V] (p : V ↪ M)
    (r : Fin L.size) (xs : Fin (L.arity r) → V) (b : Bool)
    (hs : SmallSupport xs) (read : U r (p ∘ xs) = b) :
    LowCertificate U hsym (actualDiagram U hsym p) r xs b := by
  classical
  by_cases hz : L.arity r = 0
  · let slots : Fin (L.arity r) → Fin 0 := fun i => Fin.cast hz i
    apply LowCertificate.nullary slots
    have he : (p : V → M) ∘ xs = Fin.elim0 ∘ slots := by
      funext i
      exact Fin.elim0 (slots i)
    change U r (Fin.elim0 ∘ slots) = b
    rwa [he] at read
  · let i₀ : Fin (L.arity r) := ⟨0,Nat.pos_of_ne_zero hz⟩
    let x := xs i₀
    by_cases hc : ∀ i, xs i = x
    · let slots : Fin (L.arity r) → Fin 1 := fun _ => 0
      have he : xs = (fun _ : Fin 1 => x) ∘ slots := funext hc
      refine LowCertificate.unary x slots he ?_
      change U r ((fun _ : Fin 1 => p x) ∘ slots) = b
      rw [he] at read
      exact read
    · obtain ⟨i₁,hi₁⟩ := not_forall.mp hc
      let y := xs i₁
      have hne : x ≠ y := Ne.symm hi₁
      let slots : Fin (L.arity r) → Fin 2 := fun i => if xs i = x then 0 else 1
      have he : xs = ![x,y] ∘ slots := by
        funext i
        by_cases hi : xs i = x
        · simp [slots,hi]
        · have hy : xs i = y := by
            rcases hs i i₀ i₁ with h | h | h
            · exact (hi h).elim
            · exact h
            · exact (hne h).elim
          simp [slots,hi,hy,Ne.symm hne]
      have hp : p x ≠ p y := p.injective.ne hne
      let a : (source U hsym).Atom (pack U (p x)).1 (pack U (p y)).1 :=
        ⟨pairProfile U (p x) (p y),⟨(pack U (p x)).2,(pack U (p y)).2,hp,rfl⟩⟩
      refine LowCertificate.pair x y hne slots he a ?_ ?_
      · exact (colour_some_iff U _ _ a).mpr ⟨hp,rfl⟩
      · change U r (![p x,p y] ∘ slots) = b
        have he₂ : (p : V → M) ∘ (![x,y] ∘ slots) = ![p x,p y] ∘ slots := by
          funext i
          change p (![x,y] (slots i)) = ![p x,p y] (slots i)
          generalize slots i = j
          fin_cases j <;> rfl
        rwa [he,he₂] at read

theorem actual_low_refines [Finite V] (p : V ↪ M) {D : Partial L V}
    (hp : LowRealizes U D p) : LowRefines U hsym (actualDiagram U hsym p) D :=
  fun r xs b hs hd => actual_low_certificate U hsym p r xs b hs (hp r xs b hs hd)

theorem actual_factor_refines [Finite V] (p : V ↪ M) {D : Partial L V}
    {m : ℕ} (F : Fin m → FrozenFactor U D) (hp : LowRealizes U D p) :
    FactorRefines U hsym (actualDiagram U hsym p) F := by
  constructor
  · intro j x
    funext a
    exact hp a.1 ((F j).inclusion ∘ (fun _ : Fin 1 => x) ∘ a.2)
      ((F j).table a.1 ((fun _ : Fin 1 => x) ∘ a.2))
      (fun _ _ _ => Or.inl rfl) ((F j).agrees _ _)
  · intro j x y hne
    let xx := (F j).inclusion x
    let yy := (F j).inclusion y
    have hxy : xx ≠ yy := (F j).inclusion.injective.ne hne
    have hp' : p xx ≠ p yy := p.injective.ne hxy
    let a : (source U hsym).Atom (pack U (p xx)).1 (pack U (p yy)).1 :=
      ⟨pairProfile U (p xx) (p yy),⟨(pack U (p xx)).2,(pack U (p yy)).2,hp',rfl⟩⟩
    refine ⟨a,(colour_some_iff U _ _ a).mpr ⟨hp',rfl⟩,?_⟩
    funext t
    have hs := (smallSupport_fin (show 2 ≤ 2 from le_rfl) t.2).comp
      ((F j).inclusion ∘ ![x,y])
    have hh := hp t.1 ((F j).inclusion ∘ ![x,y] ∘ t.2)
      ((F j).table t.1 (![x,y] ∘ t.2)) hs ((F j).agrees _ _)
    have he : (p : V → M) ∘ ((F j).inclusion ∘ ![x,y] ∘ t.2) =
        ![p xx,p yy] ∘ t.2 := by
      funext i
      change p ((F j).inclusion (![x,y] (t.2 i))) = ![p xx,p yy] (t.2 i)
      generalize t.2 i = k
      fin_cases k <;> rfl
    change U t.1 (![p xx,p yy] ∘ t.2) =
      (F j).table t.1 (![x,y] ∘ t.2)
    rwa [he] at hh

/-- Strict targets supply the exact source completion premise without
assuming homogeneity or any pair completion/injectivization theorem. -/
def CertifiedPairCompletion.of_actual [Finite V] {D : Partial L V} {m : ℕ}
    (F : Fin m → FrozenFactor U D) (p : V ↪ M) (hp : LowRealizes U D p) :
    CertifiedPairCompletion U hsym D F where
  diagram := actualDiagram U hsym p
  low := actual_low_refines U hsym p hp
  frozen := actual_factor_refines U hsym p F hp
  cycles C := (actualHom U hsym p).cycleHom _ C

theorem SupportNormal.to_strict (normal : SupportNormal U hsym) :
    Full.StrictSupportNormal U := by
  intro n D m F hc hcov hpair
  obtain ⟨p,hp,_⟩ := hpair
  exact normal n D m F hc hcov ⟨CertifiedPairCompletion.of_actual U hsym F p hp⟩

end
end CCO.FullPhaseLift.Full.Shadow
