import CCO.ProfileHelly.Completion

/-! C33: apply the GENERIC algebraic constructor directly to an actual
partial strong amalgam. Its whole carrier, old factor images and exact
intersection are preserved, rather than replaced by a homomorphic target. -/
universe u v a b c z
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι}

theorem complete_span (laws : TableLaws T) (helly : Word.Helly (T := T))
    {A : Type a} {L : Type b} {R : Type c} {W : Type z} [Finite W]
    {sortA : A → ι} {sortL : L → ι} {sortR : R → ι} {sortW : W → ι}
    (B : CompleteNetwork T sortA) (C : CompleteNetwork T sortL) (D : CompleteNetwork T sortR)
    (f : Network.Embedding B.toNetwork C.toNetwork)
    (g : Network.Embedding B.toNetwork D.toNetwork)
    (P : Network T sortW) (alg : P.Algebraic)
    (l : Network.Embedding C.toNetwork P) (r : Network.Embedding D.toNetwork P)
    (commutes : ∀ x, l.point (f.point x) = r.point (g.point x))
    (intersection : ∀ x y, l.point x = r.point y ↔ ∃ a, f.point a = x ∧ g.point a = y) :
    ∃ N : CompleteNetwork T sortW, P.Extends N.toNetwork ∧
      ∃ (l' : Network.Embedding C.toNetwork N.toNetwork)
        (r' : Network.Embedding D.toNetwork N.toNetwork),
        (∀ x, l'.point x = l.point x) ∧ (∀ y, r'.point y = r.point y) ∧
        (∀ x, l'.point (f.point x) = r'.point (g.point x)) ∧
        ∀ x y, l'.point x = r'.point y ↔ ∃ a, f.point a = x ∧ g.point a = y := by
  obtain ⟨N,hN⟩ := P.complete_of_algebraic laws helly alg
  let l' := Network.Embedding.extend C l hN
  let r' := Network.Embedding.extend D r hN
  exact ⟨N,hN,l',r',(fun _ => rfl),(fun _ => rfl),commutes,intersection⟩

end CCO.ProfileHelly
