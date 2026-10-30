import CCO.PairSafeSplit.Strong.Realization
import CCO.PairSafeSplit.Strong.RealizationTriangles

/-! B048 C10. A requested legal DISTINCT-root pair has one actual global
marking realizing both requested bits. No homogeneous-seed premise. -/
universe u v w t
namespace CCO.FullPhaseLift.Detours
open APCharacter RigidGroupoid.Geometry
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}

theorem allowed_root_pair (P : SourcePhase S H C A) {i j : ι}
    (a : S.Atom i j) (ε η : Bit) (ha : P.allows (some a) ε η) :
    ∃ (x : X i) (y : X j) (mark : Sigma X → Bit), S.colour x y = some a ∧
      P.masks.GlobalMarking mark ∧ mark ⟨i,x⟩ = ε ∧ mark ⟨j,y⟩ = η := by
  classical
  obtain ⟨x,y,hxy⟩ := S.realized a
  let point : Fin 2 → Sigma X := ![⟨i,x⟩,⟨j,y⟩]
  let bits : Fin 2 → Bit := ![ε,η]
  have legal : Age.Legal S P.masks point bits := by
    constructor
    · intro k
      fin_cases k
      · exact ha.1
      · exact ha.2.1
    · intro k l
      fin_cases k <;> fin_cases l
      · change P.allows (S.colour x x) ε ε
        rw [(S.colour_none_iff x x).mpr rfl]
        exact (P.allows_identity i _ _).mpr ⟨rfl,ha.1⟩
      · exact (by change P.allows (S.colour x y) ε η; rwa [hxy])
      · exact PairSafeSplit.Strong.Realization.allows_pair_reverse P ⟨i,x⟩ ⟨j,y⟩ _ _
          (by rwa [hxy])
      · change P.allows (S.colour y y) η η
        rw [(S.colour_none_iff y y).mpr rfl]
        exact (P.allows_identity j _ _).mpr ⟨rfl,ha.2.1⟩
  obtain ⟨mark,hm,he⟩ := PairSafeSplit.Strong.Realization.global_marking_of_legal_tuple P point bits legal
  exact ⟨x,y,mark,hxy,hm,he 0,he 1⟩

end
end CCO.FullPhaseLift.Detours
