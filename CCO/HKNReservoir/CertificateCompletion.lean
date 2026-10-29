import CCO.HKNReservoir.Certificate

universe v w t y
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} {S : AtomicSource.{0,v,w} Unit (fun _ => M)}
variable {G : Type t} [Group G] [MulAction G M] {H : HomogeneousSource S G}
variable [Countable M] [DecidableEq M] [Infinite M] {R : ResidualData S H}
variable {B : Finset (Owner S H R)} {hB : PacketInvariant S H R B}
variable {Δ : Subgroup (SourceGamma S H R B)}
variable {A : Set (SourceCarrier S H R B)}
variable {hA : (sourceStructure S H R B hB).IsClosed A}
variable {Z : Type y}
variable {E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z}
variable {hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E}
namespace PacketCertificate

/-- The literal identity from B₀ to its completion retains every original
relation and the WHOLE named unary functions. No hole filling is applied
to B₀ itself, and its original automorphisms continue to act there. -/
def identityHom (c : PacketCertificate S H R B hB Δ A hA E hLocal) :
    Structure.Homomorphism (sourceAction S H R B Δ) E (encode c.completionData) where
  lang := 1
  toFun := id
  map_rel := by
    intro n R xs hx
    cases R with
    | owner b =>
      have ht : xs = (fun _ => xs 0) := funext (fun i => congrArg xs (Subsingleton.elim _ _))
      rw [ht] at hx
      have ho := (PacketRecovery.owner_iff (sourceTag S H R B Δ)
        (finiteSourceData S H R B hB A hA) E hLocal (xs 0) b).mp hx
      change ownerLabel S H R B (c.point (xs 0)) = sourceTag S H R B Δ 1 b
      simpa only [map_one,Equiv.Perm.one_apply] using (c.owner (xs 0)).trans ho
    | fine a =>
      have ht : xs = ![xs 0,xs 1] := by funext i; fin_cases i <;> rfl
      have hh := c.fine a (xs 0) (xs 1) (ht ▸ hx)
      exact hh
  map_func := by
    intro n F xs
    cases F with
    | translate g =>
      have ht : xs = (fun _ => xs 0) := funext (fun i => congrArg xs (Subsingleton.elim _ _))
      intro y hy
      obtain ⟨z,hz,rfl⟩ := hy
      change z ∈ {PacketRecovery.move (sourceTag S H R B Δ)
        (finiteSourceData S H R B hB A hA) E hLocal g (xs 0)}
      rw [ht] at hz
      exact (PacketRecovery.func_value (sourceTag S H R B Δ)
        (finiteSourceData S H R B hB A hA) E hLocal g (xs 0)) ▸ hz

@[simp] theorem identityHom_lang (c : PacketCertificate S H R B hB Δ A hA E hLocal) : c.identityHom.lang = 1 := rfl
@[simp] theorem identityHom_apply (c : PacketCertificate S H R B hB Δ A hA E hLocal) (x : Z) : c.identityHom x = x := rfl
end PacketCertificate
end
end CCO.HKNReservoir
