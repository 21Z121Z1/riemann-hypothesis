import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsCyclicClassPolynomial

-- bundled from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Polynomial NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar

namespace GlobalTheory.HT

def frobMin {k : Type} [Field k] [Fintype k] (A : AbVar k) : ℚ[X] := minpoly ℚ (toEnd0 A (frob A))

def IsFrobField {k : Type} [Field k] [Fintype k] (A : AbVar k) (F : Type) [Field F] [CharZero F]
    [Algebra F (End0 A)] (π : F) : Prop :=
  algebraMap F (End0 A) π = toEnd0 A (frob A) ∧ Algebra.adjoin ℚ {π} = ⊤

def TateQ : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (l : ℕ) [Fact l.Prime], (l : k) ≠ 0 → ∀ A B : AbVar k,
    Function.Injective (tateHomQ l A B) ∧ LinearMap.range (tateHomQ l A B) = galHomV l A B

def FrobFieldExists : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (A : AbVar k), IsSimple A →
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra F (End0 A)) (π : F), IsFrobField A F π

def Structure : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (A : AbVar k), IsSimple A →
    ∀ (F : Type) [Field F] [NumberField F] [Algebra F (End0 A)] (π : F), IsFrobField A F π →
      IsWeil (Fintype.card k) π ∧ Algebra.IsCentral F (End0 A) ∧ IsSimpleRing (End0 A) ∧
      (∀ x : End0 A, x ≠ 0 → IsUnit x) ∧
      ∃ d : ℕ, Module.finrank F (End0 A) = d ^ 2 ∧ 2 * A.dim = d * Module.finrank ℚ F ∧
        (charpoly (frob A)).map (algebraMap ℤ ℚ) = minpoly ℚ π ^ d ∧
        ∀ v : HeightOneSpectrum (𝓞 F), ((ringChar k : ℕ) : 𝓞 F) ∉ v.asIdeal →
          Nonempty (v.adicCompletion F ⊗[F] End0 A ≃ₐ[v.adicCompletion F]
            Matrix (Fin d) (Fin d) (v.adicCompletion F))

def InvAtP : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (A : AbVar k), IsSimple A →
    ∀ (F : Type) [Field F] [NumberField F] [Algebra F (End0 A)] (π : F), IsFrobField A F π →
      ∀ (p a f m : ℕ) (v : HeightOneSpectrum (𝓞 F)), p.Prime → Fintype.card k = p ^ a →
        Ideal.absNorm v.asIdeal = p ^ f → v.valuation F π = WithZero.exp (-(m : ℤ)) →
        HasInv (v.adicCompletionIntegers F) (v.adicCompletion F) (v.adicCompletion F ⊗[F] End0 A)
          ((m : ℚ) * f / a)

def InvAtReal : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (A : AbVar k), IsSimple A →
    ∀ (F : Type) [Field F] [NumberField F] [Algebra F (End0 A)] (π : F), IsFrobField A F π →
      ∀ [Algebra F ℝ], ∃ n : ℕ,
        Nonempty (ℝ ⊗[F] End0 A ≃ₐ[ℝ] Matrix (Fin n) (Fin n) (Quaternion ℝ))

def Injective : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (A B : AbVar k), IsSimple A → IsSimple B →
    (Isog A B ↔ frobMin A = frobMin B)

def Honda : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (L : Type) [Field L] [CharZero L] (π : L), IsWeil (Fintype.card k) π →
    ∃ A : AbVar k, IsSimple A ∧ frobMin A = minpoly ℚ π

def HondaTate : Prop :=
  FrobFieldExists ∧ Structure ∧ InvAtP ∧ InvAtReal ∧ Injective ∧ Honda

def IsCMSet (L : Type) [Field L] [NumberField L] [IsCMField L] (S : Finset (L ≃ₐ[ℚ] L)) : Prop :=
  ∀ s, s ∈ S ↔ (IsCMField.complexConj L).restrictScalars ℚ * s ∉ S

def IsCMData {L : Type} [Field L] [NumberField L] (S : Finset (L ≃ₐ[ℚ] L)) {k : Type} [Field k] (A : AbVar k)
    (ι : 𝓞 L →+* End A) (j : 𝓞 L →+* k) : Prop :=
  2 * A.dim = Module.finrank ℚ L ∧
    ∃ a : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct (𝓞 L) A.X, (∀ x, Hom.hom (ι x) = a.act x) ∧
      (open Classical in IsLieType a fun s : S =>
        j.comp (RingOfIntegers.mapRingHom (s.1 : L →+* L)))

def IsDieudonne {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [Fintype k] [CharP k p] [PerfectRing k p]
    (A : AbVar k) {M : Type} [AddCommGroup M] [Module (WittVector p k) M]
    (ρ : (End A)ᵐᵒᵖ →+* Module.End (WittVector p k) M)
    (Φ : M →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] M) : Prop :=
  Module.Free (WittVector p k) M ∧ Module.Finite (WittVector p k) M ∧
    Module.finrank (WittVector p k) M = 2 * A.dim ∧ (∀ f m, Φ (ρ f m) = ρ f (Φ m)) ∧
    (∀ a, Fintype.card k = p ^ a → ∀ m, Φ^[a] m = ρ (MulOpposite.op (frob A)) m) ∧
    ∀ f : End A, IsIsogeny (A := A) (B := A) f → Function.Bijective (ρ (MulOpposite.op f)) → ¬ p ∣ deg (A := A) (B := A) f

end GlobalTheory.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoNeZeroClosure
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.LTors

variable {K : Type} [Field K] (l : ℕ) [Fact l.Prime]

def tv (A : AbVar K) : Tl l A →ₗ[ℤ_[l]] Vl l A := TensorProduct.mk ℤ_[l] ℚ_[l] (Tl l A) 1

def IsLPow {A : AbVar K} (G : Subgroup A.Pt) : Prop := Finite G ∧ ∃ a : ℕ, Nat.card G = l ^ a

def IsLatOver {A : AbVar K} (L : Submodule ℤ_[l] (Vl l A)) : Prop := L.FG ∧ LinearMap.range (tv l A) ≤ L

def latSet {A : AbVar K} (G : Subgroup A.Pt) : Set (Vl l A) :=
  {x | ∃ (n : ℕ) (t : Tl l A), x = (((l : ℚ_[l]) ^ n)⁻¹ ⊗ₜ[ℤ_[l]] t) ∧ t.lev n ∈ G}

def LTorsLatticeSt : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K),
    (∀ G : Subgroup A.Pt, IsLPow l G →
      ∃ L : Submodule ℤ_[l] (Vl l A), (L : Set (Vl l A)) = latSet l G ∧ IsLatOver l L) ∧
    (∀ L : Submodule ℤ_[l] (Vl l A), IsLatOver l L →
      ∃! G : Subgroup A.Pt, IsLPow l G ∧ (L : Set (Vl l A)) = latSet l G) ∧
    (∀ G : Subgroup A.Pt, IsLPow l G →
      (∃ (B : AbVar K) (q : A ⟶ B), IsIsogeny q ∧ (ptMap q).ker = G ∧ deg q = Nat.card G) ∧
      ∀ (B : AbVar K) (q : A ⟶ B), IsIsogeny q → (ptMap q).ker = G →
        Function.Injective (tmap l A B q) ∧ Function.Bijective (vmap l q) ∧
        {x : Vl l A | vmap l q x ∈ LinearMap.range (tv l B)} = latSet l G ∧
        ∀ (l' : ℕ) [Fact l'.Prime], l' ≠ l → (l' : K) ≠ 0 → Function.Bijective (tmap l' A B q))

example : IsAlgClosed (AlgebraicClosure (ZMod 3)) := inferInstance

end GlobalTheory.AV.LTors
end
end

