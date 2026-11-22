import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMVal

variable {E : Type} [Field E] [NumberField E]

def IsCMType {I : Type} (φ : I → E →+* ℂ) : Prop :=
  ∀ σ : E →+* ℂ, ∃! i, σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)

def UnramFin (E : Type) [Field E] [NumberField E] : Prop := differentIdeal (OF E) (𝓞 E) = ⊤

def Over (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (OF E)) : Prop :=
  P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = v.asIdeal

def Splits (v : HeightOneSpectrum (OF E)) : Prop := ∃ P P' : HeightOneSpectrum (𝓞 E), P ≠ P' ∧ Over P v ∧ Over P' v

def expIn (𝔣 : Ideal (OF E)) (v : HeightOneSpectrum (OF E)) : ℕ := multiplicity v.asIdeal 𝔣

def IsBaseCond (𝔣 : Ideal (OF E)) : Prop :=
  𝔣 ≠ ⊥ ∧ 𝔣 ≠ ⊤ ∧ ∀ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 → Splits v ∧ expIn 𝔣 v ≤ 2 ∧
    ∃ l : ℕ, l.Prime ∧ l ≠ 2 ∧ (l : OF E) ∈ v.asIdeal ∧ ¬ (l : ℤ) ∣ discr E ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = l

def IsFinSetSplitPlacesCoprimeConductor (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Prop :=
  ∀ q ∈ Q, Splits q ∧ ¬ q.asIdeal ∣ 𝔣

def condQ (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) : Ideal (OF E) := 𝔣 * ∏ q ∈ Q, q.asIdeal

def IsValChar {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E))
    (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  IsUnitary χ ∧ TrivOnF χ ∧ HasInf χ φ (fun i => (κ i : ℤ) + s) ∧
    ∀ (v : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Over P v →
      (v ∈ Q → LevelLe χ P 1) ∧ (v ∉ Q → ExpAt χ P (expIn 𝔣 v))

def IntAt (l : ℕ) (a : ℂ) : Prop := ∃ n : ℕ, n.Coprime l ∧ IsIntegral ℤ ((n : ℂ) * a)

def UnitAt (l : ℕ) (a : ℂ) : Prop := a ≠ 0 ∧ IntAt l a ∧ IntAt l a⁻¹

def LInf {I : Type} [Fintype I] (m : I → ℤ) (s : ℂ) : ℂ :=
  ∏ i, (2 * (2 * (Real.pi : ℂ)) ^ (-(s + (|m i| : ℤ))) * Complex.Gamma (s + (|m i| : ℤ)))

end GlobalTheory.CMVal
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
section
noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R']
  {S S' : Scheme.{0}}

def IsGPull {b : Base D R} {gb : GBase D.toG R'} {N : ℕ} {s' : S' ⟶ Sp R'} {s : S ⟶ Sp R}
    (o' : GObj gb N s') (o : Obj b N s) (f : S' ⟶ S) : Prop :=
  ∃ (φA : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φA ∧ IsSquare φA φ₂ ∧
    (∀ c : D.O, (o'.act.act c).left ≫ φA = φA ≫ (o.act.act c).left) ∧ Nonempty (LBIso o'.P (o.P.pull φ₂)) ∧
    ∀ y : D.La, (o'.eta y).left ≫ φA = f ≫ (o.eta y).left

end GlobalTheory.UPel.HT.Gen
end
end

