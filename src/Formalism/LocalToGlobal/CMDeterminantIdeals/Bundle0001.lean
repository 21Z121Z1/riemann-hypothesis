import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.StatementA
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def DegAlg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L M : MLine K), L.Good → M.Good →
    (L.tensor M).Good ∧ (L.tensor M).deg = L.deg + M.deg ∧ L.dual.Good ∧ L.dual.deg = - L.deg ∧
      ∀ k : ℕ, (L.pow k).Good ∧ (L.pow k).deg = k * L.deg

def DegProdPow : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [Fintype V] (ℓ : V → MLine K) (k : V → ℕ), (∀ v, (ℓ v).Good) →
    (MLine.prodPow ℓ k).Good ∧ (MLine.prodPow ℓ k).deg = ∑ v, (k v : ℝ) * (ℓ v).deg

def ProdFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : MLine K) (x : K), L.Good → x ≠ 0 →
    L.deg = Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x * L.I⁻¹) : ℚ) : ℝ) -
      ∑ σ : K →+* ℂ, Real.log (L.len σ x)

def ProdIneq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : MLine K) (x : K), L.Good → x ≠ 0 → x ∈ L.I →
    - ∑ σ : K →+* ℂ, Real.log (L.len σ x) ≤ L.deg

def MemOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (x : K), I ≠ 0 →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c I ∧ p.valuation K x ≤ p.valuation K c) → x ∈ I

def NormOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (c : HeightOneSpectrum (𝓞 K) → K), I ≠ 0 →
    (∀ p, IsLocGen p (c p) I) →
    (Function.support fun p : HeightOneSpectrum (𝓞 K) =>
      FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (c p))).Finite ∧
    Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) =
      ∑ᶠ p : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K p (FractionalIdeal.spanSingleton (𝓞 K)⁰ (c p)) : ℝ) *
        Real.log (Ideal.absNorm p.asIdeal : ℝ)

def DetGood : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : MLat K m), L.Good →
    IsFractional (𝓞 K)⁰ L.detSub ∧ L.detLine.Good

def DetFree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : MLat K m) (b : Fin m → Fin m → K), L.Good →
    L.M = Submodule.span (𝓞 K) (Set.range b) →
    L.detLine.deg = - (1 / 2) * ∑ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (L.H σ) σ b).det.re

def DetMono : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L L' : MLat K m), L.Good → L'.Good → L'.H = L.H → L'.M ≤ L.M →
    L'.detLine.deg ≤ L.detLine.deg

def HadamardPD : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef → A.det.re ≤ ∏ i, (A i i).re

def HadamardIdeals : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : MLat K m) (ℓ : Fin m → MLine K) (u : Fin m → Fin m → K) (La : ℝ),
    L.Good → (∀ j, (ℓ j).Good) → LinearIndependent K u → (∀ j, ∀ a ∈ (ℓ j).I, a • u j ∈ L.M) → 0 < La →
    (∀ σ j, L.sq σ (u j) ≤ (La * (ℓ j).n σ) ^ 2) →
    ∑ j, (ℓ j).deg - (m : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ L.detLine.deg

def DetLatDeg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : MLat K m) (b : Fin m → Fin m → K), L.Good →
    ReciprocityTheory.MultiplicativeHeights.IsKBasisIn L.M b → L.detLine.deg = ReciprocityTheory.MultiplicativeHeights.latDeg L.H L.M b

end Formalism.L2.LamCM
end
end

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.StatementC
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def CoeffCauchy : Prop :=
  ∀ (V : Type) [Fintype V] (G : MvPolynomial V ℂ) (ρ : V → ℝ) (S : ℝ) (μ : V →₀ ℕ), (∀ v, 0 < ρ v) →
    (∀ z : V → ℂ, (∀ v, ‖z v‖ ≤ ρ v) → ‖MvPolynomial.eval z G‖ ≤ S) →
    ‖MvPolynomial.coeff μ G‖ * ∏ v, ρ v ^ μ v ≤ S

def LamEnd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (NN : MLine K) (cf : K) (S : (K →+* ℂ) → ℝ) (B : ℝ),
    NN.Good → cf ≠ 0 → cf ∈ NN.I → (∀ σ, 0 < S σ) → 0 < B → (∀ σ, NN.len σ cf ≤ S σ * B) →
    - NN.deg - (Module.finrank ℚ K : ℝ) * Real.log B ≤ ∑ σ : K →+* ℂ, Real.log (S σ)

def pDeg (logOm : ℝ) : ℝ := (1 + |logOm|) / 2

def lineNN {K : Type} [Field K] [NumberField K] {g : ℕ} {V : Type} [Fintype V] (de : MLine K) (ℓ : Fin g → MLine K)
    (c : V → Fin g) (μ : V → ℕ) (n : ℕ) : MLine K :=
  (de.pow n).tensor (MLine.prodPow (fun v => ℓ (c v)) μ).dual

def CMNumbers {K : Type} [Field K] [NumberField K] {g : ℕ} (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ) : Prop :=
  Lie.Good ∧ (∀ j, (ℓ j).Good) ∧ de.Good ∧ LinearIndependent K u ∧ (∀ j, ∀ a ∈ (ℓ j).I, a • u j ∈ Lie.M) ∧ 1 ≤ La ∧
  (∀ σ j, Lie.sq σ (u j) ≤ (La * (ℓ j).n σ) ^ 2) ∧ (∀ j, (ℓ j).ndeg = logOm / 2) ∧
  de.ndeg ≤ (1 / 2) * Lie.detLine.dual.ndeg + (g : ℝ) / 4 * Real.log (2 * Real.pi)

def DegDe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ), CMNumbers Lie ℓ u de La logOm →
    de.ndeg ≤ (g : ℝ) * (pDeg logOm + (1 / 2) * Real.log La)

def DegNN : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin g) (μ : V → ℕ) (n : ℕ),
    CMNumbers Lie ℓ u de La logOm →
    (lineNN de ℓ c μ n).Good ∧
    (lineNN de ℓ c μ n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)

def LamNumber : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ)
    (S : (K →+* ℂ) → ℝ) (Rr : ℝ),
    CMNumbers Lie ℓ u de La logOm → MvPolynomial.coeff μ G ≠ 0 → MvPolynomial.coeff μ G ∈ (lineNN de ℓ c μ n).I →
    (∀ σ, 0 < S σ) → 0 < Rr →
    (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * de.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) →
    - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤
      (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)

end Formalism.L2.LamCM
end
end

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
section
noncomputable section

namespace Formalism.L2.LamCM

open IsLocalRing
open scoped ComplexOrder

abbrev FrVar {B : Type} (m : B → ℕ) : Type := Σ b : B, Fin (m b) × Fin (m b)

variable {B : Type} {m : B → ℕ}

def evalFr {R : Type} [CommRing R] (P : MvPolynomial (FrVar m) R) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) : R :=
  MvPolynomial.eval (fun v : FrVar m => X v.1 v.2.2 v.2.1) P

def substFr {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) (P : MvPolynomial (FrVar m) R) :
    MvPolynomial (FrVar m) R :=
  MvPolynomial.bind₁ (fun v : FrVar m => ∑ j, MvPolynomial.C (U v.1 j v.2.2) * MvPolynomial.X (⟨v.1, (v.2.1, j)⟩ : FrVar m)) P

def LemmaGCore : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    (Infinite (ResidueField R) ∨ P.totalDegree + ∑ b, m b < Nat.card (ResidueField R)) →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R, (∀ b, IsUnit (X b).det) →
      evalFr P (fun b => (X b).map (algebraMap R K)) ∈ Set.range (algebraMap R K)) →
    ∀ μ, MvPolynomial.coeff μ P ∈ Set.range (algebraMap R K)

def BigResExt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
    Finite (ResidueField V) → ∀ N : ℕ,
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra V W),
      IsAdicComplete (maximalIdeal W) W ∧ Finite (ResidueField W) ∧ N < Nat.card (ResidueField W) ∧
      Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W)

def LemmaG : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) →
    (∀ (W KW : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field KW] [Algebra W KW] [IsFractionRing W KW]
      [Algebra V W] (f : K →+* KW), IsAdicComplete (maximalIdeal W) W → Finite (ResidueField W) →
      IsLocalHom (algebraMap V W) → (∀ a : V, f (algebraMap V K a) = algebraMap W KW (algebraMap V W a)) →
      ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) W, (∀ b, IsUnit (X b).det) →
        evalFr (MvPolynomial.map f P) (fun b => (X b).map (algebraMap W KW)) ∈ Set.range (algebraMap W KW)) →
    ∀ μ, MvPolynomial.coeff μ P ∈ Set.range (algebraMap V K)

def SubstGauss : Prop :=
  ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (c : ∀ b, Fin (m b) → K),
    (∀ μ, MvPolynomial.coeff μ P ∈ Set.range (algebraMap R K)) →
    (∀ b j k, c b j * U b j k ∈ Set.range (algebraMap R K)) →
    ∀ μ : FrVar m →₀ ℕ, MvPolynomial.coeff μ (substFr U P) * ∏ v : FrVar m, c v.1 v.2.2 ^ μ v ∈ Set.range (algebraMap R K)

def IsEquiv [DecidableEq B] (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ) : Prop :=
  ∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) ℂ),
    (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
    evalFr P (Function.update X b (X b * t)) = ReciprocityTheory.MultiplicativeHeights.triChar (a b) t * evalFr P X

def ArchTie : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (Hm U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (nn : ∀ b, Fin (m b) → ℝ) (C La : ℝ) (r : ℕ),
    (∀ b, (Hm b).PosDef) → IsEquiv a P →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ, (∀ b, (X b).conjTranspose * Hm b * X b = 1) → ‖evalFr P X‖ ≤ C) →
    (∀ b j, 0 < nn b j) → 0 ≤ La → (∀ b, m b ≤ r) →
    (∀ b j, ReciprocityTheory.MultiplicativeHeights.hq (Hm b) (U b j) ≤ (La * nn b j) ^ 2) →
    ∀ z : FrVar m → ℂ, (∀ v : FrVar m, ‖z v‖ * nn v.1 v.2.2 ≤ 1) →
      ‖MvPolynomial.eval z (substFr U P)‖ ≤ C * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i)

def SubstHomog : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ), IsEquiv a P →
    ∀ μ : FrVar m →₀ ℕ, MvPolynomial.coeff μ (substFr U P) ≠ 0 → ∑ v : FrVar m, μ v = ∑ b, ∑ i, a b i

end Formalism.L2.LamCM
end
end

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.StatementP
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

def IsBaseChangeLine {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K)
    (L1 : MLine K1) : Prop :=
  ((L1.I : Submodule (𝓞 K1) K1) = Submodule.span (𝓞 K1) (algebraMap K K1 '' {x | x ∈ L.I})) ∧
  ∀ σ : K1 →+* ℂ, L1.n σ = L.n (σ.comp (algebraMap K K1))

def NdegBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1),
    L.Good → IsBaseChangeLine L L1 → L1.Good ∧ L1.ndeg = L.ndeg

def BaseChangeExists : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K),
    ∃ L1 : MLine K1, IsBaseChangeLine L L1

def LocGenBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1)
    (p : HeightOneSpectrum (𝓞 K)) (p1 : HeightOneSpectrum (𝓞 K1)) (c : K), L.I ≠ 0 → IsBaseChangeLine L L1 →
    (∀ a : 𝓞 K, a ∈ p.asIdeal ↔ (algebraMap (𝓞 K) (𝓞 K1) a) ∈ p1.asIdeal) → IsLocGen p c L.I →
    IsLocGen p1 (algebraMap K K1 c) L1.I

end Formalism.L2.LamCM
end
end

