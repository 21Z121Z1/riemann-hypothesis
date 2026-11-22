import Mathlib

-- bundled from Formalism.PeriodIntegrals.PhNormUnits
section
noncomputable section

open Classical

namespace PI.PhNormUnits

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def zc {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) : ℂ_[p] := algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])

section Ops

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

def add (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex

def mulBy (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a ph

def be (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

end Ops

def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X → p ≠ 2 →
    ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) →
    (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) → (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) →
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖β.2‖ = 1 ∧ ‖γ.1‖ = 1 ∧ ‖γ.2‖ = 1 ∧ α = β + γ) →
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) →
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))) →
    ∀ α ∈ S, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))

end PI.PhNormUnits
end
end

-- bundled from Formalism.PeriodIntegrals.PhProdConv
section
noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhProdConv

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsFdegG (μ : Measure G) (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def coefM (σ : G → (H →L[ℂ] H)) (w : H) : G → ℂ := fun g => ⟪w, σ g w⟫_ℂ

def phOf (σ : G → (H →L[ℂ] H)) (w : H) (d : ℝ) : G → ℂ := fun g => (d : ℂ) * star (coefM σ w g)

def IsOpInt {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (μ : Measure G)
    (π : G → (K →L[ℂ] K)) (ph : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  ∀ x y : K, ⟪x, T y⟫_ℂ = ∫ g, ph g * ⟪x, π g y⟫_ℂ ∂μ

def IsRowProj {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : G → (K →L[ℂ] K)) (m : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  (∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧ T.comp T = T ∧ ∀ a, T.comp ((π a).comp T) = m a • T

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def ProdConv : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    [∀ i, SecondCountableTopology (G i)] (μ : ∀ i, Measure (G i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, (μ i).IsMulLeftInvariant] [∀ i, (μ i).IsInvInvariant] (ph m : ∀ i, G i → ℂ),
    (∀ i, Integrable (ph i) (μ i)) → (∀ i, PhConv (μ i) (ph i) (m i)) →
      Integrable (fun g : ∀ i, G i => ∏ i, ph i (g i)) (Measure.pi μ) ∧
      PhConv (Measure.pi μ) (fun g => ∏ i, ph i (g i)) (fun g => ∏ i, m i (g i))

end PI.PhProdConv
end
end

-- bundled from Formalism.PeriodIntegrals.PhSchurConv
section
noncomputable section

open MeasureTheory NumberField
open scoped InnerProductSpace

namespace PI.PhSchurConv

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsURep (ρ : G → (H →L[ℂ] H)) : Prop :=
  ρ 1 = 1 ∧ (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) ∧ (∀ g v, ‖ρ g v‖ = ‖v‖) ∧
    ∀ v, Continuous fun g => ρ g v

def IsFdegG (μ : Measure G) (σ : G → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  0 < d ∧ ∀ v w v' w' : H,
    Integrable (fun g => ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ) μ ∧
    ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)

def coefM (σ : G → (H →L[ℂ] H)) (w : H) : G → ℂ := fun g => ⟪w, σ g w⟫_ℂ

def phOf (σ : G → (H →L[ℂ] H)) (w : H) (d : ℝ) : G → ℂ := fun g => (d : ℂ) * star (coefM σ w g)

def IsOpInt {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (μ : Measure G)
    (π : G → (K →L[ℂ] K)) (ph : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  ∀ x y : K, ⟪x, T y⟫_ℂ = ∫ g, ph g * ⟪x, π g y⟫_ℂ ∂μ

def IsRowProj {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (π : G → (K →L[ℂ] K)) (m : G → ℂ) (T : K →L[ℂ] K) : Prop :=
  (∀ x y : K, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) ∧ T.comp T = T ∧ ∀ a, T.comp ((π a).comp T) = m a • T

def PhConv (μ : Measure G) (ph m : G → ℂ) : Prop :=
  m 1 = 1 ∧ (∀ g, ph g⁻¹ = star (ph g)) ∧
    ∀ x y : G, Integrable (fun g => ph g * ph (x⁻¹ * g⁻¹ * y)) μ ∧
      ∫ g, ph g * ph (x⁻¹ * g⁻¹ * y) ∂μ = m x * ph y

end Defs

def SchurConv : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (Hσ : Type) [NormedAddCommGroup Hσ] [InnerProductSpace ℂ Hσ]
    (σ : G → (Hσ →L[ℂ] Hσ)) (d : ℝ) (w : Hσ),
    IsURep σ → IsFdegG μ σ d → ‖w‖ = 1 →
      PhConv μ (phOf σ w d) (coefM σ w) ∧
      ∀ u u' : Hσ, Integrable (fun g => phOf σ w d g * ⟪u', σ g u⟫_ℂ) μ ∧
        ∫ g, phOf σ w d g * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ

end PI.PhSchurConv
end
end

-- bundled from Formalism.PeriodIntegrals.PhiCubeOfFactor
section
noncomputable section

open Classical

namespace PI.PhiCubeOfFactor

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

end

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def phAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a (-logMv E : PowerSeries ℂ_[p])

def eAt {p : ℕ} [Fact p.Prime] {σ : Type*} (E : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a E

def Lemma : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex E : PowerSeries ℂ_[p]) (Q : MvPowerSeries (Fin 2) ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff E = 1 →
    add l ex (Xv 0) (Xv 1) * sub l ex (Xv 0) (Xv 1) * eAt E (add l ex (Xv 0) (Xv 1)) *
        eAt E (sub l ex (Xv 0) (Xv 1)) =
      Q * eAt E (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 * eAt E (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 →
    (∃ n : MvPowerSeries (Fin 2) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      Q = add l ex (Xv 0) (Xv 1) * sub l ex (Xv 0) (Xv 1) * n) →
    Simeq (phAt E (add l ex (Xv 0) (Xv 1)) + phAt E (sub l ex (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * phAt E (Xv 0) + 2 * phAt E (Xv 1))

end PI.PhiCubeOfFactor
end
end

-- bundled from Formalism.PeriodIntegrals.PowBddInt
section
namespace PI

open Matrix

def PowBddInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (γ : Matrix (Fin k) (Fin k) E) (N : ℕ), 0 < N →
    (∀ (n : ℕ) (i j : Fin k), IsIntegral ℤ ((N : E) * (γ ^ n) i j)) →
    ∀ i, IsIntegral ℤ (γ.charpoly.coeff i)

end PI
end

-- bundled from Formalism.PeriodIntegrals.PrimeCount
section
noncomputable section

namespace PI

def pr (y : ℝ) : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime

def PrimeCountBound : Prop := ∀ y : ℝ, 1 < y → ((pr y).card : ℝ) < 1.26 * y / Real.log y

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.PrimeSums
section
namespace PI

def PrimeLogOverP : Prop :=
  ∀ Y : ℝ, 1 < Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y

def ThetaBound : Prop :=
  ∀ Y : ℝ, 1 < Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) ≤ 1.02 * Y

def PrimeLogOverPSqTail : Prop :=
  ∀ X : ℝ, 0 < X → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) →
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X

end PI
end

-- bundled from Formalism.PeriodIntegrals.PrimesDyadicRS
section
namespace PI.PrimesDyadicRS

def Claim : Prop :=
  ∀ y : ℝ, 41 / 2 ≤ y →
    3 * y / (5 * Real.log y) < (Nat.primeCounting ⌊2 * y⌋₊ : ℝ) - (Nat.primeCounting ⌊y⌋₊ : ℝ)

end PI.PrimesDyadicRS
end

-- bundled from Formalism.PeriodIntegrals.ProdUnitInert
section
noncomputable section

namespace PI.ProdUnitInert

open Classical

abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

def lamC {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : ℂ) : ℂ_[p] :=
  if h : x ∈ Qbar then lam ⟨x, h⟩ else 0

end PI.ProdUnitInert

namespace PI

open PI.ProdUnitInert

def ProdUnitInert : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (K : IntermediateField ℚ E) (c : E →+* E) (φ₀ : E →+* ℂ) (S : Type) [Fintype S]
    (emb : S → E →+* ℂ), Function.Injective emb → (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) →
    Fintype.card S = Module.finrank K E → (∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x)) →
    Module.finrank ℚ K = 2 → ∀ (d p : ℕ) [Fact p.Prime] (b : K), b ^ 2 = ((-(d : ℤ) : ℤ) : K) →
    jacobiSym (-(d : ℤ)) p = -1 → ∀ (lam : Qbar →+* ℂ_[p]) (z : E), z * c z = 1 →
    ‖lamC lam (∏ s, emb s z)‖ = 1

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.QuadDiff
section
noncomputable section

namespace PI

open NumberField IntermediateField

def QuadDiff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (θ : E), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : E) →
    (((differentIdeal ℤ (𝓞 ℚ⟮θ⟯)).map (algebraMap (𝓞 ℚ⟮θ⟯) (𝓞 E)) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) θ

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.QuotInv
section
open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI

abbrev MtM (m : ℕ) := Fin m → Fin m → ℂ

def lmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := a * Matrix.of x

def rmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := Matrix.of x * a

def IsMatGroup {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G ∧ (∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) ∧
    ∀ a ∈ G, a⁻¹ ∈ G ∧ a * a⁻¹ = 1

def IsHaarOnM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulQ s) = μ

def IsRightInvM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  ∀ s ∈ S, μ.map (rmulQ s) = μ

def IsQuotM {m : ℕ} (μG μS ν : Measure (MtM m)) : Prop :=
  ∀ f : MtM m → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν

def QuotientSetting {m : ℕ} (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)) : Prop :=
  IsMatGroup G ∧ IsMatGroup S ∧ S ⊆ G ∧ IsHaarOnM G μG ∧ IsHaarOnM S μS ∧ IsRightInvM G μG ∧ IsRightInvM S μS ∧
    IsQuotM μG μS ν

def QuotInv : Prop :=
  ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)), QuotientSetting G S μG μS ν →
    ∀ F : MtM m → ℝ≥0∞, Measurable F →
      (∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) →
      ∀ g ∈ G, ∫⁻ x, F (fun i j => (Matrix.of x * g) i j) ∂ν = ∫⁻ x, F x ∂ν

def QuotYoung : Prop :=
  ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)), QuotientSetting G S μG μS ν →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      (e : Matrix (Fin m) (Fin m) ℂ → ℂ) (Φ : Matrix (Fin m) (Fin m) ℂ → V),
      Integrable (fun x : MtM m => e (Matrix.of x)) μG →
      AEStronglyMeasurable (fun x : MtM m => Φ (Matrix.of x)) μG →
      (∀ s ∈ S, ∀ g ∈ G, ‖Φ (s * g)‖ = ‖Φ g‖) →
      (∃ M : ℝ, ∀ g ∈ G, ‖Φ g‖ ≤ M) →
      (∫⁻ x, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν) < ⊤ →
      (∫⁻ x, (‖∫ g, e (Matrix.of g) • Φ (Matrix.of x * Matrix.of g) ∂μG‖₊ : ℝ≥0∞) ^ 2 ∂ν) < ⊤

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.QuotNuSigma
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PI.QuotNuSigma

def Target : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μG : Measure G) [IsFiniteMeasureOnCompacts μG] (A B : Set G) (μA μB ν : Measure G),
    (SigmaFinite μA ∧ μA ≠ 0 ∧ μA Aᶜ = 0 ∧ ∀ s ∈ A, μA.map (fun x => s * x) = μA) →
    (SigmaFinite μB ∧ μB ≠ 0 ∧ μB Bᶜ = 0 ∧ ∀ s ∈ B, μB.map (fun x => s * x) = μB) →
    (∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (s * x) ∂((μA.prod μB).map (fun p => p.1 * p.2))) ∂ν) →
    SigmaFinite ν

end PI.QuotNuSigma
end
end

