import Mathlib

-- bundled from Formalism.PeriodIntegrals.JetsPhW
section
noncomputable section

open Classical

namespace PI.JetsPhW

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def dX {A : Type*} [CommRing A] (f : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk fun n => ((n : A) + 1) * PowerSeries.coeff (n + 1) f

def IsWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) : Prop :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  wq = 1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3

def omegaW {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  (-(2 : PowerSeries ℂ_[p]) * wq - X * dX wq) * (wq * (c W.a₁ * X + c W.a₃ * X ^ 3 * wq - 2))⁻¹

def flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => if n = 0 then 0 else PowerSeries.coeff (n - 1) (omegaW W wq) / n

section Ops

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

def add (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex

def sub (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l - PowerSeries.subst b l) ex

def mulBy (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a ph

def be (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

end Ops

def jet {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (i : ℕ) : ℂ_[p] :=
  (i.factorial : ℂ_[p]) * PowerSeries.coeff i (PowerSeries.subst ex ph : PowerSeries ℂ_[p])

def cubeE {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p] :=
  phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
    phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
    phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)

def High : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    Simeq (cubeE (flog W wq) ex ph) 0 →
    ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (jet ex ph i)

def One : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X → p ≠ 2 →
    Simeq (phAt ph (mulBy (flog W wq) ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())) →
    IsIntP (jet ex ph 1)

def Two : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex (flog W wq) = PowerSeries.X →
    Simeq (be (flog W wq) ex ph (mulBy (flog W wq) ex a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be (flog W wq) ex ph (Xv 0) (mulBy (flog W wq) ex b (Xv 1))) →
    IsIntP ((a - b) * jet ex ph 2)

def Target : Prop := High ∧ One ∧ Two

def LogOk {p : ℕ} [Fact p.Prime] (l ex : PowerSeries ℂ_[p]) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧
    ∃ v : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.coeff n v)) ∧ v * dX l = 1

def InvOmega : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    IsIntP W.a₁ → IsIntP W.a₂ → IsIntP W.a₃ → IsIntP W.a₄ → IsIntP W.a₆ → IsWq W wq →
    ∃ v : PowerSeries ℂ_[p], (∀ n, IsIntP (PowerSeries.coeff n v)) ∧ v * dX (flog W wq) = 1

def HighG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    Simeq (cubeE l ex ph) 0 → ∀ i : ℕ, i ≠ 1 → i ≠ 2 → IsIntP (jet ex ph i)

def OneG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex → p ≠ 2 →
    Simeq (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) (phAt ph (Xv ())) →
    IsIntP (jet ex ph 1)

def TwoG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (a b : ℂ_[p]), LogOk l ex →
    Simeq (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex b (Xv 1))) →
    IsIntP ((a - b) * jet ex ph 2)

def Glue : Prop := InvOmega → HighG → OneG → TwoG → Target

end PI.JetsPhW
end
end

-- bundled from Formalism.PeriodIntegrals.KerIso
section
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerIso

def IsIsom {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E → E) {n : Type} [Fintype n]
    (g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : Prop :=
  ∀ x y, ∑ w, algebraMap K E (g x w) * cj (algebraMap K E (g y w))
      = algebraMap K E (∑ a, Algebra.trace K E (x a * cj (y a)))

def AtP {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n] (M : Set E)
    (g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → E, (∀ a, x a ∈ M) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : K) * g x w ∈ (algebraMap (𝓞 K) K).range) ∧
  ∀ v : Fin 4 × n → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : E) * g.symm v a ∈ M

def detRel {K E : Type} [Field K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    (g g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : K :=
  LinearMap.det ((g₀.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))

def ordK {K : Type} [Field K] [NumberField K] (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) : ℤ :=
  -WithZero.log (𝔭.valuation K x)

def IsConj (K : Type) {E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) : Prop :=
  (∀ x, cj (cj x) = x) ∧ (∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') ∧
    ∃ k : K, cj (algebraMap K E k) ≠ algebraMap K E k

def DetOrdIndep : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E] (n : Type) [Fintype n] (M : Set E) (p : ℕ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (g g' g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)),
    p.Prime → ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal → AtP M g p → AtP M g' p →
      ordK 𝔭 (detRel g g₀) = ordK 𝔭 (detRel g' g₀)

def DetOrdFin : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : Type) [Fintype n]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), I ≠ 0 →
    ∀ (S : ℕ → Prop) (pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (gp : ℕ → ((Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))) (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)),
      (∀ p, p.Prime → S p → ((p : ℕ) : 𝓞 K) ∈ (pp p).asIdeal) →
      (∀ p, p.Prime → S p → AtP {x : E | x ∈ I} (gp p) p) →
        {p : ℕ | p.Prime ∧ S p ∧ ordK (pp p) (detRel (gp p) g₀) ≠ 0}.Finite

def FourSq : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (n : Type) [Fintype n],
    Module.finrank ℚ K = 2 → Fintype.card n = Module.finrank K E → IsConj K cj →
    (∀ x : E, x ≠ 0 → 0 < Algebra.trace ℚ E (x * cj x)) →
      ∃ g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K), IsIsom cj g

def ExtC : Prop :=
  ∀ (K E : Type) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E] (n : Type) [Fintype n] (φ : K →+* ℂ)
    (τ : n → E →+* ℂ), Function.Injective τ → (∀ i k, τ i (algebraMap K E k) = φ k) →
    Fintype.card n = Module.finrank K E → ∀ g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K),
      ∃ gC : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
        ∀ x : Fin 4 → E, gC (fun w => τ w.2 (x w.1)) = fun w => φ (g x w)

def SplitsAt (K : Type) {E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (p : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 K), P.IsPrime ∧ ((p : ℕ) : 𝓞 K) ∈ P ∧ ∃ a b : 𝓞 K,
    cj (algebraMap K E (a : K)) = algebraMap K E (b : K) ∧ a ∈ P ∧ b ∉ P

def SelfDualI (K : Type) {E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Prop :=
  ∀ y : E, y ∈ I ↔ ∀ x ∈ I, Algebra.trace K E (x * cj y) ∈ (algebraMap (𝓞 K) K).range

def LocIso : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (n : Type) [Fintype n]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (p : ℕ),
    Module.finrank ℚ K = 2 → IsConj K cj → p.Prime → SplitsAt K cj p → SelfDualI K cj I →
    (∃ g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K), IsIsom cj g₀) →
      ∃ g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K), IsIsom cj g ∧ AtP {x : E | x ∈ I} g p

end PI.KerIso
end
end

-- bundled from Formalism.PeriodIntegrals.LatDefs
section
noncomputable section

namespace PI

def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}

def area (Λ : AddSubgroup ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, a = |((starRingEnd ℂ) w₁ * w₂).im|}

def U1 (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => G (z + ω) * Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))

def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2

def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3

def discr (Λ : AddSubgroup ℂ) : ℂ := g2 Λ ^ 3 - 27 * g3 Λ ^ 2

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.LatLocGlob
section
noncomputable section

namespace PI.LatLocGlob

def loc {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (p : Ideal R) (L : Submodule R V) : Set V :=
  {x | ∃ s : R, s ∉ p ∧ s • x ∈ L}

def IsFullLat (K : Type) {R V : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup V] [Module K V]
    [Module R V] [IsScalarTower R K V] (L : Submodule R V) : Prop :=
  L.FG ∧ Submodule.span K (L : Set V) = ⊤

def LatLocGlob : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (L0 : Submodule R V), IsFullLat K L0 →
    ∀ M : Ideal R → Set V,
      (∀ p : Ideal R, p.IsMaximal → ∃ N : Submodule R V, IsFullLat K N ∧ M p = loc p N) →
      Set.Finite {p : Ideal R | p.IsMaximal ∧ M p ≠ loc p L0} →
      ∃! L : Submodule R V, IsFullLat K L ∧ ∀ p : Ideal R, p.IsMaximal → loc p L = M p

end PI.LatLocGlob
end
end

-- bundled from Formalism.PeriodIntegrals.LatMin
section
namespace PI

open MvPolynomial

def LatMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x

end PI
end

-- bundled from Formalism.PeriodIntegrals.LeafCoeffVal
section
noncomputable section

namespace PI

open Finset

def posSub {n' : ℕ} (s : Fin n') (d : ℕ) : Fin n' :=
  ⟨(s.val + n' * d - d) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

def posAdd {n' : ℕ} (s : Fin n') (e : ℕ) : Fin n' :=
  ⟨(s.val + e) % n', Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt)⟩

def IsLeaf (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) : Prop :=
  (∀ i, PowerSeries.constantCoeff (t i) = 0) ∧
  ∀ (i : Fin h) (n : ℕ), ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (posSub i k)) ^ (p ^ (2 * k))) / (p : K) ^ k =
    if i.val = 0 ∧ n = 1 then 1 else 0

def ze3 (p : ℕ) {K : Type} [Field K] {h : ℕ} (t : Fin h → PowerSeries K) (i1 : Fin h) : PowerSeries K :=
  PowerSeries.mk fun n =>
    ∑ k ∈ range (n + 1), PowerSeries.coeff n ((t (posSub i1 k)) ^ (p ^ (2 * k + 1))) / (p : K) ^ (k + 1)

def LeafCoeffVal : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (i0 : Fin 1) (t : Fin 1 → PowerSeries ℚ), IsLeaf p t → ∀ e : ℕ,
    padicValRat p (PowerSeries.coeff (p ^ 3 * p ^ e) ((-ze3 p t (posAdd i0 1)) ^ (p ^ e)) / ((p ^ e).factorial : ℚ)) =
      -(((p : ℤ) + 1) * (p : ℤ) ^ e + padicValNat p (p ^ e).factorial)

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.LocBasisPlace
section
open NumberField

namespace PI

def LocBasisPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ρ : E →+* ℂ_[p]) (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)), L.FG → Submodule.span E (L : Set (Fin N → E)) = ⊤ →
    ∃ P : Matrix (Fin N) (Fin N) E, P.det ≠ 0 ∧
      (∀ a, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ s • P.transpose a ∈ L) ∧
      ∀ x ∈ L, ∃ s : 𝓞 E, ‖ρ (s : E)‖ = 1 ∧ ∃ c : Fin N → 𝓞 E, s • x = ∑ a, c a • P.transpose a

end PI
end

-- bundled from Formalism.PeriodIntegrals.LocBasisSemi
section
open NumberField

namespace PI

def LocBasisSemi : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (p : ℕ), p.Prime →
    ∀ Y : Submodule (𝓞 K) V, Y.FG →
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧
      (∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ (s : K) • b i ∈ Y) ∧
      ∀ y ∈ Y, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : Fin r → 𝓞 K, (s : K) • y = ∑ i, ((c i : 𝓞 K) : K) • b i

end PI
end

-- bundled from Formalism.PeriodIntegrals.LocFramePrim
section
noncomputable section

namespace PI.LocFramePrim

open NumberField IsDedekindDomain
open scoped TensorProduct Classical

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def inclR : E →+* R ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).toRingHom

def ratTup {M n : ℕ} (X : Fin n → Fin M → E) : Fin n → Fin M → R ⊗[F] E :=
  fun a i => inclR R (X a i)

def ratV {n : ℕ} (x : Fin n → E) : Fin n → R ⊗[F] E := fun i => inclR R (x i)

end Alg

abbrev Fv (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) := v.adicCompletion F

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def latLoc (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) :
    Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' Λ)

end Level

section Frames

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

abbrev TupV (n a : ℕ) : Type := Fin a → Fin n → Fv F v ⊗[F] E

def OEv : Set (Fv F v ⊗[F] E) :=
  SetLike.coe (Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ))

def sc (x : Fv F v) : Fv F v ⊗[F] E := x ⊗ₜ[F] (1 : E)

variable {n : ℕ} (Λ : Set (Fin n → E))

def IsPrim {a : ℕ} (X : TupV (E := E) v n a) : Prop :=
  (∀ i, X i ∈ latLoc (E := E) v Λ) ∧
  ∀ c : Fin a → Fv F v ⊗[F] E, (∑ i, c i • X i) ∈ latLoc (E := E) v Λ → ∀ i, c i ∈ OEv (E := E) v

def IsDiffVal (d : Fv F v) : Prop :=
  d ≠ 0 ∧ (∀ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v d) ∧
    ∃ x ∈ differentIdeal ℤ (𝓞 F), Valued.v (algebraMap F (Fv F v) (x : F)) = Valued.v d

def dV : Fv F v := if h : ∃ d, IsDiffVal v d then h.choose else 1

def alp (r : ℕ) (a : Fin (r + 1)) : Fv F v := if (a : ℕ) < r then (dV v)⁻¹ ^ (r - (a : ℕ)) else 1

def locF {r : ℕ} (X : TupV (E := E) v n (r + 1)) : TupV (E := E) v n (r + 1) :=
  fun a => sc (E := E) v (alp v r a) • X a

end Frames

section Split

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ddE : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
  ((Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (differentIdeal ℤ (𝓞 F)) : Ideal (𝓞 E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 E)) E)

variable {F}

def latSpan {n r : ℕ} (aa : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (w : Fin r → Fin n → E) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ aa a ∧ y = x • w a}

end Split

def Statement : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (n r : ℕ) (Λ Lb : Submodule (𝓞 E) (Fin n → E))
    (e f : Fin r → Fin n → E) (z : Fin n → E),
    Λ.FG →
    Λ = latSpan (fun a : Fin r => ddE F ^ (-((r : ℤ) - (a : ℕ)))) e ⊔ Lb ⊔
      latSpan (fun a : Fin r => (ddE F ^ (-((r : ℤ) - (a : ℕ))))⁻¹) f →
    LinearIndependent E (Fin.append e f) →
    (∀ y ∈ Lb, y ∈ Submodule.span E (Set.range e ∪ Set.range f) → y = 0) →
    z ∈ Lb →
    (∀ c : E, c • z ∈ Lb → ∃ o : 𝓞 E, (o : E) = c) →
    IsPrim v (Λ : Set (Fin n → E))
      (locF v (ratTup (Fv F v) (Fin.snoc e z : Fin (r + 1) → Fin n → E)))

end PI.LocFramePrim
end
end

-- bundled from Formalism.PeriodIntegrals.LocalEnd
section
open NumberField IsDedekindDomain

namespace PI

def LocalEndHomeo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (τ : v.adicCompletion F →+* v.adicCompletion F),
    Continuous τ ∧ ∃ τ' : v.adicCompletion F →+* v.adicCompletion F, Continuous τ' ∧ ∀ a, τ (τ' a) = a

end PI
end

-- bundled from Formalism.PeriodIntegrals.LpLower
section
noncomputable section

namespace PI

def lpFeasible (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : Set ℝ :=
  {y | ∃ xs : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ xs s i) ∧
    (∀ s i, (¬ Odd i ∨ d ≤ i) → xs s i = 0) ∧
    (∀ s, (∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i) +
      (∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i) ≤ Ds s) ∧
    y = ∑ s, ∑ i ∈ Finset.range d, xs s i}

def lpF (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : ℝ :=
  (l : ℝ) / ((l : ℝ) ^ 2 - 1) * (∑ s, Ds s) - sSup (lpFeasible l d Ds)

def LpLower : Prop :=
  ∀ (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ), 2 ≤ l → (∀ s, 0 ≤ Ds s) →
    (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) ≤ lpF l d Ds

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.Minkowski
section
namespace PI

def minkowskiExp (N p : ℕ) : ℕ := ∑ i ∈ Finset.range (N + 1), N / (p ^ i * (p - 1))

def minkowskiM (N : ℕ) : ℕ := ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ minkowskiExp N p

def MinkowskiBound : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)), Finite G →
    Nat.card G ∣ minkowskiM N

end PI
end

