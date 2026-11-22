import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ptsOver (𝕜 : Type) [Field 𝕜] (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → 𝕜) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, aeval z f = 0}

def algPts (p : ℕ) [Fact p.Prime] (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → PadicAlgCl p) :=
  {z | z ∈ ptsOver (PadicAlgCl p) P ∧ ∀ q, IsAlgebraic ℚ (z q)}

def HasVal (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (w : 𝕜) : Prop :=
  ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
    aeval y g = s * aeval y h ∧ aeval z h ≠ 0 ∧ aeval z g = w * aeval z h

def ValLe (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [NormedField 𝕜] (z : (Σ k, ι k) → 𝕜) (r : ℝ) :
    Prop :=
  ∀ w, HasVal y a s z w → ‖w‖ ≤ r

def supMet {𝕜 : Type} [NormedField 𝕜] (a : K → ℤ) (z : (Σ k, ι k) → 𝕜) : ℝ :=
  ∏ k, ‖fun i : ι k => z ⟨k, i⟩‖ ^ a k

def IsFormOff (P : Ideal (MRing ι)) (u : MRing ι) : Prop :=
  (∃ d, IsMultiHomog u d) ∧ u ∉ P

def powH (A : HermLine ι) (q : ℕ) : HermLine ι where
  a := fun k => (q : ℤ) * A.a k
  h z := A.h z ^ q
  pos z hz := pow_pos (A.pos z hz) q
  smul c z hc := by
    rw [A.smul c z hc, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]

def shiftH (A : HermLine ι) (t : ℝ) : HermLine ι where
  a := A.a
  h z := Real.exp t * A.h z
  pos z hz := mul_pos (Real.exp_pos t) (A.pos z hz)
  smul c z hc := by rw [A.smul c z hc]; ring

def normHt (II : IntersectionSystem) (P : Ideal (MRing ι)) (A : HermLine ι) (D : ℕ) : ℝ :=
  II K ι P (D + 1) (fun _ => A) / (((D : ℝ) + 1) * geomDeg P A D)

def embMean {F : Type} [Field F] [NumberField F] (t : (F →+* ℂ) → ℝ) : ℝ :=
  (∑ sg, t sg) / Fintype.card (F →+* ℂ)

structure IsModelOver (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [Algebra F Ω] (D : ℕ) : Prop where
  one_le : 1 ≤ D
  arith : IsArithVar (mCoordIdeal y) (D + 1)
  bir : Birational y
  uniq : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z

structure IsNefH (P : Ideal (MRing ι)) (M : HermLine ι) : Prop where
  semipos : ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P M
  conj : IsConjInvariantH M
  nef : NefOnFibres P M.a

structure IsGenH (P : Ideal (MRing ι)) (L : HermLine ι) (Λ : ℝ) : Prop where
  pos : 0 < Λ
  semipos : ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P L
  conj : IsConjInvariantH L
  mono : ∃ a : K → ℕ, (L.a = fun k => (a k : ℤ)) ∧ ∀ z ∈ mcPts P, ∀ μ : (Σ k, ι k) →₀ ℕ,
    (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ * L.h z

structure MultBound (y : (Σ k, ι k) → Ω) {F : Type} [Field F] [Algebra F Ω] (M L : HermLine ι) (θ : Ω)
    (u : MRing ι) (c : ℕ → ℝ) (t : (F →+* ℂ) → ℝ) : Prop where
  fin : ∀ (p : ℕ) [Fact p.Prime], ∀ z ∈ algPts p (mCoordIdeal y), aeval z u ≠ 0 →
    ∀ w, HasVal y (L.a - M.a) θ z w → ‖w‖ * supMet M.a z ≤ Real.exp (c p) * supMet L.a z
  arch : ∀ (sg : F →+* ℂ), ∀ z ∈ mcPts (mCoordIdeal y), LiesOver y sg z → aeval z u ≠ 0 →
    ∀ w, HasVal y (L.a - M.a) θ z w → ‖w‖ * M.h z ≤ Real.exp (t sg) * L.h z

def HasMultiplier (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] (M L : HermLine ι)
    (B : ℝ) : Prop :=
  ∃ (θ : Ω) (u : MRing ι) (S : Finset ℕ) (c : ℕ → ℝ) (t : (F →+* ℂ) → ℝ),
    θ ≠ 0 ∧ IsFormOff (mCoordIdeal y) u ∧ (∀ p ∈ S, p.Prime) ∧ (∀ p, 0 ≤ c p) ∧ (∀ p, p ∉ S → c p = 0) ∧
    (∀ sg, t (NumberField.ComplexEmbedding.conjugate sg) = t sg) ∧ MultBound y M L θ u c t ∧
    ∑ p ∈ S, c p + embMean t ≤ B

end GlobalTheory.CompanionTheory.Ar.Small
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P MeasureTheory GlobalTheory.CompanionTheory.Ar.PB Filter Topology

variable {Ψ : Type} [Fintype Ψ] {N e : ℕ}

abbrev LowEnt (Ψ : Type) (N : ℕ) : Type := Ψ × {p : Fin N × Fin N // p.2 < p.1}

def lowMat (q : LowEnt Ψ N ≃ Fin e) (z : Fin e → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => if h : b < a then z (q ⟨τ, ⟨(a, b), h⟩⟩) else if a = b then 1 else 0

def cellDom (j : ℕ) (q : LowEnt Ψ N ≃ Fin e) : Set (Fin e → ℂ) := {z | ∀ τ, InFlagDomain N j (lowMat q z τ)}

def cellDens (j : ℕ) (q : LowEnt Ψ N ≃ Fin e) (z : Fin e → ℂ) : ℝ :=
  ∏ τ, ∏ i : Fin N, Real.exp (-4 * gramLog (sigForm N j) i (lowMat q z τ))

def cellVol (j : ℕ) (q : LowEnt Ψ N ≃ Fin e) (FF : Set (Fin e → ℂ)) : ENNReal :=
  ∫⁻ z in FF, ENNReal.ofReal (cellDens j q z)

structure PieceUnif (S : AnSys e (Ψ × Fin N)) (j n : ℕ) where

  q : Fin n → (LowEnt Ψ N ≃ Fin e)

  π : Fin n → (Fin e → ℂ) → S.X

  FF : Fin n → Set (Fin e → ℂ)
  mem_open : ∀ k, ∀ z ∈ cellDom j (q k), π k z ∈ S.open'
  param : ∀ k, ∀ z ∈ cellDom j (q k), ∃ V, z ∈ V ∧ V ⊆ cellDom j (q k) ∧ IsParam S.A V (π k)
  pot : ∀ k, ∀ z ∈ cellDom j (q k), ∀ p : Ψ × Fin N, ∃ G : (Fin e → ℂ) → ℂ, AnalyticAt ℂ G z ∧
    ∀ᶠ z' in 𝓝 z, (S.potH p).φ (π k z) (π k z') = stepPot N j p.2 (lowMat (q k) z' p.1) + (G z').re
  meas : ∀ k, MeasurableSet (FF k)
  sub : ∀ k, FF k ⊆ cellDom j (q k)
  inj : ∀ k, Set.InjOn (π k) (FF k)
  disj : Pairwise fun k k' => Disjoint (π k '' FF k) (π k' '' FF k')
  cover : IsNull S.A (⋃ k, π k '' FF k)ᶜ

def PieceUnif.vol {S : AnSys e (Ψ × Fin N)} {j n : ℕ} (U : PieceUnif S j n) (k : Fin n) : ENNReal :=
  cellVol j (U.q k) (U.FF k)

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

