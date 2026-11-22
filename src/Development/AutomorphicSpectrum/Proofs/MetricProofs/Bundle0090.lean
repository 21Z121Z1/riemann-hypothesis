import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0062
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0044
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernel
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.IntegralKernel

theorem exists_clear_denominators {g : ℕ} (w : Fin g → ℚ) :
    ∃ (D : ℤ) (v : Fin g → ℤ), D ≠ 0 ∧ ∀ i, (v i : ℚ) = (D : ℚ) * w i := by
  classical
  have hdvd : ∀ i, ∃ k : ℤ, (∏ j, ((w j).den : ℤ)) = ((w i).den : ℤ) * k := fun i =>
    Finset.dvd_prod_of_mem (fun j => ((w j).den : ℤ)) (Finset.mem_univ i)
  choose k hk using hdvd
  refine ⟨∏ j, ((w j).den : ℤ), fun i => (w i).num * k i, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (w j).den_nz
  · intro i
    rw [hk i]
    push_cast
    have h := Rat.mul_den_eq_num (w i)
    rw [← h]
    ring

theorem cast_mulVec {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) (i : Fin g) :
    (((S *ᵥ v) i : ℤ) : ℚ) = ((S.map (Int.cast : ℤ → ℚ)) *ᵥ (fun j => (v j : ℚ))) i := by
  simp [Matrix.mulVec, dotProduct]

theorem exists_smul_eq_mulVec (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) (hS : Sᵀ = S)
    (u : Fin g → ℤ) (hu : ∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) :
    ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  classical
  let Sq : Matrix (Fin g) (Fin g) ℚ := S.map (Int.cast : ℤ → ℚ)
  let uq : Fin g → ℚ := fun i => (u i : ℚ)
  have hSq : Sqᵀ = Sq := by
    ext i j
    have := congrFun (congrFun hS i) j
    simp only [Matrix.transpose_apply] at this
    simp [Sq, this]

  have hker : ∀ w : Fin g → ℚ, Sq *ᵥ w = 0 → uq ⬝ᵥ w = 0 := by
    intro w hw
    obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators w
    have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • w := by
      funext j; simp [hv j]
    have hSv : S *ᵥ v = 0 := by
      funext i
      have h1 := cast_mulVec S v i
      rw [hvq, Matrix.mulVec_smul] at h1
      have h2 : (((S *ᵥ v) i : ℤ) : ℚ) = 0 := by
        rw [h1]
        change ((D : ℚ) • (Sq *ᵥ w)) i = 0
        rw [hw]; simp
      exact_mod_cast h2
    have h0 := hu v hSv
    have h1 : ((u ⬝ᵥ v : ℤ) : ℚ) = (D : ℚ) * (uq ⬝ᵥ w) := by
      simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, hv, uq]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0] at h1
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    simpa [hDq] using h1.symm
  let f : (Fin g → ℚ) →ₗ[ℚ] (Fin g → ℚ) := Sq.mulVecLin
  let φ : Module.Dual ℚ (Fin g → ℚ) :=
    { toFun := fun w => uq ⬝ᵥ w
      map_add' := fun a b => dotProduct_add uq a b
      map_smul' := fun r a => by simp [dotProduct_smul] }
  have hφ : φ ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact hker w (by simpa [f] using hw)
  obtain ⟨ψ, hψ⟩ := hφ
  let c : Fin g → ℚ := fun i => ψ (Pi.single i 1)
  have hψc : ∀ w, ψ w = c ⬝ᵥ w := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ' w]
    simp [map_sum, c, dotProduct, mul_comm]
  have hu_eq : uq = Sq *ᵥ c := by
    funext i
    have h1 : φ (Pi.single i 1) = uq i := by
      change uq ⬝ᵥ Pi.single i 1 = uq i
      simp
    have h2 : φ (Pi.single i 1) = ψ (Sq *ᵥ Pi.single i 1) := by
      rw [← hψ]; rfl
    rw [← h1, h2, hψc, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSq]
    simp
  obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators c
  refine ⟨D, v, hD, ?_⟩
  funext i
  have h1 := cast_mulVec S v i
  have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • c := by
    funext j; simp [hv j]
  rw [hvq, Matrix.mulVec_smul] at h1
  have h2 : (((D • u) i : ℤ) : ℚ) = (((S *ᵥ v) i : ℤ) : ℚ) := by
    rw [h1]
    change _ = ((D : ℚ) • (Sq *ᵥ c)) i
    rw [← hu_eq]
    simp [uq]
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.IntegralKernel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsKerProj
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem exists_isKerProj (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) :
    ∃ Pr : Matrix (Fin g) (Fin g) ℝ, IsKerProj S Pr := by
  classical
  set M : Matrix (Fin g) (Fin g) ℝ := S.map (fun x : ℤ => (x : ℝ)) with hM
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin g)) := LinearMap.ker (Matrix.toEuclideanLin M)
  let P : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g) :=
    (K.starProjection : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g))
  let Pr : Matrix (Fin g) (Fin g) ℝ := Matrix.toEuclideanLin.symm P
  have hPr : Matrix.toEuclideanLin Pr = P := LinearEquiv.apply_symm_apply _ _
  have hmv : ∀ v : Fin g → ℝ, Pr *ᵥ v = WithLp.ofLp (P (WithLp.toLp 2 v)) := by
    intro v
    rw [← hPr, Matrix.toEuclideanLin_apply]
  have hidem : ∀ x, P (P x) = P x := by
    intro x
    have hx : K.starProjection x ∈ K := Submodule.starProjection_apply_mem K x
    exact (Submodule.starProjection_eq_self_iff).2 hx
  refine ⟨Pr, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hmv, hmv,
      WithLp.toLp_ofLp, hidem]
  · have hs : Pr.IsHermitian := by
      rw [Matrix.isHermitian_iff_isSymmetric, hPr]
      exact Submodule.starProjection_isSymmetric K
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hs.eq
  · intro v
    rw [hmv]
    constructor
    · intro h
      have hk : WithLp.toLp 2 v ∈ K := by
        have h' : M *ᵥ v = 0 := h
        rw [LinearMap.mem_ker, Matrix.toEuclideanLin_apply]
        simp [h']
      have : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := (Submodule.starProjection_eq_self_iff).2 hk
      rw [this]
    · intro h
      have h1 : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := by
        rw [← WithLp.toLp_ofLp (p := 2) (P (WithLp.toLp 2 v)), h]
      have hk : WithLp.toLp 2 v ∈ K := (Submodule.starProjection_eq_self_iff).1 h1
      rw [LinearMap.mem_ker, Matrix.toEuclideanLin_apply] at hk
      have h' : M *ᵥ v = 0 := by simpa using hk
      exact h'

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSmoothMetricsNonnegDensity
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxTwist

theorem isSheet_bot_of_isSetSheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hS : ∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (hγ : IsSetSheet S Ψ y w γ) : IsSheet ⊥ Ψ y w γ := by
  refine ⟨hγ.1, hγ.2.mono fun y' hy' => ⟨hy'.1, ⟨hS _ hy'.2.1, fun f hf => ?_⟩, hy'.2.2⟩⟩
  rw [Ideal.mem_bot.1 hf]
  simp

theorem exists_dominating_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by
  intro K _ ι _ e L hL
  classical
  choose T hTs hTp hLTp using fun j =>
    GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.proof GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof K ι (L j) (hL j)
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hTs j)
  refine ⟨fun j => ((L j).tensor (T j)).tensor (T j), fun j => isSmoothHerm_tensor (hLT j) (hTs j), ?_⟩
  intro S Ψ hS
  have hab : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ → |maDensity (fun j y' => pot L j (γ y')) y| ≤
        3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => GroundTheory.Heights₂.Heights.Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp
      (isSheet_bot_of_isSetSheet hS hγ)
  have hnn : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ →
        0 ≤ maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => nonneg_of_mul_nonneg_right ((abs_nonneg _).trans (hab hγ)) (by positivity)
  refine ⟨fun g y w hg => ?_, fun g g' y w hgg => ?_⟩
  · unfold setSheetDensity
    split_ifs with hγ
    · exact mul_nonneg (hg _) (hnn hγ.choose_spec)
    · exact le_rfl
  · unfold setSheetDensity
    by_cases hγ : ∃ γ, IsSetSheet S Ψ y w γ
    · rw [dif_pos hγ, dif_pos hγ]
      have hs := hγ.choose_spec
      have hmem : hγ.choose y ∈ S := hs.2.self_of_nhds.2.1
      have hg := hgg _ hmem
      rw [abs_mul]
      calc |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y|
          ≤ g' (hγ.choose y) * (3 ^ e * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) :=
            mul_le_mul hg (hab hs) (abs_nonneg _) ((abs_nonneg _).trans hg)
        _ = 3 ^ e * (g' (hγ.choose y) * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) := by ring
    · rw [dif_neg hγ, dif_neg hγ]
      simp

end GlobalTheory.CompanionTheory.Ar.Pub.CxTwist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def proj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k × ι k) → ℂ :=
  fun q => z ⟨q.1, q.2.1⟩ * starRingEnd ℂ (z ⟨q.1, q.2.2⟩) / ((∑ i, ‖z ⟨q.1, i⟩‖ ^ 2 : ℝ) : ℂ)

def Pts (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Set ((Σ k, ι k × ι k) → ℂ) :=
  proj '' conePts P

variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)}

def rep (x : Pts P) : (Σ k, ι k) → ℂ := x.2.choose

theorem rep_mem (x : Pts P) : rep x ∈ conePts P := x.2.choose_spec.1

theorem proj_rep (x : Pts P) : proj (rep x) = x.1 := x.2.choose_spec.2

variable (P) in

def src (p : (k : K) → ι k) : Set (Pts P) := {x | ∀ k, rep x ⟨k, p k⟩ ≠ 0}

variable (P) in

def coord (p : (k : K) → ι k) (x : Pts P) : Fin (Fintype.card (Σ k, ι k)) → ℂ :=
  renPt (affCoord p (rep x))

variable (P) in

def ideal (p : (k : K) → ι k) : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  (chartIdeal P p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)

open Classical in

def lift (p : (k : K) → ι k) (q : Σ k, ι k) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  if q.2 = p q.1 then 1 else X (Fintype.equivFin (Σ k, ι k) q)

variable (P) in

def bd (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  ((chartIdeal (P ⊔ D) p).map (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)).radical

theorem finite_minimalPrimes (I : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : I.minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

variable (P) in

def rc (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : ℕ := (finite_minimalPrimes (P ⊔ D)).toFinset.card

variable (P) in

def compIdeal (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).1

variable (P) in

def comp (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) : Set (Pts P) :=
  {x | ∀ f ∈ compIdeal P D k, eval (rep x) f = 0}

def ordAlong (Q P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (f : MvPolynomial (Σ k, ι k) ℂ) : ℕ :=
  sSup {m : ℕ | ∃ s ∉ Q, s * f ∈ Q ^ m ⊔ P}

theorem compIdeal_mem (D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (k : Fin (rc P D)) :
    compIdeal P D k ∈ (P ⊔ D).minimalPrimes := by
  exact (Set.Finite.mem_toFinset _).1 ((finite_minimalPrimes (P ⊔ D)).toFinset.equivFin.symm k).2

theorem eval_lift (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) (q : Σ k, ι k) :
    eval (coord P p x) (lift p q) = affCoord p (rep x) q := by
  classical
  unfold lift
  split_ifs with h
  · obtain ⟨k, i⟩ := q
    simp only at h
    subst h
    simp [affCoord, hx k]
  · simp [coord, renPt]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPointsStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_base_point_maps_to_points : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.comp_v_mem_mcPts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointRegularStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_base_point_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (s : M.Ω), zb ∈ mcPts (mCoordIdeal M'.x) → RegAt M.x (mCoordIdeal (zb ∘ Cv.v)) s → RegAt M'.x (mCoordIdeal zb) (Cv.φ s) ∧ valAt M'.x (Cv.φ s) zb = valAt M.x s (zb ∘ Cv.v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi.regAt_φ_valAt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi.regAt_φ_valAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi.regAt_φ_valAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFrameCompatibilityStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frame_compatibility : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal b) → M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ τ, IsBlockDiag j (Cv.trans F' F b τ) ∧ (Cv.trans F' F b τ).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.trans_blockDiag_det | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.trans_blockDiag_det | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.trans_blockDiag_det <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesValueAtPointStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_frames_value_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → (∀ τ, IsBlockDiag j (h τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', z ⟨k', m'⟩ = a * CovMap.LocImg.plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.img Cv F' F z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M'.blk z ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F' F (basePart M'.blk z) p.1 * h p.1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTransferIdealEqStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_transfer_ideal_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M), mCoordIdeal (transPt Cv) = mCoordIdeal y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mCoordIdeal_transPt | exact GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mCoordIdeal_transPt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovGraph.mCoordIdeal_transPt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeightStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height : FlagHeight := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.flagHeight_holds | exact GlobalTheory.CompanionTheory.Ar.PB.flagHeight_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.flagHeight_holds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeScalarFactorStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_change_scalar_factor : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), M.IsFrame F₁ → M.IsFrame F₂ → (∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F₂.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ ρ : M.Ω, ρ ≠ 0 ∧ ∀ (m : ι k) (I' : Finset (Fin N)), IsStepRows N j p.2 I' → ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = ρ * F₂.u ⟨k, m⟩ I' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.plucker_change_of_frame | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.plucker_change_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.plucker_change_of_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalNormComparisonStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameData_local_norm_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ z ∈ pO M Rb keep v F kb V r h, ∀ z' ∈ mcPts (mCoordIdeal (y ∘ v)), SameOrbit z' z → z' ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε z' = pRho M Rb keep v F kb r h ε z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main | exact GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main <;> assumption)
end

