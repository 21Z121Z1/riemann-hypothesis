import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaar
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.RiemConst

theorem riemHaar_eq_smul (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)]
    (ν : Measure (realSU X.Ψ X.Gm)) (hr : 1 ≤ r) (hx : IsOrth X x) (hν : ν.IsHaarMeasure)
    (hfib : ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) →
      ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν =
        ∫⁻ z, φ (cpt X x z) ∂muF X x) :
    riemHaar X.Ψ X.Gm x = ENNReal.ofReal
      (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  obtain ⟨hdc, hd0, hdet⟩ := GlobalTheory.T.chartDensity_continuousAt_zero_eq_one E r X x hx
  obtain ⟨hf, hnd⟩ := GlobalTheory.T.totallyRealDegree_and_chartDimension_eq E r X
  obtain ⟨σ, ρ, D₁, hρ, hσ0, hσc, hσB, hσD, hD₁⟩ := GlobalTheory.T.exists_specialUnitary_section_lowerUnitriangular_chart E r X x hx
  obtain ⟨t, Dt, htx, htmul, htc, htD, hDt, hstab⟩ := GlobalTheory.T.exists_diagonalTorus_parametrisation_orthonormalFrame E r X x hx
  have ht0 : t 0 = 1 := by
    have h := congrArg (fun g => (t 0)⁻¹ * g) (htmul 0 0)
    simp only [add_zero, inv_mul_cancel, inv_mul_cancel_left] at h
    exact h.symm
  let D : ChartSp X →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ) :=
    D₁.comp (ContinuousLinearMap.fst ℝ (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ)) +
      Dt.comp (ContinuousLinearMap.snd ℝ (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ))
  have hQD := GlobalTheory.T.hasStrictFDerivAt_mul_curves_matrixGroup_identity X.Ψ r (realSU X.Ψ X.Gm) (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ) σ t D₁ Dt hσ0 ht0 hσD htD
  have hspec : ∀ w : ChartSp X, D w ∈ realLie X.Ψ X.Gm ∧
      (∀ τ a b, b < a → inFrame x (D w) τ a b = nmat X w.1 τ a b) ∧
        ∀ τ a, inFrame x (D w) τ a a = Complex.I * (angles (w.2 τ) a : ℂ) := by
    intro w
    have hDw : D w = D₁ w.1 + Dt w.2 := rfl
    have e : ∀ τ, inFrame x (D w) τ = inFrame x (D₁ w.1) τ + inFrame x (Dt w.2) τ := by
      intro τ
      simp only [inFrame, hDw]
      rw [show Matrix.of ((D₁ w.1 + Dt w.2) τ) = Matrix.of (D₁ w.1 τ) + Matrix.of (Dt w.2 τ) from rfl,
        Matrix.mul_add, Matrix.add_mul]
    obtain ⟨h1, h2, h3⟩ := hD₁ w.1
    obtain ⟨h4, h5⟩ := hDt w.2
    refine ⟨?_, fun τ a b hab => ?_, fun τ a => ?_⟩
    · rw [hDw]; exact (realLie X.Ψ X.Gm).add_mem h1 h4
    · rw [e, Matrix.add_apply, h2 τ a b hab, h5, if_neg (ne_of_gt hab), add_zero]
    · rw [e, Matrix.add_apply, h3, h5, if_pos rfl, zero_add]
  obtain ⟨hDinj, hriem⟩ := GlobalTheory.T.riemannianMeasure_lieAlgebra_eq_smul_map_chartLebesgue E r X x hr hx D hspec
  have hform := GlobalTheory.T.haar_specialUnitary_product_chart_formula E r X x ν σ t ρ hr hx hν hfib hρ hσc hσB htx htmul htc hstab
  have hsurj := GlobalTheory.T.specialUnitary_near_one_eq_chart_mul E r X x σ t ρ hx hρ hσ0 hσc hσB htx htmul htc hstab
  set m := (r - 1) * X.Ψ.card with hm
  set a : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi) ^ m) with ha
  have hpi : 0 < (2 * Real.pi) ^ m := by positivity
  have ha0 : a ≠ 0 := by
    rw [ha, Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have htend : Tendsto (fun w : ChartSp X => ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ m)) (𝓝 0) (𝓝 a) := by
    have h1 : ContinuousAt (fun w : ChartSp X => densF X x w.1) 0 :=
      ContinuousAt.comp (g := densF X x) (f := Prod.fst) (x := (0 : ChartSp X)) hdc continuous_fst.continuousAt
    have h2 := (ENNReal.continuous_ofReal.continuousAt).tendsto.comp ((h1.div_const ((2 * Real.pi) ^ m)).tendsto)
    rw [ha]
    simpa [Function.comp_def, hd0] using h2
  have hρ' : 0 < min ρ Real.pi := lt_min hρ Real.pi_pos
  have hQ0 : (fun w : ChartSp X => σ w.1 * t w.2) 0 = 1 := by simp [hσ0, ht0]
  haveI : (volume : Measure (X.Ψ → Fin (r - 1) → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ChartSp X)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (V (nd X))) (volume : Measure (X.Ψ → Fin (r - 1) → ℝ))
  have hlim := GlobalTheory.T.matrixGroup_chart_density_at_identity X.Ψ r (realSU X.Ψ X.Gm) ν (ChartSp X) volume (fun w => σ w.1 * t w.2) D
    (fun w => ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ m)) a (min ρ Real.pi) hQD hQ0 hDinj hsurj htend
    ha0 hatop hρ' hform
  obtain ⟨hRH, hRdens⟩ := GlobalTheory.SUVol.DensOne.tangentHaar_riemLie X.Ψ X.Gm X.Gm_det x hdet
  have hRH' : (riemHaar X.Ψ X.Gm x).IsHaarMeasure := hRH
  set k := (riemHaar X.Ψ X.Gm x).haarScalarFactor ν with hkdef
  have hk : riemHaar X.Ψ X.Gm x = k • ν := Measure.isMulLeftInvariant_eq_smul _ _
  set K := ENNReal.ofReal (2 ^ nd X * Real.sqrt r ^ X.Ψ.card) with hKdef
  have hK0 : K ≠ 0 := by
    rw [hKdef, Ne, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast hr)
    positivity
  have hKtop : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : Tendsto (fun ε : ℝ => (k : ℝ≥0∞) * (ν (grpBall (realSU X.Ψ X.Gm) ε) /
      ((volume : Measure (ChartSp X)).map D) (tanBall X.Ψ r ε)) * K⁻¹) (𝓝[>] 0) (𝓝 ((k : ℝ≥0∞) * a * K⁻¹)) :=
    ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top))
      (Or.inr (ENNReal.inv_ne_top.2 hK0))
  unfold HasDensityOne at hRdens
  have h2 : Tendsto (fun ε : ℝ => (k : ℝ≥0∞) * (ν (grpBall (realSU X.Ψ X.Gm) ε) /
      ((volume : Measure (ChartSp X)).map D) (tanBall X.Ψ r ε)) * K⁻¹) (𝓝[>] 0) (𝓝 1) := by
    refine hRdens.congr fun ε => ?_
    rw [show tangentHaar (realSU X.Ψ X.Gm) (riemLie X.Ψ X.Gm x) = riemHaar X.Ψ X.Gm x from rfl, hk, hriem]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hK0) (Or.inl hKtop)]
    ring
  have e := tendsto_nhds_unique h1 h2
  have hkval : (k : ℝ≥0∞) = ENNReal.ofReal
      (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) := by
    have e' : (k : ℝ≥0∞) * (a * K⁻¹) = 1 := by rw [← mul_assoc]; exact e
    have hai : a⁻¹ = ENNReal.ofReal ((2 * Real.pi) ^ m) := by
      rw [ha, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
    rw [ENNReal.eq_inv_of_mul_eq_one_left e', ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop), inv_inv, hai,
      hKdef, ← ENNReal.ofReal_mul hpi.le]
    congr 1
    rw [hf, hnd, hm]
    generalize r * (r - 1) / 2 = n1
    generalize r - 1 = n2
    ring
  rw [hk, ← hkval]
  ext s _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.RiemConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW
open scoped FourierTransform

namespace GlobalTheory.JSW.MirCinf

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def IsRapidFamInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X)
    (k : GL (Fin n) (Cinf E) → X → ℂ) (γ : X → GL (Fin n) (Cinf E)) (η : GL (Fin n) (Cinf E) → X → Z →L[ℝ] ℝ) :
    Prop :=
  (∀ i j, Measurable fun x =>(γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
  (∀ (X₀ : Type) [MeasurableSpace X₀] (γ₀ : X₀ → GL (Fin n) (Cinf E)),
    (∀ i j, Measurable fun x =>(γ₀ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) →
      Measurable (fun p : X₀ × X =>k (γ₀ p.1) p.2) ∧ ∀ z, Measurable fun p : X₀ × X =>η (γ₀ p.1) p.2 z) ∧
  ∀ N : ℕ, ∃ (C : ℝ) (M : ℕ), ∀ q, Integrable (fun x =>‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N) ν ∧
    ∫ x, ‖k q x‖ * (htInf (γ x) * (1 + ‖η q x‖)) ^ N ∂ν ≤ C * htInf q ^ M

def sandCLMInf (A B : Matrix (Fin n) (Fin n) (Cinf E)) :
    (Fin n → Fin n → Cinf E) →L[ℝ] (Fin n → Fin n → Cinf E) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x i j =>(A * Matrix.of x * B) i j
      map_add' := fun x y =>by
        funext i j
        change (A * (Matrix.of x + Matrix.of y) * B) i j = (A * Matrix.of x * B) i j + (A * Matrix.of y * B) i j
        rw [mul_add, add_mul, Matrix.add_apply]
      map_smul' := fun c x =>by
        funext i j
        change (A * (c • Matrix.of x) * B) i j = c • (A * Matrix.of x * B) i j
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply] }

theorem sandCLMInf_apply (A B : Matrix (Fin n) (Fin n) (Cinf E)) (x : Fin n → Fin n → Cinf E) (i j : Fin n) :
    sandCLMInf A B x i j = (A * Matrix.of x * B) i j := rfl

def jacInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ := ∏ w : InfinitePlace E, Complex.normSq (x.det w) ^ n

open Classical in

def secKInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (R : ℝ) (σ₀ : Fin n → Fin n → Cinf E)
    (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : ℂ :=
  if IsUnit (Matrix.of p.1) ∧ htInf (toGLInf (Matrix.of p.1)) ≤ R * htInf q then
    ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * κ p.2 *
      (𝐞 (τ p.2 (0, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1) σ₀)) : ℂ)
  else 0

def secEtaInf {X Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : Z →L[ℝ] (Fin n → Fin n → Cinf E))
    (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ) (q : GL (Fin n) (Cinf E))
    (p : (Fin n → Fin n → Cinf E) × X) : Z →L[ℝ] ℝ :=
  (τ p.2).comp ((ContinuousLinearMap.id ℝ Z).prod
    ((sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of p.1)).comp L))

theorem jacInf_mul (x y : Matrix (Fin n) (Fin n) (Cinf E)) : jacInf (x * y) = jacInf x * jacInf y := by
  simp only [jacInf, Matrix.det_mul, Pi.mul_apply, map_mul, mul_pow, Finset.prod_mul_distrib]

example (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] :
    IsRapidFamInf (Measure.dirac ()) (fun (_ : GL (Fin n) (Cinf E)) (_ : Unit) =>(1 : ℂ)) (fun _ =>1)
      (fun _ _ =>(0 : Z →L[ℝ] ℝ)) := by
  refine ⟨fun _ _ =>measurable_const, fun X₀ _ γ₀ _ =>⟨measurable_const, fun _ =>measurable_const⟩, fun N =>
    ⟨htInf (1 : GL (Fin n) (Cinf E)) ^ N, 0, fun q =>⟨integrable_const _, ?_⟩⟩⟩
  simp

end GlobalTheory.JSW.MirCinf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerDifferentiableOn
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin.Holo

open Matrix
open scoped ComplexOrder

noncomputable section

theorem differentiable_det {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {n : Type*} [Fintype n]
    [DecidableEq n] (f : F → Matrix n n ℂ) (hf : ∀ i j, Differentiable ℂ fun x => f x i j) :
    Differentiable ℂ fun x => (f x).det := by
  simp only [Matrix.det_apply']
  fun_prop

theorem det_block_ne {r p : ℕ} (hp : p ≤ r) (m : Matrix (Fin r) (Fin r) ℂ)
    (hpos : ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp)).PosDef) :
    (m.submatrix (Fin.castLE hp) (Fin.castLE hp)).det ≠ 0 := by
  intro hdet
  set A := m.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  have hdc : (A.map (starRingEnd ℂ)).det = 0 := by
    rw [show A.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix A from rfl, ← RingHom.map_det, hdet, map_zero]
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdc
  have h := hpos.dotProduct_mulVec_pos hv
  set u : Fin r → ℂ := fun k => ∑ b, starRingEnd ℂ (m k (Fin.castLE hp b)) * v b with hu_def
  have hu : ∀ i : Fin p, u (Fin.castLE hp i) = 0 := fun i => by
    have := congrFun hAv i
    simpa [hA, Matrix.mulVec, dotProduct, u] using this
  have hq : star v ⬝ᵥ ((mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ)).submatrix (Fin.castLE hp) (Fin.castLE hp) *ᵥ v) =
      ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) := by
    simp only [dotProduct, mulVec, Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.map_apply, hu_def, map_sum, map_mul, Complex.conj_conj,
      Finset.mul_sum, Finset.sum_mul, Pi.star_apply, Matrix.diagonal_apply, mul_ite, ite_mul, mul_zero,
      zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [RCLike.star_def]
    ring
  have hq' : ∑ k : Fin r, ((sgn p (k : ℕ) : ℝ) : ℂ) * (starRingEnd ℂ (u k) * u k) =
      ((∑ k : Fin r, sgn p (k : ℕ) * Complex.normSq (u k) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
  rw [hq, hq', Complex.zero_lt_real] at h
  refine absurd h (not_lt.2 (Finset.sum_nonpos fun k _ => ?_))
  by_cases hk : (k : ℕ) < p
  · have h0 : u k = 0 := by
      have := hu ⟨k, hk⟩
      rwa [show Fin.castLE hp ⟨k, hk⟩ = k from Fin.ext rfl] at this
    simp [h0]
  · simp only [sgn, if_neg hk]
    nlinarith [Complex.normSq_nonneg (u k)]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem det_Mx₂₂_ne (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (τ : X.Ψ) : (KU.Mx X x0 x τ).toBlocks₂₂.det ≠ 0 := by
  have h0 := ExF.det_ne_of_orth X ho τ
  set m := (mat x0 τ)⁻¹ * mat x τ with hm
  have hxm : mat x τ = mat x0 τ * m := by
    rw [hm, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 h0)]
  have hg : gram τ.1 X.Gm (mat x τ) = mᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
      m.map (starRingEnd ℂ) := by
    rw [hxm, FrameDegreeData.gram_mul, ho τ]
  have hpos := X.gramPos_posDef hx τ
  rw [Data.gramPos, hg] at hpos
  have hb : (KU.Mx X x0 x τ).toBlocks₂₂ = m.submatrix (Fin.castLE X.p0_le) (Fin.castLE X.p0_le) := by
    ext i j
    simp [KU.Mx, KU.tl, Matrix.toBlocks₂₂, KU.eT_inr, m]
  rw [hb]
  exact det_block_ne X.p0_le m hpos

theorem differentiable_Mx (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) (i j) :
    Differentiable ℂ fun x : Frame X.Ψ r => KU.Mx X x0 x τ i j := by
  simp only [KU.Mx, KU.tl, Matrix.submatrix_apply, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

theorem qS_differentiableOn (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (k : ℕ) :
    DifferentiableOn ℂ (qS X x0 k) X.dom := by
  have hd1 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).det := fun τ =>
    differentiable_det _ (differentiable_Mx X x0 τ)
  have hd2 : ∀ τ, Differentiable ℂ fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det := fun τ =>
    differentiable_det (fun x => (KU.Mx X x0 x τ).toBlocks₂₂) fun i j =>
      differentiable_Mx X x0 τ (Sum.inr i) (Sum.inr j)
  have hq : qS X x0 k = ∏ τ, fun x : Frame X.Ψ r =>
      ((KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) ^ k := by
    funext x
    simp [qS, Finset.prod_apply]
  rw [hq]
  refine Finset.prod_induction _ (fun g : Frame X.Ψ r → ℂ => DifferentiableOn ℂ g X.dom)
    (fun a b ha hb => ha.mul hb) (differentiableOn_const 1) fun τ _ => ?_
  have hne : ∀ x ∈ X.dom, (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2 ≠ 0 := fun x hx =>
    pow_ne_zero 2 (det_Mx₂₂_ne X ho hx τ)
  have h1 := (hd1 τ).differentiableOn (s := X.dom)
  have h2 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom :=
    ((hd2 τ).differentiableOn).pow 2
  have h3 : DifferentiableOn ℂ (fun x => (KU.Mx X x0 x τ).det / (KU.Mx X x0 x τ).toBlocks₂₂.det ^ 2) X.dom :=
by
    simp only [div_eq_mul_inv]
    exact h1.mul (h2.inv hne)
  exact h3.pow k

theorem qS_holomorphicOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r),
    IsOrth X x0 → ∀ k : ℕ, DifferentiableOn ℂ (qS X x0 k) X.dom :=
  fun _ _ _ _ _ X x0 ho k => qS_differentiableOn X x0 ho k

end

end GlobalTheory.ScalarPoin.Holo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerRmulBorel
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory

namespace GlobalTheory.ScalarPoin

noncomputable section

theorem det_ratio_pow_mul_borel_eq_weight_prod {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (k : ℕ) (b : Frame X.Ψ r) (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) (M : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) :
    ((M * KU.tl X (mat b τ)).det / (M * KU.tl X (mat b τ)).toBlocks₂₂.det ^ 2) ^ k =
      (∏ i, b τ i i ^ laS X k τ i) * (M.det / M.toBlocks₂₂.det ^ 2) ^ k := by
  set T := KU.tl X (mat b τ) with hT
  have h22 : (M * T).toBlocks₂₂ = M.toBlocks₂₂ * T.toBlocks₂₂ := by
    rw [KU.toBlocks₂₂_mul, KU.tl_bor₁₂ X hb τ, Matrix.mul_zero, zero_add]
  set D1 : ℂ := ∏ j : Fin (r - X.p0), b τ (KU.eT X (Sum.inl j)) (KU.eT X (Sum.inl j)) with hD1
  set D2 : ℂ := ∏ i : Fin X.p0, b τ (KU.eT X (Sum.inr i)) (KU.eT X (Sum.inr i)) with hD2
  have hD2ne : D2 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => FrameDegreeData.bdiag_ne X hb τ _
  have hdetT : T.det = D1 * D2 := by
    have ht : (mat b τ).BlockTriangular id := fun i j hij => (hb τ).2 i j hij
    rw [hT, KU.tl, Matrix.det_submatrix_equiv_self, Matrix.det_of_upperTriangular ht,
      ← Fintype.prod_equiv (KU.eT X) (fun s => mat b τ (KU.eT X s) (KU.eT X s)) _ (fun _ => rfl),
      Fintype.prod_sum_type]
    rfl
  have hdetT22 : T.toBlocks₂₂.det = D2 := by
    have ht : T.toBlocks₂₂.BlockTriangular id := by
      intro i j hij
      simp only [hT, KU.tl, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, KU.eT_inr]
      exact (hb τ).2 _ _ (show (Fin.castLE X.p0_le j : ℕ) < Fin.castLE X.p0_le i from hij)
    rw [Matrix.det_of_upperTriangular ht]
    rfl
  have hchar : (∏ i, b τ i i ^ laS X k τ i) = D1 ^ k * (D2 ^ k)⁻¹ := by
    rw [← Fintype.prod_equiv (KU.eT X) (fun s => b τ (KU.eT X s) (KU.eT X s) ^ laS X k τ (KU.eT X s)) _
      (fun _ => rfl), Fintype.prod_sum_type, hD1, hD2, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_inv_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      have : X.p0 ≤ (KU.eT X (Sum.inl j) : ℕ) := by simp [KU.eT]
      simp [laS, this]
    · refine Finset.prod_congr rfl fun i _ => ?_
      have : ¬ X.p0 ≤ (KU.eT X (Sum.inr i) : ℕ) := by simp [KU.eT]
      simp [laS, this, zpow_neg]
  rw [Matrix.det_mul, h22, Matrix.det_mul, hdetT, hdetT22, hchar, ← inv_pow, ← mul_pow, ← mul_pow]
  congr 1
  have hc : D2 * (D2 ^ 2)⁻¹ = D2⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hD2ne, one_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, mul_inv]
  calc M.det * (D1 * D2) * ((M.toBlocks₂₂.det ^ 2)⁻¹ * (D2 ^ 2)⁻¹)
      = D1 * (D2 * (D2 ^ 2)⁻¹) * (M.det * (M.toBlocks₂₂.det ^ 2)⁻¹) := by ring
    _ = _ := by rw [hc]

theorem qS_rmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → qS X x0 k (rmul x b) = bchar (laS X k) b * qS X x0 k x := by
  intro E _ _ _ r X x0 k x b hb
  unfold qS bchar
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [KU.Mx_rmul]
  exact det_ratio_pow_mul_borel_eq_weight_prod X k b hb τ _

end

end GlobalTheory.ScalarPoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusTangentVectorsAddMonoidHomStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_tangentVectors_addMonoidHom : ∀ (k : Type) [Field k] (X : Type) [AddCommGroup X], ∃ U : (X →+ k) → (epsPt (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X), Function.Injective U ∧ (∀ l, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (U l).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ splitTorus (Sp k) X).left) ∧ (∀ l l', U (l + l') = U l * U l') ∧ (∀ (t : k) l, (U ((AddMonoidHom.mulLeft t).comp l)).left = spMap (epsScale t) ≫ (U l).left) ∧ ∀ (τ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X) (ρ : X →+ X), (∀ χ, chV τ χ = charUnit (Sp k) X (ρ χ)) → ∀ l, U l ≫ τ = U (l.comp ρ) := by
  first | exact @GlobalTheory.splitTorus_tangent_addHom | exact GlobalTheory.splitTorus_tangent_addHom | (intros; apply GlobalTheory.splitTorus_tangent_addHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StaircaseIdealConjugateInverse
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem exists_ringEquiv_mem_iff_star {E : Type} [Field E] [NumberField E] [StarRing E] :
    ∃ σ : FractionalIdeal (𝓞 E)⁰ E ≃+* FractionalIdeal (𝓞 E)⁰ E,
      ∀ (a : FractionalIdeal (𝓞 E)⁰ E) (x : E), x ∈ σ a ↔ star x ∈ a := by
  let τ : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (starRingAut : E ≃+* E)
  have hτ : ∀ x : E, IsFractionRing.ringEquivOfRingEquiv (K := E) (L := E) τ x = star x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap, star_div₀]
    rfl
  refine ⟨FractionalIdeal.ringEquivOfRingEquiv E E τ, fun a x => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    have h := (congrArg star (hτ y)).trans (star_star y)
    exact h.symm ▸ hy
  · exact ⟨star x, h, (hτ (star x)).trans (star_star x)⟩

theorem stairId_ne_zero_and_mem_rev_iff : ∀ (D : D7) (𝔞 𝔞' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), 𝔞 ≠ 0 → (∀ x, x ∈ 𝔞' ↔ star x ∈ 𝔞) → ∀ (c : ℕ) (p : Fin c), stairId 𝔞 𝔞' c p ≠ 0 ∧ ∀ x, x ∈ stairId 𝔞 𝔞' c p.rev ↔ star x ∈ (stairId 𝔞 𝔞' c p)⁻¹ := by
  intro D 𝔞 𝔞' h0 h c p
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_mem_iff_star (E := D.host.E)
  have h1 : σ 𝔞 = 𝔞' := by
    ext x
    rw [hσ, h]
  have h2 : σ 𝔞' = 𝔞 := by
    ext x
    rw [hσ, h, star_star]
  have h0' : 𝔞' ≠ 0 := h1 ▸ (map_ne_zero_iff _ σ.injective).2 h0
  refine ⟨mul_ne_zero (pow_ne_zero _ h0) (inv_ne_zero (pow_ne_zero _ h0')), fun x => ?_⟩
  have h3 : σ (stairId 𝔞' 𝔞 c p.rev) = stairId 𝔞 𝔞' c p.rev := by
    unfold stairId
    rw [map_mul, map_inv₀, map_pow, map_pow, h1, h2]
  rw [← stairId_rev, ← hσ, h3]

end GlobalTheory.ChiGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSL2AdelesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_SL2_adeles : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ g : Matrix (Fin 2) (Fin 2) (AF F), g.det = 1 → g ∈ closure {x : Matrix (Fin 2) (Fin 2) (AF F) | ∃ γ : Matrix (Fin 2) (Fin 2) F, γ.det = 1 ∧ ∃ h : Matrix (Fin 2) (Fin 2) (AF F), h.det = 1 ∧ ε • (h - 1) = h - 1 ∧ x = γ.map (algebraMap F (AF F)) * h} := by
  first | exact @GlobalTheory.StrongApproximationSL2.strongApprox_SL2 | exact GlobalTheory.StrongApproximationSL2.strongApprox_SL2 | (intros; apply GlobalTheory.StrongApproximationSL2.strongApprox_SL2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameProductCharacterInverseStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_product_character_inverse : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (hle : ∀ w : ↥Pg, l.Mb ≤ w.1.asIdeal) (K : Type) [Field K] (σ : K →+* ℂ) (μ : (AE D)ˣ →* Circle) (χ : ∀ w : ↥Pg, (Formalism.L2.DIV.kP w.1)ˣ →* Kˣ), LatticeBasisLifts.IsInvTame σ Pg μ χ → LevelLiftConditions.IsInvTame σ l.Mb (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) μ (chiProd hle χ) := by
  first | exact @GlobalTheory.GeoActCompare.TameAB.isInvTame_chiProd | exact GlobalTheory.GeoActCompare.TameAB.isInvTame_chiProd | (intros; apply GlobalTheory.GeoActCompare.TameAB.isInvTame_chiProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsEigenBasis
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.EigenReduction

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

open MonObj in

theorem isCombAtG_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

end GlobalTheory.EigenReduction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentTranslationMeasurePreservingStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_translation_measure_preserving : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GL (Fin n) (Cinf E)), u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n) → ∃ τ : Vp E n ≃ᵐ Vp E n, MeasurePreserving τ volume volume ∧ ∀ t, nu (τ t) = nu t * (u : Matrix (Fin n) (Fin n) (Cinf E)) := by
  first | exact @GlobalTheory.WhitBump.exists_shear_measurePreserving | exact GlobalTheory.WhitBump.exists_shear_measurePreserving | (intros; apply GlobalTheory.WhitBump.exists_shear_measurePreserving <;> assumption)
end

