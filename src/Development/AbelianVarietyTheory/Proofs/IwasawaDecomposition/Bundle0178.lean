import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
import Formalism.LocalRingCardinality.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0173
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology

namespace GlobalTheory.GardingVec

theorem contDiff_setIntegral_nat {X P E : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K) {a : X → E} (ha : Continuous a)
    (m : ℕ) : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (Ψ : P × E → F),
      ContDiff ℝ ∞ Ψ → ContDiff ℝ m fun p => ∫ x in K, Ψ (p, a x) ∂μ := by
  first
  | exact @_root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral
  | exact _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral
  | (apply _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SetIntegralSmoothness.contDiff_setIntegral ..)

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_list_prod {n : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (l : List (P → Matrix (Fin n) (Fin n) ℂ)) (h : ∀ f ∈ l, ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p => (l.map fun f => f p).prod := by
  induction l with
  | nil => simpa using contDiff_const
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))

theorem contDiff_expProd {n k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
  have := contDiff_list_prod (List.ofFn fun i => fun t : Fin k → ℝ => NormedSpace.exp (t i • Xs i)) (by
    intro f hf
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hf
    have h1 : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact h1.comp ((contDiff_apply ℝ ℝ i).smul contDiff_const))
  simpa [List.map_ofFn, Function.comp_def] using this

theorem contDiff_conjTranspose {n : ℕ} : ContDiff ℝ ∞ fun x : Matrix (Fin n) (Fin n) ℂ => xᴴ := by
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun x => xᴴ
      map_add' := fun x y => conjTranspose_add x y
      map_smul' := fun c x => by simp [conjTranspose_smul] }
  exact (LinearMap.toContinuousLinearMap L).contDiff

open Formalism.MainNotions.S in

theorem exists_garding {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) :
    ∃ v : H, v ≠ 0 ∧ ∀ (k : ℕ) (x : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ x →
      (∀ t, x t ∈ UJset ε) → ContDiff ℝ ∞ fun t => σ (x t) v := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := Formalism.REAL.isClosedEmbeddingMatrix n ε
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set μ := Formalism.REAL.muG ε
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : Formalism.REAL.UJ ε => σ (umat g) w := (hcont w).comp_continuous hu hmem
  have hone : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := hmem 1
  have hnb : {g | ‖σ g w - w‖ < ‖w‖ / 2} ∈ 𝓝[UJset ε] (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have h := (hcont w 1 hone) (Metric.ball_mem_nhds _ (half_pos hwpos))
    simpa [h1, Set.preimage, dist_eq_norm] using h
  obtain ⟨U, hU, hUs⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hnb
  obtain ⟨φ, hφU, hφc, hφ, hφr, hφ1⟩ := exists_contDiff_tsupport_subset (n := ⊤) hU
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => (hφr ⟨y, rfl⟩).1
  have hψ : Continuous fun g : Formalism.REAL.UJ ε => φ (umat g) := hφ.continuous.comp hu
  have hψc : HasCompactSupport fun g : Formalism.REAL.UJ ε => φ (umat g) := hφc.comp_isClosedEmbedding hemb
  have hint : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g) • σ (umat g) w) μ :=
    (hψ.smul hb).integrable_of_hasCompactSupport hψc.smul_right
  have hψi : Integrable (fun g : Formalism.REAL.UJ ε => φ (umat g)) μ := hψ.integrable_of_hasCompactSupport hψc
  have hpos : 0 < ∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ :=
    hψ.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hψc (fun g => hφ0 _)
      (by show φ 1 ≠ 0; rw [hφ1]; exact one_ne_zero)
  refine ⟨∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ, ?_, ?_⟩
  · intro h0
    have e1 : ∫ g : Formalism.REAL.UJ ε, (φ (umat g) • σ (umat g) w - φ (umat g) • w) ∂μ
        = -((∫ g : Formalism.REAL.UJ ε, φ (umat g) ∂μ) • w) := by
      rw [integral_sub hint (hψi.smul_const w), h0, integral_smul_const, zero_sub]
    have e2 : ‖∫ g : Formalism.REAL.UJ ε, (φ (umat g) • σ (umat g) w - φ (umat g) • w) ∂μ‖
        ≤ ∫ g : Formalism.REAL.UJ ε, φ (umat g) * (‖w‖ / 2) ∂μ := by
      refine norm_integral_le_of_norm_le (hψi.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hφ0 _)]
      by_cases hg : φ (umat g) = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hUs ⟨hφU (subset_tsupport _ hg), hmem g⟩)) (hφ0 _)
    rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hpos.le, integral_mul_const] at e2
    nlinarith [mul_pos hpos hwpos]
  · intro k x hx hxG
    let y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ := fun t => Formalism.REAL.Jm ε * (x t)ᴴ * Formalism.REAL.Jm ε
    have hy : ContDiff ℝ ∞ y := (contDiff_const.mul (contDiff_conjTranspose.comp hx)).mul contDiff_const
    have hyx : ∀ t, y t * x t = 1 := fun t => by
      have h : (x t)ᴴ * Formalism.REAL.Jm ε * x t = Formalism.REAL.Jm ε := hxG t
      calc y t * x t = Formalism.REAL.Jm ε * ((x t)ᴴ * Formalism.REAL.Jm ε * x t) := by simp only [y, Matrix.mul_assoc]
        _ = 1 := by rw [h, Formalism.REAL.Jm_mul_self]
    have hxy : ∀ t, x t * y t = 1 := fun t => mul_eq_one_comm.1 (hyx t)
    have hform : ∀ t, σ (x t) (∫ g : Formalism.REAL.UJ ε, φ (umat g) • σ (umat g) w ∂μ)
        = ∫ g : Formalism.REAL.UJ ε, φ (y t * umat g) • σ (umat g) w ∂μ := by
      intro t
      obtain ⟨z, hz⟩ : x t ∈ Set.range (fun g : Formalism.REAL.UJ ε => umat g) := by
        rw [show Set.range (fun g : Formalism.REAL.UJ ε => umat g) = _ from hrange]; exact hxG t
      have hz' : umat z = x t := hz
      rw [← ContinuousLinearMap.integral_comp_comm _ hint,
        ← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => φ (y t * umat g) • σ (umat g) w) z]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have e : umat (z * g) = x t * umat g := by rw [← hz']; rfl
      simp only [e]
      rw [← Matrix.mul_assoc, hyx, Matrix.one_mul, hmul _ (hxG t) _ (hmem g),
        ContinuousLinearMap.map_smul_of_tower]
      rfl
    simp only [hform]
    refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
    have hC : IsCompact (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1) (tsupport φ)) :=
      ((isCompact_closedBall t₀ 1).image hx.continuous).mul hφc
    have hK := hemb.isCompact_preimage hC
    have hs : ContDiff ℝ ∞ fun t => ∫ g in (fun g : Formalism.REAL.UJ ε => umat g) ⁻¹'
        (Set.image2 (· * ·) (x '' Metric.closedBall t₀ 1) (tsupport φ)),
        φ (y t * umat g) • σ (umat g) w ∂μ :=
      contDiff_infty.2 fun m => contDiff_setIntegral_nat μ hK (hu.prodMk hb) m
        (fun z : (Fin k → ℝ) × (Matrix (Fin n) (Fin n) ℂ × H) => φ (y z.1 * z.2.1) • z.2.2)
        ((hφ.comp ((hy.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd))).smul
          (contDiff_snd.comp contDiff_snd))
    refine hs.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Metric.closedBall_mem_nhds t₀ one_pos] with t ht
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    refine hg ⟨x t, ⟨t, ht, rfl⟩, y t * umat g, subset_tsupport _ fun h => hne (by rw [h, zero_smul]), ?_⟩
    show x t * (y t * umat g) = umat g
    rw [← Matrix.mul_assoc, hxy, Matrix.one_mul]

theorem conj_mem {n : ℕ} {ε : Fin n → Bool} {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg' : gᴴ * G * g = G) :
    P * g * P⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [h, hg', ← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem exp_mem {n : ℕ} {G X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (hX : Xᴴ * G + G * X = 0) (t : ℝ) :
    (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G := by
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹ := by
    have h2 : Xᴴ = G * (-X) * G⁻¹ := by
      rw [Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
        Matrix.mul_one]
    rw [conjTranspose_smul, h2]
    simp
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp (t • X)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem list_prod_mem {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (l : List (Matrix (Fin n) (Fin n) ℂ))
    (h : ∀ g ∈ l, gᴴ * G * g = G) : l.prodᴴ * G * l.prod = G := by
  induction l with
  | nil => simp
  | cons g l ih =>
    have h1 := h g (by simp)
    have h2 := ih fun g hg => h g (by simp [hg])
    rw [List.prod_cons, conjTranspose_mul]
    calc l.prodᴴ * gᴴ * G * (g * l.prod) = l.prodᴴ * (gᴴ * G * g) * l.prod := by simp only [Matrix.mul_assoc]
      _ = G := by rw [h1, h2]

theorem exists_smoothVec {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    ∃ v : H, v ≠ 0 ∧ Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  obtain ⟨v, hv, hs⟩ := exists_garding hσ
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  refine ⟨v, hv, fun k Xs hX => hs k _ ((contDiff_const.mul (contDiff_expProd Xs)).mul contDiff_const) fun t => ?_⟩
  refine conj_mem hP h (list_prod_mem _ fun g hg => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
  exact exp_mem hG (hX i) _

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sm_ne_bot (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) :
    M.sm τ ≠ ⊥ := by
  obtain ⟨h1, h2, h3, -⟩ := M.ds τ
  obtain ⟨v, hv, hs⟩ := exists_smoothVec h3 (M.fr_unit τ) (M.fr_gram τ)
  exact (Submodule.ne_bot_iff _).2 ⟨v, Submodule.subset_span hs, hv⟩

end GlobalTheory.GardingVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseSpanCoherentVectorsFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CoherentDense

open MvPolynomial

theorem eq_zero_of_hasSum_pow (a : ℕ → ℂ) (h : ∀ t : ℂ, HasSum (fun n => t ^ n * a n) 0) : a = 0 := by
  have h1 : HasFPowerSeriesAt (0 : ℂ → ℂ) (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    rw [hasFPowerSeriesAt_iff]
    exact Filter.Eventually.of_forall fun t => by
      simpa [FormalMultilinearSeries.coeff_ofScalars] using h t
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).1 h1.eq_zero

theorem eq_zero_of_hasSum_monomial {σ : Type} [Fintype σ] (c : (σ →₀ ℕ) → ℂ)
    (h : ∀ x : σ → ℂ, HasSum (fun α : σ →₀ ℕ => c α * α.prod fun l k => x l ^ k) 0) : c = 0 := by
  classical
  let S : ℕ → Finset (σ →₀ ℕ) := fun n => (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset
  have hS : ∀ n α, α ∈ S n ↔ α.degree = n := fun n α => by simp [S]
  have key : ∀ n, (∑ α ∈ S n, monomial α (c α) : MvPolynomial σ ℂ) = 0 := by
    intro n
    refine MvPolynomial.funext fun x => ?_
    have h1 : (fun m => eval x (∑ α ∈ S m, monomial α (c α) : MvPolynomial σ ℂ)) = 0 := by
      refine eq_zero_of_hasSum_pow _ fun t => ?_
      have h2 := (h (t • x)).tsum_fiberwise (fun α => α.degree)
      refine h2.congr_fun fun m => ?_
      have e : ((fun α : σ →₀ ℕ => α.degree) ⁻¹' {m}) = (S m : Set (σ →₀ ℕ)) := by
        ext α; simp [hS]
      rw [e, Finset.tsum_subtype' (S m) (fun α : σ →₀ ℕ => c α * α.prod fun l k => (t • x) l ^ k), map_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [eval_monomial, ← (hS m α).1 hα, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
      ring
    simpa using congrFun h1 n
  funext α
  have h3 := congrArg (coeff α) (key α.degree)
  rw [coeff_sum, Finset.sum_eq_single α (fun β _ hβ => by simp [coeff_monomial, hβ])
    (fun hα => absurd ((hS _ α).2 rfl) hα)] at h3
  simpa using h3

theorem factorial_mul_coeff_expPS {σ : Type} [Fintype σ] (x : σ → ℂ) (α : σ →₀ ℕ) :
    α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (expPS (∑ l, x l • X l)) =
      α.prod fun l k => x l ^ k := by
  classical
  have hdeg : (α.sum fun _ e => e) = α.degree := by
    rw [Finsupp.degree_apply]; rfl
  rw [MvPowerSeries.coeff_apply, expPS, Finset.sum_eq_single α.degree]
  · rw [coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
    have hs : (α.prod fun _ k => k.factorial) * α.multinomial = α.degree.factorial := by
      rw [Finsupp.multinomial_eq, Finsupp.degree_apply, ← Nat.multinomial_spec]; rfl
    have hs' : α.prod (fun _ k => (k.factorial : ℂ)) * (α.multinomial : ℂ) = (α.degree.factorial : ℂ) := by
      rw [← hs]; simp [Finsupp.prod]
    have h0 : (α.degree.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← mul_div_assoc, ← mul_assoc, hs', mul_div_cancel_left₀ _ h0]
  · intro k _ hk
    rw [coeff_linearCombination_X_pow_of_fintype, if_neg (by rw [hdeg]; exact Ne.symm hk), zero_div]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

theorem eq_zero_of_inner_monomial {σ : Type} [DecidableEq σ] (F : Fock σ) (u : F.H)
    (h : ∀ α, inner ℂ u (F.ι (monomial α 1)) = 0) : u = 0 := by
  refine F.dense.eq_zero_of_inner_left ℂ ?_
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, inner_add_right, hf, hg, add_zero]
  | monomial β c =>
    have e : (monomial β c : MvPolynomial σ ℂ) = c • monomial β 1 := by simp [smul_monomial]
    rw [e, map_smul, inner_smul_right, h, mul_zero]

theorem hasSum_inner {σ : Type} [DecidableEq σ] (F : Fock σ) (u v : F.H) :
    HasSum (fun α : σ →₀ ℕ => inner ℂ u (F.ι (monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ)) *
      inner ℂ (F.ι (monomial α 1)) v) (inner ℂ u v) := by
  let m : (σ →₀ ℕ) → ℝ := fun α => α.prod fun _ k => (k.factorial : ℝ)
  have hm : ∀ α, 0 < m α := fun α => Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _)
  have hm' : ∀ α : σ →₀ ℕ, α.prod (fun _ k => (k.factorial : ℂ)) = (m α : ℂ) := fun α => by
    simp [m, Finsupp.prod]
  let r : (σ →₀ ℕ) → ℂ := fun α => (((√(m α))⁻¹ : ℝ) : ℂ)
  have hr : ∀ α, (starRingEnd ℂ) (r α) = r α := fun α => Complex.conj_ofReal _
  have hr2 : ∀ α, r α * r α = (m α : ℂ)⁻¹ := fun α => by
    simp only [r]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (hm α).le, Complex.ofReal_inv]
  have hm0 : ∀ α, (m α : ℂ) ≠ 0 := fun α => by exact_mod_cast (hm α).ne'
  have hr0 : ∀ α, r α ≠ 0 := fun α h => inv_ne_zero (hm0 α) (by rw [← hr2, h, mul_zero])
  let b : (σ →₀ ℕ) → F.H := fun α => r α • F.ι (monomial α 1)
  have hb : Orthonormal ℂ b := by
    rw [orthonormal_iff_ite]
    intro α β
    simp only [b, inner_smul_left, inner_smul_right, F.fockIP, hr]
    split_ifs with h
    · subst h
      rw [← mul_assoc, hr2, hm', inv_mul_cancel₀ (hm0 α)]
    · simp
  have hsp : (Submodule.span ℂ (Set.range b))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    refine eq_zero_of_inner_monomial F w fun α => ?_
    have := Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self α)) hw
    simpa [b, inner_smul_right, hr0] using this
  have h := (HilbertBasis.mkOfOrthogonalEqBot hb hsp).hasSum_inner_mul_inner u v
  refine h.congr_fun fun α => ?_
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  simp only [b, inner_smul_left, inner_smul_right, hr, hm', div_eq_mul_inv, ← hr2]
  ring

end GlobalTheory.CoherentDense

open GlobalTheory.CoherentDense in

theorem GlobalTheory.dense_span_coherent : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (e : (Ix P Q → ℂ) → F.H), (∀ x, HasCoeff F (e x) (expPS (gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x))) → Dense (Submodule.span ℂ (Set.range e) : Set F.H) := by
  intro P Q F e he
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have hg : ∀ x : Ix P Q → ℂ, gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x = ∑ l, x l • MvPolynomial.X l := fun x => by
    simp [gaussPoly, MvPolynomial.smul_eq_C_mul]
  have h := eq_zero_of_hasSum_monomial
    (fun α => inner ℂ u (F.ι (MvPolynomial.monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ))) fun x => by
      have h1 := hasSum_inner F u (e x)
      rw [Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self x)) hu] at h1
      simpa only [he x _, hg, factorial_mul_coeff_expPS] using h1
  refine eq_zero_of_inner_monomial F u fun α => ?_
  have h2 := congrFun h α
  have h0 : α.prod (fun _ k => (k.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simpa [h0] using h2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfAffineHyperplaneLineSums
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.FiniteRadon

open Classical in

theorem card_annihilator_mul (k W : Type) [Field k] [Fintype k] [AddCommGroup W] [Module k W]
    [Fintype (Module.Dual k W)] (y : W) (hy : y ≠ 0) :
    Fintype.card k * (Finset.univ.filter (fun g : Module.Dual k W => g y = 0)).card
      = Fintype.card (Module.Dual k W) := by
  let ev : Module.Dual k W →ₗ[k] k := Module.Dual.eval k W y
  have hev : ∀ g, ev g = g y := fun g => rfl
  have hs : Function.Surjective ev := by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hy
    intro t
    exact ⟨t • f, by simp [hev, hf]⟩
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker ev)
  have h2 : Nat.card (Module.Dual k W ⧸ LinearMap.ker ev) = Nat.card k :=
    Nat.card_congr (ev.quotKerEquivOfSurjective hs).toEquiv
  have h3 : Nat.card (LinearMap.ker ev)
      = (Finset.univ.filter (fun g : Module.Dual k W => g y = 0)).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun g => by simp [LinearMap.mem_ker, hev]))
  rw [← h3, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, h1, h2, mul_comm]

theorem eq_zero_of_hyperplane_sums (k W M : Type) [Field k] [Fintype k] [DecidableEq k]
    [AddCommGroup W] [Module k W] [Finite W] [AddCommGroup M] [Module ℂ M] (ψ : W → M)
    (_h0 : ψ 0 = 0)
    (h1 : ∀ g : Module.Dual k W, g ≠ 0 → ∑ᶠ x ∈ {x | g x = 1}, ψ x = 0)
    (h2 : ∀ x, ∑ a : kˣ, ψ ((a : k) • x) = 0) (x0 : W) : ψ x0 = 0 := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Finite (Module.Dual k W) :=
    Finite.of_injective (fun g : Module.Dual k W => (g : W → k)) DFunLike.coe_injective
  haveI : Fintype (Module.Dual k W) := Fintype.ofFinite _
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hcancel : ∀ (n : ℕ) (m : M), n ≠ 0 → n • m = 0 → m = 0 := by
    intro n m hn h
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [← Nat.cast_smul_eq_nsmul ℂ] at h
    rw [← one_smul ℂ m, ← inv_mul_cancel₀ hn', mul_smul, h, smul_zero]
  have A : ∀ (g : Module.Dual k W) (t : k), ∑ x, (if g x = t then ψ x else 0) = 0 := by
    intro g t
    by_cases ht : t = 0
    · subst ht
      apply hcancel (Fintype.card kˣ) _ Fintype.card_ne_zero
      have e : ∀ a : kˣ, ∑ x, (if g x = 0 then ψ x else 0)
          = ∑ x, (if g x = 0 then ψ ((a : k) • x) else 0) := by
        intro a
        rw [← Equiv.sum_comp (MulAction.toPerm a)]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp [MulAction.toPerm, Units.smul_def]
      rw [← Finset.card_univ, ← Finset.sum_const, Finset.sum_congr rfl (fun a _ => e a),
        Finset.sum_comm]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : g x = 0
      · simp only [hx, if_true]; exact h2 x
      · simp [hx]
    · by_cases hg : g = 0
      · subst hg
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [Ne.symm ht]
      · have h := h1 (t⁻¹ • g) (smul_ne_zero (inv_ne_zero ht) hg)
        rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
        refine Eq.trans ?_ h
        refine Finset.sum_congr rfl fun x _ => ?_
        have : (t⁻¹ • g) x = 1 ↔ g x = t := by
          simp only [LinearMap.smul_apply, smul_eq_mul]
          rw [inv_mul_eq_one₀ ht, eq_comm]
        simp only [Set.indicator_apply, Set.mem_setOf_eq, this]
  have T : ∑ x, ψ x = 0 := by simpa using A 0 0
  have B : ∑ x, (Finset.univ.filter (fun g : Module.Dual k W => g (x - x0) = 0)).card • ψ x
      = 0 := by
    have : ∑ g : Module.Dual k W, ∑ x, (if g x = g x0 then ψ x else 0) = 0 :=
      Finset.sum_eq_zero fun g _ => A g _
    rw [Finset.sum_comm] at this
    rw [← this]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const]
    simp only [map_sub, sub_eq_zero]
  set N := Fintype.card (Module.Dual k W) with hN
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
  have C : ∀ x, Fintype.card k •
      ((Finset.univ.filter (fun g : Module.Dual k W => g (x - x0) = 0)).card • ψ x)
      = N • ψ x + (if x = x0 then (r * N) • ψ x0 else 0) := by
    intro x
    rw [← mul_smul]
    by_cases hx : x = x0
    · subst hx
      simp only [sub_self, map_zero, Finset.filter_true, Finset.card_univ, if_true, hr]
      rw [← add_smul]; congr 1; ring
    · have := card_annihilator_mul k W (x - x0) (sub_ne_zero.mpr hx)
      rw [if_neg hx, add_zero, hN, ← this]
      congr!
  have D := congrArg (fun m => Fintype.card k • m) B
  simp only [Finset.smul_sum, C] at D
  simp only [smul_zero, Finset.sum_add_distrib, ← Finset.smul_sum, T,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_add] at D
  exact hcancel _ _ (Nat.mul_ne_zero (show r ≠ 0 by omega) Fintype.card_ne_zero) D

end GlobalTheory.FiniteRadon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMorphismOfStalkMapsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_of_stalk_maps : ∀ (B T S : Scheme.{0}) (t : T ⟶ B) (s : S ⟶ B) (h : ∀ x : T, Spec (T.presheaf.stalk x) ⟶ S), LocallyOfFiniteType s → IsSeparated s → IsLocallyNoetherian T → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T → (∀ x, h x ≫ s = T.fromSpecStalk x ≫ t) → (∀ (x ξ : T) (e : ξ ⤳ x), (∀ y, y ⤳ ξ → y = ξ) → Spec.map (T.presheaf.stalkSpecializes e) ≫ h x = h ξ) → ∃ g : T ⟶ S, ∀ x, T.fromSpecStalk x ≫ g = h x := by
  first | exact @GlobalTheory.GlueStalk.exists_glue_of_stalks | exact GlobalTheory.GlueStalk.exists_glue_of_stalks | (intros; apply GlobalTheory.GlueStalk.exists_glue_of_stalks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMulGaloisConjEqPrimeImagQuadraticStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_galois_conj_eq_prime_imagQuadratic : ∀ (K : Type) [Field K] [NumberField K], IsEmpty (K →+* ℝ) → Module.finrank ℚ K = 2 →
    ∀ (j : K →+* Qb) (π : 𝓞 K) (p : ℕ), Ideal.absNorm (Ideal.span {π}) = p →
      ∃ σ : Qb →ₐ[ℚ] Qb, j (π : K) * σ (j (π : K)) = (p : Qb) := by
  first | exact @GlobalTheory.RayFieldNorm.exists_mul_conj_eq_norm | exact GlobalTheory.RayFieldNorm.exists_mul_conj_eq_norm | (intros; apply GlobalTheory.RayFieldNorm.exists_mul_conj_eq_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPlaceIsTeichmullerLiftFbarStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_isTeichmuller_lift_Fbar : ∀ (g : ℕ) [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ), (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ (A : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g), IsTeich A κ t := by
  first | exact @GlobalTheory.TeichPlace.exists_place_isTeich | exact GlobalTheory.TeichPlace.exists_place_isTeich | (intros; apply GlobalTheory.TeichPlace.exists_place_isTeich <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjMapProportionalSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_proj_map_proportional_sections : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (I : W.IdealSheafData) (L : LB X) (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (q : W ⟶ Sp R), GeneratesAlong I σ g → FinalTheorems.EffCartier I → ∃ ψ : W ⟶ PSpace R m, ψ ≫ PSpace.str R m = q ∧ Proportional σ g ψ := by
  first | exact @GlobalTheory.ProjBlowup.exists_proportional | exact GlobalTheory.ProjBlowup.exists_proportional | (intros; apply GlobalTheory.ProjBlowup.exists_proportional <;> assumption)
end

