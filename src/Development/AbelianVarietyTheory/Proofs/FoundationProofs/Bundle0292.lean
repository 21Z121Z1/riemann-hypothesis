import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PosDefOneSubOfSumSqLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.HolDS

theorem posDef_one_sub_of_sum_sq_lt {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (M : Matrix m n ℂ)
    (h : ∑ i, ∑ j, ‖M i j‖ ^ 2 < 1) : (1 - Mᴴ * M).PosDef := by
  have key : ∀ {k : Type} [Fintype k] (v : k → ℂ), star v ⬝ᵥ v = ((∑ a, ‖v a‖ ^ 2 : ℝ) : ℂ) := by
    intro k _ v
    simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_sum,
      Complex.ofReal_pow]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self M)) fun x hx => ?_
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec, key, key, ← Complex.ofReal_sub, Complex.zero_lt_real]
  have hpos : 0 < ∑ a, ‖x a‖ ^ 2 := by
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hx
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨a, Finset.mem_univ _, by
      have : 0 < ‖x a‖ := norm_pos_iff.2 ha
      positivity⟩
  have hle : ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ (∑ i, ∑ j, ‖M i j‖ ^ 2) * ∑ a, ‖x a‖ ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M i j‖) (fun j => ‖x j‖))
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  nlinarith

theorem exists_congr_one_of_posDef {n : Type} [Fintype n] [DecidableEq n] {S : Matrix n n ℂ} (h : S.PosDef) :
    ∃ d : Matrix n n ℂ, IsUnit d.det ∧ dᴴ * S * d = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 h.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  have hd : B.det ≠ 0 := by
    have h2 := h.det_pos.ne'
    rw [hB, Matrix.det_mul] at h2
    exact right_ne_zero_of_mul h2
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det _ hd.isUnit, ?_⟩
  rw [hB, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd.isUnit]
  simp

theorem exists_inU_zOf_eq {p q : ℕ} (Z : Fin p × Fin q → ℂ) (h : ∑ i, ∑ j, ‖Z (i, j)‖ ^ 2 < 1) :
    ∃ x : Mat p q, InU x ∧ zOf x = Z := by
  set M : Matrix (Fin p) (Fin q) ℂ := Matrix.of fun i j => Z (i, j) with hM
  obtain ⟨d, hd, hd1⟩ := exists_congr_one_of_posDef (posDef_one_sub_of_sum_sq_lt M h)
  obtain ⟨a, -, ha1⟩ := exists_congr_one_of_posDef (posDef_one_sub_of_sum_sq_lt Mᴴ (by
    rw [Finset.sum_comm]
    simpa [hM] using h))
  rw [Matrix.conjTranspose_conjTranspose] at ha1
  refine ⟨Matrix.fromBlocks a (M * d) (Mᴴ * a) d, ?_, ?_⟩
  · unfold InU
    rw [Jm_eq, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_inj]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc] at ha1 hd1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← ha1]; abel
    · abel
    · abel
    · rw [← hd1]; abel
  · funext ij
    simp only [zOf, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    rfl

theorem eq_zero_of_eval_zOf (p q : ℕ) (P : PolB p q)
    (h : ∀ x : Mat p q, InU x → MvPolynomial.eval (zOf x) P = 0) : P = 0 := by
  set e : ℝ := 1 / ((p : ℝ) * q + 1) with he
  have hpq : (0 : ℝ) ≤ (p : ℝ) * q := by positivity
  have he0 : 0 < e := by positivity
  have he1 : e * ((p : ℝ) * q + 1) = 1 := by rw [he]; field_simp
  have hele : e ≤ 1 := by nlinarith
  refine MvPolynomial.funext_set (fun _ => Metric.ball (0 : ℂ) e)
    (fun _ => infinite_of_mem_nhds (0 : ℂ) (Metric.ball_mem_nhds _ he0)) fun Z hZ => ?_
  have hZ' : ∀ ij, ‖Z ij‖ ^ 2 ≤ e := fun ij => by
    have h1 : ‖Z ij‖ < e := by simpa using hZ ij (Set.mem_univ _)
    have := norm_nonneg (Z ij)
    nlinarith
  obtain ⟨x, hx, rfl⟩ := exists_inU_zOf_eq Z (by
    calc _ ≤ ∑ _i : Fin p, ∑ _j : Fin q, e :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hZ' _
      _ = (p : ℝ) * q * e := by simp [mul_assoc]
      _ < 1 := by nlinarith)
  rw [h x hx, map_zero]

end GlobalTheory.HolDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta.Param

open PowerSeries

theorem isWpSer_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) {a b : K} {P : PowerSeries K}
    (h : IsWpSer a b P) : IsWpSer (f a) (f b) (PowerSeries.map f P) := by
  have hd : derivativeFun (PowerSeries.map f P) = PowerSeries.map f (derivativeFun P) := by
    ext n
    simp [derivativeFun, coeff_derivative]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.1, map_one]
  · have := congrArg (PowerSeries.map f) h.2
    simp only [map_pow, map_sub, map_mul, map_C, map_X, map_ofNat] at this
    rw [hd]
    exact this

theorem isWpSer_rescale {K : Type*} [CommRing K] (e : K) {a b : K} {P : PowerSeries K}
    (h : IsWpSer a b P) : IsWpSer (e ^ 4 * a) (e ^ 6 * b) (rescale e P) := by
  have hd : X * derivativeFun (rescale e P) = rescale e (X * derivativeFun P) := by
    ext n
    cases n with
    | zero => simp [coeff_rescale]
    | succ n => simp [coeff_rescale, coeff_succ_X_mul, derivativeFun, coeff_derivative, mul_assoc, pow_succ']
  have hC : ∀ c : K, rescale e (C c) = C c := by
    intro c
    ext n
    cases n <;> simp [coeff_rescale, coeff_C]
  refine ⟨?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, coeff_zero_eq_constantCoeff_apply, h.1]
    simp
  · have := congrArg (rescale e) h.2
    rw [hd]
    rw [map_pow, map_sub] at this
    simp only [map_pow (rescale e), map_sub (rescale e), map_mul (rescale e) _ P, map_mul (rescale e) (C _),
      map_mul (rescale e) 4, hC, rescale_X, map_ofNat] at this
    rw [this]
    simp only [map_mul, map_pow]
    ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe' (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  simp [lamC]

theorem theta_series_map_coefficients (lam : Qbar →+* ℂ_[p]) (F : ℂ → ℂ) (T : PowerSeries Qbar)
    (h : PowerSeries.mk (coef1 F) = PowerSeries.map (algebraMap Qbar ℂ) T) :
    GL3Theta.ser1 lam F = PowerSeries.map lam T := by
  ext n
  have := congrArg (coeff n) h
  rw [coeff_mk, coeff_map] at this
  rw [GL3Theta.ser1, coeff_mk, coeff_map, ← lamC_coe']
  exact congrArg (lamC lam) this

theorem invariants (g : GL3Theta.G1 p) (a b : Qbar) (ha : g2 g.abelian₂ = a) (hb : g3 g.abelian₂ = b) :
    g.W.c₄ / 12 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 4 * g.lam a ∧
    g.W.c₆ / 216 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 6 * g.lam b ∧
    g.W.b₂ / 12 = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r := by
  have e : ∀ x : Qbar, lamC g.lam (-(x : ℂ) / 4) = -g.lam x / 4 := by
    intro x
    have : -(x : ℂ) / 4 = ((-x / 4 : Qbar) : ℂ) := by
      push_cast; rfl
    rw [this, lamC_coe', map_div₀, map_neg, map_ofNat]
  unfold GL3Theta.G1.W
  rw [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.variableChange_c₆,
    WeierstrassCurve.variableChange_b₂]
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, wModel, ha, hb, e]
  refine ⟨by ring, by ring, by ring⟩

theorem exists_algebraic_series (Λ : AddSubgroup ℂ) (hL : IsLat Λ) (a b w : Qbar) (ha : g2 Λ = a) (hb : g3 Λ = b)
    (hσ : AlgEnt (sgStar Λ)) (v : ℂ) (hv : v ∉ Λ) (hw : wpF Λ v = w) :
    ∃ P₀ S : PowerSeries Qbar, IsWpSer a b P₀ ∧
      PowerSeries.mk (coef1 (sgStar Λ)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) ∧
      PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.map (algebraMap Qbar ℂ) (S ^ 2 * lineSer P₀ w) := by
  obtain ⟨P, hP, hPv⟩ := GlobalTheory.T.exists_weierstrassPSeries_and_sigmaStarQuotientSeries Λ hL
  obtain ⟨P₀, hP₀, -⟩ := GlobalTheory.T.existsUnique_isWeierstrassPSeries Qbar a b
  rw [ha, hb] at hP
  have hPP : P = PowerSeries.map (algebraMap Qbar ℂ) P₀ :=
    (GlobalTheory.T.existsUnique_isWeierstrassPSeries ℂ a b).unique hP (isWpSer_map (algebraMap Qbar ℂ) hP₀)
  have h0 : coef1 (sgStar Λ) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar Λ)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar Λ) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  refine ⟨P₀, S, hP₀, hS, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := ℂ)))
  rw [hPv v hv, hS, hPP, hw]
  simp only [lineSer, map_mul, map_pow, map_sub, map_X, map_C]
  have : algebraMap Qbar ℂ w = (w : ℂ) := rfl
  rw [this]
  ring

theorem subst_lineSer {K : Type*} [Field K] (l E q S P : PowerSeries K) (ε r w : K) (hl0 : constantCoeff l = 0)
    (hE : X * E = l * subst (C ε * l) S)
    (hform : X ^ 2 * (subst l (rescale ε P) : PowerSeries K) = l ^ 2 * lineSer q (-(ε ^ 2 * r))) :
    (subst (C ε * l) (S ^ 2 * lineSer P w) : PowerSeries K) = E ^ 2 * lineSer q (ε ^ 2 * (w - r)) := by
  have hl : HasSubst l := HasSubst.of_constantCoeff_zero' hl0
  have hel : HasSubst (C ε * l) := HasSubst.of_constantCoeff_zero' (by simp [hl0])
  have hres : subst l (rescale ε P) = (subst (C ε * l) P : PowerSeries K) := by
    rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' ε) hl, subst_smul hl, subst_X hl, smul_eq_C_mul]
  rw [hres] at hform
  have hCs : subst (C ε * l) (C w : PowerSeries K) = (C w : PowerSeries K) := by
    rw [← coe_substAlgHom hel]
    exact (substAlgHom hel).commutes w
  apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne_zero (R := K)))
  rw [← mul_assoc, ← mul_pow, hE]
  simp only [lineSer, map_mul, map_pow, map_sub, map_neg] at hform ⊢
  rw [subst_mul hel, subst_pow hel, subst_sub hel, subst_mul hel, subst_pow hel, subst_X hel, hCs]
  linear_combination (subst (C ε * l) S : PowerSeries K) ^ 2 * hform

theorem constantCoeff_l (g : GL3Theta.G1 p) : constantCoeff g.l = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, GL3Theta.G1.l, flog, coeff_mk]; simp

theorem X_mul_ePhi1 (g : GL3Theta.G1 p) (S : PowerSeries ℂ_[p]) (hS : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * S) :
    X * ePhi1 g.lam g.abelian₂ g.C g.wq = g.l * subst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) S := by
  have hl0 := constantCoeff_l g
  have hel : HasSubst (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) :=
    HasSubst.of_constantCoeff_zero' (by rw [map_mul, hl0, mul_zero])
  have hS' : sgSer g.lam g.abelian₂ = X * S := hS
  ext n
  cases n with
  | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, map_mul, map_mul, hl0,
      constantCoeff_X, zero_mul, zero_mul]
  | succ n =>
    rw [coeff_succ_X_mul, ePhi1, coeff_mk, hS', ← C_eq_algebraMap, ← GL3Theta.G1.W, ← GL3Theta.G1.l,
      subst_mul hel, subst_X hel, mul_assoc, coeff_C_mul, inv_mul_cancel_left₀ (Units.ne_zero _)]

theorem sqTh_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (sqTh g.abelian₂ v) ∧ g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨a, ha⟩ : ∃ a : Qbar, g2 g.abelian₂ = a := ⟨⟨_, h2⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Qbar, g3 g.abelian₂ = b := ⟨⟨_, h3⟩, rfl⟩
  obtain ⟨w, hw'⟩ : ∃ w : Qbar, wpF g.abelian₂ v = w := ⟨⟨_, hw⟩, rfl⟩
  obtain ⟨P₀, S, hP₀, hS, hT⟩ := exists_algebraic_series g.abelian₂ hL a b w ha hb hσ v hv hw'
  refine ⟨⟨hL.differentiable_sqTh v, fun n => ?_⟩, ?_⟩
  · have := congrArg (coeff n) hT
    rw [coeff_mk, coeff_map] at this
    rw [this]
    exact SetLike.coe_mem _
  obtain ⟨i4, i6, i2⟩ := invariants g a b ha hb
  have hform := GlobalTheory.T.weierstrassP_formalGroupLog_uniformises p g.W g.wq
    (rescale ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) (PowerSeries.map g.lam P₀)) hq
    (by rw [i4, i6]; exact isWpSer_rescale _ (isWpSer_map g.lam hP₀))
  rw [i2, ← GL3Theta.G1.l] at hform
  have hE := X_mul_ePhi1 g (PowerSeries.map g.lam S) (by rw [theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X])
  have hm : PowerSeries.map g.lam (S ^ 2 * lineSer P₀ w) =
      PowerSeries.map g.lam S ^ 2 * lineSer (PowerSeries.map g.lam P₀) (g.lam w) := by
    simp only [lineSer, map_mul, map_pow, map_sub, map_X, map_C]
  rw [GL3Theta.G1.atU, ← C_eq_algebraMap, theta_series_map_coefficients g.lam _ _ hT, hm, xAt, hw', lamC_coe']
  exact subst_lineSer _ _ _ _ _ _ _ _ (constantCoeff_l g) hE hform

end GlobalTheory.EvenTheta.Param
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleConstantEqNegOnePow
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleSign

theorem exists_coords {V R ι : Type} [AddCommGroup V] [CommRing R] (P : Ideal R) (A B C : AddSubgroup V)
    (f : (ι → R) →+ V) (hB : ∀ a, f a ∈ B) (hk : ∀ a, f a ∈ A ↔ ∀ i, a i ∈ P)
    (hs : ∀ z ∈ B, ∃ a, z - f a ∈ A ∧ z - f a ∈ C) :
    ∃ (e : (B ⧸ A.addSubgroupOf B) ≃ (ι → R ⧸ P)) (a : (B ⧸ A.addSubgroupOf B) → ι → R),
      ∀ q, (((Quotient.out q : B) : V) - f (a q) ∈ A ∧ ((Quotient.out q : B) : V) - f (a q) ∈ C) ∧
        ∀ i, Ideal.Quotient.mk P (a q i) = e q i := by
  choose g hg using hs
  let a : (B ⧸ A.addSubgroupOf B) → ι → R := fun q => g _ (Quotient.out q : B).2
  have ha : ∀ q, ((Quotient.out q : B) : V) - f (a q) ∈ A ∧ ((Quotient.out q : B) : V) - f (a q) ∈ C :=
    fun q => hg _ _
  let e : (B ⧸ A.addSubgroupOf B) → (ι → R ⧸ P) := fun q i => Ideal.Quotient.mk P (a q i)
  have hinj : Function.Injective e := by
    intro q q' h
    have h1 : f (a q' - a q) ∈ A := (hk _).2 fun i => by
      have := congrFun h i
      exact Ideal.Quotient.eq.1 this.symm
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    have h2 := A.add_mem (A.sub_mem (ha q').1 (ha q).1) h1
    rw [map_sub] at h2
    convert h2 using 1
    push_cast; abel
  have hsurj : Function.Surjective e := by
    intro t
    let b : ι → R := fun i => Quotient.out (t i)
    let q : B ⧸ A.addSubgroupOf B := QuotientAddGroup.mk ⟨f b, hB b⟩
    have h1 : (QuotientAddGroup.mk (Quotient.out q) : B ⧸ A.addSubgroupOf B) = QuotientAddGroup.mk ⟨f b, hB b⟩ :=
      QuotientAddGroup.out_eq' q
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    have h2 : f (b - a q) ∈ A := by
      have := A.add_mem h1 (ha q).1
      rw [map_sub]
      convert this using 1
      push_cast; abel
    refine ⟨q, funext fun i => ?_⟩
    have h3 := Ideal.Quotient.eq.2 ((hk _).1 h2 i)
    rw [← Ideal.Quotient.mk_out (t i)]
    exact h3.symm
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, a, fun q => ⟨ha q, fun i => rfl⟩⟩

def ch (D : D7) (s : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Real.sqrt D.host.d * s.re + s.im : ℝ) : ℂ))

theorem bc_eq (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : bc D T x y = ch D (Hf D T x y) := rfl

theorem ch_add (D : D7) (s t : ℂ) : ch D (s + t) = ch D s * ch D t := by
  rw [ch, ch, ch, ← Complex.exp_add, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem ch_zero (D : D7) : ch D 0 = 1 := by simp [ch]

theorem ch_ne_zero (D : D7) (s : ℂ) : ch D s ≠ 0 := Complex.exp_ne_zero _

theorem bc_sum_left (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type} (s : Finset ι) (x : ι → VC D N N') (y : VC D N N') :
    bc D T (∑ i ∈ s, x i) y = ∏ i ∈ s, bc D T (x i) y := by
  induction s using Finset.induction_on with
  | empty => simp [bc_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bc_add_left, ih]

theorem bc_sum_right (D : D7) (T : Tor D) {N N' : ℕ} {ι : Type} (s : Finset ι) (x : VC D N N') (y : ι → VC D N N') :
    bc D T x (∑ i ∈ s, y i) = ∏ i ∈ s, bc D T x (y i) := by
  induction s using Finset.induction_on with
  | empty => simp [bc_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, bc_add_right, ih]

def sumHom {V R ι : Type} [Fintype ι] [AddCommGroup V] [CommRing R] (X : ι → R →+ V) : (ι → R) →+ V where
  toFun a := ∑ i, X i (a i)
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

theorem sumHom_apply {V R ι : Type} [Fintype ι] [AddCommGroup V] [CommRing R] (X : ι → R →+ V) (a : ι → R) :
    sumHom X a = ∑ i, X i (a i) := rfl

theorem sign_of_pow {μ : ℂ} {r : ℕ} {r₀ m : ℝ} (h0 : 0 < r₀) (hm : 0 < m) (h8 : μ ^ 8 = 1)
    (h : μ * (r₀ : ℂ) = (-1) ^ r * (m : ℂ)) : μ = (-1) ^ r := by
  have hr : (r₀ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have h1 : μ = (-1) ^ r * ((m / r₀ : ℝ) : ℂ) := by
    push_cast; field_simp; exact h
  have h2 : (m / r₀) ^ 8 = 1 := by
    rw [h1, mul_pow, ← pow_mul, mul_comm r 8, pow_mul] at h8
    norm_num at h8
    exact_mod_cast h8
  have h3 : m / r₀ = 1 := (pow_eq_one_iff_of_nonneg (div_pos hm h0).le (by norm_num)).1 h2
  rw [h1, h3]; simp

theorem mu_eq_sign : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ),
    Trip D T A₁ A₂ A₃ e μ → ∀ (P : Ideal (𝓞 D.host.E)) (r : ℕ), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) →
    (∃ a, a - sgO D a ∉ P) → TriDat D T A₁ A₂ A₃ P r → μ = (-1) ^ r := by
  intro D T N N' A₁ A₂ A₃ e μ hT P r hP hσ hne hD
  obtain ⟨r₀, hr₀, hμ⟩ := GlobalTheory.TripleConstant.mu_form D T N N' A₁ A₂ A₃ e μ hT
  obtain ⟨n₁, n₂, n₃, -, -, -, -, -, h8, -⟩ := hT
  obtain ⟨X, Y, φ, hH, hm, hp, s₂, s₃, k₁, k₂⟩ := hD
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  have : Finite (𝓞 D.host.E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hP0
  let _ : Fintype (𝓞 D.host.E ⧸ P) := Fintype.ofFinite _
  let χ : Fin r → 𝓞 D.host.E → ℂ := fun i s => ch D (φ i s)
  have χadd : ∀ i a b, χ i (a + b) = χ i a * χ i b := fun i a b => by simp only [χ, map_add, ch_add]
  have hYX : ∀ i a a', bc D T (Y i a') (X i a) = χ i (a' * sgO D a) := fun i a a' => by
    rw [bc_eq, hH, if_pos rfl]
  have hYX' : ∀ i j a a', i ≠ j → bc D T (Y i a') (X j a) = 1 := fun i j a a' h => by
    rw [bc_eq, hH, if_neg h, ch_zero]
  have hXY' : ∀ i j a a', i ≠ j → bc D T (X j a) (Y i a') = 1 := fun i j a a' h => by
    rw [bc_eq, ← Hf_conj, hH, if_neg h, map_zero, ch_zero]
  have χP : ∀ i, ∀ a ∈ P, χ i a = 1 := fun i a ha => by
    have := hYX i 1 a
    rw [map_one (sgO D), mul_one] at this
    rw [← this]
    exact n₂.2.1 _ (hp i a ha).2.2 _ (hm i 1).1
  have χne : ∀ i, ∃ a, χ i (a + sgO D a) ≠ 1 := fun i => by
    by_contra hc
    push Not at hc
    have c1 : ∀ j a, bc D T (X i 1) (Y j a) = bc D T (Y j a) (X i 1) := fun j a => by
      by_cases h : j = i
      · subst h
        have e1 := n₁.2.1 _ (hm j 1).2.2 _ (hm j a).2.2
        rw [bc_add_left, bc_add_right, bc_add_right, n₂.2.1 _ (hm j 1).1 _ (hm j a).1,
          n₃.2.1 _ (hm j 1).2.1 _ (hm j a).2.1, hYX, one_mul, one_mul, mul_one] at e1
        have e2 := hc a
        rw [χadd] at e2
        rw [hYX, map_one (sgO D), mul_one]
        exact mul_right_cancel₀ (ch_ne_zero D _) (e1.trans e2.symm)
      · rw [hYX' j i _ _ h, hXY' j i _ _ h]
    have c2 : X i 1 ∈ A₃ := n₃.2.2 _ fun y hy => by
      obtain ⟨a, ha⟩ := s₃ y hy
      have hy' : y = (y - ∑ j, Y j (a j)) + ∑ j, Y j (a j) := by abel
      rw [hy', bc_add_left, bc_add_right, n₂.2.1 _ ha.2 _ (hm i 1).1, n₂.2.1 _ (hm i 1).1 _ ha.2,
        bc_sum_left, bc_sum_right]
      simp only [c1]
    obtain ⟨a, ha⟩ := s₃ _ c2
    have c3 : ∑ j, Y j (a j) ∈ A₂ := by
      have := A₂.sub_mem (hm i 1).1 ha.2
      simpa using this
    have c4 : ∑ j, Y j (a j) ∈ A₁ := A₁.sum_mem fun j _ => (hp j _ (k₂ a c3 j)).2.1
    have c5 : X i 1 ∈ A₁ := by
      have := A₁.add_mem ha.1 c4
      simpa using this
    have c6 : ∑ j, X j ((Pi.single i 1 : Fin r → 𝓞 D.host.E) j) = X i 1 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, map_zero]
      · simp
    have c7 := k₁ (Pi.single i 1) (c6 ▸ c5) i
    rw [Pi.single_eq_same] at c7
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 c7)
  have hG : ∀ i, ∃ m : ℝ, 0 < m ∧
      ∑ᶠ q : 𝓞 D.host.E ⧸ P, χ i (Quotient.out q * sgO D (Quotient.out q)) = -(m : ℂ) := fun i =>
    GlobalTheory.NormGauss.finsum_norm_neg _ (sgO D) P (sgO_sgO D) hσ hne (χ i) (χadd i) (χP i) (χne i)
  choose m hm0 hmG using hG
  have kX : ∀ a, sumHom X a ∈ A₁ ↔ ∀ i, a i ∈ P := fun a =>
    ⟨k₁ a, fun h => by rw [sumHom_apply]; exact A₁.sum_mem fun i _ => (hp i _ (h i)).1.1⟩
  have kY : ∀ a, sumHom Y a ∈ A₂ ↔ ∀ i, a i ∈ P := fun a =>
    ⟨k₂ a, fun h => by rw [sumHom_apply]; exact A₂.sum_mem fun i _ => (hp i _ (h i)).2.2⟩
  have mX : ∀ a, sumHom X a ∈ A₂ := fun a => by
    rw [sumHom_apply]; exact A₂.sum_mem fun i _ => (hm i _).1
  have mY : ∀ a, sumHom Y a ∈ A₃ := fun a => by
    rw [sumHom_apply]; exact A₃.sum_mem fun i _ => (hm i _).2.1
  have mXY : ∀ a, sumHom X a + sumHom Y a ∈ A₁ := fun a => by
    rw [sumHom_apply, sumHom_apply, ← Finset.sum_add_distrib]
    exact A₁.sum_mem fun i _ => (hm i _).2.2
  obtain ⟨e₂, a₂, h₂⟩ := exists_coords P A₁ A₂ A₃ (sumHom X) mX kX
    (fun z hz => (s₂ z hz).imp fun a ha => ⟨ha.1, ha.2⟩)
  obtain ⟨e₃, a₃, h₃⟩ := exists_coords P A₂ A₃ A₁ (sumHom Y) mY kY
    (fun z hz => (s₃ z hz).imp fun a ha => ⟨ha.2, ha.1⟩)
  let F : (Fin r → 𝓞 D.host.E ⧸ P) × (Fin r → 𝓞 D.host.E ⧸ P) → ℂ := fun p =>
    if p.1 = p.2 then ∏ i, χ i (Quotient.out (p.2 i) * sgO D (Quotient.out (p.2 i))) else 0
  have key : ∀ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂),
      (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then
        bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) =
      F (Equiv.prodCongr e₃ e₂ p) := by
    rintro ⟨q₃, q₂⟩
    obtain ⟨⟨u1, u3⟩, u⟩ := h₂ q₂
    obtain ⟨⟨v2, v1⟩, v⟩ := h₃ q₃
    have x2 := (Quotient.out q₂ : A₂).2
    have y3 := (Quotient.out q₃ : A₃).2
    simp only [F, Equiv.prodCongr_apply, Prod.map]
    generalize ((Quotient.out q₂ : A₂) : VC D N N') = x at *
    generalize ((Quotient.out q₃ : A₃) : VC D N N') = y at *
    have hiff : y + x ∈ A₁ ↔ e₃ q₃ = e₂ q₂ := by
      have w : y + x = sumHom X (a₂ q₂ - a₃ q₃) + ((x - sumHom X (a₂ q₂)) + (y - sumHom Y (a₃ q₃)) +
          (sumHom X (a₃ q₃) + sumHom Y (a₃ q₃))) := by rw [map_sub]; abel
      rw [w, A₁.add_mem_cancel_right (A₁.add_mem (A₁.add_mem u1 v1) (mXY _)), kX, funext_iff]
      refine forall_congr' fun i => ?_
      rw [← u, ← v, eq_comm, Ideal.Quotient.eq, Pi.sub_apply]
    by_cases h : e₃ q₃ = e₂ q₂
    · rw [if_pos (hiff.2 h), if_pos h]
      have wx : x = sumHom X (a₂ q₂) + (x - sumHom X (a₂ q₂)) := by abel
      have wy : y = sumHom Y (a₃ q₃) + (y - sumHom Y (a₃ q₃)) := by abel
      rw [wy, bc_add_left, n₂.2.1 _ v2 _ x2, mul_one, wx, bc_add_right, n₃.2.1 _ (mY _) _ u3, mul_one,
        sumHom_apply, sumHom_apply, bc_sum_left]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [bc_sum_right, Finset.prod_eq_single i (fun j _ hj => hYX' i j _ _ hj.symm) (by simp), hYX]
      set t := Quotient.out (e₂ q₂ i) with ht
      have t2 : a₂ q₂ i - t ∈ P := Ideal.Quotient.eq.1 (by rw [u, ht, Ideal.Quotient.mk_out])
      have t3 : a₃ q₃ i - t ∈ P := Ideal.Quotient.eq.1 (by rw [v, h, ht, Ideal.Quotient.mk_out])
      have w : a₃ q₃ i * sgO D (a₂ q₂ i) = t * sgO D t +
          ((a₃ q₃ i - t) * sgO D (a₂ q₂ i) + t * sgO D (a₂ q₂ i - t)) := by rw [map_sub]; ring
      rw [w, χadd, χP i _ (P.add_mem (P.mul_mem_right _ t3) (P.mul_mem_left _ (hσ _ t2))), mul_one]
    · rw [if_neg (mt hiff.1 h), if_neg h]
  rw [finsum_congr key, finsum_comp_equiv (Equiv.prodCongr e₃ e₂) (f := F), finsum_eq_sum_of_fintype,
    Fintype.sum_prod_type_right] at hμ
  simp only [F, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hμ
  simp only [finsum_eq_sum_of_fintype] at hmG
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ)
    (fun i (t : 𝓞 D.host.E ⧸ P) => χ i (Quotient.out t * sgO D (Quotient.out t)))] at hμ
  simp only [hmG] at hμ
  refine sign_of_pow hr₀ (Finset.prod_pos fun i (_ : i ∈ Finset.univ) => hm0 i) h8 ?_
  rw [hμ, Finset.prod_neg]
  simp

end GlobalTheory.TriangleSign
end
end

