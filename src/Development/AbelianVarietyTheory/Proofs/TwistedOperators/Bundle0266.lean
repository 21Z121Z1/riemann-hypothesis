import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0274
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationMultilinearNormSq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowEvalHHNorm

open GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem norm_sq_toLp_eq {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {f : X.B.I.GA → ℂ} (hf : MemLp f 2 (muX X)) :
    ‖(hf.toLp f : L2X X)‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(muX X) := by
  rw [@norm_sq_eq_re_inner ℂ, MeasureTheory.L2.inner_def]
  have h1 : (fun a => ⟪(hf.toLp f : L2X X) a, (hf.toLp f : L2X X) a⟫_ℂ) =
      fun a => (((‖(hf.toLp f : L2X X) a‖ ^ 2 : ℝ)) : ℂ) := by
    funext a; rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [h1, integral_complex_ofReal]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha]

def phi (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R))
    (y : ∀ τ, Wsub R X c τ) : X.B.I.GA → ℂ :=
  fun x => ev (MP R) (vecOf R X c y) S
    (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)

theorem vecOf_update [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau)
    (z : Wsub R X c τ) :
    vecOf R X c (Function.update y τ z) =
      Function.update (vecOf R X c y) τ ⟨(c τ).symm (z : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z⟩ := by
  funext σ
  by_cases hσ : σ = τ
  · subst hσ
    simp [vecOf]
  · simp [vecOf, Function.update_of_ne hσ]

theorem phi_add [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (y : ∀ τ, Wsub R X c τ)
    (τ : D.what₂.Tau) (z₁ z₂ : Wsub R X c τ) :
    phi R X h t c S (Function.update y τ (z₁ + z₂)) =
      phi R X h t c S (Function.update y τ z₁) + phi R X h t c S (Function.update y τ z₂) := by
  funext x
  simp only [phi, ev_apply, vecOf_update, Pi.add_apply]
  have e : (⟨(c τ).symm ((z₁ + z₂ : Wsub R X c τ) : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (z₁ + z₂)⟩ :
      (MP R).sm τ) = ⟨(c τ).symm (z₁ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z₁⟩ +
        ⟨(c τ).symm (z₂ : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z₂⟩ :=
    Subtype.ext (by simp)
  rw [e, S.map_update_add]
  rfl

theorem phi_smul [DecidableEq D.what₂.Tau] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (y : ∀ τ, Wsub R X c τ)
    (τ : D.what₂.Tau) (a : ℂ) (z : Wsub R X c τ) :
    phi R X h t c S (Function.update y τ (a • z)) =
      (starRingEnd ℂ a) • phi R X h t c S (Function.update y τ z) := by
  funext x
  simp only [phi, ev_apply, vecOf_update, Pi.smul_apply]
  have e : (⟨(c τ).symm ((a • z : Wsub R X c τ) : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ (a • z)⟩ :
      (MP R).sm τ) = (starRingEnd ℂ a) • ⟨(c τ).symm (z : X.B.H (X.pl.symm τ)), symm_mem_sm R X c τ z⟩ :=
    Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ])
  rw [e, S.map_update_smul]
  rfl

end GlobalTheory.RowEvalHHNorm

namespace GlobalTheory.RowEvalHHNorm

open GlobalTheory.RowEvalHH

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem phi_memLp_integral (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (S : MMap (MP R)) (K : ℝ)
    (hK : ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) →
      MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)) 2 (muX X) ∧
      ∫ x, ‖ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)‖ ^ 2 ∂(muX X) = K)
    (y : ∀ τ, Wsub R X c τ) :
    MemLp (phi R X h t c S y) 2 (muX X) ∧
      ∫ x, ‖phi R X h t c S y x‖ ^ 2 ∂(muX X) = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  by_cases h0 : ∃ τ, (y τ : X.B.H (X.pl.symm τ)) = 0
  · obtain ⟨τ, hτ⟩ := h0
    have hv : vecOf R X c y τ = 0 := Subtype.ext (by simp [vecOf, hτ])
    have hz : phi R X h t c S y = 0 := by
      funext x
      simp only [phi, ev_apply, S.map_coord_zero τ hv]
      rfl
    have hp : ∏ σ, ‖(y σ : X.B.H (X.pl.symm σ))‖ ^ 2 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ τ) (by simp [hτ])
    rw [hz, hp]
    refine ⟨MeasureTheory.MemLp.zero, ?_⟩
    simp
  · push_neg at h0
    have hn : ∀ τ, ‖((c τ).symm (y τ : X.B.H (X.pl.symm τ)) : (MP R).H τ)‖ = ‖(y τ : X.B.H (X.pl.symm τ))‖ :=
      fun τ => LinearIsometryEquiv.norm_map _ _
    have hpos : ∀ τ, 0 < ‖(y τ : X.B.H (X.pl.symm τ))‖ := fun τ => norm_pos_iff.2 (h0 τ)
    let u : (MP R).Vec := fun τ => ((‖(y τ : X.B.H (X.pl.symm τ))‖⁻¹ : ℝ) : ℂ) • vecOf R X c y τ
    have hu : ∀ τ, ‖(u τ : (MP R).H τ)‖ = 1 := by
      intro τ
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      show |‖(y τ : X.B.H (X.pl.symm τ))‖⁻¹| * ‖((c τ).symm (y τ : X.B.H (X.pl.symm τ)) : (MP R).H τ)‖ = 1
      rw [hn, abs_of_pos (inv_pos.2 (hpos τ)), inv_mul_cancel₀ (hpos τ).ne']
    have hvec : vecOf R X c y = fun τ => ((‖(y τ : X.B.H (X.pl.symm τ))‖ : ℝ) : ℂ) • u τ := by
      funext τ
      apply Subtype.ext
      simp only [u, Submodule.coe_smul, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hpos τ).ne', Complex.ofReal_one, one_smul]
    set a : ℂ := ∏ τ, ((‖(y τ : X.B.H (X.pl.symm τ))‖ : ℝ) : ℂ) with ha
    have hphi : phi R X h t c S y = fun x => a * ev (MP R) u S
        (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t) := by
      funext x
      simp only [phi, ev_apply]
      rw [hvec, S.map_smul_univ]
      rfl
    obtain ⟨hm, hi⟩ := hK u hu
    have hna : ‖a‖ = ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ := by
      rw [ha, norm_prod]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [hphi]
    refine ⟨hm.const_mul a, ?_⟩
    simp only [norm_mul, mul_pow]
    rw [integral_const_mul, hi, hna, Finset.prod_pow]
    ring

theorem evF_multilinear_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ∀ S ∈ EP R F, ∃ (f : MultilinearMap ℂ (fun τ => ↥(GlobalTheory.RowEvalHH.Wsub R X c τ)) (L2X X)) (K : ℝ), (∀ y, f y = GlobalTheory.RowEvalHH.evF R X h t c S y) ∧ ∀ y, ‖f y‖ ^ 2 = K * ∏ τ, ‖(y τ : X.B.H (X.pl.symm τ))‖ ^ 2 := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM t c ht S hS
  obtain ⟨c0, -, hc0⟩ := GlobalTheory.EvalNormTransfer.evalTranslate_norm R F X h hL hG hM t ht
  set K : ℝ := c0 * (ipM (MP R) R.ν0 R.fd0 S S).re with hKdef
  have hK : ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) →
      MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)) 2 (muX X) ∧
      ∫ x, ‖ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _
        ((iotaX X h).symm x) t)‖ ^ 2 ∂(muX X) = K := fun v₀ hv =>
    ⟨(hc0 v₀ hv S hS).1, (hc0 v₀ hv S hS).2.1⟩
  have hmem : ∀ y, MemLp (phi R X h t c S y) 2 (muX X) := fun y =>
    (phi_memLp_integral R X h t c S K hK y).1
  let L : (∀ τ, Wsub R X c τ) → L2X X := fun y => (hmem y).toLp (phi R X h t c S y)
  have hL_add : ∀ [DecidableEq D.what₂.Tau] (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau) (z₁ z₂ : Wsub R X c τ),
      L (Function.update y τ (z₁ + z₂)) = L (Function.update y τ z₁) + L (Function.update y τ z₂) := by
    intro _ y τ z₁ z₂
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (phi_add R X h t c S y τ z₁ z₂) x)
  have hL_smul : ∀ [DecidableEq D.what₂.Tau] (y : ∀ τ, Wsub R X c τ) (τ : D.what₂.Tau) (a : ℂ) (z : Wsub R X c τ),
      L (Function.update y τ (a • z)) = (starRingEnd ℂ a) • L (Function.update y τ z) := by
    intro _ y τ a z
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun (phi_smul R X h t c S y τ a z) x)
  let f : MultilinearMap ℂ (fun τ => ↥(Wsub R X c τ)) (L2X X) :=
    { toFun := fun y => conjL (muX X) (L y)
      map_update_add' := fun y τ z₁ z₂ => by
        rw [hL_add, map_add]
      map_update_smul' := fun y τ a z => by
        rw [hL_smul, LinearIsometryEquiv.map_smulₛₗ, starRingEnd_self_apply] }
  refine ⟨f, K, fun y => ?_, fun y => ?_⟩
  · show conjL (muX X) (L y) = evF R X h t c S y
    unfold evF
    split
    · rfl
    · exact absurd (hmem y) ‹_›
  · show ‖conjL (muX X) (L y)‖ ^ 2 = _
    rw [LinearIsometryEquiv.norm_map, norm_sq_toLp_eq]
    exact (phi_memLp_integral R X h t c S K hK y).2

end GlobalTheory.RowEvalHHNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousAtDetRootOne
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar unitScalar)

noncomputable section

namespace GlobalTheory.ExtCharCont

open GlobalTheory.ExtChar Polynomial

theorem charpoly_smul_comp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {c : ℂ} (hc : c ≠ 0) :
    (c • M).charpoly = C (c ^ n) * M.charpoly.comp (C c⁻¹ * X) := by
  apply Polynomial.funext
  intro t
  rw [eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, Matrix.eval_charpoly, Matrix.eval_charpoly]
  have h := Matrix.det_smul (Matrix.scalar (Fin n) (c⁻¹ * t) - M) c
  rw [Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext i j
  simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]
  split_ifs <;> field_simp

theorem isRegSS_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {c : ℂ} (hc : c ≠ 0) (h : IsRegSS M) :
    IsRegSS (c • M) := by
  unfold IsRegSS at *
  obtain ⟨a, b, hab⟩ := h
  rw [charpoly_smul_comp M hc]
  have h1 := congrArg (fun p : ℂ[X] => p.comp (C c⁻¹ * X)) hab
  simp only [add_comp, mul_comp, one_comp] at h1
  refine ⟨C (c ^ n)⁻¹ * a.comp (C c⁻¹ * X), C (c ^ n)⁻¹ * C c * b.comp (C c⁻¹ * X), ?_⟩
  have e1 : (C (c ^ n)⁻¹ * C (c ^ n) : ℂ[X]) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hc), C_1]
  have e2 : (C c * C c⁻¹ : ℂ[X]) = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hc, C_1]
  rw [derivative_C_mul, derivative_comp, derivative_C_mul, derivative_X, mul_one]
  linear_combination h1 + (a.comp (C c⁻¹ * X) * M.charpoly.comp (C c⁻¹ * X) +
    C c * C c⁻¹ * b.comp (C c⁻¹ * X) * (derivative M.charpoly).comp (C c⁻¹ * X)) * e1 +
    b.comp (C c⁻¹ * X) * (derivative M.charpoly).comp (C c⁻¹ * X) * e2

variable {n : ℕ} (ε : Fin n → Bool)

theorem umat_mul' (a b : UJ ε) : umat (a * b) = umat a * umat b := rfl

theorem continuousAt_detRoot_one : ContinuousAt (detRoot ε) 1 := by
  have h1 : Continuous fun g : UJ ε => (umat g).det :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_det
  have h2 : (umat (1 : UJ ε)).det ∈ Complex.slitPlane := by
    have : umat (1 : UJ ε) = 1 := rfl
    rw [this, Matrix.det_one]
    exact Complex.one_mem_slitPlane
  have h3 : ContinuousAt (fun g : UJ ε => Complex.arg (umat g).det) 1 :=
    ContinuousAt.comp (f := fun g : UJ ε => (umat g).det) (Complex.continuousAt_arg h2) h1.continuousAt
  exact Circle.exp.continuous.continuousAt.comp (h3.div_const _)

def locRoot (s y : UJ ε) : Circle := detRoot ε s * detRoot ε (s⁻¹ * y)

theorem continuousAt_locRoot (s : UJ ε) : ContinuousAt (locRoot ε s) s := by
  have h : ContinuousAt (fun y : UJ ε => detRoot ε (s⁻¹ * y)) s := by
    exact (continuousAt_detRoot_one ε).comp_of_eq ((continuous_const.mul continuous_id).continuousAt (x := s))
      (inv_mul_cancel s)
  exact continuousAt_const.mul h

variable [NeZero n]

theorem locRoot_pow (s y : UJ ε) : ((locRoot ε s y : Circle) : ℂ) ^ n = (umat y).det := by
  rw [locRoot, Circle.coe_mul, mul_pow, detRoot_pow ε (NeZero.ne n), detRoot_pow ε (NeZero.ne n),
    ← Matrix.det_mul, ← umat_mul', mul_inv_cancel_left]

def locPart (s y : UJ ε) : SUJ ε :=
  ⟨unitScalar ε (locRoot ε s y)⁻¹ * y, by
    show (umat (unitScalar ε (locRoot ε s y)⁻¹ * y)).det = 1
    rw [det_unitScalar_mul, Circle.coe_inv, inv_pow, locRoot_pow, inv_mul_cancel₀]
    intro h0
    have := GlobalTheory.SqIntSU.norm_det_umat ε y
    rw [h0, norm_zero] at this
    exact zero_ne_one this⟩

theorem continuousAt_locPart (s : UJ ε) : ContinuousAt (locPart ε s) s := by
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
  show ContinuousAt (fun y => unitScalar ε (locRoot ε s y)⁻¹ * y) s
  exact ((GlobalTheory.SqIntSU.continuous_unitScalar ε).continuousAt.comp (continuousAt_locRoot ε s).inv).mul continuousAt_id

theorem scalarMul_loc (s y : UJ ε) : scalarMul ε (locRoot ε s y, locPart ε s y) = y := by
  show unitScalar ε (locRoot ε s y) * (unitScalar ε (locRoot ε s y)⁻¹ * y) = y
  rw [← unitScalar_inv, mul_inv_cancel_left]

theorem isRegSS_unitScalar_mul (z : Circle) (y : UJ ε) (h : IsRegSS (ujMat ε y)) :
    IsRegSS (ujMat ε (unitScalar ε z * y)) := by
  have e : ujMat ε (unitScalar ε z * y) = (z : ℂ) • ujMat ε y := by
    show (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * ujMat ε y = _
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [e]
  exact isRegSS_smul _ (Circle.coe_ne_zero z) h

theorem continuousAt_avgChar (m : ℤ) (Θ' : SUJ ε → ℂ)
    (hΘ : ∀ g : SUJ ε, IsRegSS (suMat ε g) → ContinuousAt Θ' g) (g : SUJ ε) (hg : IsRegSS (suMat ε g)) :
    ContinuousAt (avgChar ε m Θ') g := by
  unfold avgChar
  refine continuousAt_const.mul (tendsto_finset_sum _ fun j _ => ?_)
  have h : ContinuousAt (fun x : SUJ ε => Θ' (cen ε j * x)) g :=
    ContinuousAt.comp (f := fun x : SUJ ε => cen ε j * x)
      (hΘ _ (isRegSS_unitScalar_mul ε (ZMod.toCircle j)⁻¹ (g : UJ ε) hg))
      (continuous_const.mul continuous_id).continuousAt
  exact continuousAt_const.mul h

theorem continuousAt_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (m : ℤ) (Θ' : SUJ ε → ℂ), (∀ g : SUJ ε, IsRegSS (suMat ε g) → ContinuousAt Θ' g) → ∀ s : UJ ε, IsRegSS (ujMat ε s) → ContinuousAt (GlobalTheory.ExtChar.extChar ε m Θ') s := by
  intro n _ ε m Θ' hΘ s hs
  have e : extChar ε m Θ' = fun y => ((locRoot ε s y : Circle) : ℂ) ^ m * avgChar ε m Θ' (locPart ε s y) := by
    funext y
    rw [← extChar_scalarMul, scalarMul_loc]
  rw [e]
  have h1 : ContinuousAt (fun y => ((locRoot ε s y : Circle) : ℂ)) s :=
    continuous_subtype_val.continuousAt.comp (continuousAt_locRoot ε s)
  refine (h1.zpow₀ m (Or.inl (Circle.coe_ne_zero _))).mul ?_
  exact ContinuousAt.comp (f := locPart ε s)
    (continuousAt_avgChar ε m Θ' hΘ _ (isRegSS_unitScalar_mul ε (locRoot ε s s)⁻¹ s hs))
    (continuousAt_locPart ε s)

end GlobalTheory.ExtCharCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedHeisenbergWeilTranslateAtZer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResHeisCont

theorem continuous_res_heisO : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ u : WO V W, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W u (ω p f)) 0 := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 h𝓨 f hf u
  have hψ := hω.std.1
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).1
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓨.2.2]; exact ENNReal.one_lt_top⟩
  have hy : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B 0 := by
    unfold isoPart
    exact (continuous_id.matrix_mul continuous_const).add continuous_const
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f hf K hK
  unfold res
  refine continuousAt_of_dominated (bound := fun _ => c) ?_ ?_ (integrable_const c) ?_
  · exact Filter.Eventually.of_forall fun p =>
      ((GlobalTheory.HeisOrtho.continuous_heisO hψ (hω.om_pres p f hf).cont u).comp hy).aestronglyMeasurable
  · filter_upwards [hKn] with p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ]; exact hc p hp _
  · refine Filter.Eventually.of_forall fun y => ?_
    unfold heisO
    exact (continuous_const.mul (hω.om_cont f hf _)).continuousAt

end GlobalTheory.ResHeisCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRestrictedWeilFirstFactorApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ResFirstCont

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem continuous_res_left : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∀ x, Continuous fun m : GA D V => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) x := by
  intro D V V' W r C B ψ χS χT ω hω μ 𝓨 h𝓨 f hf x
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓨.2.2]; exact ENNReal.one_lt_top⟩
  have hy : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B x := by
    unfold isoPart
    exact (continuous_id.matrix_mul continuous_const).add continuous_const
  refine continuous_iff_continuousAt.2 fun m₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds m₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f hf (K ×ˢ {1})
    (hK.prod isCompact_singleton)
  unfold res
  refine continuousAt_of_dominated (bound := fun _ => c) ?_ ?_ (integrable_const c) ?_
  · exact Filter.Eventually.of_forall fun m =>
      ((hω.om_pres (m, 1) f hf).cont.comp hy).aestronglyMeasurable
  · filter_upwards [hKn] with m hm
    exact Filter.Eventually.of_forall fun y => hc (m, 1) ⟨hm, rfl⟩ _
  · refine Filter.Eventually.of_forall fun y => ?_
    exact ((hω.om_cont f hf _).comp (Continuous.prodMk_left 1)).continuousAt

end GlobalTheory.ResFirstCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTrivially
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BesIso

theorem symplO_negSp_eq {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have hinv : (-S.gram)⁻¹ = -S.gram⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det S)])
  have h : hO (negSp S) T x y = -hO S T x y := by
    simp only [hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  rw [symplO_eq, symplO_eq, h, mul_neg, map_neg]

theorem hO_extX_eq {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a : Mx D T.rank ρ) (u : WO S T) :
    hO S T (d.extX T a) u = hO S T (d.extX T a) (d.extY T (u ⬝ d.jY)) := by
  have hu : u = d.extX T (u ⬝ d.jX) + d.ext0 T (u ⬝ d.j0) + d.extY T (u ⬝ d.jY) := ((d.coordS T).symm_apply_apply u).symm
  have h1 := d.hO_ext T a (u ⬝ d.jX) 0 (u ⬝ d.jY) 0 (u ⬝ d.j0)
  have h2 := d.hO_ext T a 0 0 (u ⬝ d.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h1 h2
  rw [← hu] at h1
  rw [h1, h2]
  simp [pairS, hO]

end GlobalTheory.AscFin.BesIso

open GlobalTheory.AscFin.BesIso in

theorem GlobalTheory.AscFin.BesIso.splits_iso : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have sd : ∀ i, i ≤ D.R.m → 1 ≤ i → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := fun i hi h1 =>
    (G.isV (X := .grid i 0) ⟨hi, Nat.zero_le _⟩ (fun j hj => by injection hj with e1 e2; omega)).sd
  have sdV := isSelfDualC_neg (sd (2 * ρ + 2) h (by omega))
  have sdW := sd (2 * ρ + 1) (by omega) (by omega)
  have hmx : ∀ w, w ∈ latRow G (2 * ρ + 1) → MxAt (fun _ => True) w := fun w hw =>
    ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdV sdW (fun _ => True) w).1 hw.1).1
  refine ⟨fun i j => ?_, fun a ha => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hmx u hu i k)
  · have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdV sdW (fun _ => True) _ (hmx _ ha)).1 ha.1 u hu.1
    rw [symplO_negSp_eq, AddChar.map_neg_eq_inv, inv_eq_one] at key
    rw [symplO_eq] at key ⊢
    rw [← hO_extX_eq]
    exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal TensorProduct

namespace GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def term (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E) : ℂ :=
  res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G) 0

def phase (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r) : ℂ :=
  ψ (symplO V W (isoPart V W C' (Matrix.map y (incA D))) (isoPart V W C κ))

def pairQ (W : HSp D) {r : ℕ} (y : Matrix (Fin W.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin W.rank) D.host.E :=
  D.host.xi0 • (adj D y * W.gram)

def ratPair (W : HSp D) {r : ℕ} (y x : Matrix (Fin W.rank) (Fin r) D.host.E) : ℝ :=
  ((Algebra.trace ℚ D.host.E (Matrix.trace (pairQ W y * x)) : ℚ) : ℝ)

def dirAt (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin r) ℂ) : Matrix (Fin W.rank) (Fin V.rank) ℂ :=
  z * (adj D C * V.gram).map (tauE D τ)

def derAlong (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) (x : Matrix (Fin W.rank) (Fin r) D.host.E) (G : WO V W → ℂ) : WO V W → ℂ :=
  ∑ τ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (dirAt V W C τ (x.map (tauE D τ))) G

def finLift {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  x.map fun e => (pairA D.host.F 0 1 : AF D.host.F) ⊗ₜ[D.host.F] e

end GlobalTheory.MixedTerm

end
end

