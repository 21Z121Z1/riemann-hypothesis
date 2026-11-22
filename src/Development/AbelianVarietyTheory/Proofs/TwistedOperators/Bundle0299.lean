import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0148
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0269
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0286
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFockVacuumCauchyRiemann
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.HeisTranslCR

open GlobalTheory.FockCompare GlobalTheory.VacUnique

theorem deriv_twisted_line_at {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] (F : R → ℂ) (hF : Differentiable ℝ F)
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a w u : R) :
    deriv (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a (t • u) : ℂ)) * F (w + t • u)) 0 =
      fderiv ℝ F w u - Real.pi * Complex.I * (om a u : ℂ) * F w := by
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 : HasDerivAt (fun t : ℝ => F (w + t • u)) (fderiv ℝ F w u) 0 := by
    have h := (hF (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * (om a (t • u) : ℂ))
      (-(Real.pi * Complex.I) * (om a u : ℂ)) 0 := by
    have e : (fun t : ℝ => -(Real.pi * Complex.I) * (om a (t • u) : ℂ)) =
        fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * (om a u : ℂ)) := by
      funext t
      rw [LinearMap.map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (-(Real.pi * Complex.I) * (om a u : ℂ))
  have h4 := (h3.cexp.mul h2).deriv
  refine Eq.trans h4 ?_
  simp only [zero_smul, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul]
  ring

theorem differentiable_phase {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a : R) :
    Differentiable ℝ fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) := by
  have h : Differentiable ℝ fun w : R => ((om a w : ℝ) : ℂ) :=
    Complex.ofRealCLM.differentiable.comp (LinearMap.toContinuousLinearMap (om a)).differentiable
  exact ((differentiable_const _).mul h).cexp

theorem fderiv_phase_mul {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R] (F : R → ℂ)
    (hF : Differentiable ℝ F) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (a w u : R) :
    fderiv ℝ (fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) * F w) w u =
      Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) *
        (fderiv ℝ F w u - Real.pi * Complex.I * (om a u : ℂ) * F w) := by
  have hG : Differentiable ℝ fun w : R => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) * F w :=
    (differentiable_phase om a).mul hF
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 := (hG (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero, Function.comp_def] at h2
  rw [← h2.deriv]
  have e : (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a (w + t • u) : ℂ)) * F (w + t • u)) =
      fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om a w : ℂ)) *
        (Complex.exp (-(Real.pi * Complex.I) * (om a (t • u) : ℂ)) * F (w + t • u)) := by
    funext t
    rw [LinearMap.map_add, Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [e, deriv_const_mul_field, deriv_twisted_line_at F hF om a w u]

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

theorem heisO_real_at (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (y : WO S T) (w : RW T S) :
    heisO ψ S T (iotaW σ T S w) f y =
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S y) w : ℂ)) * f (y + iotaW σ T S w) := by
  unfold heisO
  rw [GlobalTheory.OrientedChar.char_symplOH D θ ψ h.inf hψ S T _ _ (Or.inr (h.real_iota T S w)), h.pi_iota]

open Classical in

theorem dRho_eq_at (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (y : WO S T) (hF : Differentiable ℝ fun v : RW T S => f (y + iotaW σ T S v)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : RW T S) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f (y + iotaW σ T S w) =
      fderiv ℝ (fun v : RW T S => f (y + iotaW σ T S v)) w (Pi.single τ z) -
        Real.pi * Complex.I * (omO S T (piW θ T S y + w) (Pi.single τ z) : ℂ) * f (y + iotaW σ T S w) := by
  refine Eq.trans ?_ (deriv_twisted_line_at _ hF (omO S T) (piW θ T S y + w) w (Pi.single τ z))
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ z t, heisO_real_at h hψ, (piW θ T S).map_add, h.pi_iota, add_assoc,
    ← (iotaW σ T S).map_add]

open Classical in

theorem heis_translate_cauchy_riemann : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ y : WO S T, Differentiable ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) ∧ ∀ w z : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w z + Complex.I * fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) = (Real.pi : ℂ) * Complex.I * ((GlobalTheory.VacUnique.omO S T w z : ℂ) + Complex.I * (GlobalTheory.VacUnique.omO S T w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) : ℂ)) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y := by
  intro D θ σ h ψ hψ S T A B f hf y
  have hF : Differentiable ℝ fun v : RW T S => f (y + iotaW σ T S v) :=
    (GlobalTheory.OrientedHeis.theta_sm h hf.1 y).differentiable (by simp)
  have hG : (fun w : RW T S => heisO ψ S T (iotaW σ T S w) f y) = fun w : RW T S =>
      Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S y) w : ℂ)) * f (y + iotaW σ T S w) := by
    funext w
    exact heisO_real_at h hψ S T f y w
  rw [hG]
  refine ⟨(differentiable_phase (omO S T) (piW θ T S y)).mul hF, fun w z => ?_⟩
  rw [fderiv_phase_mul _ hF, fderiv_phase_mul _ hF]
  rw [heisO_real_at h hψ S T f y w]
  set a := piW θ T S y with ha
  set Fd := fderiv ℝ (fun v : RW T S => f (y + iotaW σ T S v)) w with hFd
  set Fw := f (y + iotaW σ T S w) with hFw
  let L : RW T S →+ ℂ :=
    { toFun := fun s => Fd s - Real.pi * Complex.I * (omO S T (a + w) s : ℂ) * Fw
      map_zero' := by simp
      map_add' := fun x x' => by
        rw [ContinuousLinearMap.map_add, LinearMap.map_add, Complex.ofReal_add]
        ring }
  have hL : L z + Complex.I * L (jO S T A.cart B.cart z) = 0 := by
    rw [← Finset.univ_sum_single z, map_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun τ _ => ?_
    have h1 := congrFun (hf.2 τ (z τ)) (y + iotaW σ T S w)
    have h2 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z τ) f (y + iotaW σ T S w) +
        Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (A.cart τ) (B.cart τ) (z τ)) f
          (y + iotaW σ T S w) = 0 := h1
    have h3 := dRho_eq_at h hψ S T f y hF τ (z τ) w
    have h4 := dRho_eq_at h hψ S T f y hF τ (cplxO (A.cart τ) (B.cart τ) (z τ)) w
    have h5 := GlobalTheory.VacUnique.Ann.jO_single S T A.cart B.cart τ (z τ)
    have h6 : L (Pi.single τ (z τ)) + Complex.I * L (Pi.single τ (cplxO (A.cart τ) (B.cart τ) (z τ))) = 0 :=
      (congrArg₂ (fun a b : ℂ => a + Complex.I * b) h3 h4).symm.trans h2
    exact (congrArg (fun b => L (Pi.single τ (z τ)) + Complex.I * L b) h5).trans h6
  have e1 : L z = Fd z - Real.pi * Complex.I * ((omO S T a z : ℂ) + (omO S T w z : ℂ)) * Fw := by
    show Fd z - Real.pi * Complex.I * (omO S T (a + w) z : ℂ) * Fw = _
    rw [LinearMap.map_add, LinearMap.add_apply, Complex.ofReal_add]
  have e2 : L (jO S T A.cart B.cart z) = Fd (jO S T A.cart B.cart z) - Real.pi * Complex.I *
      ((omO S T a (jO S T A.cart B.cart z) : ℂ) + (omO S T w (jO S T A.cart B.cart z) : ℂ)) * Fw := by
    show Fd _ - Real.pi * Complex.I * (omO S T (a + w) _ : ℂ) * Fw = _
    rw [LinearMap.map_add, LinearMap.add_apply, Complex.ofReal_add]
  rw [e1, e2] at hL
  linear_combination (Complex.exp (-(Real.pi * Complex.I) * (omO S T a w : ℂ))) * hL

end GlobalTheory.HeisTranslCR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianAdjointLawsStandardCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.AdjLawPf

variable {D : D7}

theorem inv_mul_gram (V : HSp D) : ((HSpace.gram V)⁻¹.map (incA D)) * ((HSpace.gram V).map (incA D)) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.OrientedAdjoint.gram_mul_inv V)

theorem gramI_conj (V : HSp D) : (((HSpace.gram V)⁻¹.map (incA D)).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) :=
  GlobalTheory.OrientedAdjoint.inv_conj (cA D) _ _ (GlobalTheory.OrientedAdjoint.gram_mul_inv V) (GlobalTheory.OrientedAdjoint.gram_conj V)

theorem conjT_mul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) (B : Matrix (Fin n) (Fin k) (AE D)) :
    ((A * B).map (cA D))ᵀ = (B.map (cA D))ᵀ * (A.map (cA D))ᵀ := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem conjT_conjT {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) : (((A.map (cA D))ᵀ).map (cA D))ᵀ = A := by
  ext i j; simp [GlobalTheory.DualPairCheck.cA_cA]

theorem adjO_eq (S T : HSp D) (y : WO T S) :
    (adjO S T y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      HMul.hMul (HMul.hMul ((HSpace.gram T)⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose) ((HSpace.gram S).map (incA D)) := rfl

theorem adj_invol (S T : HSp D) (x : WO S T) : adjO S T (adjO T S x) = x := by
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj]
  simp only [← Matrix.mul_assoc]
  rw [inv_mul_gram, Matrix.one_mul, Matrix.mul_assoc, inv_mul_gram, Matrix.mul_one]

theorem adj_add (S T : HSp D) (y y' : WO T S) : adjO S T (y + y') = adjO S T y + adjO S T y' := by
  rw [adjO_eq, adjO_eq, adjO_eq]
  have e : ((y + y' : WO T S) : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) =
      (y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) + (y' : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D) := by
    ext i j; simp
  rw [e, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem hO_eq (S T : HSp D) (x y : WO S T) : hO S T x y = Matrix.trace (adjO T S y * x) := by
  rw [adjO_eq]
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem hO_herm (S T : HSp D) (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  rw [hO_eq, hO_eq]
  have e : cA D (Matrix.trace (adjO T S y * x)) = Matrix.trace (((adjO T S y * x).map (cA D))ᵀ) := by
    rw [Matrix.trace_transpose]; simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
  rw [e, conjT_mul, adjO_eq, conjT_mul, conjT_mul, conjT_conjT, GlobalTheory.OrientedAdjoint.gram_conj, gramI_conj,
    adjO_eq, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem hO_adj (S T : HSp D) (x y : WO T S) : hO S T (adjO S T x) (adjO S T y) = hO T S y x := by
  rw [hO_eq, hO_eq, adj_invol, Matrix.trace_mul_comm]

theorem adj_sympl (S T : HSp D) (y y' : WO T S) :
    symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y' := by
  unfold symplO
  rw [hO_adj, ← hO_herm, ← GlobalTheory.DualPairCheck.trace_cA, map_mul, GlobalTheory.DualPairCheck.cA_cA,
    GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_adj (S T : HSp D) (y y' : WO T S) :
    symplOH S T (adjO S T y) (adjO S T y') = -symplOH T S y y' := by
  unfold symplOH; rw [adj_sympl, mul_neg]

end GlobalTheory.AdjLawPf

namespace GlobalTheory.AdjLawPf

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by simp [Formalism.L2.Theta.mt]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (V : HSp D) (g : GA D V) : mt V g * mt V g⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem mt_inv_mul (V : HSp D) (g : GA D V) : mt V g⁻¹ * mt V g = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem conjT_gram (V : HSp D) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V g⁻¹ := by
  calc ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * (mt V g * mt V g⁻¹) := by
        rw [mt_mul_inv, Matrix.mul_one]
    _ = (((mt V g).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) * mt V g) * mt V g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.DualPairCheck.mt_unit]

theorem gramI_conjT (V : HSp D) (h : GA D V) :
    ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = mt V h * ((HSpace.gram V)⁻¹.map (incA D)) := by
  have k : ((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D)) = ((HSpace.gram V).map (incA D)) * mt V h := by
    rw [conjT_gram, inv_inv]
  calc ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ = ((HSpace.gram V)⁻¹.map (incA D)) * ((mt V h⁻¹).map (cA D))ᵀ * (((HSpace.gram V).map (incA D)) * ((HSpace.gram V)⁻¹.map (incA D))) := by
        rw [GlobalTheory.OrientedAdjoint.gram_mul_inv, Matrix.mul_one]
    _ = ((HSpace.gram V)⁻¹.map (incA D)) * (((mt V h⁻¹).map (cA D))ᵀ * ((HSpace.gram V).map (incA D))) * ((HSpace.gram V)⁻¹.map (incA D)) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [k, ← Matrix.mul_assoc, inv_mul_gram, Matrix.one_mul]

theorem adj_act (S T : HSp D) (g : GA D S) (h : GA D T) (y : WO T S) :
    adjO S T (actO T S h g y) = actO S T g h (adjO S T y) := by
  unfold actO
  rw [adjO_eq, adjO_eq, conjT_mul, conjT_mul]
  simp only [← Matrix.mul_assoc]
  rw [gramI_conjT, Matrix.mul_assoc _ ((mt S g).map (cA D))ᵀ, conjT_gram]
  simp only [Matrix.mul_assoc]

theorem adj_ratW (S T : HSp D) (γ : Matrix (Fin S.rank) (Fin T.rank) D.host.E) :
    adjO S T (ratW S T γ) = ratW T S (HMul.hMul (HMul.hMul (HSpace.gram T)⁻¹ (γ.map star)ᵀ) (HSpace.gram S)) := by
  have e : ((γ.map (incA D)).map (cA D))ᵀ = ((γ.map star)ᵀ).map (incA D) := by
    ext i j; simp [GlobalTheory.DualPairCheck.cA_incA]
  rw [adjO_eq]
  unfold ratW
  rw [e, Matrix.map_mul, Matrix.map_mul]

theorem adj_rat_of (S T : HSp D) (y : WO T S) (hy : y ∈ ratL S T) : adjO S T y ∈ ratL T S := by
  obtain ⟨γ, rfl⟩ := hy
  exact ⟨_, (adj_ratW S T γ).symm⟩

theorem adj_rat (S T : HSp D) (y : WO T S) : adjO S T y ∈ ratL T S ↔ y ∈ ratL S T :=
  ⟨fun h => by have := adj_rat_of T S _ h; rwa [adj_invol] at this, adj_rat_of S T y⟩

theorem adj_half (S T : HSp D) (e : AE D) (y : WO T S) (hy : IsHalf e y) : IsHalf (cA D e) (adjO S T y) := by
  intro i j
  have hy' : ∀ k l, cA D e * cA D (y k l) = cA D (y k l) := fun k l => by rw [← map_mul, hy]
  rw [adjO_eq]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (incA D ((HSpace.gram T)⁻¹ i l) * incA D (HSpace.gram S k j)) * hy' k l

theorem adj_cont (S T : HSp D) : Continuous (adjO S T) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have h : Continuous fun y : WO T S => ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D))ᵀ :=
    (continuous_id.matrix_map (GlobalTheory.HeckeConj.continuous_cA D)).matrix_transpose
  exact (continuous_const.matrix_mul h).matrix_mul continuous_const

set_option synthInstance.maxHeartbeats 400000 in
theorem adj_infPart (S T : HSp D) (u : WO T S) (hu : u.map (infPart D) = 0) : (adjO S T u).map (infPart D) = 0 := by
  have h0 : ∀ k l, infPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show infPart D (adjO S T u i j) = 0
  simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.infPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

set_option synthInstance.maxHeartbeats 400000 in
theorem adj_finPart (S T : HSp D) (u : WO T S) (hu : u.map (finPart D) = 0) : (adjO S T u).map (finPart D) = 0 := by
  have h0 : ∀ k l, finPart D (u k l) = 0 := fun k l => by
    have := congrFun (congrFun hu k) l
    simpa only [Matrix.map_apply, Matrix.zero_apply] using this
  refine Matrix.ext fun i j => ?_
  show finPart D (adjO S T u i j) = 0
  simp only [adjO_eq, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    GlobalTheory.PlaceIdem.finPart_cA, h0, map_zero, mul_zero, zero_mul, Finset.sum_const_zero]

def adjHom (S T : HSp D) : WO T S →+ WO S T := AddMonoidHom.mk' (adjO S T) (adj_add S T)

theorem conj_psi (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp

theorem adj_heis (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (y : WO T S) (f : WO S T → ℂ) :
    heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f) := by
  funext w
  simp only [heisO, dag, map_mul, adj_add, symplOH_adj, conj_psi ψ hψ, neg_neg]

theorem adj_theta (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (S T : HSp D) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (dag S T f) where
  quasi γ w := by
    simp only [dag]
    rw [adj_add, adj_ratW, hf.quasi, map_mul, conj_psi ψ hψ, ← adj_ratW, symplOH_adj]
    simp only [neg_neg]
  level := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap (adjHom S T), hUo.preimage (adj_cont S T), fun u hu h0 => ?_⟩
    rw [adj_heis ψ hψ]
    exact congrArg (dag S T) (hU (adjO S T u) hu (adj_infPart S T u h0))
  cont := Complex.continuous_conj.comp (hf.cont.comp (adj_cont S T))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((adjHom S T).comp L) ((adj_cont S T).comp hL) (fun t => adj_finPart S T _ (hfin t))
      (adjO S T w)
    have e : (fun t => dag S T f (w + L t)) =
        fun t => Complex.conjCLE (f (adjO S T w + (adjHom S T).comp L t)) := by
      funext t; simp [dag, adj_add, adjHom]
    rw [e]
    exact Complex.conjCLE.contDiff.comp h

theorem adjLaw : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, AdjLaw ψ S T := by
  intro D ψ hψ S T
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  exact { invol := adj_invol S T
          add := adj_add S T
          cont := adj_cont S T
          sympl := adj_sympl S T
          act := adj_act S T
          rat := adj_rat S T
          half := adj_half S T
          Heisenberg₂ := adj_heis ψ hn S T
          theta := adj_theta ψ hn S T }

end GlobalTheory.AdjLawPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HolomorphicUpToFactorOfLoweringKilledTorusWeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdSpan.ConjHol

open GlobalTheory.HolRead in

theorem holUpTo_of_lowKilled : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (la : Wt C.X.Ψ T.rank) (m : D.what₂.Tau → ℤ) (φ : GA D T → ℂ), LowKilled C.θ T B φ → (∀ (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (g : GA D T), φ (g * torAt C.θ T B ρ t) = cexp (((∑ a, ((m ρ - la (C.m.e ρ) a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) * φ g) → HolUpTo C B la (detPow C.θ T m) φ := by
  intro D S T C B hB la m φ hL htor g
  have R : GlobalTheory.SmoothForms.RealPoints C.θ T := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 C.θ C.inf T
  obtain ⟨U1, U2, U3⟩ := GlobalTheory.T.conjugateModel_unitFrames_eq_movedOrthonormalFrames D S T C B hB
  obtain ⟨dMul, dNe, dExp⟩ := GlobalTheory.T.realPlaceDeterminantPower_mul_ne_zero_exp D C.θ C.inf T m
  let F : Frame C.X.Ψ T.rank → ℂ := fun y =>
    if h : IsUnitFr C.X y then φ (g * (U2 y h).choose) / detPow C.θ T m (U2 y h).choose else 0
  have hF : ∀ a ∈ GinfC T, F (C.xB (C.mvB a B)) = φ (g * a) / detPow C.θ T m a := by
    intro a ha
    have hy := U1 a
    simp only [F, dif_pos hy]
    rw [U3 _ (U2 _ hy).choose_spec.1 a ha (U2 _ hy).choose_spec.2]
  obtain ⟨Q, Q1, Q2⟩ := GlobalTheory.T.exists_extension_torusEquivariant_orthonormalFrames _ _ C.X la F (by
    intro y hy t
    obtain ⟨a, ha, rfl⟩ := U2 y hy
    let s : D.what₂.Tau → Fin T.rank → ℝ := fun ρ c => -t (C.m.e ρ) c
    obtain ⟨hk, hk2⟩ := GlobalTheory.T.compactTorusProductRealPlaces_spec D S T C B hB s
    have e1 := xB_mvB_mul C B hB a (torProd C.θ T B s) (fun τ => diagonal fun c => cexp ((t τ c : ℂ) * I)) fun ρ => ?_
    · erw [← e1]
      rw [hF _ (mul_mem ha hk), hF a ha, ← mul_assoc,
      apply_mul_torProd C.θ T B _ φ htor, apply_mul_torProd C.θ T B _ _ (GlobalTheory.T.realPlaceDeterminantPower_mul_compactTorusElement D S T C B hB m)]
      have hb : (bchar la fun τ => (diagonal fun c => cexp ((t τ c : ℂ) * I) : Matrix (Fin T.rank) (Fin T.rank) ℂ)) =
          cexp (((∑ ρ, ∑ c, ((la (C.m.e ρ) c : ℝ)) * t (C.m.e ρ) c : ℝ) : ℂ) * I) := by
        unfold bchar
        rw [← Equiv.prod_comp C.m.e]
        push_cast
        rw [Finset.sum_mul, Complex.exp_sum]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [Finset.sum_mul, Complex.exp_sum]
        refine Finset.prod_congr rfl fun c _ => ?_
        rw [diagonal_apply_eq, ← Complex.exp_int_mul, mul_assoc]
      have hA : cexp (((∑ ρ, ∑ c, ((m ρ - la (C.m.e ρ) c : ℤ) : ℝ) * s ρ c : ℝ) : ℂ) * I) =
          cexp (((∑ ρ, ∑ c, ((m ρ : ℤ) : ℝ) * s ρ c : ℝ) : ℂ) * I) *
            cexp (((∑ ρ, ∑ c, ((la (C.m.e ρ) c : ℝ)) * t (C.m.e ρ) c : ℝ) : ℂ) * I) := by
        rw [← Complex.exp_add, ← add_mul]
        congr 2
        rw [← Complex.ofReal_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [s]; push_cast; ring
      rw [hb, hA]
      field_simp [dNe a, Complex.exp_ne_zero]
    · rw [hk2]
      show _ = B ρ * (diagonal fun c => cexp ((t (C.m.e ρ) c : ℂ) * I)).map (starRingEnd ℂ) * (B ρ)⁻¹
      rw [diagonal_map (map_zero _)]
      congr 3
      funext c
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
      simp only [s]; push_cast; ring_nf)
  have hQ : ∀ a ∈ GinfC T, Q (C.xB (C.mvB a B)) = φ (g * a) / detPow C.θ T m a := fun a ha => by
    rw [Q1 _ (U1 a), hF a ha]
  refine ⟨Q, GlobalTheory.T.differentiableOn_frames_of_killedNilpotentDerivative _ _ C.X la Q Q2 fun y hy => ?_, Q2, fun a ha => ?_⟩
  swap
  · rw [hQ a ha]; field_simp [dNe a]
  obtain ⟨a, ha, rfl⟩ := U2 y hy
  have hs : DifferentiableAt ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0 :=
    (((GlobalTheory.SmoothForms.isSmoothInf_iff φ).1 ((GlobalTheory.SmoothForms.smooth_iff R φ).1 hL.1) (g * a)).differentiable
      (by simp)) 0
  let L : Frame C.X.Ψ T.rank →L[ℝ] GlobalTheory.SmoothForms.LieN T := LinearMap.toContinuousLinearMap (toLieC C R B)
  let lam : GlobalTheory.SmoothForms.LieN T →L[ℝ] ℂ := trCL T m
  let f : GlobalTheory.SmoothForms.LieN T → ℂ := fun Y =>
    (detPow C.θ T m a)⁻¹ * (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y) * cexp (-lam Y))
  have key : ∀ Z ∈ unitLie C.X, Q (rmul (C.xB (C.mvB a B)) (expFr Z)) = f (L Z) := by
    intro Z hZ
    have he := GlobalTheory.SmoothForms.isExpFam_expInf R (L Z)
    rw [← xB_mvB_mul C B hB a _ _ fun ρ => ?_, hQ _ (mul_mem ha he.1), dMul, dExp]
    · simp only [f, lam, trCL_apply, mul_assoc, Complex.exp_neg]
      field_simp [dNe a]
    · show infMat _ _ (C.θ ρ) _ = _
      rw [he.2 ρ]
      change NormedSpace.exp ((toLieC C R B Z ρ).1) = _
      rw [(GlobalTheory.T.conjFrameToRealLieAlgebra_spec D S T C R B hB Z hZ).1 ρ,
        Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det _).2 (isUnit_det_B C hB ρ))]
      congr 2
      exact (exp_map_conj _).symm
  have h0 : (0 : Frame C.X.Ψ T.rank) ∈ unitLie C.X := fun τ => by
    have : mat (0 : Frame C.X.Ψ T.rank) τ = 0 := rfl
    simp [this]
  let Dφ := fderiv ℝ (fun Y : GlobalTheory.SmoothForms.LieN T => φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T Y)) 0
  have hE : HasFDerivAt (fun Y : GlobalTheory.SmoothForms.LieN T => cexp (-lam Y)) (cexp (-lam 0) • -lam) 0 :=
    lam.hasFDerivAt.neg.cexp
  have hfd := (hs.hasFDerivAt.mul hE).const_mul (detPow C.θ T m a)⁻¹
  have hfd' : HasFDerivAt f ((detPow C.θ T m a)⁻¹ • (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) •
      (cexp (-lam 0) • -lam) + cexp (-lam 0) • Dφ)) (L 0) := by
    have h0L : L 0 = 0 := map_zero L
    rw [h0L]; exact hfd
  refine ⟨_ , (hfd'.comp (0 : Frame C.X.Ψ T.rank) L.hasFDerivAt).hasFDerivWithinAt.congr key (key 0 h0), ?_⟩
  intro τ c d hcd Z hZ Z' hZ' e
  obtain ⟨ρ, rfl⟩ := C.m.e.surjective τ
  have hD := GlobalTheory.T.fderiv_conjFrameToRealLie_loweringOperator_eq_zero D S T C R B hB φ hL (g * a) ρ c d hcd Z Z' hZ hZ' e
  have hT := GlobalTheory.T.weightedTrace_conjFrameToRealLie_loweringOperator D S T C R B hB m ρ c d hcd Z Z' hZ hZ' e
  have hℓ : ∀ W : Frame C.X.Ψ T.rank, ((detPow C.θ T m a)⁻¹ • (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) •
      (cexp (-lam 0) • -lam) + cexp (-lam 0) • Dφ)).comp L W = (detPow C.θ T m a)⁻¹ *
      (φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) * (cexp (-lam 0) * -trLin T m (toLieC C R B W)) +
        cexp (-lam 0) * Dφ (toLieC C R B W)) := fun W => rfl
  rw [hℓ, hℓ]
  linear_combination ((detPow C.θ T m a)⁻¹ * cexp (-lam 0)) * hD -
    ((detPow C.θ T m a)⁻¹ * φ (g * a * GlobalTheory.SmoothForms.expInf C.θ T 0) * cexp (-lam 0)) * hT

end GlobalTheory.AdSpan.ConjHol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedIntertwiningIntegralNonzeroStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_intertwining_integral_nonzero : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.LanglandsClassification → ∀ (n : ℕ) (ε : Fin n → Bool) (I : IndModule ε), I.Positive → ∀ ν : Measure (UJ ε), IsHaarSub I.Nbar ν → ∀ v : I.V, v ≠ 0 → ∃ f ∈ I.fns, IsKFinFun f ∧ ∃ h ∈ I.oppFns, I.IsIntegral ν f h ∧ ⟪v, h 1⟫_ℂ ≠ 0 := by
  first | exact @GlobalTheory.IntertwiningDense.intertwining_values_dense | exact GlobalTheory.IntertwiningDense.intertwining_values_dense | (intros; apply GlobalTheory.IntertwiningDense.intertwining_values_dense <;> assumption)
end

