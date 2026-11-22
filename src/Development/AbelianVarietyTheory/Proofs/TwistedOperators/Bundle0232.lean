import Mathlib
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PositionOneOfUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrix
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem recursive_matrixPower_eq_matrix_pow {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) :
    Matrix.of (Formalism.REAL.epow E k) = (Matrix.of E) ^ k := by
  induction k with
  | zero =>
    ext a b
    simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ k ih =>
    ext a b
    rw [pow_succ, ← ih]
    simp [Formalism.REAL.epow, Matrix.mul_apply]

theorem scalarMatrix_mul_algebraMatrix_mul_apply {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((algebraMap ℂ A).mapMatrix P.transpose * M * (algebraMap ℂ A).mapMatrix Q.transpose) a b
      = ∑ c, ∑ d, (P c a * Q b d) • M c d := by
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, mul_comm]

theorem etr_conj_scalar_matrix {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  set L : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix P.transpose with hL
  set R : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix (P⁻¹).transpose with hR
  have hLR : L * R = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one, map_one]
  have hRL : R * L = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one, map_one]
  have hE : Matrix.of (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) = L * Matrix.of E * R := by
    ext a b
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply]
    rfl
  have hpow : ∀ m : ℕ, (L * Matrix.of E * R) ^ m = L * (Matrix.of E) ^ m * R := by
    intro m
    induction m with
    | zero => simp [hLR]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc L * Matrix.of E ^ m * R * (L * Matrix.of E * R)
          = L * Matrix.of E ^ m * (R * L) * Matrix.of E * R := by simp only [mul_assoc]
        _ = L * (Matrix.of E ^ m * Matrix.of E) * R := by rw [hRL]; simp only [mul_assoc, one_mul]
  have hk := recursive_matrixPower_eq_matrix_pow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k
  rw [hE, hpow, ← recursive_matrixPower_eq_matrix_pow] at hk
  have hent : ∀ a, Formalism.REAL.epow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k a a
      = ∑ c, ∑ d, (P c a * P⁻¹ a d) • Formalism.REAL.epow E k c d := by
    intro a
    have := congrFun (congrFun hk a) a
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply] at this
    exact this
  unfold Formalism.REAL.etr
  simp only [hent]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Matrix.mul_apply, h1, Matrix.one_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GluingLawHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Chain.RealIt.GlueProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {a b : ℕ}

open Classical in

def rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : PolF D b a :=
  ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ)

def ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : LPol b a →ₗ[ℂ] PolF D b a :=
  LinearMap.mulRight ℂ (rest τ P) ∘ₗ (MvPolynomial.rename (fun s => (τ, s))).toLinearMap

theorem ins_apply (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    ins τ P p = MvPolynomial.rename (fun s => (τ, s)) p * rest τ P := rfl

open Classical in
theorem glue_update (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (p : LPol b a) :
    glue (Function.update P τ p) = ins τ P p := by
  rw [ins_apply, glue, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), rest]
  congr 1
  · rw [Function.update_self]
  · refine Finset.prod_congr rfl fun ρ hρ => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hρ)]

theorem glue_eq (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) : glue P = ins τ P (P τ) := by
  classical
  rw [← glue_update, Function.update_eq_self]

theorem pderiv_other {τ ρ : D.what₂.Tau} (h : ρ ≠ τ) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (MvPolynomial.rename (fun s => (ρ, s)) p : PolF D b a) = 0 := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p t hp =>
    rw [map_mul, Derivation.leibniz, hp, MvPolynomial.rename_X, MvPolynomial.pderiv_X_of_ne]
    · simp
    · intro e
      exact h (congrArg Prod.fst e)

theorem pderiv_rest (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) :
    MvPolynomial.pderiv (τ, s) (rest τ P) = 0 := by
  classical
  unfold rest
  refine Finset.prod_induction _ (fun q : PolF D b a => MvPolynomial.pderiv (τ, s) q = 0) ?_ ?_ ?_
  · intro x y hx hy
    rw [Derivation.leibniz, hx, hy]; simp
  · simp
  · intro ρ hρ
    exact pderiv_other (Finset.ne_of_mem_erase hρ) s _

theorem pderiv_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.pderiv (τ, s) (ins τ P p) = ins τ P (MvPolynomial.pderiv s p) := by
  classical
  have hinj : Function.Injective (fun s : Fin b × Fin a => (τ, s)) := fun x y e => congrArg Prod.snd e
  have := MvPolynomial.pderiv_rename hinj s p
  rw [ins_apply, ins_apply, Derivation.leibniz, pderiv_rest, ← this]
  simp [mul_comm]

theorem mul_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (s : Fin b × Fin a) (p : LPol b a) :
    MvPolynomial.X (τ, s) * ins τ P p = ins τ P (MvPolynomial.X s * p) := by
  rw [ins_apply, ins_apply, map_mul, MvPolynomial.rename_X, mul_assoc]

theorem rai_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : raiO τ ε ε' i j (ins τ P p) = ins τ P (rai ε ε' i j p) := by
  unfold raiO rai
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.neg_apply, map_smul, map_neg, Derivation.coeFn_coe]
    rw [← pderiv_ins]

theorem low_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (i : Fin b) (j : Fin a) (p : LPol b a) : lowO τ ε ε' i j (ins τ P p) = ins τ P (low ε ε' i j p) := by
  unfold lowO low
  by_cases h : ε' i = ε j
  · simp only [h, if_true, LinearMap.smul_apply, map_smul, Derivation.coeFn_coe]
    rw [← pderiv_ins]
  · simp only [h, if_false, LinearMap.smul_apply, LinearMap.mulLeft_apply, map_smul]
    rw [← mul_ins]

theorem fockS_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (X : Matrix (Fin a) (Fin a) ℂ) (p : LPol b a) :
    fockS τ ε ε' X (ins τ P p) = ins τ P (locS ε ε' X p) := by
  unfold fockS locS
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add,
    Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

theorem fockT_ins (τ : D.what₂.Tau) (P : D.what₂.Tau → LPol b a) (ε : Fin a → Bool) (ε' : Fin b → Bool)
    (Y : Matrix (Fin b) (Fin b) ℂ) (p : LPol b a) :
    fockT τ ε ε' Y (ins τ P p) = ins τ P (locT ε ε' Y p) := by
  unfold fockT locT
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.add_apply, map_sum, map_smul, map_add,
    Module.End.mul_apply, low_ins, rai_ins]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h : j = k <;> simp [h]

theorem glue_span :
    Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol b a) → PolF D b a)) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue
  | (apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonomialRangeMembership.span_range_glue <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonomialRangeMembership.span_range_glue ..)

theorem glueLaw : ∀ (D : D7) (a b : ℕ), GlueLaw D a b := by
  intro D a b
  refine ⟨glue_span, fun τ ε ε' P => ⟨fun X => ?_, fun Y => ?_⟩⟩
  · rw [glue_update, glue_eq τ P, fockS_ins]
  · rw [glue_update, glue_eq τ P, fockT_ins]

end GlobalTheory.Chain.RealIt.GlueProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergMatrixCoeffRealLineSkewStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) g) (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g) 0 ∧ ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g = -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  first | exact @GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew | exact GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew | (intros; apply GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianActionColumnBase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SrcHalfOne
open GlobalTheory.EmbChart (tensAt atPlace)
open GlobalTheory.AdelicU (splitProj compFin isCMExt_host)
variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := Formalism.L2.Theta.cA_cA z
theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]; rfl

theorem compFin_cA (z : AE D) : compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem piW_cA_idem : piW τ (cA D (idem τ)) = 0 :=
  ((chart_piW τ).2.1 _).2 (GlobalTheory.EmbChart.isSplitIdem_idem τ).2.1

theorem piW_idem : piW τ (idem τ) = 1 := by
  change splitProj τ (compFin _ _ v (idem τ)) = 1
  rw [GlobalTheory.EmbChart.compFin_idem, GlobalTheory.AdelicU.splitProj_splitIdem]

theorem piW_alg (a : Fv D.host.F v) : piW τ (algebraMap (AF D.host.F) (AE D) (atPlace v a)) = a := by
  rw [(chart_piW τ).2.2.1]
  exact GlobalTheory.AdelicU.evalV_singleFin_self v a

theorem piW_cA (z : AE D) : piW τ (cA D z) = splitProj (τ.comp D.sp.cm.sig) (compFin D.host.F D.host.E v z) := by
  change splitProj τ (compFin _ _ v (cA D z)) = _
  rw [compFin_cA, GlobalTheory.AdelicU.splitProj_comp]

def plcC (y : Fv D.host.F v) : AE D := cA D (idem τ) * algebraMap (AF D.host.F) (AE D) (atPlace v y)

def plcW (y : Fv D.host.F v) : AE D := idem τ * algebraMap (AF D.host.F) (AE D) (atPlace v y)

theorem piW_plcC (y) : piW τ (plcC τ y) = 0 := by rw [plcC, map_mul, piW_cA_idem, zero_mul]
theorem piW_cA_plcC (y) : piW τ (cA D (plcC τ y)) = y := by
  rw [plcC, map_mul, cA_cA', cA_alg, map_mul, piW_idem, piW_alg, one_mul]

theorem plcC_add (y y') : plcC τ (y + y') = plcC τ y + plcC τ y' := by
  rw [plcC, plcC, plcC, map_add, map_add, mul_add]

theorem continuous_piW : Continuous (piW τ) := by
  have hev : Continuous (GlobalTheory.AdelicU.evFin D.host.F v) :=
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  have h := GlobalTheory.AutFunCompare.continuous_tensNU (E := D.host.E) (GlobalTheory.AdelicU.evFin D.host.F v).toLinearMap
    (fun a b => map_mul (GlobalTheory.AdelicU.evFin D.host.F v) a b) hev
  exact (GlobalTheory.AdelicU.continuous_splitProj τ).comp h

theorem idem_mul_self : idem τ * idem τ = idem τ := (GlobalTheory.EmbChart.isSplitIdem_idem τ).1

def plcCH : Fv D.host.F v →+ AE D := AddMonoidHom.mk' (plcC τ) (plcC_add τ)

section Frame

variable (V : HSp D) {ι : Type} [Fintype ι] [DecidableEq ι] (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

def rowL (y : Fin V.rank → D.host.E) : ι → Fv D.host.F v := (τ ∘ (star y ᵥ* V.gram)) ᵥ* cols β

def crd (x : Fin V.rank → D.host.E) : ι → Fv D.host.F v := what₂ β *ᵥ (τ ∘ x)

end Frame

section FJ

variable {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) {n : Type} [Fintype n] [DecidableEq n]
  {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * (σ + 1))) (Fin V.rank)}
  {t : ℕ → Fv D.host.F v}

variable {τ}

open GlobalTheory.RootEx (colE rowE)

variable (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t)
include hβ

end FJ

section Jac

variable {V V₀ L : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E)

end Jac
end GlobalTheory.SrcHalfOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChangeStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_isometry_base_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k k' : Type) [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k'] (ψ : k →ₐ[F] k') (x : plusUnits P k) (φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)) (h : IsIsom P k J x.1.1 φ), ∃ (x' : plusUnits P k') (φ' : (k' ⊗[F] Fld P) ≃ₗ[k' ⊗[F] E] (Fin n → k' ⊗[F] E)) (h' : IsIsom P k' J x'.1.1 φ'), x'.1.1 = Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P)) x.1.1 ∧ gam h' = mapH σ J ψ (gam h) ∧ ∀ t, torEmb h' (mapH (star' P) (one₁ P) ψ t) = mapH σ J ψ (torEmb h t) := by
  first | exact @GlobalTheory.TrEll.BaseChg.exists_isom_baseChange | exact GlobalTheory.TrEll.BaseChg.exists_isom_baseChange | (intros; apply GlobalTheory.TrEll.BaseChg.exists_isom_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointMatrixHalfIdempotentSmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleFrameAdjointMatrix_half_idempotent_smul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (c : D.host.E) (x : WO S T), IsHalf (cA D e) x → adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  first | exact @GlobalTheory.AdjScalar.adjA_half_smul | exact GlobalTheory.AdjScalar.adjA_half_smul | (intros; apply GlobalTheory.AdjScalar.adjA_half_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IncASmulMemAdelicCompletionMatrixGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.incA_smul_mem_adelicCompletionMatrixGroup : ∀ (D : D7) (S T : HSp D) (Λ : Lt D.host.E S.rank) (L1 L2 : Lt D.host.E T.rank) (c : D.host.E), (∀ v ∈ L1, c • v ∈ L2) → ∀ u ∈ hatA S T (tens Λ L1), incA D c • u ∈ hatA S T (tens Λ L2) := by
  first | exact @GlobalTheory.HatScalar.incA_smul_mem_hatA | exact GlobalTheory.HatScalar.incA_smul_mem_hatA | (intros; apply GlobalTheory.HatScalar.incA_smul_mem_hatA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedKFiniteRestriction
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.DualInd

theorem dualFn_values : ∀ (n : ℕ) (ε : Fin n → Bool) (I : Datum ε) (φ : UJ ε → I.V), φ ∈ I.fns → IsKFinFun φ →
    (∃ f' ∈ I.dualFns, IsKFinFun f' ∧ ∀ k ∈ KG ε, f' k = φ k) ∧ IsKFinIn I.M I.σ (φ 1) ∧
      (φ ≠ 0 → ∃ k ∈ KG ε, φ k ≠ 0) := by
  intro n ε I φ hφ hKφ
  obtain ⟨hcont, hlaw⟩ := mem_indFun_top.1 hφ
  obtain ⟨h, hc, h1, hhK, hh⟩ := exists_height I.flag I.pos

  set S : Set (UJ ε → I.V) := {ψ | ∃ k ∈ KG ε, ψ = fun g => φ (g * k)} with hS
  have hSfns : Submodule.span ℂ S ≤ I.fns := Submodule.span_le.2 fun ψ ⟨k, _, e⟩ => e ▸ indFun_mul_right hφ trivial
  haveI : FiniteDimensional ℂ (Submodule.span ℂ S) := hKφ
  refine ⟨?_, ?_, ?_⟩
  · set c : Fin I.a → ℂ := -star I.s - I.s with hc'
    have hec : Continuous fun g => Complex.exp (pairing I.j c (h g)) := by unfold pairing; fun_prop
    let L : (UJ ε → I.V) →ₗ[ℂ] (UJ ε → I.V) :=
      { toFun := fun ψ g => Complex.exp (pairing I.j c (h g)) • ψ g
        map_add' := fun ψ ψ' => funext fun g => smul_add _ _ _
        map_smul' := fun r ψ => funext fun g => smul_comm _ r _ }
    refine ⟨L φ, mem_indFun_top.2 ⟨hec.smul hcont, fun u hu m hm x t ht g => ?_⟩, ?_, fun k hk => ?_⟩
    · show Complex.exp _ • φ _ = _ • I.σ (uMat m) (Complex.exp _ • φ g)
      rw [hh u hu m hm x t ht g, hlaw u hu m hm x t ht g, map_smul, smul_smul, smul_smul, ← Complex.exp_add,
        ← Complex.exp_add]
      congr 2
      simp only [pairing, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc', Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
      push_cast
      ring
    · have hle : Submodule.span ℂ {ψ : UJ ε → I.V | ∃ k ∈ KG ε, ψ = fun g => L φ (g * k)} ≤
          (Submodule.span ℂ S).map L := by
        rw [Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro ψ ⟨k, hk, rfl⟩
        refine ⟨fun g => φ (g * k), ⟨k, hk, rfl⟩, funext fun g => ?_⟩
        show Complex.exp _ • φ _ = Complex.exp _ • φ _
        rw [hhK g k hk]
      exact Submodule.finiteDimensional_of_le hle
    · show Complex.exp _ • φ k = φ k
      have : h k = 0 := by simpa [h1] using hhK 1 k hk
      simp [this, pairing]
  · have h1N : (1 : UJ ε) ∈ flagN ε I.W := ⟨fun i y _ => by simp [show uMat (1 : UJ ε) = 1 from rfl], fun y _ => by simp [show uMat (1 : UJ ε) = 1 from rfl]⟩
    let ev : (UJ ε → I.V) →ₗ[ℂ] I.V := LinearMap.proj (1 : UJ ε)
    refine ⟨(Submodule.span ℂ S).map ev, inferInstance, ⟨φ, Submodule.subset_span ⟨1, (KG ε).one_mem, by simp⟩, rfl⟩,
      ?_⟩
    rintro k ⟨hkK, hkM⟩ _ ⟨ψ, hψ, rfl⟩

    let T : (UJ ε → I.V) →ₗ[ℂ] (UJ ε → I.V) :=
      { toFun := fun ψ g => ψ (g * k)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hT : (Submodule.span ℂ S).map T ≤ Submodule.span ℂ S := by
      rw [Submodule.map_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨k', hk', rfl⟩, rfl⟩
      exact ⟨k * k', (KG ε).mul_mem hkK hk', funext fun g => by simp [T, mul_assoc]⟩
    refine ⟨T ψ, hT ⟨ψ, hψ, rfl⟩, ?_⟩
    have := (mem_indFun_top.1 (hSfns hψ)).2 1 h1N k hkM 0 1 isSplit_one 1
    simp only [one_mul, mul_one] at this
    show ψ (1 * k) = I.σ (uMat k) (ψ 1)
    rw [one_mul, this]
    simp [pairing]
  · intro hne
    by_contra hall
    push_neg at hall
    refine hne (funext fun g => ?_)
    obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact I.flag g
    obtain ⟨u, hu, m, hm, x, t, ht, e⟩ := exists_langlands_decomp I.flag I.pos hp
    have hk' : k ∈ KG ε := ((KG_eq ε).symm ▸ hk :)
    have hg : g = u * m * t * k := by rw [← e, inv_mul_cancel_right]
    rw [hg, hlaw u hu m hm x t ht k, hall k hk']
    simp

end GlobalTheory.DualInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionInStagesIntertwining
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageFun_law : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (τ : Matrix (Fin n) (Fin n) ℂ → (U →L[ℂ] U)) (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (s : Fin a → ℂ) (s' : Fin b → ℂ) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V), (∀ m ∈ leviOne ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W') → (∀ x t, IsSplit ε W x t → IsSplit ε W' (x ∘ β) t ∧ ∀ m ∈ leviOne ε W, m * t = t * m) → (∀ v, τ 1 v = v) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (s' + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) → (∀ y ∈ leviOne ε W, ∀ f f' : Fsp, (∀ g, f'.1 g = f.1 (g * y)) → σ (uMat y) (ι f) = ι f') → ∀ {F : UJ ε → U}, F ∈ indFun ⊤ (fun _ => 1) W' τ s' → (∀ g, restr (leviOne ε W) F g ∈ Fsp) → ∀ u ∈ flagN ε W, ∀ m ∈ leviOne ε W, ∀ x t, IsSplit ε W x t → ∀ g, stageFun (leviOne ε W) Fsp ι F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • σ (uMat m) (stageFun (leviOne ε W) Fsp ι F g) := by
  intro n a b ε j W W' β U V _ _ _ _ τ σ s s' Fsp ι hconj hsplit hτ hpair htrans F hF hmem u hu m hm x t ht g
  set M := leviOne ε W with hM
  have uMat_one : uMat (1 : UJ ε) = 1 := rfl
  have hlaw := (mem_indFun_top.1 hF).2
  have h1N : (1 : UJ ε) ∈ flagN ε W' := ⟨fun i y _ => by simp [uMat_one], fun y _ => by simp [uMat_one]⟩

  have hN : ∀ u' ∈ flagN ε W', ∀ h, F (u' * h) = F h := fun u' hu' h => by
    have := hlaw u' hu' 1 (leviOne ε W').one_mem 0 1 isSplit_one h
    simpa [uMat_one, hτ, pairing] using this
  obtain ⟨ht', hcomm⟩ := hsplit x t ht
  have hA : ∀ h, F (t * h) = Complex.exp (pairing j (s + rho n j) x) • F h := fun h => by
    have := hlaw 1 h1N 1 (leviOne ε W').one_mem (x ∘ β) t ht' h
    simpa [uMat_one, hτ, hpair] using this
  have hr : restr M F (u * m * t * g) = Complex.exp (pairing j (s + rho n j) x) • restr M F (m * g) := by
    funext m'
    by_cases hm' : m' ∈ M
    · rw [Pi.smul_apply, restr_of_mem _ _ hm', restr_of_mem _ _ hm']
      have e1 : m' * (u * m * t * g) = (m' * u * m'⁻¹) * (t * ((m' * m) * g)) := by
        rw [← mul_assoc t, ← hcomm _ (M.mul_mem hm' hm)]; group
      rw [e1, hN _ (hconj m' hm' u hu), hA, mul_assoc]
    · rw [Pi.smul_apply, restr_of_not_mem _ _ hm', restr_of_not_mem _ _ hm', smul_zero]
  have hr2 : ∀ h, restr M F (m * g) h = restr M F g (h * m) := fun h => by
    by_cases hh : h ∈ M
    · rw [restr_of_mem _ _ hh, restr_of_mem _ _ (M.mul_mem hh hm), mul_assoc]
    · rw [restr_of_not_mem _ _ hh, restr_of_not_mem _ _ (fun e => hh (by simpa using M.mul_mem e (M.inv_mem hm)))]
  rw [stageFun_of_mem ι (hmem g), stageFun_of_mem ι (hmem _)]
  have e2 : (⟨restr M F (u * m * t * g), hmem _⟩ : Fsp) = Complex.exp (pairing j (s + rho n j) x) • ⟨restr M F (m * g), hmem _⟩ :=
    Subtype.ext hr
  rw [e2, map_smul, htrans m hm ⟨_, hmem g⟩ ⟨_, hmem (m * g)⟩ hr2]

end GlobalTheory.RealInd.Stages
end

