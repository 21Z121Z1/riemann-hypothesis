import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3049
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3077
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationsSamePointDifferByIsometryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' D'' : PLat O bar) (t : Λ → D'.La) (t' : Λ → D''.La) P P' (y : Sp ℂ ⟶ F.X) e e', 0 < N → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D'' t' P' y e' → ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), IsMarkedIsom N D' D'' t t' w ∧ (∀ x, P' (w x) = h (P x)) ∧ ∀ z, e' (h z) = e z := by
  first | exact @GlobalTheory.PELU.unifAt_cmp | exact GlobalTheory.PELU.unifAt_cmp | (intros; apply GlobalTheory.PELU.unifAt_cmp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtFlagCellGradedLinePotentialStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffAt_flagCellGradedLinePotential : ∀ (ι : Type) (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m), (G (bsL ε w) x.1).PosDef → MContDiffAt 2 (fun v => G v x.1) (bsL ε w) → ContDiffAt ℝ 2 (cellPot ε G x) w ∧ 0 < grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 := by
  first | exact @GlobalTheory.CellPotSmooth.cellPot_contDiffAt | exact GlobalTheory.CellPotSmooth.cellPot_contDiffAt | (intros; apply GlobalTheory.CellPotSmooth.cellPot_contDiffAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnMixedChernFormDensityInChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_mixedChernFormDensityInChart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c : AlgChart p σ D), ContinuousOn (dens L c) c.e.source := by
  first | exact @GlobalTheory.Mix.continuousOn_dens | exact GlobalTheory.Mix.continuousOn_dens | (intros; apply GlobalTheory.Mix.continuousOn_dens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementExistsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_refinement_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ρ' : M.X ⟶ X) (V₀ : Cover Y) (q : ℕ), q ≠ 0 → ∃ (V : Cover Y) (a : V.X ⟶ V₀.X) (g : V.G ⟶ V₀.G) (ρ'' : V.X ⟶ X), a ≫ V₀.p = V.p ∧ V.j ≫ a = g ≫ V₀.j ∧ g ≫ V₀.π = V.π ∧ g (genericPoint V.G) = genericPoint V₀.G ∧ V.j ≫ ρ'' = V.π ≫ M.j ≫ ρ' ∧ CharZero V.X.functionField ∧ (∃ ζ : V.X.functionField, IsPrimitiveRoot ζ q) ∧ SplitK t (K := V.X.functionField) (V.X.fromSpecStalk (genericPoint V.X) ≫ ρ'') q := by
  first | exact @GlobalTheory.HtGen.SplitCover.exists_cover | exact GlobalTheory.HtGen.SplitCover.exists_cover | (intros; apply GlobalTheory.HtGen.SplitCover.exists_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (KK κ t).fnMap.PullbackBijectiveDegreesOneTwo ∧ ((KK κ t).res (pE κ t i)).fnMap.PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs | exact GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs | (intros; apply GlobalTheory.PDForm.crystalline_forget_forms_bijective_site_and_pairs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureMatrixPowProductEntrySmoothDbarClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.PowCurv

def Good (n : ℕ) (v : V n) (f : V n → Ev n) : Prop :=
  (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((f x : Alt n)) S) v) ∧ dbarAt (fun x => (f x : Alt n)) v = 0

variable {n : ℕ} {v : V n}

theorem diff_of_smooth {α : V n → Alt n} (h : ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) (S) :
    DifferentiableAt ℝ (fun x => (bas n).repr (α x) S) v := by
  have h1 := h S
  exact h1.differentiableAt (by simp)

theorem good_const (c : Ev n) : Good n v (fun _ => c) := by
  refine ⟨fun S => (GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).1 (c : Alt n) S, ?_⟩
  exact (GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.2.2.1 (c : Alt n)

theorem good_sum {J : Type} (s : Finset J) (f : J → V n → Ev n) (h : ∀ j ∈ s, Good n v (f j)) :
    Good n v (fun x => ∑ j ∈ s, f j x) := by
  have hfun : ∀ x, ((∑ j ∈ s, f j x : Ev n) : Alt n) = ∑ j ∈ s, (f j x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).2.1 J s (fun j x => (f j x : Alt n)) (fun j hj => (h j hj).1), ?_⟩
  rw [(GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.1 J s (fun j x => (f j x : Alt n))
    (fun j hj S => diff_of_smooth (α := fun x => (f j x : Alt n)) (h j hj).1 S)]
  exact Finset.sum_eq_zero fun j hj => (h j hj).2

theorem good_mul (f g : V n → Ev n) (hf : Good n v f) (hg : Good n v g) : Good n v (fun x => f x * g x) := by
  have hfun : ∀ x, ((f x * g x : Ev n) : Alt n) = (f x : Alt n) * (g x : Alt n) := by
    intro x
    push_cast
    rfl
  unfold Good
  beta_reduce
  simp only [hfun]
  refine ⟨(GlobalTheory.T.smooth_coefficient_forms_closed_under_operations n v).2.2.2 (fun x => (f x : Alt n)) (fun x => (g x : Alt n)) hf.1 hg.1, ?_⟩
  rw [(GlobalTheory.T.dbar_operator_local_calculus_complex_forms n v).2.2.2.2 f (fun x => (g x : Alt n))
    (diff_of_smooth (α := fun x => (f x : Alt n)) hf.1) (diff_of_smooth (α := fun x => (g x : Alt n)) hg.1)]
  rw [hf.2, hg.2]
  simp

variable {r : Type} [Fintype r] [DecidableEq r]

theorem goodM_mul (M N : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j))
    (hN : ∀ i j, Good n v (fun x => N x i j)) (i j : r) : Good n v (fun x => (M x * N x) i j) := by
  have hfun : (fun x => (M x * N x) i j) = fun x => ∑ k ∈ Finset.univ, M x i k * N x k j := by
    funext x
    rw [Matrix.mul_apply]
  rw [hfun]
  exact good_sum Finset.univ (fun k x => M x i k * N x k j) fun k _ => good_mul _ _ (hM i k) (hN k j)

theorem goodM_pow (M : V n → Matrix r r (Ev n)) (hM : ∀ i j, Good n v (fun x => M x i j)) (k : ℕ) (i j : r) :
    Good n v (fun x => (M x ^ k) i j) := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero]
    exact good_const _
  | succ k ih =>
    simp only [pow_succ]
    exact goodM_mul (fun x => M x ^ k) M (fun a b => ih a b) hM i j

theorem goodM_curv (G : V n → Matrix r r ℂ) (hG : MContDiffAt ∞ G v) (hd : IsUnit (G v).det) (i j : r) :
    Good n v (fun x => curvEv G x i j) := ⟨((GlobalTheory.T.curvatureMatrixEvenForms_entries_smooth_coefficients n r G v hG hd) i j).2, GlobalTheory.T.dbar_curvatureMatrixEvenForms_eq_zero n r G v hG hd i j⟩

end GlobalTheory.PowCurv

open GlobalTheory.PowCurv in

theorem GlobalTheory.ChernCalc.powCurv_entry_smooth_dbar : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → ∀ (k l : ℕ) (i j : r), (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) S) v) ∧ dbarAt (fun x => ((curvEv G x ^ k * curvEv G' x ^ l) i j : Alt n)) v = 0 := by
  intro n r _ _ G G' v hG hd hG' hd' k l i j
  exact goodM_mul (fun x => curvEv G x ^ k) (fun x => curvEv G' x ^ l)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G hG hd c d) k a b)
    (fun a b => goodM_pow _ (fun c d => goodM_curv G' hG' hd' c d) l a b) i j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerPullbackHolomorphicStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvature_power_pullback_holomorphic : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → (∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') = pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n)) ∧ ∀ k, (powAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (powAt G (φ w) k) ∧ (chernAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (chernAt G (φ w) k) := by
  first | exact @GlobalTheory.ChernCalc.curv_pow_chern_comp_holo | exact GlobalTheory.ChernCalc.curv_pow_chern_comp_holo | (intros; apply GlobalTheory.ChernCalc.curv_pow_chern_comp_holo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticHermitianSkew
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.LiftPair
open scoped Matrix TensorProduct NNReal

namespace GlobalTheory.ThK.PairConv

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_herm_of_skew (hCM : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (hd : J.det ≠ 0) : ∃ c₀ : E, c₀ ≠ 0 ∧ IsHermND σ (c₀ • J.map σ) := by
  obtain ⟨x, hx⟩ := GlobalTheory.SkewToHerm.exists_sigma_ne σ hCM
  have hss := GlobalTheory.SiegelSet.sigma_sigma hCM
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_sub, hss]
    rw [hJ j i]
    ring
  · have hdet : (J.map σ).det = σ J.det := by rw [AlgHom.map_det]; rfl
    rw [Matrix.det_smul, hdet]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx))) ((map_ne_zero_iff σ σ.toRingHom.injective).2 hd)

theorem exists_rat_ht_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) :
    ∃ γ ∈ ratU σ J, (ht (γ * h) : ℝ) ≤ 2 * qht h := by
  have h1 : (1 : ℝ≥0) ≤ qht h := le_ciInf fun γ => one_le_heightGL F _
  have h2 : qht h < 2 * qht h := by
    rw [two_mul]; exact lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one h1)
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt h2
  exact ⟨γ.1, γ.2, by exact_mod_cast hγ.le⟩

theorem thetaSum_moderateGrowth (hcm : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {n m : ℕ}
    {JX : Matrix (Fin n) (Fin n) E} {JY : Matrix (Fin m) (Fin m) E}
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m)) {χX χY : Chr F E}
    {om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ)}
    (hW : IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om)
    {Φ : (Fin n × Fin m → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin m)) :
    ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖thetaSum F (om (g, h) Φ)‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  obtain ⟨v, -, ⟨τ⟩⟩ := GlobalTheory.Orb.exists_split_place_notMem hcm ∅
  let B : Base F E := ⟨ψ, fun w => Classical.choice inferInstance, 0, 0, ∅, fun v => absurd v.2 (Finset.notMem_empty _), v, τ⟩
  let X : Spc F E n := ⟨JX, ⊥, 0, 1⟩
  let Y : Spc F E m := ⟨JY, ⊥, 0, 1⟩
  exact GlobalTheory.ThetaFree.theta_moderateGrowth F E σ B n m X Y ⟨co, fun _ => 0, 0, ∅⟩ χX χY om ⟨hψ, hW⟩ Φ hΦ

end

theorem integrableOn_mul_conj_theta : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), GlobalTheory.ThK.KP → ∀ (hcm : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n m : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin m) (Fin m) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → ∀ (hY : ∀ i j, σ (JY j i) = -JY i j) (hYd : JY.det ≠ 0) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JY)) (Fin n × Fin m)), (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F, co.e (incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) → ∀ χX χY : Chr F E, IsHecke F E χX → IsHecke F E χY → ∀ om : UA σ JX × UA σ JY →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JY) co χX χY om → ∀ f : UA σ JY → ℂ, Continuous f → (∀ γ ∈ ratU σ JY, ∀ h, f (γ * h) = f h) → (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (g : UA σ JX) (μ : Measure (UA σ JY)) (𝓕 : Set (UA σ JY)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ JY) 𝓕 μ → IntegrableOn (fun h => f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))) 𝓕 μ := by
  intro F E _ _ _ _ _ σ hK hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hW f hfc _ hdec Φ hΦ g μ 𝓕 hμ h𝓕
  have hS := hW.isUSplitting
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c₀, hc₀, hJ⟩ := exists_herm_of_skew hcm hY hYd
  have heq := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := JY) hσ hc₀
  haveI : BorelSpace (UA σ JY) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2
    (GlobalTheory.ThKContSmall.measure_fundamental_domain_lt_top hK.siegelSetUnitary hcm hJ _ heq μ hμ 𝓕 h𝓕).ne
  have hcont : Continuous fun h : UA σ JY => thetaSum F (om (g, h) Φ) := by
    obtain ⟨l, hl, hlt⟩ := GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin m)
    have h1 : Continuous fun x : UA σ JX × UA σ JY => thetaSum F (om x Φ) :=
      (hS.cont l hl Φ hΦ).congr fun x => hlt _ (hS.pres _ _ hΦ)
    exact h1.comp (continuous_const.prodMk continuous_id)
  have hinv : ∀ γ ∈ ratU σ JY, ∀ h, thetaSum F (om (g, γ * h) Φ) = thetaSum F (om (g, h) Φ) := by
    intro γ hγ h
    have e : om (g, γ * h) Φ = om (1, γ) (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hW 1 (one_mem _) γ hγ _
      (hS.pres _ _ hΦ)
  obtain ⟨C, k, hC⟩ := thetaSum_moderateGrowth hcm hψ co hW hΦ
  obtain ⟨D, hD⟩ := hdec k
  refine Integrable.of_bound (hfc.mul (Complex.continuous_conj.comp hcont)).aestronglyMeasurable
    (max C 0 * ((ht g : ℝ) * 2) ^ k * D) (.of_forall fun h => ?_)
  obtain ⟨γ, hγ, hγh⟩ := exists_rat_ht_le h
  have hg0 : (0 : ℝ) ≤ ht g := NNReal.coe_nonneg _
  have b : ‖thetaSum F (om (g, h) Φ)‖ ≤ max C 0 * ((ht g : ℝ) * (2 * qht h)) ^ k := by
    rw [← hinv γ hγ h]
    refine (hC g _).trans ?_
    have h0 : (0 : ℝ) ≤ (ht g : ℝ) * ht (γ * h) := mul_nonneg hg0 (NNReal.coe_nonneg _)
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left hγh hg0) k) (pow_nonneg h0 _)
      (le_max_right _ _)
  rw [norm_mul, Complex.norm_conj]
  calc ‖f h‖ * ‖thetaSum F (om (g, h) Φ)‖ ≤ ‖f h‖ * (max C 0 * ((ht g : ℝ) * (2 * qht h)) ^ k) :=
        mul_le_mul_of_nonneg_left b (norm_nonneg _)
    _ = max C 0 * ((ht g : ℝ) * 2) ^ k * (‖f h‖ * (qht h : ℝ) ^ k) := by
        rw [← mul_assoc (ht g : ℝ), mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hD h) (mul_nonneg (le_max_right _ _) (pow_nonneg (by linarith) _))

end GlobalTheory.ThK.PairConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcLeviFormEqZeroOfComplexLineInvariantStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ddcLeviForm_eq_zero_of_complexLine_invariant : ∀ (n : ℕ) (u : V n → ℝ) (z ξ η : V n), ContDiffAt ℝ 2 u z → (∀ (x : V n) (c : ℂ), u (x + c • ξ) = u x) → ddc u z ξ η = 0 ∧ ddc u z η ξ = 0 := by
  first | exact @GlobalTheory.ddc_eq_zero_of_invariant | exact GlobalTheory.ddc_eq_zero_of_invariant | (intros; apply GlobalTheory.ddc_eq_zero_of_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullbackStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_pairing_pullback : GlobalTheory.CovTop.Hypotheses₂ → ∃ s : ℚ, s ≠ 0 ∧ ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ (L : LB A.left), L.IsLB → ∀ ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A), GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A L ψ → ∀ (n : ℕ) (u : Fin n → (epsR K ⟶ A)) (θ : Matrix (Fin n) (Fin n) K), (∀ a, IsTangent (u a)) → GlobalTheory.CechKS.IsCechKS A A' i L u θ → ∀ (hb : Fin n → GlobalTheory.DeRham.HdR A), (∀ b, GlobalTheory.DeRham.IsLieImage (hb b) (u b)) → ∀ f ∈ GlobalTheory.DeRham.Fil A, ∀ w : epsR K ⟶ A, IsLieComb (fun a => (s : K) * ∑ b, θ a b * ψ f (hb b)) u w → GlobalTheory.DeRham.IsKSValue h f w := by
  first | exact @GlobalTheory.CechKS.exists_const_isKSValue | exact GlobalTheory.CechKS.exists_const_isKSValue | (intros; apply GlobalTheory.CechKS.exists_const_isKSValue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeSumDerivativesEqEisensteinJets
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.HilbFam

theorem iterD_defSum_eq_jet : EisExp → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (s N : ℕ) (g : (I → ℂ) → ℂ) (κ : I → ℕ) (u : List I), 2 ≤ Module.finrank ℚ (FR E) → 1 ≤ s → 0 < N → HasLevel N L → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsDefSum φ (2 * s) Λ g → (∀ i, u.count i = κ i) → iterD u g 0 = (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * jet (2 * s) L (fun j ↦ κ (e.symm j)) τ 1 (starRingEnd ℂ (τ : ℂ) - τ) := by
  intro hE E _ _ _ I _ _ φ e θ τ Λ L n s N g κ u hf hs hN hL hφ hθ hn hLΛ hg hu
  have hI : Nonempty I := by
    obtain ⟨σ⟩ : Nonempty (FR E →+* ℂ) := by
      rw [← Fintype.card_pos_iff, NumberField.Embeddings.card]; omega
    exact ⟨e.symm (NumberField.ComplexEmbedding.IsReal.embedding
      (IsTotallyReal.complexEmbedding_isReal σ))⟩
  set W : (Emb (FR E) → ℂ) → ℂ := fun w ↦ (cK (FR E) (2 * s) : ℂ) *
    gval (2 * s) L (fun j ↦ (τ : ℂ) + w j * (1 * (τ : ℂ) + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + w j * 1) with hW
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : g =ᶠ[nhds 0] fun z ↦ (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) * W (fun j ↦ z (e.symm j)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : I → ℂ) one_pos] with z hz
    have hzp : z ∈ polydisc I := fun i ↦ by
      have := norm_le_pi_norm z i
      rw [Metric.mem_ball, dist_zero_right] at hz
      exact lt_of_le_of_lt this hz
    obtain ⟨G, hG, hgz⟩ := hg z hzp
    have hv := GlobalTheory.T.deformedLattice_value_eq_hilbertEisenstein_value E I φ e θ τ Λ L n (2 * s) z G hI ⟨s, two_mul s⟩ hφ hθ hn hLΛ hG
    have hu' := GlobalTheory.HilbFam.gval_eq_of_isGVal (FR E) (2 * s) L _ _ _ hv
    simp only [hW]
    rw [hu', hgz]
    have : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) = (cK (FR E) (2 * s) : ℂ) := rfl
    rw [this, inv_pow, ← pow_mul, mul_comm (Module.finrank ℚ (FR E)) (2 * s)]
    have h1 : (n : ℂ) ^ (2 * s * Module.finrank ℚ (FR E)) ≠ 0 := pow_ne_zero _ hn0
    rw [mul_left_comm, mul_inv_cancel_left₀ h1]
  rw [GlobalTheory.HilbFam.iterD_eq_of_eventuallyEq I u g _ 0 key, GlobalTheory.HilbFam.iterD_const_mul_reindex I (Emb (FR E)) e u W _ 0]
  congr 1
  have hc : ∀ j, (u.map e).count j = κ (e.symm j) := fun j ↦ by
    rw [← hu (e.symm j)]
    conv_lhs => rw [← e.apply_symm_apply j]
    convert List.count_map_of_injective u e e.injective (e.symm j)
  have := GlobalTheory.T.iterated_derivative_eq_hilbert_eisenstein_jet hE (FR E) hf s N L hs hN hL τ 1 (starRingEnd ℂ (τ : ℂ) - τ) (fun j ↦ κ (e.symm j)) (u.map e) τ.im_pos hc
  exact this

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationThetaSeriesAlgebraicOverFractionFiel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.ThetaSer

theorem hasSum_map_of_sumF {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] {I : Ideal R} {F C : Type} [Field F]
    [Algebra (FractionRing R) F] [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing R) C]
    (hC : GlobalTheory.Ex.CExt R I C) (em : F →ₐ[FractionRing R] C) {Ix : Type} {x : Ix → F} {s : F}
    (h : GlobalTheory.UT.SumF I F x s) : HasSum (fun i => em (x i)) (em s) := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  letI : Module R C := Module.compHom C (algebraMap R (FractionRing R))
  let f : F →ₗ[R] C :=
    { toFun := em
      map_add' := em.map_add
      map_smul' := fun r y => by
        change em ((algebraMap R (FractionRing R) r) • y) = (algebraMap R (FractionRing R) r) • em y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes] }
  refine GlobalTheory.Ex.AdicNormSum.main R I C hC Ix _ _ ?_
  obtain ⟨M, hfg, hs, hx, hn⟩ := h
  refine ⟨M.map f, hfg.map f, Submodule.mem_map_of_mem hs, fun i => Submodule.mem_map_of_mem (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hn n
  refine ⟨S, fun T hT => ?_⟩
  have := Submodule.mem_map_of_mem (f := f) (hS T hT)
  rw [Submodule.map_smul''] at this
  simpa [f, map_sub, map_sum] using this

theorem theta_series_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (Ix : Type) (p : Ix → QkPt D.toPre (Kb R) (m ^ 2)), ∃ v : Ix → Kb R, ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : Ix → QkPt D.toPre C (m ^ 2)) (q : Ix → N.QT (m ^ 2)), (∀ i, QkExt em.toRingHom (p i) (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx m (q i) := by
  intro R _ _ _ hB D m hm hu Ix p
  obtain ⟨⟨hN, -, -, hAC⟩, -⟩ := id hB
  haveI := hN
  have hL : Laws := GlobalTheory.lawsAndExpansions.1.1
  obtain ⟨N₀, ν₀, -⟩ := GlobalTheory.ValuesExist.exists_integral_values hL R D.toPre D.psi_even D.tau_bimult (Kb R) ⊤
    (fun _ => trivial)
  have hq₀ : ∀ i, ∃ q₀ : N₀.QT (m ^ 2), ν₀.QPt (p i) q₀ := fun i =>
    (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult (Kb R) N₀ ν₀).2.2.2.2 (m ^ 2)).1 (p i)).exists
  choose q₀ hq₀ using hq₀
  have hv : ∀ i, ∃ v, GlobalTheory.UT.SumF (maximalIdeal R) (Kb R) (N₀.txT m (q₀ i)) v := fun i => by
    obtain ⟨Jx, _, g, c, hc, hfin⟩ := GlobalTheory.T.thetaSeriesTerms_torsionPoint_finite_adic_combination R hB D N₀ ν₀ m hm hu (p i) (q₀ i) (hq₀ i)
    obtain ⟨s, hs⟩ := GlobalTheory.T.exists_adic_sum_field_of_coeff_tendsto_zero R hAC (Kb R) Jx g N₀.X c hfin
    refine ⟨s, ?_⟩
    rwa [show N₀.txT m (q₀ i) = _ from funext hc]
  choose v hv using hv
  refine ⟨v, fun C _ _ _ _ _ hC em N nu p₁ q hp hq => ?_⟩
  obtain ⟨r, hr⟩ := ν₀.th_gen nu.th
  obtain ⟨N', ν', e, hth, htx⟩ := GlobalTheory.T.thetaSeries_terms_rescale_by_generator_multiple R D.toPre D.psi_even D.tau_bimult C N nu ν₀.th r hr ν₀.th_gen
  obtain ⟨I, hlam, -, hI⟩ := GlobalTheory.GaugeHom.exists_hom R D.toPre (Kb R) C em.toRingHom
    (RingHom.ext fun x => em.commutes x) N₀ N' ν₀ ν' hth
  have hq' : ∀ i, ∃ q' : N'.QT (m ^ 2), ν'.QPt (p₁ i) q' := fun i =>
    (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult C N' ν').2.2.2.2 (m ^ 2)).1 (p₁ i)).exists
  choose q' hq' using hq'
  let a : C := algebraMap (FractionRing R) C (algebraMap R _ r)
  have hterm : ∀ i χ, N.txT m (q i) (e (I.e χ)) = a * em (N₀.txT m (q₀ i) χ) := fun i χ => by
    obtain ⟨h1, h2⟩ := hI (m ^ 2) (p i) (p₁ i) (q₀ i) (q' i) (hp i) (hq₀ i) (hq' i)
    rw [htx m (p₁ i) (q i) (q' i) (hq i) (hq' i), I.txT_eq hm (q₀ i) (q' i) h1 h2 χ, hlam, Units.val_one, _root_.one_mul]
    rfl
  have htx' : ∀ i, N.tx m (q i) = a * em (v i) := fun i => by
    have hs := (hasSum_map_of_sumF hC em (hv i)).mul_left a
    simp only [← hterm] at hs
    unfold GlobalTheory.Ex.NumD.tx
    rw [← (I.e.trans e).toEquiv.tsum_eq]
    exact hs.tsum_eq
  by_cases hr0 : r = 0
  · subst hr0
    have hz : ∀ j, nu.th.f j = 0 := fun j => by rw [hr j]; simp [scal]
    obtain ⟨r', hr'⟩ := nu.th_gen ν₀.th
    have hz₀ : ∀ j, ν₀.th.f j = 0 := fun j => by rw [hr' j, hz j, mul_zero]
    obtain ⟨N'', ν'', e'', -, htx''⟩ := GlobalTheory.T.thetaSeries_terms_rescale_by_generator_multiple R D.toPre D.psi_even D.tau_bimult (Kb R) N₀ ν₀ ν₀.th 0
      (fun j => by rw [hz₀ j, mul_zero]) ν₀.th_gen
    have h0 : ∀ i, em (v i) = 0 := fun i => by
      obtain ⟨q'', hq''⟩ := (((GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult (Kb R) N'' ν'').2.2.2.2
        (m ^ 2)).1 (p i)).exists
      have hs := hasSum_map_of_sumF hC em (hv i)
      have e0 : (fun χ => em (N₀.txT m (q₀ i) χ)) = fun _ => 0 := funext fun χ => by
        rw [← e''.apply_symm_apply χ, htx'' m (p i) (q₀ i) q'' (hq₀ i) hq''] ; simp
      rw [e0] at hs
      exact hs.unique hasSum_zero
    refine ⟨1, fun i => ?_⟩
    rw [h0 i, htx' i, h0 i, mul_zero, mul_zero]
  · have ha : a ≠ 0 := by
      intro h
      apply hr0
      have h' : algebraMap R (FractionRing R) r = 0 := (algebraMap (FractionRing R) C).injective (by rw [map_zero]; exact h)
      exact (IsFractionRing.injective R (FractionRing R)) (by rw [h', map_zero])
    refine ⟨(Units.mk0 a ha)⁻¹, fun i => ?_⟩
    rw [htx' i, Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel_left₀ ha]

end GlobalTheory.Mum.ThetaSer
end
end

