import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0824
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0813
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0822
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0779
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0828
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0825
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.ExpToSat

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CarriesInducedNodeStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carries_induced_node : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ) (U₁ U₁' : Submodule ℂ (Sm E r)) (U₂ U₂' : Submodule ℂ (Sm E s)), FlatFn e₁ → FlatFn e₂ → FinStable U₁ → FinStable U₁' → FinStable U₂ → FinStable U₂' → Carries e₁ U₁ U₁' → Carries e₂ U₂ U₂' → Carries (nodeFn e₁ e₂) (indSpan U₁ U₂) (indSpan U₁' U₂') := by
  first | exact @GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn | exact GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn | (intros; apply GlobalTheory.CompanionTheory.LimV.NodeCarry.carries_nodeFn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterPairingLocalHermitian
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.SplitPair

section gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem evInf_trace [FiniteDimensional F E] (w : InfinitePlace F) (z : AF F ⊗[F] E) :
    evInf F w (Algebra.trace (AF F) (AF F ⊗[F] E) z) =
      Algebra.trace w.Completion (w.Completion ⊗[F] E) (compInf F E w z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | tmul a x =>
    have e : compInf F E w (a ⊗ₜ[F] x) = evInf F w a ⊗ₜ[F] x := rfl
    rw [e, GlobalTheory.OppLinChar.trace_tmul', GlobalTheory.OppLinChar.trace_tmul', map_mul, AlgHom.commutes]

theorem eq_single (v : HeightOneSpectrum (𝓞 F)) (y : AF F)
    (hi : ∀ w, evInf F w y = 0) (hf : ∀ v' ≠ v, evFin F v' y = 0) :
    y = pairA F 0 (singleV F v (evFin F v y)) := by
  classical
  refine Prod.ext (funext fun w => hi w) (GlobalTheory.AdelicU.af_ext fun u => ?_)
  by_cases h : u = v
  · subst h
    change _ = singleV F u _ u
    exact (RestrictedProduct.single_eq_same _ u _).symm
  · change _ = singleV F v _ u
    exact (hf u h).trans (RestrictedProduct.single_eq_of_ne _ _ h).symm

theorem cA_eq_sigR (σ : E →ₐ[F] E) (y : AF F ⊗[F] E) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ y = sigR (AF F) σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => rfl

theorem psi_half_trace {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : HeightOneSpectrum (𝓞 F))
    (τ : E →ₐ[F] Fv F v) (ψ : AddChar (AF F) ℂ) {n : ℕ}
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (b : Matrix (Fin n) (Fin n) E)
    (hx : ∀ i j, sigR (AF F) σ (x j i) = x i j) (hb : ∀ i j, σ (b j i) = b i j)
    (hinf : ∀ w i j, compInf F E w (x i j) = 0) (hfin : ∀ v' ≠ v, ∀ i j, compFin F E v' (x i j) = 0) :
    ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (∑ i, ∑ j, x i j * inclR (AF F) (b j i))) =
      psiV F ψ v (∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i)) := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hcm.2.2.1
  set z : AF F ⊗[F] E := ∑ i, ∑ j, x i j * inclR (AF F) (b j i) with hz
  set a : Fv F v := ∑ i, ∑ j, splitProj τ (compFin F E v (x i j)) * τ (b j i) with ha
  have hzi : ∀ w, compInf F E w z = 0 := fun w => by
    simp only [hz, map_sum, map_mul, hinf, zero_mul, Finset.sum_const_zero]
  have hzf : ∀ v' ≠ v, compFin F E v' z = 0 := fun v' h => by
    simp only [hz, map_sum, map_mul, hfin v' h, zero_mul, Finset.sum_const_zero]
  have hpi : ∀ t : E →ₐ[F] Fv F v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t z =
      ∑ i, ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t (x i j) * t (b j i) := fun t => by
    simp only [hz, map_sum, map_mul, GlobalTheory.OppLinChar.piW_inclR]
  have h1 : splitProj τ (compFin F E v z) = a := hpi τ
  have h2 : splitProj (τ.comp σ) (compFin F E v z) = a := by
    refine (hpi (τ.comp σ)).trans ?_
    rw [ha, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (x i j) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (x j i) := by
      rw [← hx i j, ← cA_eq_sigR]
      exact GlobalTheory.OppLinChar.piW_cA hcm τ (x j i)
    rw [e, AlgHom.comp_apply, hb i j]
    rfl
  set y : AF F := algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E) z with hy
  have hv : evFin F v y = a := by
    rw [hy, map_mul, AlgHom.commutes, GlobalTheory.OppLinChar.evFin_trace, GlobalTheory.OppLinChar.trace_split hcm τ, h1, h2,
      ← two_mul, ← mul_assoc, ← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul]
    norm_num
  have hs := eq_single v y
    (fun w => by rw [hy, map_mul, evInf_trace, hzi, map_zero, mul_zero])
    (fun v' h => by rw [hy, map_mul, GlobalTheory.OppLinChar.evFin_trace, hzf v' h, map_zero, mul_zero])
  rw [hv] at hs
  rw [hs]
  rfl

end gen

theorem pch_rat_split : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (ψ : AddChar (AF D.host.F) ℂ) (x : hermA D n),
    (∀ w i j, compInf D.host.F D.host.E w (x.1 i j) = 0) → (∀ v' ≠ v, ∀ i j, cv D v' (x.1 i j) = 0) →
    ∀ β : HermE D n, pch ψ x.1 (rat β.1) =
      psiV D.host.F ψ v (Matrix.trace (tauC τ x.1 * β.1.map τ)) := by
  intro D n v τ ψ x hinf hfin β
  have hx : ∀ i j, sigR (AF D.host.F) D.sp.cm.sig (x.1 j i) = x.1 i j := fun i j =>
    congrFun (congrFun x.2 i) j
  have hb : ∀ i j, D.sp.cm.sig (β.1 j i) = β.1 i j := fun i j => congrFun (congrFun β.2 i) j
  exact psi_half_trace (isCMExt_host D) v τ ψ x.1 β.1 hx hb hinf hfin

end GlobalTheory.CompanionTheory.Jp.SplitPair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureKernelMemJacquetKernelStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_kernel_mem_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (z : V ⊗[ℂ] W), clT τ W z = 0 → z ∈ twKer (topRep τ W) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.mem_twKer_topRep_of_clT_eq_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocompactnessStatement
section
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompactness : CoCpt := by
  first | exact @GlobalTheory.CompanionTheory.MassCocompact.coCpt | exact GlobalTheory.CompanionTheory.MassCocompact.coCpt | (intros; apply GlobalTheory.CompanionTheory.MassCocompact.coCpt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientHeisenbergEquivarianceStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_heisenberg_equivariance : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (s : ℂ) (f : G D n → ℂ), IsLaw χ s f → ∀ (η : Mx D ρ p) (z : hermA D ρ) (x : Mx D ρ p) (h : G D n), Wz M m ψ b₀ f (M.sh η * (M.nzx z x * h)) = chz ψ b₀ z * GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x η * Wz M m ψ b₀ f (M.sh η * h) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx | exact GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx | (intros; apply GlobalTheory.CompanionTheory.FJE.Wz_sh_nzx <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPull
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
variable {D : D7} {n : ℕ}

theorem npow_inv (x : ℝ≥0) (t : ℂ) : (((((x : ℝ))⁻¹ : ℝ)) : ℂ) ^ (-t) = npow x t := by
  have harg : Complex.arg ((x : ℝ) : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (NNReal.coe_nonneg x)]
    exact Real.pi_pos.ne
  unfold npow
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]

theorem npow_add_of (x : ℝ≥0) (hx : x ≠ 0) (s t : ℂ) : npow x (s + t) = npow x s * npow x t := by
  unfold npow
  exact Complex.cpow_add _ _ (by exact_mod_cast hx)

theorem jtR_hermTo (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n)) (φ : Mx D V.rank n → ℂ)
    (b : hermA D n) :
    PositivityTheory.PfSWUS.Loc.jtR (HeckeCharacterZeroLocus.SiegelWeilU.AF D.host.F) D.sp.cm.sig (HSpace.gram V) ψ (μ.map tupInv)
      (fun X => φ (tupOf X)) (hermTo b) = Jt ψ V μ φ b := by
  obtain ⟨k1, -, -, -, -, -⟩ := lattice_Mx D V.rank n
  haveI : IsTopologicalAddGroup (Mx D V.rank n) := k1
  haveI : BorelSpace (Mx D V.rank n) := ⟨rfl⟩
  haveI : BorelSpace (Fin n → Fin V.rank → AE D) := borel_tup
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  unfold PositivityTheory.PfSWUS.Loc.jtR Jt
  rw [integral_map_of tupInv tupOf tupOf_tupInv tupInv_tupOf tupInv_add continuous_tupInv continuous_tupOf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hg : gramR (AF D.host.F) D.sp.cm.sig V.gram (tupInv y) = GlobalTheory.StdUnn.inner V y y := by
    ext a c
    exact hR_tup V y y a c
  change φ y * ψ (PositivityTheory.PfSWUS.Loc.trPair _ b.1 (gramR (AF D.host.F) D.sp.cm.sig V.gram (tupInv y))) = _
  rw [hg]
  rfl

theorem trace_pull (a : GL (Fin n) (AE D)) (B : Mx D n n) (b : hermA D n) :
    Matrix.trace (HMul.hMul (adj a.1 * B * a.1) (pull a b).1 : Mx D n n) = Matrix.trace (HMul.hMul B b.1 : Mx D n n) := by
  have h1 : adj (a⁻¹).1 * adj a.1 = 1 := by
    rw [← adj_mul]
    have : a.1 * (a⁻¹).1 = 1 := by simp
    rw [this]
    simp [adj]
  have h2 : a.1 * (a⁻¹).1 = 1 := by simp
  show Matrix.trace (adj a.1 * B * a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1)) = Matrix.trace (B * b.1)
  calc Matrix.trace (adj a.1 * B * a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1))
      = Matrix.trace (adj a.1 * (B * ((a.1 * (a⁻¹).1) * b.1 * adj (a⁻¹).1))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((B * ((a.1 * (a⁻¹).1) * b.1 * adj (a⁻¹).1)) * adj a.1) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B * b.1 * (adj (a⁻¹).1 * adj a.1)) := by
        rw [h2]
        simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = Matrix.trace (B * b.1) := by rw [h1, Matrix.mul_one]

end GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND
variable {D : D7} {n : ℕ}

theorem mono_mem (D : D7) (n : ℕ) (V : HSp D) (θ : InfFam D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : Mx D V.rank n → ℂ)
    (hθ : IsInfFam θ) (hl : ∀ τ, l τ ≠ 0) (hs : ∀ τ, IsCartanInv (gramAt D V τ) (s τ)) (hφ : IsMonoFock θ V l s φ) :
    φ ∈ fockA θ V n l s ∧ φ ∈ schwartzA θ V.rank n := by
  refine ⟨?_, GlobalTheory.CompanionTheory.IfrAdd.mem_schwartzA_of_isMonoFock hθ hl hs hφ⟩
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := hφ
  have hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    have h1 := GlobalTheory.CompanionTheory.IfrAdd.mem_SB_of_isPureFin bs (Φf := fun X => g fun i j => X j i) (Φv := gv) hp
    have h2 := GlobalTheory.CompanionTheory.SiegelND.SchGlue.isSB_swap (D := D) h1
    exact ⟨h2.1, h2.2⟩
  exact Submodule.subset_span ⟨_, g, hg, rfl⟩

theorem sect_w (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (H : G D n → ℝ≥0)
    (hω : IsWeilSch ψ χ θ V μ ω) (nb : hermA D n → G D n) (hnb : IsNMap nb) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0)
    (Φ : schwartzA θ V.rank n) (z : ℂ) (b : hermA D n) :
    sect ω H Φ z (w * nb b * 1) = npow (H (w * nb b)) (z - s0 V n) * Jt ψ V μ Φ.1 b := by
  rw [mul_one]
  unfold sect Jt
  congr 1
  rw [map_mul, Module.End.mul_apply, hω.weyl w hw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h0 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) y = 0 := by
    simp [GlobalTheory.StdUnn.inner, adj]
  show (ω (nb b) Φ).1 y * ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V 0 y))) = _
  rw [h0, hω.unip (nb b) b.1 (hnb b)]
  simp [mul_comm]

theorem jt_pull (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank n))
    (𝓕 : Set (Mx D V.rank n)) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕) (φ : Mx D V.rank n → ℂ) (a : GL (Fin n) (AE D))
    (b : hermA D n) :
    Jt ψ V μ φ (pull a b) = npow (absA D (Matrix.GeneralLinearGroup.det a)) (V.rank : ℂ) *
      Jt ψ V μ (fun x : Mx D V.rank n => φ (HMul.hMul x a.1)) b := by
  have hr0 : absA D (Matrix.GeneralLinearGroup.det a) ≠ 0 :=
    ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (absA D)).ne_zero
  have key := GlobalTheory.RightMulJac.integral_mul_right D V.rank n μ 𝓕 hμ a
    (fun x => φ x * ψ (halfTr (Matrix.trace (HMul.hMul (pull a b).1 (GlobalTheory.StdUnn.inner V x x) : Mx D n n))))
  have e : ∀ y : Mx D V.rank n, Matrix.trace (HMul.hMul (pull a b).1 (GlobalTheory.StdUnn.inner V (HMul.hMul y a.1) (HMul.hMul y a.1)) : Mx D n n) =
      Matrix.trace (HMul.hMul b.1 (GlobalTheory.StdUnn.inner V y y) : Mx D n n) := by
    intro y
    have h1 : adj (a⁻¹).1 * adj a.1 = 1 := (astar a).val_inv
    have h2 : a.1 * (a⁻¹).1 = 1 := by simp
    have hin : GlobalTheory.StdUnn.inner V (HMul.hMul y a.1) (HMul.hMul y a.1) = adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1 := by
      unfold GlobalTheory.StdUnn.inner
      rw [adj_mul]
      simp only [Matrix.mul_assoc]
    rw [hin]
    show Matrix.trace ((a⁻¹).1 * b.1 * adj (a⁻¹).1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1)) = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y)
    calc Matrix.trace ((a⁻¹).1 * b.1 * adj (a⁻¹).1 * (adj a.1 * GlobalTheory.StdUnn.inner V y y * a.1))
        = Matrix.trace ((a⁻¹).1 * (b.1 * ((adj (a⁻¹).1 * adj a.1) * GlobalTheory.StdUnn.inner V y y * a.1))) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((b.1 * ((adj (a⁻¹).1 * adj a.1) * GlobalTheory.StdUnn.inner V y y * a.1)) * (a⁻¹).1) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y * (a.1 * (a⁻¹).1)) := by
          rw [h1]
          simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = Matrix.trace (b.1 * GlobalTheory.StdUnn.inner V y y) := by rw [h2, Matrix.mul_one]
  unfold Jt
  simp only [e] at key
  rw [key, ← mul_assoc]
  have : npow (absA D (Matrix.GeneralLinearGroup.det a)) (V.rank : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (-(V.rank : ℂ)) = 1 := by
    unfold npow
    rw [← Complex.cpow_add _ _ (by exact_mod_cast hr0), add_neg_cancel, Complex.cpow_zero]
  rw [this, one_mul]

end GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.ThetaGlue
variable {D : D7} {n : ℕ}

theorem ifrB_eq_meanC (D : D7) (r : ℕ) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure)
    (φ : Mx D V.rank r → ℂ) (μH : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μH.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μH) (β : HermE D r) (hβ : β.1.det ≠ 0) :
    IfrB V ν φ β = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕
      (HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank (HSpace.gram V) (fun X => φ (tupOf X))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig (HSpace.gram V) X = β.1}) := by
  have hrank : ∀ (δ : GL (Fin V.rank) D.host.E) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E),
      (δ.1 * ξ).rank = ξ.rank := fun δ ξ =>
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit)
  have hL := GlobalTheory.CompanionTheory.SplitGram.leftInv_subtypeSum V φ
    (fun x : Matrix (Fin V.rank) (Fin r) D.host.E => x.rank = r ∧ gramQ V x = β.1)
    (fun δ hδ ξ h => ⟨(hrank δ ξ).trans h.1, (GlobalTheory.CompanionTheory.SplitGram.gramQ_mul V hδ ξ).trans h.2⟩)
  have hI := average_eq_meanC V ν μH hν hμ 𝓕 h𝓕 _ hL
  have hS : HeckeCharacterZeroLocus.SiegelWeilU.thetaS D.host.F D.host.E D.sp.cm.sig V.rank V.gram (fun X => φ (tupOf X))
      {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = β.1} =
      fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
        φ (GlobalTheory.SiegelFormula.invPt V h x.1) := by
    funext h
    refine (tsum_congr fun X => ?_).trans ((fibEquiv V β hβ).tsum_eq
      fun x => φ (GlobalTheory.SiegelFormula.invPt V h x.1))
    exact congrArg φ (tupOf_actW V h X.1)
  rw [hS]
  exact hI

def pullE (a : GL (Fin n) (AE D)) : hermA D n ≃+ hermA D n where
  toFun := pull a
  invFun := pull a⁻¹
  left_inv b := by
    apply Subtype.ext
    show (a⁻¹⁻¹).1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj (a⁻¹⁻¹).1 = b.1
    have h1 : adj (a⁻¹).1 * adj a.1 = 1 := (astar a).val_inv
    have h2 : a.1 * (a⁻¹).1 = 1 := by simp
    rw [inv_inv]
    calc a.1 * ((a⁻¹).1 * b.1 * adj (a⁻¹).1) * adj a.1
        = (a.1 * (a⁻¹).1) * b.1 * (adj (a⁻¹).1 * adj a.1) := by simp only [Matrix.mul_assoc]
      _ = b.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  right_inv b := by
    apply Subtype.ext
    show (a⁻¹).1 * ((a⁻¹⁻¹).1 * b.1 * adj (a⁻¹⁻¹).1) * adj (a⁻¹).1 = b.1
    have h1 : adj a.1 * adj (a⁻¹).1 = 1 := (astar a).inv_val
    have h2 : (a⁻¹).1 * a.1 = 1 := by simp
    rw [inv_inv]
    calc (a⁻¹).1 * (a.1 * b.1 * adj a.1) * adj (a⁻¹).1
        = ((a⁻¹).1 * a.1) * b.1 * (adj a.1 * adj (a⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = b.1 := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  map_add' x y := by
    apply Subtype.ext
    show (a⁻¹).1 * (x.1 + y.1) * adj (a⁻¹).1 = (a⁻¹).1 * x.1 * adj (a⁻¹).1 + (a⁻¹).1 * y.1 * adj (a⁻¹).1
    rw [Matrix.mul_add, Matrix.add_mul]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_pull (a : GL (Fin n) (AE D)) : Continuous (pull a) := by
  obtain ⟨j1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const)).subtype_mk _

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_pull (D : D7) (n : ℕ) (lam : Measure (hermA D n)) (hl : lam.IsAddHaarMeasure)
    (a : GL (Fin n) (AE D)) (F : hermA D n → ℂ) (hF : Integrable F lam) : Integrable (fun b => F (pull a b)) lam := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : SecondCountableTopology (hermA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (hermA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  haveI : LocallyCompactSpace (hermA D n) := (GlobalTheory.CompanionTheory.HermVol.isClosed_hermA (D := D) (r := n)).locallyCompactSpace
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : IsTopologicalAddGroup (Matrix (Fin n) (Fin n) (AE D)) := i1
  haveI := hl
  have hc : Continuous (pullE a) := continuous_pull a
  have hc' : Continuous (pullE a).symm := continuous_pull a⁻¹
  let M : hermA D n ≃ₜ hermA D n := { toEquiv := (pullE a).toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  haveI hH : (lam.map (pullE a)).IsAddHaarMeasure := (pullE a).isAddHaarMeasure_map lam hc hc'
  have e := Measure.isAddLeftInvariant_eq_smul (lam.map (pullE a)) lam
  have h1 : Integrable F (lam.map (pullE a)) := by
    rw [e]
    exact hF.smul_measure ENNReal.coe_ne_top
  have hemb : MeasurableEmbedding (pullE a) := M.measurableEmbedding
  exact hemb.integrable_map_iff.1 h1

end GlobalTheory.CompanionTheory.MM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionTranslateJacquetKernelStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_function_translate_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (a : Fin t → k) (z : Z), cosetFn t hc a z - cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.cosetFn_sub_cosetFn_zero_mem_twKer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTermsUniformlySummable
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf

theorem law_facts : ∀ {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {s : ℂ} {f : G D n → ℂ}, IsHeckeChar D χ → Continuous f → IsLaw χ s f → (n : ℝ) / 2 < s.re →
    LeftInv (P D n ⊓ GF D n) f ∧
    (∀ q ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat q) = a.1 → Matrix.GeneralLinearGroup.det a = 1 → ∀ g, f (q * g) = f g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧ ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) f g q‖ ≤ u q := by
  intro D n χ s f hχ hc hl hs
  haveI := t2Space_adeleRing' (F := D.host.F)
  refine ⟨fun γ hγ g => ?_, fun q hq a ha h1 g => ?_, fun C hC => ?_⟩
  · obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨a, ha⟩ := exists_blkA hp
    obtain ⟨u, hu⟩ := det_rat hr a ha
    have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hu]; exact absE_inclR u
    have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hu]; exact hχ.2 u
    rw [hl γ hp a ha g, h1, h2]
    simp [npow]
  · rw [hl q hq a ha g, h1]
    simp [npow]
  · have hlaw : IndLaw (GlobalTheory.StdUnn.PolesModel.modP (D := D) (n := n))
        (χ.comp GlobalTheory.StdUnn.PolesModel.detP) (s + (n : ℂ) / 2) f := fun p g =>
      hl p p.2 (GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n) p) rfl g
    have h1 : Continuous (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n)) :=
      PolesModel.isIwasawa.continuous_iwAbs GlobalTheory.StdUnn.Model.isClosed_P PolesModel.continuous_modP GlobalTheory.StdUnn.Model.isCompact_K
    have h2 : Continuous fun g => Real.log (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n) g) :=
      (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
    have hcf : Continuous fun x : ℂ × G D n => flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s x.1 x.2 := by
      simp only [flatSec, npow_eq_exp (iwAbs_pos _ _ _)]
      exact (hc.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
        (continuous_fst.sub continuous_const)).cexp)
    obtain ⟨u, hu, hb⟩ := exists_majorant (Φ := fun z => flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s z)
      (χ := χ.comp PolesModel.detP) (ρ := (n : ℝ) / 2) (σ := (n : ℝ) / 2) PolesModel.isIwasawa GlobalTheory.StdUnn.Model.isCompact_K
      hcf.continuousOn
      (fun z _ => by
        have := (PolesModel.isIwasawa (D := D) (n := n)).indLaw_flatSec hlaw z
        push_cast
        exact this) PolesModel.summable_spherical (S := {s}) isCompact_singleton (Set.singleton_subset_iff.2 hs) hC
    have e : flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s s = f := funext fun x => by
      simp [flatSec, npow_eq_exp (iwAbs_pos _ _ _)]
    refine ⟨u, hu, fun q g hg => ?_⟩
    have := hb q s rfl g hg
    rwa [e] at this

end GlobalTheory.CompanionTheory.ZUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentToSaturationStatement
section
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_to_saturation : PositivityTheory.Rg.BcB.F.Tail.PExp.ExpToSat := by
  first | exact @GlobalTheory.CompanionTheory.ExpProd.expToSat | exact GlobalTheory.CompanionTheory.ExpProd.expToSat | (intros; apply GlobalTheory.CompanionTheory.ExpProd.expToSat <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end

