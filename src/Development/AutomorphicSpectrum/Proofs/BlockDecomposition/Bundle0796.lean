import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0790
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacter
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

open GlobalTheory.Mem.Chr.CharModel

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem logFin_eq_zero_of_integral (t : (Af E)ˣ)
    (h1 : (t : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E)
    (h2 : ((t⁻¹ : (Af E)ˣ) : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : logFin E t = 0 := by
  have : GlobalTheory.Idele.idealOf t = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]
    intro v
    have e := congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)
    rw [map_mul, map_one] at e
    have a1 : Valued.v ((t : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h1 v
    have a2 : Valued.v (((t⁻¹ : (Af E)ˣ) : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h2 v
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  simp [logFin, this]

theorem det_mem_of_entries {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ a b, M a b ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem logFin_det_of_mem {N : ℕ} {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logFin E (GeneralLinearGroup.det c) = 0 := by
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E N).1 hc
  refine logFin_eq_zero_of_integral _ (det_mem_of_entries _ _ h1) ?_
  rw [← map_inv]
  exact det_mem_of_entries _ _ h2

theorem logNorm_finId (u : (Af E)ˣ) : logNorm E (finId E u) = - logFin E u := by
  have h1 : finPart E (finId E u) = u := Units.ext (by
    change (1 : Af E) - 1 + u = u
    simp)
  have h2 : infPart E (finId E u) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, h2, logInf_one, zero_sub]

theorem norm_det_unitary_at {N : ℕ} (k : Kinf E N) (v : InfinitePlace E) :
    ‖((GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) v‖ = 1 := by
  have hd : (k : Matrix (Fin N) (Fin N) (Cinf E)).det ∈ unitary (Cinf E) := Matrix.det_of_mem_unitary k.2
  have h : star ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v) * (k : Matrix (Fin N) (Fin N) (Cinf E)).det v = 1 :=
    congrFun (Unitary.star_mul_self_of_mem hd) v
  have h2 := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at h2
  exact (mul_self_eq_one_iff.1 h2).resolve_right (by linarith [norm_nonneg ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v)])

theorem logNorm_det_cf (N : ℕ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logNorm E (GeneralLinearGroup.det (cf N k c)) = 0 := by
  rw [cf, map_mul, logNorm_mul, det_infGL, det_finGL, Model.logNorm_infId, logNorm_finId, logFin_det_of_mem hc,
    Finset.sum_eq_zero fun v _ => by rw [norm_det_unitary_at, Real.log_one, mul_zero]]
  simp

theorem chiDet_absC_cf (N : ℕ) (w : ℂ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    chiDet N (GlobalTheory.CuspRep.Model.absC E w) (cf N k c) = 1 := by
  apply Units.ext
  change Complex.exp (w * (logNorm E (GeneralLinearGroup.det (cf N k c)) : ℂ)) = 1
  rw [logNorm_det_cf N k hc]
  simp

end

theorem absFn_flat : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (w : ℂ),
    FlatFn (absFn (E := E) N w) := by
  intro E _ _ _ N w
  refine ⟨fun x => Units.ne_zero _, fun x k c hc => ?_, ?_⟩
  · simp only [absFn, map_mul, chiDet_absC_cf N w k hc, mul_one]
  · have h : absFn (E := E) N w = (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).1 := funext fun x => by
      rw [mulChi_apply]
      simp [absFn, oneFn]
    rw [h]
    exact (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).2

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_right_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM | exact GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM | (intros; apply GlobalTheory.CompanionTheory.AdelicUnimod.isMulRightInvariant_GA_CM <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslate
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.TorusDeriv

noncomputable def blockL (E : Type) [Field E] (r s : ℕ) : Lie E (r + s) :=
  ∑ i : Fin r, toL (Matrix.single (Fin.castAdd s i) (Fin.castAdd s i) (1 : Cinf E))

theorem blockL_apply (E : Type) [Field E] (r s : ℕ) (i j : Fin (r + s)) (w : InfinitePlace E) :
    blockL E r s i j w = if i = j then (if (i : ℕ) < r then (1 : ℂ) else 0) else 0 := by
  have e : blockL E r s i j w =
      ∑ k : Fin r, ((Matrix.single (Fin.castAdd s k) (Fin.castAdd s k) (1 : Cinf E)) i j) w := by
    simp only [blockL, Finset.sum_apply]
    rfl
  rw [e]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have : Fin.castAdd s (⟨i, hi⟩ : Fin r) = i := Fin.ext rfl
        simp [this]
      · intro b _ hb
        have : Fin.castAdd s b ≠ i := fun h => hb (Fin.ext (show (b : ℕ) = i from congrArg Fin.val h))
        simp [Matrix.single_apply, this]
      · simp
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : Fin.castAdd s k ≠ i := fun h => hi (by rw [← h]; exact k.2)
      simp [Matrix.single_apply, this]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬ (Fin.castAdd s k = i ∧ Fin.castAdd s k = j) := fun h => hij (h.1.symm.trans h.2)
    simp [Matrix.single_apply, this]

theorem hasDerivAt_entries {ι : Type} [Fintype ι] {a : ℕ} (f : ℝ → Fin a → Fin a → ι → ℂ) (X : Fin a → Fin a → ι → ℂ)
    (h : ∀ i j w, HasDerivAt (fun t => f t i j w) (X i j w) 0) : HasDerivAt f X 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => h i j w

theorem hasDerivAt_aInf (E : Type) [Field E] [NumberField E] (r s : ℕ) :
    HasDerivAt (fun t : ℝ => toL (aInf E (r + s) r t).val) (blockL E r s) 0 := by
  refine hasDerivAt_entries _ _ fun i j w => ?_
  rw [blockL_apply]
  have e : (fun t : ℝ => (toL (aInf E (r + s) r t).val) i j w) = fun t : ℝ =>
      if i = j then Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0) else 0 := by
    funext t
    by_cases hij : i = j
    · subst hij
      simp [aInf]
    · simp [aInf, hij]
  rw [e]
  by_cases hij : i = j
  · simp only [if_pos hij]
    by_cases hi : (i : ℕ) < r
    · simp only [if_pos hi]
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).cexp
    · simp only [if_neg hi]
      simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  · simp only [if_neg hij]
    exact hasDerivAt_const _ _

theorem lie_blockL (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) :
    lie E (r + s) (blockL E r s) =
      ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.CapelliTrace.sum_Eop _ _, blockL, map_sum]
  rfl

theorem hasDerivAt_aT_right : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  intro E _ _ _ r s F g t
  have h0 : aInf E (r + s) r 0 = 1 := Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)
  have h1 := hasDerivAt_curve F (g * aT E (r + s) r t) (aInf E (r + s) r) (blockL E r s) h0
    (hasDerivAt_aInf E r s)
  have h2 : HasDerivAt (fun u : ℝ => F.1 ((g * aT E (r + s) r t) * infGL E (r + s) (aInf E (r + s) r (u - t))))
      (lieD (blockL E r s) F.1 (g * aT E (r + s) r t)) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
  rw [← lie_blockL]
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have e : aT E (r + s) r u = aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r (u - t)) := by
    rw [← aT, ← PExpFin.aT_add]
    congr 1
    ring
  simp only []
  rw [e, mul_assoc]

end GlobalTheory.CompanionTheory.Conc.TorusDeriv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterOrthogonalityStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_character_orthogonality : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, b₀.1.det ≠ 0 → ∀ a b : Matrix (Fin ρ) (Fin p) D.host.E → ℂ, Summable (fun η => ‖a η‖) → Summable (fun η => ‖b η‖) → ∫ x in m.𝓕, (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt η) * a η) * conj (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x (GlobalTheory.CompanionTheory.FJE.rt ξ) * b ξ) ∂m.μ = ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, a η * conj (b η) := by
  first | exact @GlobalTheory.CompanionTheory.FJE.parseval | exact GlobalTheory.CompanionTheory.FJE.parseval | (intros; apply GlobalTheory.CompanionTheory.FJE.parseval <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPrimitiveVectorPairingStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_primitive_vector_pairing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => x) → ∃ y : Fin M → R ⊗[F] E, hR R σ J x y = 1 := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreePartner.exists_partner | exact GlobalTheory.CompanionTheory.WeilSiegel.FreePartner.exists_partner | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreePartner.exists_partner <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqL2InnerStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_l2_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ → ∀ x y : Sm E N, x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → ∫ g in F, x.1 g * (starRingEnd ℂ) (y.1 g) ∂μ = ⟪l2Map μ y, l2Map μ x⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner | exact GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSat2InvTConj
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS
open GlobalTheory.LFun.ConjPlace (invT dGL apply_heckeVec_shift Tj_invT Tj_shift_self map_mem_Ov_iff mem_iff_invT satEig_inv_mul satEig_zero)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ThetaSatPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

variable {u w : Pl E}

def pairInv (c : u.adicCompletion E ≃+* w.adicCompletion E) (a b : ℕ) : GLw a u × GLw b u ≃* GLw a w × GLw b w :=
  MulEquiv.prodCongr (invT c a) (invT c b)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def pairConj (c : u.adicCompletion E ≃+* w.adicCompletion E) (k : GLw a u × GLw b u) :
    GLw a u × GLw b u ≃* GLw a w × GLw b w :=
  MulEquiv.trans (MulAut.conj k⁻¹) (pairInv c a b)

theorem embT_cw (a : ℕ) (u : Pl E) (g : GLw a (GlobalTheory.ThetaSatake.cw u)) :
    embT a (GlobalTheory.ThetaSatake.cw u) g =
      embW a u (PhiU a _ * invT (GlobalTheory.ThetaSatake.cloc u) a g * (PhiU a _)⁻¹) := by
  change GlobalTheory.ThetaPull.thetaA E a (finGL E a (locGL E a (GlobalTheory.ThetaSatake.cw u) g)) = finGL E a (locGL E a u _)
  rw [GlobalTheory.ThetaPull.thetaA_finGL, GlobalTheory.ThetaSatake.theta_locGL, GlobalTheory.ThetaSatake.thetaGL_conj]

theorem invT_symm {K K' : Type} [Field K] [Field K'] (c : K ≃+* K') (n : ℕ) (g : GL (Fin n) K') :
    (invT c n).symm g = invT c.symm n g := rfl

end GlobalTheory.CompanionTheory.ThetaSatPair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation
section
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.MuLocal

open Formalism.L2.Host GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUnitAt_of_valuation (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ)
    (h : ValuativeRel.valuation (w.adicCompletion E) (x : w.adicCompletion E) = 1) : IsUnitAt w x := by
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 := GlobalTheory.SmGL.ord_eq_zero_iff.2 h
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at h1
  rw [IsUnitAt, ← WithZero.exp_log h0, h1, WithZero.exp_zero]

theorem loc_eq_unrChar {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt w) :
    χ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (χ.val w) :=
  GlobalTheory.PrinSat.eq_unrChar_of_ord (fun x hx => h x (isUnitAt_of_valuation w x hx)) (GlobalTheory.PrinSat.ord_unif w)

theorem loc_pow (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (k : ℕ) (x : (w.adicCompletion E)ˣ) :
    (χ ^ k).loc w x = χ.loc w x ^ k := by
  induction k with
  | zero => simpa using HChar.loc_one w x
  | succ k ih => rw [pow_succ, HChar.loc_mul, ih, pow_succ]

theorem loc_mul_loc_conj {μ : HChar E} {e : InfinitePlace E → ℤ} (h : GlobalTheory.BCT.IsMu μ e) (w : HeightOneSpectrum (𝓞 E))
    (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ) :
    μ.loc (GlobalTheory.ThetaSatake.cw w) x * μ.loc w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) = 1 := by
  have h1 := GlobalTheory.BCT.MuProps.mu_mul_conj h (Neutral.B1.localIdele E _ x)
  rw [GlobalTheory.PolChar.ideleConj_eq, GlobalTheory.ThetaPull.conjAd_localIdele] at h1
  exact h1

theorem isUnitAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnitAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnitAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

theorem isUnifAt_conj (w : HeightOneSpectrum (𝓞 E)) (x : ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)ˣ)
    (hx : IsUnifAt (GlobalTheory.ThetaSatake.cw w) x) :
    IsUnifAt w (Units.map (conjLoc (IsCMField.complexConj E).toRingEquiv w).toMonoidHom x) :=
  ((conjLoc_spec _ w).2.2 x.val).trans hx

end GlobalTheory.CompanionTheory.MuLocal

open GlobalTheory.CompanionTheory.MuLocal Formalism.L2.Host GlobalTheory.CuspRep in

theorem GlobalTheory.CompanionTheory.MuLocal.muLoc_holds : PositivityTheory.Rg.BcB.F.RS.MuLoc := by
  intro E _ _ _ _ μ e w hμ hun
  refine ⟨loc_eq_unrChar hun, fun k => ⟨fun x hx => ?_, ?_⟩, fun u _ hu => ?_⟩
  · rw [loc_pow, hun x hx, one_pow]
  · rw [HChar.val, HChar.locK, MonoidHom.comp_apply, loc_pow]
    rfl
  · obtain rfl := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hu
    have hc := loc_mul_loc_conj hμ w
    refine ⟨fun x hx => ?_, ?_⟩
    · have h2 := hc x
      rw [hun _ (isUnitAt_conj w x hx), mul_one] at h2
      exact h2
    · have h2 := hc (atFin (GlobalTheory.ThetaSatake.cw w) (unif (GlobalTheory.ThetaSatake.cw w)))
      rw [μ.val_eq hun _ (isUnifAt_conj w _ (unif_spec _))] at h2
      exact eq_inv_of_mul_eq_one_left h2

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LambdaInvolutionNegStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lambda_involution_neg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t : GA E n, t ∈ adCent d → t.val * rm e = rm e * t.val → t.val * rm (sg d e) = rm (sg d e) * t.val → lam (sg d e) t = - lam e t := by
  first | exact @GlobalTheory.CompanionTheory.TorusAdj.lam_sg | exact GlobalTheory.CompanionTheory.TorusAdj.lam_sg | (intros; apply GlobalTheory.CompanionTheory.TorusAdj.lam_sg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecomp
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.LeviCf

theorem entries_of_unip_lev {R : Type} [CommRing R] {r s : ℕ} (S : Set R) (x : BlockIx (r + s) r → R)
    (g : GL (Fin r) R × GL (Fin s) R)
    (h : ∀ a b : Fin (r + s), ((unip x * lev R r s g : GL (Fin (r + s)) R) : Matrix (Fin (r + s)) (Fin (r + s)) R) a b ∈ S)
    (h' : ∀ a b : Fin (r + s),
      (((unip x * lev R r s g)⁻¹ : GL (Fin (r + s)) R) : Matrix (Fin (r + s)) (Fin (r + s)) R) a b ∈ S) :
    ((∀ a b : Fin r, (g.1 : Matrix (Fin r) (Fin r) R) a b ∈ S) ∧
        ∀ a b : Fin r, ((g.1⁻¹ : GL (Fin r) R) : Matrix (Fin r) (Fin r) R) a b ∈ S) ∧
      ((∀ a b : Fin s, (g.2 : Matrix (Fin s) (Fin s) R) a b ∈ S) ∧
        ∀ a b : Fin s, ((g.2⁻¹ : GL (Fin s) R) : Matrix (Fin s) (Fin s) R) a b ∈ S) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (g⁻¹) (-x)
  have hu : (unip x : GL (Fin (r + s)) R)⁻¹ = unip (-x) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have hi : (unip x * lev R r s g : GL (Fin (r + s)) R)⁻¹ = unip v * lev R r s g⁻¹ := by
    rw [_root_.mul_inv_rev, hu, ← map_inv, hv]
  rw [hi] at h'
  refine ⟨⟨fun a b => ?_, fun a b => ?_⟩, fun a b => ?_, fun a b => ?_⟩
  · rw [← unip_lev_cc x g a b]; exact h _ _
  · have := unip_lev_cc v g⁻¹ a b
    rw [Prod.fst_inv] at this
    rw [← this]; exact h' _ _
  · rw [← unip_lev_nn x g a b]; exact h _ _
  · have := unip_lev_nn v g⁻¹ a b
    rw [Prod.snd_inv] at this
    rw [← this]; exact h' _ _

theorem levi_cf_integral {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}
    (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E))
    (hc : c ∈ KO E (r + s)) (h : unip u * lev (Ad E) r s m = cf (r + s) k c) :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m = (cf r k₁ c₁, cf s k₂ c₂) := by
  obtain ⟨k₁, g₁, k₂, g₂, hm⟩ := levi_cf h
  have f1 : GeneralLinearGroup.map (pFin E) m.1 = g₁ := by
    rw [hm, cf, map_mul, pFin_infGL, pFin_finGL, one_mul]
  have f2 : GeneralLinearGroup.map (pFin E) m.2 = g₂ := by
    rw [show m.2 = cf s k₂ g₂ by rw [hm], cf, map_mul, pFin_infGL, pFin_finGL, one_mul]
  have h2 := congrArg (GeneralLinearGroup.map (pFin E)) h
  rw [map_mul, IwaAd.map_unip, IwaAd.map_lev, cf, map_mul, pFin_infGL, pFin_finGL, one_mul, f1, f2] at h2
  obtain ⟨hc1, hc2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E (r + s)).1 hc
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := entries_of_unip_lev (↑(GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : Set (Af E)) _ (g₁, g₂)
    (by rw [h2]; exact hc1) (by rw [h2]; exact hc2)
  exact ⟨k₁, g₁, k₂, g₂, (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E r).2 ⟨a1, a2⟩,
    (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E s).2 ⟨b1, b2⟩, hm⟩

end GlobalTheory.CompanionTheory.LimV.LeviCf

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointBisStatement
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_skew_adjoint_l2' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E N) (x y : Sm E N), Continuous x.1 → Continuous y.1 → Continuous (lie E N X x).1 → Continuous (lie E N X y).1 → x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X x ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X y ∈ squareIntegrableSmoothSubmoduleGL μ → ⟪l2Map μ x, l2Map μ (lie E N X y)⟫_ℂ = -⟪l2Map μ (lie E N X x), l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map | exact GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIff
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree

theorem linearIndependent_gl_mulVec {K : Type} [CommRing K] {M n : ℕ} (g : GL (Fin M) K)
    (X : Fin n → Fin M → K) (hX : LinearIndependent K X) :
    LinearIndependent K (fun a => (g : Matrix (Fin M) (Fin M) K).mulVec (X a)) := by
  have hinj : Function.Injective (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) := by
    intro x y hxy
    have h2 := congrArg (((g⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K).mulVec) hxy
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    exact h2
  exact hX.map' (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) K)) (LinearMap.ker_eq_bot.2 hinj)

theorem actW_linearIndependent_iff : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) (actW R σ J h X) ↔ LinearIndependent (R ⊗[F] E) X := by
  intro F E _ _ _ R _ _ σ M n J h X
  set g := HA.mat R σ J h with hg
  have hact : actW R σ J h X = fun a => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec (X a) := rfl
  refine ⟨fun hY => ?_, fun hX => ?_⟩
  · have h2 := linearIndependent_gl_mulVec g⁻¹ _ hY
    have h3 : (fun a => ((g⁻¹ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec
        (actW R σ J h X a)) = X := by
      funext a
      rw [hact]
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rwa [h3] at h2
  · rw [hact]
    exact linearIndependent_gl_mulVec g X hX

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree
end

