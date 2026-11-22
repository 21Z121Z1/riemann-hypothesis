import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHolomorphyInParameter
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0594
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAdmissibleLinearFunctional
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityBoundUnramified
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0642
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0681
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0685
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0691
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIntegrandIntegrable
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFAbs

open Ad3 Ad3.LFS GlobalTheory.CompanionTheory.LFHolP

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_one_ne_zero (x : Fˣ) : mp x 1 ≠ 0 := by
  have h : ((modulus (x : F) : ℝ) : ℂ) ≠ 0 := by
    have := GroundTheory.LocalField.modulus_ne_zero x.ne_zero
    exact_mod_cast this
  simpa [mp] using h

theorem continuous_integrand {ψ : AddChar F Circle} {W' : GL (Fin 2) F → ℂ}
    {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hU : ∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, W' (g * u) = W' g) (hΦ : Φ ∈ SB F) :
    Continuous fun h : GL (Fin 2) F =>
      W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h 1 := by
  obtain ⟨U, hU⟩ := hU
  have hW : Continuous W' :=
    (GlobalTheory.CompanionTheory.RankinSelbergMellinContinuation.isLocallyConstant_of_invariant W' U.toSubgroup U.isOpen hU).continuous
  exact ((hW.comp continuous_inv).mul (continuous_mp_det _)).mul (cont_inn ψ Φ hΦ)

theorem integrable_one {ψ : AddChar F Circle} {ν : Fˣ →* ℂˣ} {W' : GL (Fin 2) F → ℂ}
    {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} (hyp : Hyp ψ ν W' Φ) :
    Integrable (fun h : GL (Fin 2) F =>
      W' h⁻¹ * mp (GeneralLinearGroup.det h) (3 / 2) * inn ψ Φ h 1) (hG ψ) := by
  obtain ⟨hψ, hν, ⟨V', H, hW'⟩, hΦ⟩ := hyp
  obtain ⟨C, R, hCR⟩ := inn_bound hψ hΦ
  obtain ⟨C', hI⟩ := GlobalTheory.CompanionTheory.LFGInt2.gInt2 F ψ hψ ν hν V' H W' hW' R
  have hI1 := (hI 1 1).1
  have e2 : dg2 (1 : Fˣ) 1 = (1 : GL (Fin 2) F) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg2]
  have hC : 0 ≤ C :=
    le_trans (mul_nonneg (norm_nonneg _) (dk_pos (1 : GL (Fin 2) F)).le) (hCR 1).1
  refine (hI1.const_mul C).mono' (continuous_integrand (H.smooth W' hW') hΦ).aestronglyMeasurable
    (Eventually.of_forall fun h => ?_)
  have hd := dk_pos h
  by_cases hz : inn ψ Φ h 1 = 0
  · simp only [hz, mul_zero, norm_zero]
    exact mul_nonneg hC (Set.indicator_nonneg (fun k _ => by positivity) _)
  · have hm := (hCR h).2 hz
    rw [Set.indicator_of_mem hm, e2, one_mul, norm_mul, norm_mul, norm_mp_det]
    have h32 : dk h ^ (3 / 2 : ℂ).re = dk h ^ (1 / 2 : ℝ) * dk h := by
      have : (3 / 2 : ℂ).re = 1 / 2 + 1 := by norm_num
      rw [this, Real.rpow_add hd, Real.rpow_one]
    rw [h32]
    have hw : 0 ≤ ‖W' h⁻¹‖ * dk h ^ (1 / 2 : ℝ) := by positivity
    calc ‖W' h⁻¹‖ * (dk h ^ (1 / 2 : ℝ) * dk h) * ‖inn ψ Φ h 1‖
        = (‖W' h⁻¹‖ * dk h ^ (1 / 2 : ℝ)) * (‖inn ψ Φ h 1‖ * dk h) := by ring
      _ ≤ (‖W' h⁻¹‖ * dk h ^ (1 / 2 : ℝ)) * C := mul_le_mul_of_nonneg_left (hCR h).1 hw
      _ = C * (‖W' h⁻¹‖ * (modulus ((GeneralLinearGroup.det h : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)) := by
          unfold dk
          ring

theorem integrable_wPhi : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle)
    (ν : Fˣ →* ℂˣ) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ),
    Ad3.LFS.Hyp ψ ν W' Φ → ∀ g : GL (Fin 3) F,
    Integrable (fun h : GL (Fin 2) F =>
      W' h⁻¹ * Ad3.mp (GeneralLinearGroup.det h) (3 / 2) * Ad3.LFS.inn ψ Φ h g) (Ad3.LFS.hG ψ) := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp g
  have hyp1 : Hyp ψ ν W' (rtr g Φ) :=
    ⟨hyp.1, hyp.2.1, hyp.2.2.1, GlobalTheory.CompanionTheory.LFTrans.rtr_mem_SB g hyp.2.2.2⟩
  have hne := mp_one_ne_zero (GeneralLinearGroup.det g)
  refine ((integrable_one hyp1).const_mul (mp (GeneralLinearGroup.det g) 1)⁻¹).congr
    (Eventually.of_forall fun h => ?_)
  simp only [GlobalTheory.CompanionTheory.LFTrans.inn_rtr, one_mul]
  field_simp

end GlobalTheory.CompanionTheory.LFAbs
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdOfMemTsupport
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.FinPol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_nrmL (hU : Unr E) (n : ℕ) (w : Pl E) : Continuous (nrmL n w) := by
  have ht := ThBasic.continuous_thL hU n w
  by_cases hs : IsSplitAt w
  · have e : nrmL n w = id := funext fun y => by simp [nrmL, hs]
    rw [e]
    exact continuous_id
  · have e : nrmL n w = fun y => y * thL n w y := funext fun y => by simp [nrmL, thL, hs]
    rw [e]
    exact continuous_id.mul ht

theorem isClosed_KGL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsClosed (GlobalTheory.LFun.KGL w n : Set (GLw n w)) :=
  (ThBasic.twist_basic E hU n w).2.2.2.2.2.1.isClosed

theorem nrmL_mem_KGL (hU : Unr E) (n : ℕ) (w : Pl E) {y : GLw n w} (hy : y ∈ GlobalTheory.LFun.KGL w n) :
    nrmL n w y ∈ GlobalTheory.LFun.KGL w n := by
  have ht := ThBasic.thL_mem_KGL hU n w y hy
  unfold nrmL
  unfold thL at ht
  split_ifs at ht ⊢ with hs
  · exact hy
  · exact mul_mem hy ht

theorem mem_prod_of_mem_tsupport (hU : Unr E) (a b : ℕ) (w : Pl E) {y : GLw a w × GLw b w}
    (hy : y ∈ tsupport ((((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : Set (GLw a w × GLw b w)).indicator
      (1 : GLw a w × GLw b w → ℂ))) :
    y.1 ∈ GlobalTheory.LFun.KGL w a ∧ y.2 ∈ GlobalTheory.LFun.KGL w b := by
  have hcl : IsClosed (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : Set (GLw a w × GLw b w)) := by
    rw [Subgroup.coe_prod]
    exact (isClosed_KGL hU a w).prod (isClosed_KGL hU b w)
  have h := closure_minimal Set.support_indicator_subset hcl hy
  exact Subgroup.mem_prod.1 h

theorem finite_pairs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S → ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w, HasCompactSupport (φ w)) → (∀ᶠ w in cofinite, φ w = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : Set (GLw a w × GLw b w)).indicator 1) → {p : E[X] × E[X] | p.1 ∈ Ell E a ∧ p.2 ∈ Ell E b ∧ ∀ w ∈ S, ∃ y : GLw a w × GLw b w, φ w y ≠ 0 ∧ (nrmL a w y.1).val.charpoly = atPl w p.1 ∧ (nrmL b w y.2).val.charpoly = atPl w p.2}.Finite := by
  intro E _ _ _ hU a b S hS φ hc hφ
  let C₁ : ∀ w : Pl E, Set (GLw a w) := fun w => nrmL a w '' (Prod.fst '' tsupport (φ w))
  let C₂ : ∀ w : Pl E, Set (GLw b w) := fun w => nrmL b w '' (Prod.snd '' tsupport (φ w))
  have hC₁ : ∀ w, IsCompact (C₁ w) := fun w =>
    ((hc w).isCompact.image continuous_fst).image (continuous_nrmL hU a w)
  have hC₂ : ∀ w, IsCompact (C₂ w) := fun w =>
    ((hc w).isCompact.image continuous_snd).image (continuous_nrmL hU b w)
  have hK₁ : ∀ᶠ w in cofinite, C₁ w ⊆ GlobalTheory.LFun.KGL w a := by
    filter_upwards [hφ] with w hw
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hw] at hy
    exact nrmL_mem_KGL hU a w (mem_prod_of_mem_tsupport hU a b w hy).1
  have hK₂ : ∀ᶠ w in cofinite, C₂ w ⊆ GlobalTheory.LFun.KGL w b := by
    filter_upwards [hφ] with w hw
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hw] at hy
    exact nrmL_mem_KGL hU b w (mem_prod_of_mem_tsupport hU a b w hy).2
  refine ((GlobalTheory.T.finite_ellipticCharpoly_compact_section E a S hS C₁ hC₁ hK₁).prod (GlobalTheory.T.finite_ellipticCharpoly_compact_section E b S hS C₂ hC₂ hK₂)).subset ?_
  rintro p ⟨h₁, h₂, h⟩
  refine ⟨⟨h₁, fun w hw => ?_⟩, ⟨h₂, fun w hw => ?_⟩⟩
  · obtain ⟨y, hy, e₁, -⟩ := h w hw
    exact ⟨_, ⟨y.1, ⟨y, subset_tsupport _ hy, rfl⟩, rfl⟩, e₁⟩
  · obtain ⟨y, hy, -, e₂⟩ := h w hw
    exact ⟨_, ⟨y.2, ⟨y, subset_tsupport _ hy, rfl⟩, rfl⟩, e₂⟩

end GlobalTheory.CompanionTheory.FinPol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusHalfBlockValue
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

theorem ordL_pow_div_pow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {x y : L}
    (hx : x ≠ 0) (hy : y ≠ 0) (a b : ℕ) :
    ordL (x ^ b / y ^ a) = (b : ℤ) * ordL x - (a : ℤ) * ordL y := by
  have h : x ^ b / y ^ a =
      (((Units.mk0 x hx) ^ (b : ℤ) * (Units.mk0 y hy) ^ (-(a : ℤ)) : Lˣ) : L) := by
    simp [div_eq_mul_inv]
  rw [h, Units.val_mul, GlobalTheory.CompanionTheory.SwapInt.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
    GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow]
  simp only [Units.val_mk0]
  ring

theorem absHalf_blockDet_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) = (qV E w : ℂ) ^ (-((i : ℂ) * b - (j : ℂ) * a) / 2) := by
  intro E _ _ _ a b w i j m hi hj
  have h1 : m.1.val.det ≠ 0 := by
    have := m.1.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have h2 : m.2.val.det ≠ 0 := by
    have := m.2.isUnit
    exact ((Matrix.isUnit_iff_isUnit_det _).1 this).ne_zero
  have hq : 0 < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have ho := ordL_pow_div_pow h1 h2 a b
  rw [hi, hj] at ho
  unfold absHalf
  rw [ho]
  have hs : Real.sqrt ((qV E w : ℝ) ^ (-((b : ℤ) * (i : ℤ) - (a : ℤ) * (j : ℤ)))) =
      (qV E w : ℝ) ^ (-((i : ℝ) * b - (j : ℝ) * a) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul hq.le]
    congr 1
    push_cast
    ring
  rw [hs, Complex.ofReal_cpow hq.le, Complex.ofReal_natCast]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.CtS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityBoundUnramifiedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_bound_unramified : PositivityTheory.SiegelWeilFormula.Gunr.NuBound := by
  first | exact @GlobalTheory.CompanionTheory.GunrNuBound.nuBound | exact GlobalTheory.CompanionTheory.GunrNuBound.nuBound | (intros; apply GlobalTheory.CompanionTheory.GunrNuBound.nuBound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuLev := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev | exact GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormulaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_power_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  first | exact @GlobalTheory.CompanionTheory.GunrNu.nuPow | exact GlobalTheory.CompanionTheory.GunrNu.nuPow | (intros; apply GlobalTheory.CompanionTheory.GunrNu.nuPow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbEx
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

set_option maxHeartbeats 1600000 in

theorem orbEx : IdemEx → ApproxId → Dens → TopX → AlgRich → AlgStab → SigLaw → HermScale → OrbEx := by
  intro _hIE hAI hDens hTop hAR hAS hSL hHS D n r t hn V hV ψ hψ θ hθ b₀ hb S e hS he fib μt hfib hfibs
    hfibi hμt lam hlam hIntg
  obtain ⟨i1, i2, i3, i4, i5, hemb, i7, i8, i9⟩ := hTop D V.rank r t e
  have hT2 : ∀ a b : ℕ, T2Space (Formalism.IndefR.Datum.Mx D a b) := by
    intro a b
    obtain ⟨j1, -, -, -, -, -, -, -, -⟩ := hTop D a 0 b 1
    let f : Formalism.IndefR.Datum.Mx D a b → PositivityTheory.Rg.Rsw.Em.XS D a 0 b 1 :=
      fun x => ⟨((0 : Formalism.IndefR.Datum.Mx D a 0), x), one_smul _ _, one_smul _ _⟩
    have hf : Continuous f := (continuous_const.prodMk continuous_id).subtype_mk _
    constructor
    intro x y hxy
    obtain ⟨U, W, hU, hW, hxU, hyW, hUW⟩ := t2_separation (x := f x) (y := f y)
      (fun h => hxy (congrArg (fun w => (Subtype.val w).2) h))
    exact ⟨f ⁻¹' U, f ⁻¹' W, hU.preimage hf, hW.preimage hf, hxU, hyW, hUW.preimage f⟩
  haveI := hT2 t t
  haveI := hT2 r r
  obtain ⟨hσfin, hσY, -, hσU, hσS, hσG⟩ :=
    hSL D r t V b₀ S e hS he fib μt hfib hfibs hfibi hμt
  obtain ⟨gk, Gk, hgG, htend, hdec⟩ := hAI D t ψ hψ S e hS lam hlam
  have hRich := hAR D θ hθ V.rank r t n hn S e hS
  let k : ↥(PositivityTheory.Rg.Rsw.L.hermS D t e) → PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e → ℂ :=
    fun x z => PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val x))
      (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z))
  have hkc : Continuous (fun p : ↥(PositivityTheory.Rg.Rsw.L.hermS D t e) × PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e =>
      PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val p.1)) (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val p.2))) :=
    GlobalTheory.CompanionTheory.OrbExist.continuous_pch₂ hψ
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
      ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp (continuous_subtype_val.comp continuous_snd))
  have hD := hDens (PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e) (↥(PositivityTheory.Rg.Rsw.L.hermS D t e))
    (PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)) lam k (PositivityTheory.Rg.Rsw.Em.algA θ hn S e)
    {z | PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z) = 0}
    {z | PositivityTheory.Rg.Rsw.L.ip V (Subtype.val z).1 (Subtype.val z).1 = e • GlobalTheory.MixModel.rat (Subtype.val b₀)}
    gk (fun j z => Gk j (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)))
    hσfin hkc.measurable (fun x z => (hψ.2.1 _).le) hRich.1
    (isClosed_eq ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp continuous_subtype_val) continuous_const)
    (isClosed_eq ((GlobalTheory.CompanionTheory.OrbExist.continuous_ip_fst (r := r) (t := t) V).comp continuous_subtype_val)
      continuous_const)
    hσY
    (fun j => ⟨(hgG j).1, (hgG j).2.1, fun z _ => (hgG j).2.2 _ (GlobalTheory.CompanionTheory.OrbExist.qv_mem V b₀ _)⟩)
    htend
    (fun C hC _ hCZ ε hε => by
      have hC' : IsCompact ((fun z : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e =>
          PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) '' C) :=
        hC.image ((GlobalTheory.CompanionTheory.OrbExist.continuous_qv V b₀).comp continuous_subtype_val)
      filter_upwards [hdec _ hC'.isClosed (by
        rintro _ ⟨z, hz, rfl⟩
        exact ⟨GlobalTheory.CompanionTheory.OrbExist.qv_mem V b₀ _, GlobalTheory.CompanionTheory.OrbExist.qv_smul V b₀ e _ z.2.2,
          fun h0 => Set.disjoint_left.1 hCZ hz h0⟩) ε hε] with j hj z hz
      exact hj _ ⟨z, hz, rfl⟩)
    hIntg
  obtain ⟨ν, hνfin, hνsupp, hνint, hνcov⟩ := hD
  have hYae : ∀ᵐ z ∂(PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)),
      PositivityTheory.Rg.Rsw.L.ip V (Subtype.val z).1 (Subtype.val z).1 = e • GlobalTheory.MixModel.rat (Subtype.val b₀) :=
    MeasureTheory.ae_iff.2 hσY
  refine ⟨ν, ⟨?_, ?_, ?_, ?_, ?_⟩, hνint⟩
  · refine ⟨fun K hK => ?_⟩
    rw [hemb.map_apply]
    exact hνfin.lt_top_of_isCompact
      ((GlobalTheory.CompanionTheory.OrbExist.isClosed_fixed (a := V.rank) (r := r) (t := t)
        e).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
  · rw [hemb.map_apply]
    refine measure_mono_null ?_ hνsupp
    intro z hz hYZ
    exact hz ⟨z.2.1, z.2.2, hYZ.1, hYZ.2⟩
  · intro h hh
    let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
      GlobalTheory.CompanionTheory.EisM.liftU V r t h
    have hcov : MeasureTheory.Measure.map Θ ν = (1 : NNReal) • ν := by
      refine hνcov Θ 1 fun f hf => ⟨?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS (Formalism.L2.Theta.matHom V h) 1 hh (by simp) Θ
          (fun z => ?_) f hf
        rw [GlobalTheory.CompanionTheory.OrbExist.mm_jn, Units.val_one]
        exact (Matrix.mul_one _).symm
      · exact GlobalTheory.CompanionTheory.OrbExist.trans_int₁ _ lam k f Θ (hσU h hh Θ fun z => rfl) fun x =>
          Filter.Eventually.of_forall fun z => by
            show PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
              PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀
                (PositivityTheory.Rg.Rsw.L.mm (Formalism.L2.Theta.mt V h) (Subtype.val z).1,
                  PositivityTheory.Rg.Rsw.L.mm (Formalism.L2.Theta.mt V h) (Subtype.val z).2))
            simp only [PositivityTheory.Rg.Rsw.L.qv, PositivityTheory.Rg.Rsw.L.yv, GlobalTheory.CompanionTheory.ColumnSplitting.GramAct.ip_mt]
    have := GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiU V r t h) 1 hemb.measurable
      Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiU V r t h).continuous.measurable (fun z => rfl) hcov
    rw [one_smul] at this
    exact this
  · intro y hy
    let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
      GlobalTheory.CompanionTheory.EisM.liftS V.rank y
    have hcov : MeasureTheory.Measure.map Θ ν = (1 : NNReal) • ν := by
      refine hνcov Θ 1 fun f hf => ⟨?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS 1 (GlobalTheory.CompanionTheory.OrbExist.shU hn y) (by simp)
          (GlobalTheory.CompanionTheory.OrbExist.smul_blockMatrix_sub_one hn e 1 y 0 1 (by simp) hy (by simp) (by simp)) Θ
          (fun z => ?_) f hf
        rw [Units.val_one, show ∀ X : Matrix (Fin V.rank) (Fin n) (Formalism.L2.Theta.AE D),
          PositivityTheory.Rg.Rsw.L.mm (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) X = X from
          fun X => Matrix.one_mul X]
        refine Eq.trans ?_ (GlobalTheory.CompanionTheory.ColumnSplitting.jnBl D n t V.rank r hn (Subtype.val z).1 (Subtype.val z).2 y).symm
        show PositivityTheory.Rg.Rsw.L.jn hn (Subtype.val z).1
          ((Subtype.val z).2 + PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).1 y) = _
        rw [add_comm]
      · exact GlobalTheory.CompanionTheory.OrbExist.trans_int₁ _ lam k f Θ (hσS y hy Θ fun z => rfl) fun x =>
          hYae.mono fun z hz => by
            show PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
              PositivityTheory.Rg.Rsw.L.pch ψ _ (PositivityTheory.Rg.Rsw.L.qv V b₀
                ((Subtype.val z).1, (Subtype.val z).2 + PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).1 y))
            rw [GlobalTheory.CompanionTheory.OrbExist.qv_shear V b₀ hb e _ _ y hz hy]
    have := GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiS V.rank y) 1 hemb.measurable
      Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiS V.rank y).continuous.measurable (fun z => rfl) hcov
    rw [one_smul] at this
    exact this
  · intro g hg
    let Θ : PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e ≃ₜ PositivityTheory.Rg.Rsw.Em.XS D V.rank r t e :=
      GlobalTheory.CompanionTheory.EisM.liftG V.rank r g
    obtain ⟨c, hc, hcmap⟩ := hHS D t S e hS lam hlam g⁻¹ (GlobalTheory.CompanionTheory.OrbExist.smul_inv_sub e g hg)
    have hκ : ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ V.rank *
        ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ ^ t =
        ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) := by
      rw [map_inv, GlobalTheory.CompanionTheory.OrbExist.absA_inv]
      exact GlobalTheory.CompanionTheory.OrbExist.kap _ (GlobalTheory.CompanionTheory.OrbExist.absA_ne D _) V.rank r t hV
    have hkG : ∀ x, ∀ᵐ z ∂(PositivityTheory.Rg.Rsw.Em.sig S he (fib.prod μt)), k x z = k (c x) (Θ z) :=
      fun x => Filter.Eventually.of_forall fun z => by
        show PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val x)) (PositivityTheory.Rg.Rsw.L.qv V b₀ (Subtype.val z)) =
          PositivityTheory.Rg.Rsw.L.pch ψ (Subtype.val (Subtype.val (c x))) (PositivityTheory.Rg.Rsw.L.qv V b₀
            ((Subtype.val z).1, PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).2
              (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))))
        rw [hc x, ← GlobalTheory.CompanionTheory.OrbExist.pch_conj, GlobalTheory.CompanionTheory.OrbExist.qv_col, GlobalTheory.CompanionTheory.OrbExist.conj_cancel]
    have hcov : MeasureTheory.Measure.map Θ ν =
        ((GlobalTheory.Doubling.absA D) (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (r + t) • ν := by
      refine hνcov Θ _ fun f hf => ⟨?_, ?_⟩
      · refine GlobalTheory.CompanionTheory.OrbExist.comp_mem hθ hS hRich.2 hAS 1 (GlobalTheory.CompanionTheory.OrbExist.colU hn g) (by simp)
          (GlobalTheory.CompanionTheory.OrbExist.smul_blockMatrix_sub_one hn e 1 0 0 (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))
            (by simp) (by simp) (by simp) hg) Θ (fun z => ?_) f hf
        rw [Units.val_one, show ∀ X : Matrix (Fin V.rank) (Fin n) (Formalism.L2.Theta.AE D),
          PositivityTheory.Rg.Rsw.L.mm (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) X = X from
          fun X => Matrix.one_mul X]
        refine Eq.trans ?_ (GlobalTheory.CompanionTheory.OrbExist.jn_bl hn (Subtype.val z).1 (Subtype.val z).2 1 0 0
          (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))).symm
        show PositivityTheory.Rg.Rsw.L.jn hn (Subtype.val z).1 (PositivityTheory.Rg.Rsw.L.mm (Subtype.val z).2
          (g : Matrix (Fin t) (Fin t) (Formalism.L2.Theta.AE D))) = _
        simp only [PositivityTheory.Rg.Rsw.L.mm, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
      · rw [GlobalTheory.CompanionTheory.OrbExist.trans_int _ lam k f Θ c _ _ (hσG g hg Θ fun z => rfl) hcmap hkG, hκ]
    exact GlobalTheory.CompanionTheory.OrbExist.map_val_rel ν Subtype.val Θ (GlobalTheory.CompanionTheory.EisM.phiG V.rank r g) _ hemb.measurable
      Θ.continuous.measurable (GlobalTheory.CompanionTheory.EisM.phiG V.rank r g).continuous.measurable (fun z => rfl) hcov

end GlobalTheory.CompanionTheory.OrbExist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBiadditiveStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_biadditive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (b : HermR (Af F) σ n),
    (∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b (X + X') Y =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X' Y) ∧
    (∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b X (Y + Y') =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X Y') := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd.pairB_add <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingOnRationalTupleFormulaStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_on_rational_tuple_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψf : Af F → ℂ) (c : hermE σ n) (c₀ : Fin n) (i₀ : Fin M) (x : Af F ⊗[F] E) (s : ℕ)
      (ρ : Fin M → Fin n → 𝓞 E),
    pairB σ J ψf (hermIn (Af F) σ n c) (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ) =
      ψf (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle.pair_single | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle.pair_single | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle.pair_single <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParsevalBoundOfInnerNe
section
noncomputable section
open MeasureTheory Complex Ad3 Ad3.LR Ad3.LR.C

namespace GlobalTheory.CompanionTheory.Parseval

theorem parseval_bound : Ad3.LR.C.ParsB := fun Φ N => by
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Parseval.Max.parseval_bound_max Φ N
  exact ⟨C, fun ε hε hε1 h v hdet => by simpa [Dk] using hC ε hε hε1 h v hdet⟩

theorem parseval_bound_of_inner_ne (Φ : Sw) (N : ℕ) : ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (h : M22) (v : ℝ),
    (Matrix.of h).det ≠ 0 → h 0 0 * h 0 1 + h 1 0 * h 1 1 ≠ 0 → ‖Ae Φ ε h v‖ ≤ C * Dk N h := by
  obtain ⟨C, hC⟩ := parseval_bound Φ N
  exact ⟨C, fun ε hε hε1 h v hdet _ => hC ε hε hε1 h v hdet⟩

example : Ad3.LR.C.ParsB := parseval_bound

end GlobalTheory.CompanionTheory.Parseval
end
end

