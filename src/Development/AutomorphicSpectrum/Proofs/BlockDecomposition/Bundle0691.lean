import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0548
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsHorizontal charOf)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ.PtDictProof

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem C_mem_ptIdeal_iff (x : MP ℤ m n) (a : ℤ) :
    (C a : MRing (Bk n)) ∈ ptIdeal x ↔ (a : (MP ℤ m n).residueField x) = 0 := by
  rw [ptIdeal, ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap,
    MvPolynomial.aeval_C]
  have h : (algebraMap ℤ (MvPolynomial (Fin (m + 1)) ((MP ℤ m n).residueField x)) a) =
      MvPolynomial.C (a : (MP ℤ m n).residueField x) := by
    simp
  rw [h, MvPolynomial.C_eq_zero]

theorem evaluation_generic_injective (Z : Scheme.{0}) [IsIntegral Z] :
    Function.Injective (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom := by
  rw [← Scheme.germ_residue, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Injective.comp ?_ (germ_injective_of_isIntegral Z _ _)
  exact RingHom.injective (Z.residue (genericPoint Z)).hom

theorem dim_closure_image_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hg := (genericPoint_spec Z).image (f := j) j.isClosedEmbedding.continuous
  have hcl : closure ({j (genericPoint Z)} : Set X) = Set.range j := by
    have h1 : closure ({j (genericPoint Z)} : Set X) = closure (j '' Set.univ) := hg
    rw [h1, Set.image_univ]
    exact j.isClosedEmbedding.isClosed_range.closure_eq
  rw [hcl]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    j.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

theorem charZero_residueField_iff {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) := by
  constructor
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (f := (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom)
        (RingHom.injective _)
    exact RingHom.charZero (Z.evaluation ⊤ (genericPoint Z) (Opens.mem_top _)).hom
  · intro h
    haveI : CharZero (Z.residueField (genericPoint Z)) :=
      charZero_of_injective_ringHom (evaluation_generic_injective Z)
    exact RingHom.charZero (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom

theorem charOf_prime {P : Ideal (MRing (Bk n))} [P.IsPrime] (h : ¬ IsHorizontal P) : (charOf P).Prime := by
  unfold charOf
  rw [← Int.prime_iff_natAbs_prime]
  exact Submodule.IsPrincipal.prime_generator_of_isPrime _ h

theorem C_charOf_mem (P : Ideal (MRing (Bk n))) : (C ((charOf P : ℕ) : ℤ) : MRing (Bk n)) ∈ P := by
  have hg := Submodule.IsPrincipal.generator_mem (P.comap (C : ℤ →+* MRing (Bk n)))
  obtain ⟨c, hc⟩ := Int.dvd_natAbs.mpr
    (dvd_refl (Submodule.IsPrincipal.generator (P.comap (C : ℤ →+* MRing (Bk n)))))
  have hmem : ((charOf P : ℕ) : ℤ) ∈ P.comap (C : ℤ →+* MRing (Bk n)) := by
    unfold charOf
    rw [hc]
    exact Ideal.mul_mem_right c _ hg
  exact Ideal.mem_comap.mp hmem

theorem charOf_cast_eq_zero {Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ MP ℤ m n) :
    ((charOf (ptIdeal (j (genericPoint Z))) : ℕ) : Γ(Z, ⊤)) = 0 := by
  have h1 := (C_mem_ptIdeal_iff (j (genericPoint Z)) _).mp (C_charOf_mem _)
  have h2 := congrArg (Scheme.Hom.residueFieldMap j (genericPoint Z)).hom h1
  apply evaluation_generic_injective Z
  rw [map_natCast, map_zero]
  simpa using h2

end GlobalTheory.CompanionTheory.MixZ.PtDictProof

namespace GlobalTheory.CompanionTheory.MixZ

open GlobalTheory.CompanionTheory.MixZ.PtDictProof in

theorem ptDict : PtDict := by
  intro m n Z _ j _ d hd
  have hP := isMultiProjPrime_ptIdeal m n (j (genericPoint Z))
  haveI : (ptIdeal (j (genericPoint Z))).IsPrime := hP.1
  have hH : IsHorizontal (ptIdeal (j (genericPoint Z))) ↔ CharZero Γ(Z, ⊤) :=
    (ptIdeal_isHorizontal_iff m n _).trans (charZero_residueField_iff j)
  refine ⟨hP, hH, fun h => ?_, fun h => ⟨charOf_prime h, charOf_cast_eq_zero j⟩⟩
  have hc : CharZero ((MP ℤ m n).residueField (j (genericPoint Z))) :=
    (ptIdeal_isHorizontal_iff m n _).mp h
  have hdim : topologicalKrullDim (closure ({j (genericPoint Z)} : Set (MP ℤ m n))) = (d : ℕ) := by
    rw [dim_closure_image_generic j, hd]
  exact (GlobalTheory.T.closure_dim_iff_arithmetic_variety m n _ d hc).mp hdim

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultIntegralPowerBound
section
open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.PowerKernel

noncomputable def dens (σ : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  |y|⁻¹ * (|y| ^ (σ - 1) / (1 + |y⁻¹| * 1) ^ N)

theorem measurable_dens (σ : ℝ) (N : ℕ) : Measurable (dens σ N) := by
  unfold dens
  have h1 : Measurable fun y : ℝ => |y| := by fun_prop
  have h2 : Measurable fun y : ℝ => |y| ^ (σ - 1) := h1.pow_const _
  have h3 : Measurable fun y : ℝ => (1 + |y⁻¹| * 1) ^ N := by fun_prop
  exact (h1.inv).mul (h2.div h3)

theorem dens_nonneg (σ : ℝ) (N : ℕ) (y : ℝ) : 0 ≤ dens σ N y := by
  unfold dens
  positivity

theorem dens_neg (σ : ℝ) (N : ℕ) (y : ℝ) : dens σ N (-y) = dens σ N y := by
  simp [dens, inv_neg, abs_neg]

theorem dens_le_small (σ : ℝ) {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : 0 < y) :
    dens σ N y ≤ y ^ (σ - 1) := by
  have hyi : 0 < y⁻¹ := inv_pos.2 hy
  have hp : 0 < y ^ (σ - 1) := Real.rpow_pos_of_pos hy _
  have hb : y⁻¹ ≤ (1 + y⁻¹) ^ N := by
    calc y⁻¹ ≤ 1 + y⁻¹ := by linarith
      _ = (1 + y⁻¹) ^ 1 := (pow_one _).symm
      _ ≤ (1 + y⁻¹) ^ N := pow_le_pow_right₀ (by linarith) hN
  have hD : 0 < (1 + y⁻¹) ^ N := by positivity
  simp only [dens, abs_of_pos hy, abs_of_pos hyi, mul_one]
  rw [← mul_div_assoc, div_le_iff₀ hD, mul_comm]
  exact mul_le_mul_of_nonneg_left hb hp.le

theorem dens_le_large (σ : ℝ) (N : ℕ) {y : ℝ} (hy : 0 < y) :
    dens σ N y ≤ y ^ (σ - 2) := by
  have hyi : 0 < y⁻¹ := inv_pos.2 hy
  have hp : 0 < y ^ (σ - 1) := Real.rpow_pos_of_pos hy _
  have hb : 1 ≤ (1 + y⁻¹) ^ N := one_le_pow₀ (by linarith)
  have he : y ^ (σ - 2) = y⁻¹ * y ^ (σ - 1) := by
    rw [show σ - 2 = -1 + (σ - 1) by ring, Real.rpow_add hy, Real.rpow_neg_one]
  simp only [dens, abs_of_pos hy, abs_of_pos hyi, mul_one]
  rw [he]
  exact mul_le_mul_of_nonneg_left (div_le_self hp.le hb) hyi.le

theorem dens_integrableOn {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (dens σ N) (Ioi 0) := by
  have hA : IntegrableOn (dens σ N) (Ioc 0 1) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ (σ - 1)) (Ioc 0 1) := by
      have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := σ - 1) (by linarith)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 this
    refine Integrable.mono' hi (measurable_dens σ N).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_of_nonneg (dens_nonneg σ N y)]
    exact dens_le_small σ hN hy.1
  have hB : IntegrableOn (dens σ N) (Ioi 1) := by
    have hi : IntegrableOn (fun y : ℝ => y ^ (σ - 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine Integrable.mono' hi (measurable_dens σ N).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_of_nonneg (dens_nonneg σ N y)]
    exact dens_le_large σ N (lt_trans zero_lt_one hy)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  exact hA.union hB

theorem dens_integrable {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (dens σ N) := by
  have hI : Integrable ((Ioi (0 : ℝ)).indicator (dens σ N)) :=
    (dens_integrableOn h0 h1 hN).integrable_indicator measurableSet_Ioi
  have hJ : Integrable fun x : ℝ => (Ioi (0 : ℝ)).indicator (dens σ N) (-x) := hI.comp_neg
  refine (hI.add hJ).congr (Filter.Eventually.of_forall fun x => ?_)
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h2 : x ∉ Ioi (0 : ℝ) := by simp [hx.le]
    have h3 : -x ∈ Ioi (0 : ℝ) := by simpa using hx
    simp [Set.indicator_of_notMem h2, Set.indicator_of_mem h3, dens_neg]
  · subst hx
    simp [dens]
  · have h2 : x ∈ Ioi (0 : ℝ) := hx
    have h3 : -x ∉ Ioi (0 : ℝ) := by simp [hx.le]
    simp [Set.indicator_of_mem h2, Set.indicator_of_notMem h3]

theorem kernel_one_integrable {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) Ad3.mulR := by
  have key : Integrable (fun x : ℝ => |x|⁻¹ •
      (((|x| ^ (σ - 1) / (1 + |x⁻¹| * 1) ^ N : ℝ)) : ℂ)) volume := by
    refine ((dens_integrable h0 h1 hN).ofReal (𝕜 := ℂ)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp [dens, Complex.real_smul]
  exact ((GlobalTheory.CompanionTheory.RealTateConv.integrable_mulR_iff
    (fun x : ℝ => (((|x| ^ (σ - 1) / (1 + |x⁻¹| * 1) ^ N : ℝ)) : ℂ))).2 key).re

theorem kernel_scale (σ : ℝ) (N : ℕ) {q : ℝ} (hq : 0 < q) (t : ℝˣ) :
    |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)| ^ (σ - 1) /
        (1 + |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)⁻¹| * q) ^ N =
      q ^ (σ - 1) * (|(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) := by
  have h1 : |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)| = |(t : ℝ)| * q := by
    simp [abs_mul, abs_of_pos hq]
  have h2 : |((t * Units.mk0 q hq.ne' : ℝˣ) : ℝ)⁻¹| * q = |(t : ℝ)⁻¹| * 1 := by
    simp only [Units.val_mul, Units.val_mk0, mul_inv, abs_mul, abs_inv, abs_of_pos hq]
    field_simp
  rw [h1, h2, Real.mul_rpow (abs_nonneg _) hq.le]
  ring

theorem kernel_integral_le :
    ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N) Ad3.mulR ∧
    ∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N ∂Ad3.mulR ≤ K * q ^ (σ - 1) := by
  intro σ h0 h1 N hN
  refine ⟨∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N ∂Ad3.mulR, fun q hq => ?_⟩
  set u : ℝˣ := Units.mk0 q hq.ne' with hu
  set f : ℝˣ → ℝ := fun t => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N with hf
  have hcomp : (fun t : ℝˣ => f (t * u)) = fun t : ℝˣ =>
      q ^ (σ - 1) * (|(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * 1) ^ N) := by
    funext t
    exact kernel_scale σ N hq t
  have hint : Integrable (fun t : ℝˣ => f (t * u)) Ad3.mulR := by
    rw [hcomp]
    exact (kernel_one_integrable h0 h1 hN).const_mul _
  have hfi : Integrable f Ad3.mulR := by
    have := hint.comp_mul_right u⁻¹
    simpa using this
  refine ⟨hfi, le_of_eq ?_⟩
  rw [← integral_mul_right_eq_self f u, hcomp, integral_const_mul, mul_comm]

end GlobalTheory.CompanionTheory.PowerKernel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatementStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement_22 : CjEx → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (v : PlF E) (w : Above v), IsSplitAt w.1 →
  ∃ e : Yv a b v ≃ₜ* ((GLw a w.1 × GLw b w.1) × (GLw a w.1 × GLw b w.1)), (∀ y, (e y).1 = evw w y) ∧
    (∀ y, e (thv a b v y) = swTw (sgP a b w.1) (e y)) ∧ (∀ y, y ∈ Kv a b v ↔ e y ∈ (K2 a b w.1).prod (K2 a b w.1)) ∧
    ∀ (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), e (pv a b v (ratF E a δ₁, ratF E b δ₂)) =
      ((ratW a w.1 δ₁, ratW b w.1 δ₂),
        (ratW a w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₁),
         ratW b w.1 (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ₂))) := by
  first | exact @GlobalTheory.CompanionTheory.SplitIso.split_iso | exact GlobalTheory.CompanionTheory.SplitIso.split_iso | (intros; apply GlobalTheory.CompanionTheory.SplitIso.split_iso <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBiadditive
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd

theorem psiFin_add' (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (x y : Af F) :
    psiFin F ψ (x + y) = psiFin F ψ x * psiFin F ψ y := by
  have h : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y := by
    simp only [pairA]
    exact Prod.ext (add_zero 0).symm rfl
  simp only [psiFin]
  rw [h, AddChar.map_add_eq_mul]

theorem hR_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add, Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem hR_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → R ⊗[F] E) :
    hR R σ J x (y + y') = hR R σ J x y + hR R σ J x y' := by
  simp [hR, Formalism.UG.hform, Pi.add_apply, map_add, Matrix.mulVec_add, Matrix.add_mulVec, dotProduct_add,
    add_dotProduct, Finset.sum_add_distrib, add_mul, mul_add]

theorem pairB_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ)
    (b : HermR (Af F) σ n),
    (∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b (X + X') Y =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X' Y) ∧
    (∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E, pairB σ J (psiFin F ψ) b X (Y + Y') =
      pairB σ J (psiFin F ψ) b X Y * pairB σ J (psiFin F ψ) b X Y') := by
  intro F E _ _ _ _ _ σ M J n ψ b
  have hg1 : ∀ X X' Y : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J (X + X') Y = gram2 σ J X Y + gram2 σ J X' Y := by
    intro X X' Y
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_left _ σ J _ _ _
  have hg2 : ∀ X Y Y' : Fin n → Fin M → Af F ⊗[F] E,
      gram2 σ J X (Y + Y') = gram2 σ J X Y + gram2 σ J X Y' := by
    intro X Y Y'
    ext a c
    simp only [gram2, Pi.add_apply, Matrix.add_apply]
    exact hR_add_right _ σ J _ _ _
  refine ⟨fun X X' Y => ?_, fun X Y Y' => ?_⟩
  · simp only [pairB, hg1, Matrix.mul_add, Matrix.trace_add, map_add, psiFin_add']
  · simp only [pairB, hg2, Matrix.mul_add, Matrix.trace_add, map_add, psiFin_add']

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairAdd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingOnRationalTupleFormula
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle

theorem pair_single : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (n : ℕ) (ψf : Af F → ℂ) (c : hermE σ n) (c₀ : Fin n) (i₀ : Fin M) (x : Af F ⊗[F] E) (s : ℕ)
      (ρ : Fin M → Fin n → 𝓞 E),
    pairB σ J ψf (hermIn (Af F) σ n c) (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ) =
      ψf (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)))) := by
  intro F E _ _ _ _ _ σ M J hJ n ψf c c₀ i₀ x s ρ
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have key : ∀ a, hR (Af F) σ J (fun i => if i = i₀ then x else 0) (ratTuple J s ρ a) =
      sigR (Af F) σ x * inclR (Af F) ((s : E) * algebraMap (𝓞 E) E (ρ i₀ a)) := by
    intro a
    have hv : ∑ j, J i₀ j * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j
        = algebraMap (𝓞 E) E (ρ i₀ a) := by
      have h1 : (J *ᵥ (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a))) i₀ =
          algebraMap (𝓞 E) E (ρ i₀ a) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
      simpa [Matrix.mulVec, dotProduct] using h1
    unfold hR Formalism.UG.hform
    rw [Finset.sum_eq_single i₀]
    · simp only [if_true, JR, ratTuple, Matrix.map_apply]
      rw [← hv]
      simp only [map_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · intro i _ hi
      simp [hi]
    · simp
  have hz : ∀ (c' : Fin n) (a : Fin n), c' ≠ c₀ →
      hR (Af F) σ J (fun i => if c' = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ a) = 0 := by
    intro c' a hc
    simp [hR, Formalism.UG.hform, hc]
  have hin : ∀ a b, ((hermIn (Af F) σ n c : HermR (Af F) σ n) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) a b = inclR (Af F) (c.1 a b) := fun a b => rfl
  have htr : Matrix.trace (((hermIn (Af F) σ n c : HermR (Af F) σ n) :
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
        gram2 σ J (fun a i => if a = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ)) =
      sigR (Af F) σ x * inclR (Af F)
        ((s : E) * ∑ a, c.1 a c₀ * algebraMap (𝓞 E) E (ρ i₀ a)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hin, gram2]
    have h2 : ∀ a, ∑ c', inclR (Af F) (c.1 a c') *
        hR (Af F) σ J (fun i => if c' = c₀ ∧ i = i₀ then x else 0) (ratTuple J s ρ a) =
        inclR (Af F) (c.1 a c₀) *
          (sigR (Af F) σ x * inclR (Af F) ((s : E) * algebraMap (𝓞 E) E (ρ i₀ a))) := by
      intro a
      rw [Finset.sum_eq_single c₀]
      · simp only [true_and]
        rw [key a]
      · intro c' _ hc
        rw [hz c' a hc, mul_zero]
      · simp
    simp only [h2]
    rw [Finset.mul_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [map_mul]
    ring
  unfold pairB
  rw [htr]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.PairSingle
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhaseContinuousUnitary
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem psiFin_continuous_unit (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : Continuous (psiFin F ψ) ∧ ∀ y, ‖psiFin F ψ y‖ = 1 := by
  refine ⟨?_, fun y => hψ.2.1 _⟩
  have : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  exact hψ.1.comp this

set_option maxHeartbeats 1000000 in

theorem phaseB_pairB_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n),
    Continuous (phaseB σ J (psiFin F ψ) b) ∧ (∀ X, ‖phaseB σ J (psiFin F ψ) b X‖ = 1) ∧
    ∀ X, Continuous (pairB σ J (psiFin F ψ) b X) := by
  intro F E _ _ _ _ _ σ hσ M J n ψ hψ b
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨t1, -, -, -, hs, htr, -, -, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := t1
  obtain ⟨hc, hn⟩ := psiFin_continuous_unit F ψ hψ
  refine ⟨?_, fun X => hn _, fun X => ?_⟩
  · refine hc.comp (continuous_const.mul (htr.comp (Continuous.matrix_trace
      (Continuous.matrix_mul continuous_const (hG n M J)))))
  · refine hc.comp (htr.comp (Continuous.matrix_trace
      (Continuous.matrix_mul continuous_const ?_)))
    refine continuous_matrix fun a c => ?_
    simp only [gram2, hR, Formalism.UG.hform]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_apply j).comp (continuous_apply c))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatSplit
section
noncomputable section

open NumberField IsDedekindDomain Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatSplitAt

theorem satSplit : PositivityTheory.Rg.BcB.F.RS.SatSplit := by
  rintro E _ _ _ n π D w B ⟨σ, hc, hs⟩ ⟨b, hb, rfl⟩
  obtain ⟨P, hsub, -, hsat⟩ := GlobalTheory.PfBCI.unram_component D.h w (D.σ · w) b hb
  obtain ⟨α, hα, hσ⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ _).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hs⟩)
  obtain ⟨y, hy⟩ := hsat.exists_vec
  have hP : GlobalTheory.SmGL.HasSatake P.ρ α :=
    GlobalTheory.CompanionTheory.SatComp.hasSatake_of_isSatVecGL ⟨P.smooth, P.irred⟩ α (hα ▸ hy)
  obtain ⟨e⟩ := GlobalTheory.SmGL.SphUniq.equiv_of_parInd _ _ hP.1 hσ.1 hP.2.2 hσ.2.2 hP.2.1 hσ.2.1
  exact ⟨σ, (GlobalTheory.SmGL.IsSubquotient.of_surjective e.toIntertwiningMap e.toLinearEquiv.surjective).trans hsub, hc⟩

end GlobalTheory.CompanionTheory.SatSplitAt

end
end

