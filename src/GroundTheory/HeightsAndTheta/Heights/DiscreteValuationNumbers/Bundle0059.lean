import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSubQuotient
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtNatCastOfAddOneLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LiftFormNotMemBlowUpOf
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDivPushForward
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0054
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0055

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalEqOfVdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreFlagDegreeZero

theorem le_weight_block {κ : Type} [DecidableEq κ] {τ : κ → Type} (c : (Σ o, τ o) →₀ ℕ) {p : Σ o, τ o}
    (hp : p ∈ c.support) : c p ≤ Finsupp.weight (blockWeight τ) c p.1 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  refine le_trans (le_of_eq ?_)
    (Finset.single_le_sum (f := fun x => (c x • blockWeight τ x) p.1) (fun _ _ => Nat.zero_le _) hp)
  simp [blockWeight]

theorem aeval_eq_of_vdeg {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] {M M' : ℕ}
    {Φ : Type} [Field Φ] [Algebra O Φ] {z z' : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (h : ∀ (k : K) (i : ι k), z ⟨some (some k), i⟩ = z' ⟨some (some k), i⟩)
    {G : MRing (bundleIdx (bundleIdx ι M) M') O} {β : K → ℕ} (hG : IsMultiHomog G (GenericProjClosureDivisor.vdeg β)) :
    aeval z G = aeval z' G := by
  rw [aeval_def, aeval_def]
  apply eval₂_congr
  intro p c' hp hc
  obtain ⟨o, i⟩ := p
  have key := le_weight_block c' hp
  rw [hG hc] at key
  rcases o with _ | _ | k
  · simp [GenericProjClosureDivisor.vdeg] at key
    exact absurd key (Finsupp.mem_support_iff.mp hp)
  · simp [GenericProjClosureDivisor.vdeg] at key
    exact absurd key (Finsupp.mem_support_iff.mp hp)
  · exact h k i

theorem flag_eq_zero {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E]
    {Φ : Type*} [Field Φ] [Algebra Ω Φ] {N : ℕ} (w e : Module.Basis (Fin N) Ω E)
    {t : Fin N → Φ} (ht : LinearIndependent Ω t) (χ : Module.Dual Ω E) {k : ℕ}
    (h0 : ∑ j, flagCoord w e t k j * algebraMap Ω Φ (χ (w j)) = 0) (j : Fin N) (hj : (j : ℕ) < k) :
    χ (w j) = 0 := by
  let θ : Module.Dual Ω E := ∑ j : Fin N, (if (j : ℕ) < k then χ (w j) else 0) • w.coord j
  have hθe : ∀ i, θ (e i) = ∑ j : Fin N, (if (j : ℕ) < k then χ (w j) else 0) * w.repr (e i) j := by
    intro i
    simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  have hθ : θ = 0 := by
    refine e.ext fun i => ?_
    have key := Fintype.linearIndependent_iff.1 ht (fun i => θ (e i)) (by
      rw [← h0]
      simp only [hθe, Algebra.smul_def, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [flagCoord]
      split_ifs
      · rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul]
        ring
      · simp)
    simpa using key i
  have h := congrArg (fun f : Module.Dual Ω E => f (w j)) hθ
  simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, LinearMap.zero_apply] at h
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)] at h
  simpa [hj] using h

end SegreFlagDegreeZero

open GenericProjClosureDivisor SegreFlagClosureModel SegreFlagDegreeZero in

theorem SegreFlagDegreeZero.proof (hModel : SegreFlagClosureModel.Statement) : SegreFlagDegreeZero.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hkN
  obtain ⟨hZ, f₀, g₀, hD₀, hv₀⟩ := hModel O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ'
    hφ hφ' Φ e t ht (k + 1) (by omega) (by omega)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨f₀, g₀, hD₀, hv₀, fun h => absurd h (lt_irrefl 0)⟩
  unfold flagClosurePt at hZ hD₀ hv₀ ⊢

  have hne : ∀ κ, ∃ j, y ⟨κ, j⟩ ≠ 0 := fun κ => by
    obtain ⟨j, hj⟩ := hV.multiProj.relevant κ
    refine ⟨j, fun h0 => hj ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    simp [pointConeMap, h0]
  choose c hc using hne
  have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun κ _ => hc κ
  have hli := ht.linearIndependent
  obtain ⟨m, hm⟩ := exists_flag_ne_zero w e hli φ'
    (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) (by omega) hkN.le
  have hϖΩ : algebraMap O Ω ϖ ≠ 0 := by
    intro h0
    have hy : ϖ ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0,
        map_zero]
    rw [hV.noTorsion] at hy
    exact hϖ.ne_zero (by simpa using hy)

  obtain ⟨n, r, hr, hx⟩ :=
    TwistedDualGensExpress.proof O ϖ Ω K ι y N E B B' hB a₀ a₀' M M' φ φ' hφ hφ' c hyc m
  obtain ⟨bG, bH, G, hG, hdeg, hval⟩ :=
    express_forms (M := M) (M' := M') y w φ φ' (flagCoord w e t (k + 1)) c hyc ϖ φ (φ' m) a₀ a₀' n r hr hx
  obtain ⟨H, hHdef⟩ : ∃ H : MRing (bundleIdx (bundleIdx ι M) M') O, H = C (ϖ ^ n) * chartMonoZ O M M' c bH :=
    ⟨_, rfl⟩
  rw [← hHdef] at hval
  have hHhom : IsMultiHomog H (vdeg bH) := by
    have := (isWeightedHomogeneous_C (blockWeight (bundleIdx (bundleIdx ι M) M')) (ϖ ^ n)).mul
      (chartMonoZ_homog (O := O) (M := M) (M' := M') c bH)
    rw [hHdef]
    rwa [zero_add] at this

  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Ω, ∀ (κ : K) (i : ι κ),
      y₀ ⟨some (some κ), i⟩ = y ⟨κ, i⟩ := ⟨pairProjCoord y w φ φ' (0 : Fin N → Ω), fun κ i => by
        simp [pairProjCoord, projCoord]⟩
  have hV' : ∀ {β : K → ℕ} {F : MRing (bundleIdx (bundleIdx ι M) M') O}, IsMultiHomog F (vdeg β) →
      ∀ u : Fin N → Φ, aeval (pairProjCoord y w φ φ' u) F = algebraMap Ω Φ (aeval y₀ F) := by
    intro β F hF u
    rw [← MvPolynomial.aeval_algebraMap_apply]
    exact aeval_eq_of_vdeg (fun κ i => by simp [pairProjCoord, projCoord, hy₀]) hF

  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual Ω E, χ = aeval y₀ H • φ' m - ∑ l, aeval y₀ (G l) • φ l := ⟨_, rfl⟩
  have hχgen : ∀ u : Fin N → Φ, genVal w u χ = algebraMap Ω Φ (aeval y₀ H) * genVal w u (φ' m) -
      ∑ l, algebraMap Ω Φ (aeval y₀ (G l)) * genVal w u (φ l) := by
    intro u
    have hsub : ∀ ψ₁ ψ₂ : Module.Dual Ω E, genVal w u (ψ₁ - ψ₂) = genVal w u ψ₁ - genVal w u ψ₂ := by
      intro ψ₁ ψ₂
      simp only [genVal, LinearMap.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
    rw [hχ, hsub, genVal_smul]
    simp only [genVal_sum_smul]
  have h1 : genVal w (flagCoord w e t (k + 1)) χ = 0 := by
    simp only [hV' hHhom, hV' (hG _)] at hval
    rw [hχgen, hval, sub_self]
  have hχw := flag_eq_zero w e hli χ h1
  have hvanish : ∀ ψ : Module.Dual Ω E, (∀ j : Fin N, (j : ℕ) < k + 1 → ψ (w j) = 0) →
      genVal w (flagCoord w e t k) ψ = 0 := by
    intro ψ hψ
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [flagCoord]
    split_ifs with hj
    · rw [hψ j (by omega), map_zero, mul_zero]
    · rw [zero_mul]
  have hid : ∀ u : Fin N → Φ, genVal w u χ = 0 → aeval (pairProjCoord y w φ φ' u) H * genVal w u (φ' m) =
      ∑ l, aeval (pairProjCoord y w φ φ' u) (G l) * genVal w u (φ l) := by
    intro u hu
    rw [hχgen, sub_eq_zero] at hu
    simp only [hV' hHhom, hV' (hG _)]
    exact hu

  have hval3 : ∀ u : Fin N → Φ, genVal w u χ = 0 → aeval (pairProjCoord y w φ φ' u) (∑ l, X ⟨some none, l⟩ * G l) =
      aeval (pairProjCoord y w φ φ' u) (X ⟨none, m⟩ * H) := fun u hu =>
    val_pair (z := pairProjCoord y w φ φ' u) (v := fun l => genVal w u (φ l)) (w := genVal w u (φ' m))
      (fun l => aeval_X _ _) G (aeval_X _ _) H (hid u hu)
  have hHne : ∀ u : Fin N → Φ, aeval (pairProjCoord y w φ φ' u) H ≠ 0 := by
    intro u
    rw [hHdef, map_mul, aeval_C, aeval_chartMonoZ, IsScalarTower.algebraMap_apply O Ω Φ]
    refine mul_ne_zero ((map_ne_zero _).mpr (by rw [map_pow]; exact pow_ne_zero _ hϖΩ))
      ((map_ne_zero _).mpr (Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hc κ)))
  have hgv : ∀ u : Fin N → Φ, genVal w u (φ' m) ≠ 0 → aeval (pairProjCoord y w φ φ' u) (X ⟨none, m⟩ * H) ≠ 0 := by
    intro u hu
    rw [map_mul, aeval_X]
    exact mul_ne_zero hu (hHne u)
  have hs₁ : genVal w (flagCoord w e t (k + 1)) (φ' m) ≠ 0 := by
    intro h0
    exact hm (hvanish (φ' m) (flag_eq_zero w e hli (φ' m) h0))
  have hout : ∀ u : Fin N → Φ, genVal w u χ = 0 → genVal w u (φ' m) ≠ 0 →
      (∑ l, X ⟨some none, l⟩ * G l) ∉ pointIdeal O (pairProjCoord y w φ φ' u) ∧
        X ⟨none, m⟩ * H ∉ pointIdeal O (pairProjCoord y w φ φ' u) := by
    intro u hu hu'
    refine ⟨fun hm' => hgv u hu' ?_, fun hm' => hgv u hu' (aeval_eq_zero_of_mem hm')⟩
    rw [← hval3 u hu]
    exact aeval_eq_zero_of_mem hm'

  have hdeg3 : ∃ bf bg : Option (Option K) → ℕ, IsMultiHomog (∑ l, X ⟨some none, l⟩ * G l) bf ∧
      IsMultiHomog (X ⟨none, m⟩ * H) bg ∧ (fun o => (bf o : ℤ) - bg o) = zetaFirst a₀ - zetaSecond a₀' := by
    refine ⟨Pi.single (some none) 1 + vdeg bG, Pi.single none 1 + vdeg bH, ?_, ?_, ?_⟩
    · exact IsWeightedHomogeneous.sum _ _ _ fun l _ =>
        IsWeightedHomogeneous.mul (isWeightedHomogeneous_X O _ _) (hG l)
    · exact IsWeightedHomogeneous.mul
        (isWeightedHomogeneous_X O (blockWeight (bundleIdx (bundleIdx ι M) M')) ⟨none, m⟩) hHhom
    · funext o
      rcases o with _ | _ | κ
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
      · simp [vdeg, zetaFirst, zetaSecond]
        linarith [hdeg κ]

  have hP1 : (pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t (k + 1)))).IsPrime := hZ.multiProj.isPrime
  have hcross := IsZPair.cross (⟨hD₀.degrees, hv₀⟩ : IsZPair a₀ a₀' _ f₀ g₀) (⟨hdeg3, hval3 _ h1⟩ : IsZPair a₀ a₀' _ _ _)
  obtain ⟨hf1, hg1⟩ := hout _ h1 hs₁
  obtain ⟨hf0, hg0⟩ := hout _ (hvanish χ hχw) hm
  refine ⟨_, _, IsVerticalDivisor.of_unit_off_special hdeg3 hf1 hg1 ?_, hval3 _ h1,
    fun _ => ⟨hf0, hg0, hval3 _ (hvanish χ hχw)⟩⟩
  intro W hW hPW hWr hϖW
  obtain ⟨u, v, hu, hv, huv⟩ := hD₀.unit_off_special W hW hPW hWr hϖW
  refine ⟨u, v, hu, hv, ?_⟩
  have hmem : g₀ * (u * (∑ l, X ⟨some none, l⟩ * G l) - v * (X ⟨none, m⟩ * H)) ∈
      pointIdeal O (pairProjCoord y w φ φ' (flagCoord w e t (k + 1))) := by
    rw [show g₀ * (u * (∑ l, X ⟨some none, l⟩ * G l) - v * (X ⟨none, m⟩ * H)) =
      (X ⟨none, m⟩ * H) * (u * f₀ - v * g₀) - u * (f₀ * (X ⟨none, m⟩ * H) - (∑ l, X ⟨some none, l⟩ * G l) * g₀) by ring]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ huv) (Ideal.mul_mem_left _ _ hcross)
  exact (hP1.mem_or_mem hmem).resolve_left hD₀.den_not_mem

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBundles
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem SymmetricSpanHsymm.full : SymmetricSpanHsymm.Statement := SymmetricSpanHsymm.proof

theorem DivisorIdealCycle.full : DivisorIdealCycle.Statement.{u} := DivisorIdealCycle.proof

theorem VNumCut.full : VNumCut.Statement.{u} := VNumCut.proof CutByForm.full

theorem VertCutEff.full : VertCutEff.Statement.{u} :=
  VertCutEff.proof VNumCut.full DivisorIdealCycle.full IntNumAddFirst.full

theorem LeftExpansion.full : LeftExpansion.Statement.{u} := LeftExpansion.proof VNumCut.full

theorem RightExpansion.full : RightExpansion.Statement.{u} :=
  RightExpansion.proof VertCutEff.full DivisorIdealCycle.full

theorem ExcessPositive.full : ExcessPositive.Statement.{u} := ExcessPositive.proof

theorem AvoidingFormExists.full : AvoidingFormExists.Statement.{u} := AvoidingFormExists.proof

theorem HorizontalAvoidingForm.full : HorizontalAvoidingForm.Statement.{u} :=
  HorizontalAvoidingForm.proof

theorem LeftSideAdditiveInDegree.full : LeftSideAdditiveInDegree.Statement.{u} := LeftSideAdditiveInDegree.proof

theorem RightSideMultiplicativeInForm.full : RightSideMultiplicativeInForm.Statement.{u} :=
  RightSideMultiplicativeInForm.proof DivCycleMul.full DivCycleFiniteSupport.full

theorem CommonFactorRemoval.full : CommonFactorRemoval.Statement.{u} := CommonFactorRemoval.proof DivCycleMul.full

theorem AdditivityInDivisor.full : AdditivityInDivisor.Statement.{u} :=
  AdditivityInDivisor.proof DivCycleMul.full DivCycleFiniteSupport.full IntNumAddFirst.full
    SupSpanMultiHomog.full MinimalPrimeMultiHomog.full SpecialIdealMultiHomog.full
    SpecialIdealCorresp.full SpecialQuotDim.full DimStrictDrop.full

theorem TautologicalCase.full : TautologicalCase.Statement.{u} :=
  TautologicalCase.proof IntNumAddFirst.full MinimalPrimeMultiHomog.full SupSpanMultiHomog.full
    SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full DimStrictDrop.full

theorem FlagBundlePullbackVanish.of_open (hdim : FlagBundleDim.Statement) :
    FlagBundlePullbackVanish.Statement :=
  FlagBundlePullbackVanish.proof FieldNumbers.ProjectionFormulaContracted.full hdim

theorem FlagBundleCut.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement) :
    FlagBundleCut.Statement :=
  FlagBundleCut.proof hdim hforms hdiv FieldNumbers.CutRational.full

theorem FlagBundleLineBase.of_open (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : FlagBundleLineBase.Statement :=
  FlagBundleLineBase.proof hdim hsec hdeg
    (FieldNumbers.ProjectionFormulaDegree.of_divPushForward
      (FieldNumbers.DivPushForward.proof FieldNumbers.ContractRelDimLe.proof hloc))

theorem NumericalSegre.of_open (hdim : FlagBundleDim.Statement)
    (hforms : FlagBundleSectionForms.Statement) (hdiv : FlagBundleSectionDiv.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hloc : FieldNumbers.DivPushForwardLocal.Statement.{0}) : NumericalSegre.Statement :=
  NumericalSegre.proof FieldNumbers.IntNumAdd.full hdim (FlagBundleCut.of_open hdim hforms hdiv)
    (FlagBundlePullbackVanish.of_open hdim) (FlagBundleLineBase.of_open hdim hsec hdeg hloc)

theorem LocalCoefficient.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    LocalCoefficient.Statement.{u} :=
  LocalCoefficient.proof hl hr hring

theorem NoCommonComponentCase.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} :=
  NoCommonComponentCase.proof LeftExpansion.full RightExpansion.full (LocalCoefficient.of_open hl hr hring)
    IntNumVanish.full

theorem BlowUpModel.of_open (hrees : ReesAlgebraDim.Statement.{u}) : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof hrees

theorem BlowUpDecomposition.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) : BlowUpDecomposition.Statement.{u} :=
  BlowUpDecomposition.proof (BlowUpModel.of_open hrees) hst

theorem BlowUpInvariance.of_open (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpInvariance.Statement.{u} :=
  BlowUpInvariance.proof hvert hdiv hhor hcomp DivCycleFiniteSupport.full

theorem BlowUpReduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : BlowUpReduction.Statement.{u} :=
  BlowUpReduction.proof (BlowUpDecomposition.of_open hrees hst)
    (BlowUpInvariance.of_open hvert hdiv hhor hcomp) CommonFactorRemoval.full AdditivityInDivisor.full
    RightSideMultiplicativeInForm.full LeftSideAdditiveInDegree.full TautologicalCase.full

theorem CommonFactorInduction.of_open (hrees : ReesAlgebraDim.Statement.{u})
    (hst : BlowUpStrictTransform.Statement.{u}) (hdrop : BlowUpExcessDecreases.Statement.{u})
    (hvert : BlowUpVerticalPush.Statement.{u}) (hdiv : BlowUpDivisorPush.Statement.{u})
    (hhor : BlowUpHorizontalCorresp.Statement.{u}) (hcomp : HorizontalComponentModel.Statement.{u}) :
    CommonFactorInduction.Statement.{u} :=
  CommonFactorInduction.proof ExcessPositive.full AvoidingFormExists.full HorizontalAvoidingForm.full
    (BlowUpDecomposition.of_open hrees hst) hdrop
    (BlowUpReduction.of_open hrees hst hvert hdiv hhor hcomp) LeftSideAdditiveInDegree.full RightSideMultiplicativeInForm.full
    DivCycleMul.full

theorem VerticalDivisorsCommute.of_open (hl : LeftTermSupport.Statement.{u})
    (hr : RightTermSupport.Statement.{u}) (hring : LocalCoeffRing.Statement.{u})
    (hrees : ReesAlgebraDim.Statement.{u}) (hst : BlowUpStrictTransform.Statement.{u})
    (hdrop : BlowUpExcessDecreases.Statement.{u}) (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) : VerticalDivisorsCommute.Statement.{u} :=
  VerticalDivisorsCommute.of_steps (NoCommonComponentCase.of_open hl hr hring)
    (CommonFactorInduction.of_open hrees hst hdrop hvert hdiv hhor hcomp)

theorem HsymmPairFlagIndependence.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    HsymmPairFlagIndependence.Statement :=
  HsymmPairFlagIndependence.proof (PairNumberExpansionIndependence.proof hC2) hclos hseg

theorem FlagIndependence.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    FlagIndependence.Statement :=
  FlagIndependence.proof (PairNumberExpansionIndependence.proof hC2)
    (HsymmPairFlagIndependence.of_open hC2 hclos hseg) SymmetricSpanHsymm.full

theorem PairCocycle.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    PairCocycle.Statement :=
  PairCocycle.proof (FlagIndependence.of_open hC2 hclos hseg) hC2 IntNumAddFirst.full

theorem SubQuotient.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    SubQuotient.Statement :=
  SubQuotient.proof (FlagIndependence.of_open hC2 hclos hseg)

theorem ScalarQuotient.of_open (hC2 : VerticalDivisorsCommute.Statement.{0})
    (hclos : GenericProjClosureModel.Statement) (hseg : SegreClosureNumber.Statement) :
    ScalarQuotient.Statement :=
  ScalarQuotient.proof (FlagIndependence.of_open hC2 hclos hseg)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.FullFlag
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open ReciprocityTheory.ChartRestriction.G.Geo

def FlagPair.fullFlag' (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type*} [Field Ω]
    [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {N : ℕ}
    {V : Type*} [AddCommGroup V] [Module Ω V] {E E' : ChartBundle O (mseg x) N V} (φ : FlagPair O x E E') :
    FullFlag O x E' where
  Vs := φ.Vs
  mono := φ.mono
  dim := φ.dim
  top := φ.top
  deg := φ.deg'
  gen := φ.gen'
  gen_mem := φ.gen'_mem
  frame := φ.frame'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FullFlagVerticalSymmetric.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    ∀ (fl₁ fl₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FullFlag O x B)
      (I : IFamily (IsLocalRing.ResidueField O) ι), IsFieldIntersection I →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric →
    ∀ (n : ℕ) (Y : Fin n → K → ℤ) (R : MvPolynomial (Fin n) ℤ) (b : K → ℤ) (f g : MRing ι O),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) b f g →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
                                (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d (Fin.append fl₁.deg Y)
                                  (rename (Fin.castAdd n) G * rename (Fin.natAdd N) R))
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) f g) =
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O
          (fun W => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum I W d (Fin.append fl₂.deg Y)
            (rename (Fin.castAdd n) G * rename (Fin.natAdd N) R))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) f g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreMore
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

def VerticalDivisorFibreVariety.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O P d →
    ∀ (b : K → ℤ) (f g : MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O P b f g →
    ∀ W ∈ (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O P f g).support,
      ReciprocityTheory.ChartRestriction.G.AI.I1.IsProjVarF (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.redIdeal O W) d

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFracCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocFamilyFinite.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      {Q : Ideal (MRing (extIdx ι J) O) | Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W}.Finite

def MultiHomogPrimeAvoid.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (S : Set (Ideal (MRing ι R))), S.Finite →
    (∀ Q ∈ S, Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q) →
    ∃ (e : K → ℕ) (L : MRing ι R), IsMultiHomog L e ∧ (∀ k, 1 ≤ e k) ∧ ∀ Q ∈ S, L ∉ Q

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

