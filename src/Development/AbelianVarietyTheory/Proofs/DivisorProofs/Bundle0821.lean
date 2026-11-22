import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivWeierstrassPMulProdTranslateKernel
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem derivWeierstrassP_mul_prod_translate_kernel :
    ∀ (L : PeriodPair) (α : ℂ) (S : Finset ℂ), α ≠ 0 → Formalism.L2.Th1.F.MulStable L α → IsKerReps L α S →
      Even S.card → ∀ z, α * z ∉ L.lattice →
      L.derivWeierstrassP z * ∏ t ∈ S, L.derivWeierstrassP (z + t)
        = (∏ t ∈ S, L.derivWeierstrassP t) * α ^ 3 * L.derivWeierstrassP (α * z) := by
  intro L α S hα hst hS hev z hz
  have hper : ∀ z l, l ∈ L.lattice → L.derivWeierstrassP (z + l) = L.derivWeierstrassP z :=
    fun z l hl => L.derivWeierstrassP_add_coe z ⟨l, hl⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.T.prod_kernel_multiplier_translate_neg L α S L.derivWeierstrassP hS hst hper
  have hdiff : ∀ w, w ∉ L.lattice → DifferentiableAt ℂ L.derivWeierstrassP w := fun w hw =>
    (L.analyticOnNhd_derivWeierstrassP w hw).differentiableAt
  have hcancel : ∀ w : ℂ, α * (w / α) = w := fun w => mul_div_cancel₀ w hα
  have h1 : ∀ w, w ∉ L.lattice → w / α ∉ L.lattice := fun w hw h => by
    have := hst _ h
    rw [hcancel] at this
    exact hw this
  have h2 : ∀ w, w ∉ L.lattice → ∀ t ∈ S, w / α + t ∉ L.lattice := fun w hw t ht h => by
    have h3 := hst _ h
    rw [mul_add, hcancel] at h3
    have h4 := L.lattice.sub_mem h3 (hS.1 t ht).1
    rw [add_sub_cancel_right] at h4
    exact hw h4
  set c : ℂ := ∏ t ∈ S, L.derivWeierstrassP t with hc
  have key := GlobalTheory.T.eq_zero_of_odd_elliptic_of_tendsto' L
    (fun w => L.derivWeierstrassP (w / α) * ∏ t ∈ S, L.derivWeierstrassP (w / α + t)
      - c * α ^ 3 * L.derivWeierstrassP w) ?_ ?_ ?_ ?_ (α * z) hz
  · have e : α * z / α = z := mul_div_cancel_left₀ z hα
    simp only [e] at key
    exact sub_eq_zero.mp key
  · intro w hw
    have d0 : DifferentiableAt ℂ (fun w : ℂ => w / α) w := differentiableAt_id.div_const α
    refine DifferentiableAt.sub (DifferentiableAt.mul ?_ ?_) ((hdiff w hw).const_mul _)
    · exact DifferentiableAt.comp w (g := L.derivWeierstrassP) (hdiff _ (h1 w hw)) d0
    · refine DifferentiableAt.fun_finsetProd fun t ht => ?_
      exact DifferentiableAt.comp w (g := L.derivWeierstrassP) (f := fun w : ℂ => w / α + t)
        (hdiff _ (h2 w hw t ht)) (d0.add_const t)
  · intro w l _ hl
    have := k1 (w / α) (l / α) (by rw [hcancel]; exact hl)
    simp only [add_div, this, hper w l hl]
  · intro w _
    have e1 : ∏ t ∈ S, L.derivWeierstrassP (-w / α + t) = ∏ t ∈ S, L.derivWeierstrassP (w / α + t) := by
      rw [← k2 (w / α)]
      have : ∀ t ∈ S, L.derivWeierstrassP (-w / α + t) = (-1) * L.derivWeierstrassP (w / α - t) := by
        intro t _
        rw [neg_one_mul, ← L.derivWeierstrassP_neg]
        congr 1
        ring
      rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, hev.neg_one_pow, one_mul]
    simp only [e1]
    rw [neg_div, L.derivWeierstrassP_neg, L.derivWeierstrassP_neg]
    ring
  · have c0 := GlobalTheory.T.tendsto_cube_mul_derivWeierstrassP_neg_two L
    have tdiv : Filter.Tendsto (fun w : ℂ => w / α) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun w : ℂ => w / α) := continuous_id.div_const α
      simpa using this.tendsto 0
    have tdiv' : Filter.Tendsto (fun w : ℂ => w / α) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨tdiv.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact div_ne_zero hw hα
    have t1 := c0.comp tdiv'
    have t2 : Filter.Tendsto (fun w : ℂ => ∏ t ∈ S, L.derivWeierstrassP (w / α + t)) (𝓝[≠] 0) (𝓝 c) := by
      refine tendsto_finsetProd S fun t ht => ?_
      have ht' := (hdiff t (hS.1 t ht).2).continuousAt.tendsto
      have : Filter.Tendsto (fun w : ℂ => w / α + t) (𝓝[≠] 0) (𝓝 t) := by
        simpa using (tdiv.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).add_const t
      exact ht'.comp this
    have t3 := ((t1.const_mul (α ^ 3)).mul t2).sub (c0.const_mul (c * α ^ 3))
    have e : α ^ 3 * (-2) * c - c * α ^ 3 * (-2) = 0 := by ring
    rw [e] at t3
    refine t3.congr fun w => ?_
    simp only [Function.comp]
    field_simp

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalToUnitTensorIsPullbackIsIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem hom_to_topS_eq {Rg : Type} [CommRing Rg] {Z : Over (Sp Rg)} (f g : Z ⟶ topS Rg) : f = g := by
  haveI : IsIso (topS Rg).hom := by
    show IsIso ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id, ← Scheme.topIso_hom]
    infer_instance
  ext1
  rw [← cancel_mono (topS Rg).hom, Over.w f, Over.w g]

def θOver {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A ⟶ topS Rg ⊗ A :=
  lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)

theorem θOver_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θOver A) := by
  refine ⟨⟨snd (topS Rg) A, ?_, ?_⟩⟩
  · rw [θOver, lift_snd]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, θOver, lift_fst, Category.id_comp]
      exact hom_to_topS_eq _ _
    · rw [Category.assoc, θOver, lift_snd, Category.comp_id, Category.id_comp]

theorem θ_isIso {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : IsIso (θ A) := by
  haveI := θOver_isIso A
  have : θ A = (Over.forget _).map (θOver A) := rfl
  rw [this]
  exact (Over.forget _).map_isIso (θOver A)

theorem θ_fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ fA A = A.hom :=
  Over.w (θOver A)

theorem θ_pullback (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left)
    (p : X' ⟶ T) (t : T ⟶ Sp Rg) :
    (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧
      GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := by
  haveI := θ_isIso A
  refine ⟨fun h => ?_, θ_fA A, inferInstance⟩
  refine IsPullback.of_iso h (Iso.refl _) (asIso (θ A)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom]
    exact (θ_fA A).symm
  · simp

example : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (T X' : Scheme.{0}) (φ : X' ⟶ A.left) (p : X' ⟶ T)
    (t : T ⟶ Sp Rg), (IsPullback φ p A.hom t → IsPullback (φ ≫ GlobalTheory.HomFixUniv.θ A) p (GlobalTheory.HomFixUniv.fA A) t) ∧
    GlobalTheory.HomFixUniv.θ A ≫ GlobalTheory.HomFixUniv.fA A = A.hom ∧ IsIso (GlobalTheory.HomFixUniv.θ A) := θ_pullback

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealTopFormalLogConstOne
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem dIn_top_formalLog_map : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q]
    (σ : Type) (g : MvPowerSeries σ B), constantCoeff g = 1 →
      DIn (⊤ : Ideal B) (formalLog (map (algebraMap B Q) g)) := by
  intro B Q _ _ _ _ σ g hg α i
  classical
  obtain ⟨u, hu⟩ : IsUnit g := isUnit_iff_constantCoeff.mpr (by rw [hg]; exact isUnit_one)
  set φ := algebraMap B Q
  have hG : constantCoeff (map φ g) = 1 := by simp [hg]
  have hd : pderiv Q i (formalLog (map φ g)) = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv B i g) := by
    have h1 := mul_pderiv_formalLog hG i
    rw [pderiv_map] at h1
    have h2 : map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g = 1 := by
      rw [← map_mul, ← hu, Units.inv_mul, map_one]
    calc pderiv Q i (formalLog (map φ g))
        = (map φ (↑u⁻¹ : MvPowerSeries σ B) * map φ g) * pderiv Q i (formalLog (map φ g)) := by
          rw [h2, one_mul]
      _ = map φ ((↑u⁻¹ : MvPowerSeries σ B) * pderiv B i g) := by
          rw [mul_assoc, h1, map_mul]
  by_cases hα : α i = 0
  · exact ⟨0, Submodule.mem_top, by simp [hα]⟩
  · refine ⟨coeff (α - Finsupp.single i 1) ((↑u⁻¹ : MvPowerSeries σ B) * pderiv B i g),
      Submodule.mem_top, ?_⟩
    rw [natCast_mul_coeff_of_pderiv_eq hd hα, coeff_map]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealTopPowerSeriesLogStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_top_powerSeries_log : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] [Algebra ℚ Q], DIn (⊤ : Ideal B) (PowerSeries.log Q : MvPowerSeries Unit Q) := by
  first | exact @GlobalTheory.QLog.LogDiff.dIn_log | exact GlobalTheory.QLog.LogDiff.dIn_log | (intros; apply GlobalTheory.QLog.LogDiff.dIn_log <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstOriginNoethStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divConst_origin_noeth_alt : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T), Function.Injective i → IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 →
      bA * cA = algebraMap A (Localization.AtPrime QA) sA →
    ∃ (a : T) (w : Oˣ), jA bA = algebraMap T O a * (w : O) := by
  first | (exact @GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (exact GlobalTheory.VertUnitsNoeth.divConst_origin_noeth) | (intros; apply GlobalTheory.VertUnitsNoeth.divConst_origin_noeth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightEntriesSignsSizesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedWeight_entries_signs_sizes : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ i, ((W.T : ℤ) + W.Dd + 1) * |W.u1 τ i| ≤ |W.u τ i| + W.c0 + 4 * N ∧ (W.kc ≤ (i : ℕ) + 1 → W.u1 τ i ≤ 0) ∧ ((i : ℕ) < W.kc → 0 ≤ W.u1 τ i) := by
  first | exact @GlobalTheory.MeanTop.divided_entries | exact GlobalTheory.MeanTop.divided_entries | (intros; apply GlobalTheory.MeanTop.divided_entries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedWeight_gaps_block_and_bar : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (((b : ℕ) ≠ W.p → (W.T : ℤ) + W.Dd + 2 + 2 * N ≤ W.u1 τ a - W.u1 τ b) ∧ ((b : ℕ) = W.p → W.h0 ≤ 2 * W.T * (W.u1 τ a - W.u1 τ b) ∧ W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b - 3 * N)) ∧ ((b : ℕ) ≠ W.p → W.kc ≤ (a : ℕ) → W.h0 ≤ 4 * W.T * (W.u1 τ a - W.u1 τ b))) := by
  first | exact @GlobalTheory.MeanTop.divided_gaps | exact GlobalTheory.MeanTop.divided_gaps | (intros; apply GlobalTheory.MeanTop.divided_gaps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightNodesFarAndSpread
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Indef.Tree NumberField GlobalTheory.MeanTop

namespace GlobalTheory.MeanTop

theorem Wts.node_lower_int {ι : Type} {N : ℕ} (W : Wts ι N) (H : W.Hyp) (hd : W.IsDiv) (τ : ι) :
    ∀ (n : ℕ) (i : Fin N), (i : ℕ) + 1 = W.kc + n →
      -W.u τ i - (if W.p ≤ (i : ℕ) then W.c0 + 2 * (N : ℤ) else 0) - n * ((W.T : ℤ) + W.Dd + 1) ≤
        ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) := by
  intro n
  have hkp := H.kc_lt
  induction n with
  | zero =>
    intro i hi
    have h1 := (hd τ).1 i (by simpa using hi)
    have h2 := H.anchor τ i (by simpa using hi)
    have h3 : ¬ W.p ≤ (i : ℕ) := by omega
    simp [h1, h2, h3]
  | succ n ih =>
    intro i hi
    have hk := H.kc_pos
    have hlt : (i : ℕ) - 1 < N := by omega
    have hab : (i : ℕ) = ((⟨(i : ℕ) - 1, hlt⟩ : Fin N) : ℕ) + 1 := by simp; omega
    have ha : ((⟨(i : ℕ) - 1, hlt⟩ : Fin N) : ℕ) + 1 = W.kc + n := by simp; omega
    generalize (⟨(i : ℕ) - 1, hlt⟩ : Fin N) = a at hab ha
    have h1 := ih a ha
    have h2 := (hd τ).2 a i hab
    have hM : (0 : ℤ) < (W.T : ℤ) + W.Dd + 1 := by positivity
    generalize (W.T : ℤ) + W.Dd + 1 = M at h1 h2 hM ⊢
    set x := (W.u τ a - W.u τ i + if (i : ℕ) = W.p then -W.c0 - (2 * (N : ℤ) - 2) else 2) with hx
    have h3 := Int.mul_ediv_add_emod x M
    have h4 := Int.emod_lt_of_pos x hM
    rw [← h2] at h3
    have h5 : M * -W.u1 τ i = M * -W.u1 τ a + M * (W.u1 τ a - W.u1 τ i) := by ring
    have h6 : ((n + 1 : ℕ) : ℤ) * M = n * M + M := by push_cast; ring
    rw [h5, h6]
    by_cases hp : (i : ℕ) = W.p
    · have e1 : W.p ≤ (i : ℕ) := by omega
      have e2 : ¬ W.p ≤ (a : ℕ) := by omega
      rw [if_pos hp] at hx
      rw [if_neg e2] at h1
      rw [if_pos e1]
      linarith
    · rw [if_neg hp] at hx
      by_cases e1 : W.p ≤ (i : ℕ)
      · have e2 : W.p ≤ (a : ℕ) := by omega
        rw [if_pos e2] at h1
        rw [if_pos e1]
        linarith
      · have e2 : ¬ W.p ≤ (a : ℕ) := by omega
        rw [if_neg e2] at h1
        rw [if_neg e1]
        linarith

theorem nodes_far_and_spread : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : Wts ι N), W.Hyp → W.IsDiv → ∀ τ, (∀ i : Fin N, W.kc ≤ (i : ℕ) → W.w τ / (2 * W.T) ≤ -(W.u1 τ i : ℝ) ∧ W.w τ / (4 * W.T) ≤ |(W.u' τ i : ℝ)|) ∧ ∀ i l : Fin N, (W.u' τ i : ℝ) - W.u' τ l ≤ 3 / 2 * W.w τ / W.T := by
  intro ι _ N W H hd τ
  have hk := H.kc_pos
  have hkp := H.kc_lt
  have hpN := H.p_lt
  have hc0 : (0 : ℝ) ≤ W.c0 := by exact_mod_cast H.weightConst_nonneg
  have hT : 4 * (W.Dd : ℝ) + 4 ≤ W.T := by exact_mod_cast H.h1
  have hD : (0 : ℝ) ≤ W.Dd := by positivity
  have hN : (0 : ℝ) ≤ N := by positivity
  have hT0 : (0 : ℝ) < W.T := by linarith
  have hw := H.h3w τ
  have hS : 0 ≤ W.S := by
    have := H.h3cloud τ ⟨0, by omega⟩ (by simp; omega)
    have h0 : (0 : ℝ) ≤ W.u τ ⟨0, by omega⟩ := by exact_mod_cast this.1
    linarith [this.2]
  have hr : 0 ≤ W.eta + W.S + N := (abs_nonneg _).trans (H.h3node τ ⟨W.p, hpN⟩ hkp.le)
  have hNT : 4 * (N : ℝ) ≤ N * W.T := by nlinarith
  have hw0 : 0 ≤ W.w τ := by linarith
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = W.w τ / W.T := ⟨_, rfl⟩
  have hqT : W.w τ = q * W.T := by rw [hq]; field_simp
  have e2 : W.w τ / (2 * W.T) = q / 2 := by rw [hq]; field_simp
  have e4 : W.w τ / (4 * W.T) = q / 4 := by rw [hq]; field_simp
  have e3 : 3 / 2 * W.w τ / W.T = 3 / 2 * q := by rw [hq]; field_simp
  rw [e2, e4, e3]
  have hq20 : 20 * (N : ℝ) ≤ q := by
    have : 20 * (N : ℝ) * W.T ≤ q * W.T := by linarith
    exact le_of_mul_le_mul_right this hT0
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (W.T : ℝ) + W.Dd + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by linarith
  have hM1 : M ≤ 5 / 4 * W.T := by linarith
  have hM2 : (W.T : ℝ) ≤ M := by linarith
  have hu' : ∀ i : Fin N, (W.u1 τ i : ℝ) ≤ W.u' τ i ∧ (W.u' τ i : ℝ) ≤ W.u1 τ i + 3 * N ∧
      ((i : ℕ) < W.kc → (W.u' τ i : ℝ) = W.u1 τ i) := by
    intro i
    unfold Wts.u'
    by_cases h : (i : ℕ) < W.p
    · simp [h]
    · simp only [h, if_false]
      push_cast
      exact ⟨by linarith, le_rfl, fun h' => by omega⟩
  have node : ∀ i : Fin N, W.kc ≤ (i : ℕ) → q / 2 ≤ -(W.u1 τ i : ℝ) := by
    intro i hi
    have h1 := W.node_lower_int H hd τ ((i : ℕ) + 1 - W.kc) i (by omega)
    have hn : (((i : ℕ) + 1 - W.kc : ℕ) : ℝ) ≤ N := by
      have : (i : ℕ) + 1 - W.kc ≤ N := by omega
      exact_mod_cast this
    generalize (i : ℕ) + 1 - W.kc = n at h1 hn
    have h2 : -W.u τ i - (W.c0 + 2 * (N : ℤ)) - n * ((W.T : ℤ) + W.Dd + 1) ≤
        ((W.T : ℤ) + W.Dd + 1) * (-W.u1 τ i) := by
      have := H.weightConst_nonneg
      split_ifs at h1
      · exact h1
      · have : (0 : ℤ) ≤ N := by positivity
        linarith
    have h3 : -(W.u τ i : ℝ) - (W.c0 + 2 * (N : ℝ)) - n * M ≤ M * (-(W.u1 τ i : ℝ)) := by
      rw [hM]; exact_mod_cast h2
    have h4 := (abs_le.1 (H.h3node τ i hi)).2
    have h5 : (n : ℝ) * M ≤ q / 10 * M := mul_le_mul_of_nonneg_right (by linarith) hM0.le
    have h6 : q * M ≤ q * (5 / 4 * W.T) := mul_le_mul_of_nonneg_left hM1 hq0
    have h7 : M * (q / 2) ≤ M * (-(W.u1 τ i : ℝ)) := by nlinarith
    exact le_of_mul_le_mul_left h7 hM0
  have ent : ∀ i : Fin N, M * |(W.u1 τ i : ℝ)| ≤ |(W.u τ i : ℝ)| + W.c0 + 4 * N := by
    intro i
    rw [hM]
    exact_mod_cast (GlobalTheory.MeanTop.divided_entries ι N W H hd τ i).1
  refine ⟨fun i hi => ⟨node i hi, ?_⟩, fun i l => ?_⟩
  · have h1 := node i hi
    have h2 := (hu' i).2.1
    have h3 := neg_le_abs (W.u' τ i : ℝ)
    linarith
  · have up : M * (W.u' τ i : ℝ) ≤ W.S + W.c0 + 4 * N := by
      by_cases hi : (i : ℕ) < W.kc
      · rw [(hu' i).2.2 hi]
        have h1 := ent i
        have h2 := H.h3cloud τ i hi
        have h3 : (0 : ℝ) ≤ W.u τ i := by exact_mod_cast h2.1
        rw [abs_of_nonneg h3] at h1
        have h4 := mul_le_mul_of_nonneg_left (le_abs_self (W.u1 τ i : ℝ)) hM0.le
        linarith [h2.2]
      · have h1 := node i (by omega)
        have h2 := (hu' i).2.1
        have h3 : M * (W.u' τ i : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hM0.le (by linarith)
        linarith
    have lo : M * (-(W.u' τ l : ℝ)) ≤ W.w τ + (W.eta + W.S + N) + W.S + W.c0 + 4 * N := by
      have h1 := ent l
      have h2 : -(W.u' τ l : ℝ) ≤ |(W.u1 τ l : ℝ)| := by
        linarith [(hu' l).1, neg_le_abs (W.u1 τ l : ℝ)]
      have h3 := mul_le_mul_of_nonneg_left h2 hM0.le
      have h4 : |(W.u τ l : ℝ)| ≤ W.w τ + (W.eta + W.S + N) + W.S := by
        by_cases hl : (l : ℕ) < W.kc
        · have h2 := H.h3cloud τ l hl
          have h3 : (0 : ℝ) ≤ W.u τ l := by exact_mod_cast h2.1
          rw [abs_of_nonneg h3]
          linarith [h2.2]
        · have h5 := abs_le.1 (H.h3node τ l (by omega))
          rw [abs_le]
          constructor <;> linarith [h5.1, h5.2]
      linarith
    have h6 : q * W.T ≤ q * M := mul_le_mul_of_nonneg_left hM2 hq0
    have h7 : M * ((W.u' τ i : ℝ) - W.u' τ l) ≤ M * (3 / 2 * q) := by nlinarith
    exact le_of_mul_le_mul_left h7 hM0

end GlobalTheory.MeanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZero
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ValInj

theorem eq_zero_of_val_eq_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens) (b : Γ(A.left, U)), (∀ z ∈ pre u.ex U, val u.ex U b z = 0) → b = 0 := by
  intro A _ g L u hA U b hb
  haveI : Smooth A.hom := hA.smooth
  haveI : IsReduced A.left := isReduced_of_smooth A.hom
  refine GlobalTheory.ComplexPoints.eq_of_valAt'_eq A.hom U b 0 fun x hx hxU => ?_
  obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk x hx)
  have hzx : (u.ex z).left = x := by rw [hz]; rfl
  have h1 : val u.ex U b z = 0 := hb z (by show ⊤ ≤ (u.ex z).left ⁻¹ᵁ U; rw [hzx]; exact hxU)
  rw [show val u.ex U b z = valAt' (u.ex z).left U b from rfl, hzx] at h1
  rw [h1]
  unfold valAt' valAt
  split_ifs <;> simp

end GlobalTheory.ValInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPermStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted : ∀ (n : ℕ) (m : Fin n → ℕ) (j : ℕ), MvPolynomial.esymm (Fin n) ℤ j * Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_alternant | exact GlobalTheory.JSW.esymm_mul_alternant | (intros; apply GlobalTheory.JSW.esymm_mul_alternant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomologyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_local_vanishing_cohomology : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (m i : ℤ), 1 ≤ m → ∀ y : Ht q (sp B) m i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A') (_ : Algebra.Etale B A'), IsNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ y = 0 := by
  first | (exact @GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero) | (exact GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero) | (intros; apply GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeRestrictOpenImmersion
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.OpenRestrictPol

theorem exists_restrict_open : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left),
    IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ (V : Scheme.{0}) (j : V ⟶ S),
    IsOpenImmersion j → ∃ (A' : Over V) (_ : GrpObj A') (_ : IsCommMonObj A') (φ : A'.left ⟶ A.left),
    IsGrpPullback A' A j φ ∧ IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧
    Out.RelAmple A' (L.pull φ) := by
  intro S A _ _ L hA hL hr hamp V j _
  have hpb := isGrpPullback_pullback A j
  have := hA.proper
  exact ⟨(Over.pullback j).obj A, inferInstance, GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb,
    pullback.fst A.hom j, hpb, GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb, pull_isLB hL _,
    GlobalTheory.PolBaseChange.rigidified_pull hpb hr, GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL hamp hpb.1⟩

end GlobalTheory.OpenRestrictPol
end
end

