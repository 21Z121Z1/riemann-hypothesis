import Mathlib
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0103
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0105
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EntriesOfGaps
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BigCellVectorAestronglyMeasurable
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem bigCell_vector_aestronglyMeasurable :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), ContinuousOn H (B.GPos p.T.base) →
      AEStronglyMeasurable (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) volume := by
  intro Wp Wq _ _ _ _ _ _ P p H hH
  classical
  obtain ⟨γ, hγc, hγ⟩ := GlobalTheory.T.exists_continuous_frame_section' P.k P.r Wp Wq p.T.base p.ν' p.m₀ p.hF
  set U : Set (Fin (P.r + 1) → ℂ) := {c | (∀ a, c a ≠ 0) ∧
    Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} with hU
  have hUo : IsOpen U := by
    have h1 : IsOpen {c : Fin (P.r + 1) → ℂ | ∀ a, c a ≠ 0} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun a => isOpen_ne_fun (continuous_apply a) continuous_const
    have h2 : IsOpen {c : Fin (P.r + 1) → ℂ |
        Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' < Complex.normSq (c (Fin.last P.r))} :=
      isOpen_lt continuous_const (Complex.continuous_normSq.comp (continuous_apply _))
    exact h1.inter h2
  have key : ∀ c ∈ U, γ c ∈ B.GPos p.T.base ∧ p.V H (TBB.bigPt P.r c) = B.JF p.T.base H (γ c) := by
    intro c hc
    obtain ⟨g1, g2, g3⟩ := hγ c hc.1 hc.2
    exact ((GlobalTheory.T.besselBigCellPoint_vector_eq_bessel Wp Wq P p H c).2 hc).2 (γ c) g1 g2 g3
  have hm : AEStronglyMeasurable (fun c => B.JF p.T.base H (γ c)) (volume.restrict U) := by
    refine GlobalTheory.T.aestronglyMeasurable_besselFunction_continuousFamily P.k P.r Wp Wq p.T.base _ volume U γ (B.GPos p.T.base) H hUo hγc ?_ hH
    intro c hc q hq
    have h := (key c hc).1
    exact ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem _ hq h.1, by
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs _ hq]; exact h.2⟩
  have he : (fun c : Fin (P.r + 1) → ℂ => p.V H (TBB.bigPt P.r c)) =
      U.indicator (fun c => B.JF p.T.base H (γ c)) := by
    funext c
    by_cases hc : c ∈ U
    · rw [Set.indicator_of_mem hc]; exact (key c hc).2
    · rw [Set.indicator_of_notMem hc]; exact (GlobalTheory.T.besselBigCellPoint_vector_eq_bessel Wp Wq P p H c).1 hc
  rw [he]
  exact (aestronglyMeasurable_indicator_iff hUo.measurableSet).2 hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormTranslatePowerCombLeCoprimeTranslationStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  first | exact @GlobalTheory.MomOne.TranslNorm.norm_law | exact GlobalTheory.MomOne.TranslNorm.norm_law | (intros; apply GlobalTheory.MomOne.TranslNorm.norm_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyLiftOfSmoothComm
section
namespace GlobalTheory.HatNF.SmoothLift

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem opApply_JF (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (m : ℕ) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (Θ : B.DiffOp k r Wp Wq) (ho : B.opOrder Θ ≤ m) (hT : TransportedAlt k r A m) (hF : B.InCC A m F)
    (g : B.Mat k r) (hg : g ∈ Om k r D.z D.z')
    (hC : ∀ p, D.inSS p → opApply Θ (rho D p F) g = rho D p (opApply Θ F) g) :
    B.opApply Θ (B.JF D F) g = B.JF D (B.opApply Θ F) g := by
  have hW := jacquet_derivative_formula
  have hR := rewrite_rho_action
  have hCk : CkOn (m : ℕ∞) (GV k r) F := hF.choose_spec.1
  have hgG : g ∈ GV k r := hg.1
  have key : ∀ T ∈ Θ, Integrable (fun p => xiP D p • Rw T.word (rho D p F) g) D.μSS ∧
      Rw T.word (JF D F) g = ∫ p, xiP D p • Rw T.word (rho D p F) g ∂D.μSS := by
    intro T hT'
    have hvl : T.word.length ≤ m := (B5.len_le_order Θ hT').trans ho
    set v' := T.word.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X with hv'
    have hv'u : ∀ X ∈ v', unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact B4.nrm_unit (x := (false, Y)) (T.word_lie Y hY)
    have hv'l : v'.length ≤ m := by rw [hv', List.length_map]; exact hvl
    obtain ⟨hI, hE⟩ := (hW k r Wp Wq D A m F hT hF).2 [] v' (by simp) hv'u (by simpa using hv'l) g hg
    simp only [List.map_nil] at hI hE
    have hae : (fun p => xiP D p • rho D p (dLR [] (v'.map (AdR p)) F) g) =ᵐ[D.μSS]
        fun p => xiP D p • Rw v' (rho D p F) g := by
      filter_upwards [B5.ae_inSS D] with p hp
      have := hR k r Wp Wq D m F p hp hCk [] v' (by simp) (fun X hX => (hv'u X hX).1) (by simpa using hv'l) g hgG
      simp only [List.map_nil] at this
      rw [← this]
      rfl
    have hI' : Integrable (fun p => xiP D p • Rw v' (rho D p F) g) D.μSS := hI.congr hae
    have hfun : (fun p => xiP D p • Rw T.word (rho D p F) g) =
        fun p => (B4.pn (B4.lr [] T.word) : ℝ) • (xiP D p • Rw v' (rho D p F) g) := by
      funext p
      rw [WordIntegralScaling.rw_scale T.word (rho D p F), Pi.smul_apply, smul_comm]
    refine ⟨?_, ?_⟩
    · rw [hfun]; exact hI'.smul (B4.pn (B4.lr [] T.word))
    · rw [WordIntegralScaling.rw_scale T.word (JF D F), Pi.smul_apply, hfun, integral_smul]
      congr 1
      rw [← integral_congr_ae hae]
      exact hE
  have hRHS : JF D (opApply Θ F) g = ∫ p, xiP D p • opApply Θ (rho D p F) g ∂D.μSS := by
    show (∫ p, xiP D p • rho D p (opApply Θ F) g ∂D.μSS) = _
    refine integral_congr_ae ?_
    filter_upwards [B5.ae_inSS D] with p hp
    rw [hC p hp]
  rw [hRHS]
  unfold opApply
  simp only [WordIntegralScaling.smul_list]
  obtain ⟨_, hsum⟩ := WordIntegralScaling.int_list D.μSS Θ (fun T => T.coef g)
    (fun T p => xiP D p • Rw T.word (rho D p F) g) fun T hT' => (key T hT').1
  rw [hsum]
  congr 1
  refine List.map_congr_left fun T hT' => ?_
  rw [(key T hT').2]

theorem polyLift_of_smooth_comm (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (o κ : ℕ)
    (Θ : B.DiffOp P.k P.r Wp Wq) (a : RA P Bs) (hP : CutMP.PolyOp o κ Θ)
    (hC : ∀ p, Bs.inSS p → ∀ f : B.Mat P.k P.r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV P.k P.r) f →
      ∀ g ∈ B.GPos Bs, B.opApply Θ (B.rho Bs p f) g = B.rho Bs p (B.opApply Θ f) g)
    (hres : ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus P.k P.r Bs.z Bs.z'),
      ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = Q.resG P.k P.r (Fin.last P.r) J x.1 x.2) →
      ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', (a.1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.resG P.k P.r (Fin.last P.r) (B.opApply Θ J) x.1 x.2) :
    PolyLift P Bs o κ a := by
  refine ⟨Θ, hP, fun F hF Φ hΦ x hx => ?_⟩
  obtain ⟨ε, hε, hN⟩ := (compact_support_facts P.k P.r Wp Wq Bs F hF).1
  have hJ := bessel_function_finite_class P.k P.r Wp Wq Bs F ε hε hN
  rw [hres _ hJ Φ hΦ x hx]
  have hom : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ Om P.k P.r Bs.z Bs.z' :=
    ⟨TLB.wCell_gv Bs hx, P5.Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hx.1 hx.2.1 hx.2.2⟩
  simp only [Q.resG]
  rw [opApply_JF Bs _ (B.opOrder Θ) F Θ le_rfl (JFxG.thr_big P.k P.r (B.opOrder Θ)) (hN.2.1 _ _) _ hom
    (fun p hp => hC p hp F hF.1 _ ⟨hom.1, hom.2.2⟩)]

end GlobalTheory.HatNF.SmoothLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunWeightsSum
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.RunDepth

theorem run_weights_sum : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → WeightAlgebra.IsF' (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (fR Tp hK j).n ∧ (kaR Tp hK j).n = (fR Tp hK j).n + Tp.TO * (lR Tp hK j).n ∧ WeightFamilies.dimY D j ≤ Tp.TO ∧ D.R.r ≤ (fR Tp hK j).n := by
  intro D L Pm Tp hK j hj
  have hP : (fR Tp hK j).n = Tp.nP := rfl
  have hW : (lR Tp hK j).n = Tp.nWn := rfl
  refine ⟨GlobalTheory.RunWeightTest.isF'_fWt _ _ _ _ _ _, ?_, ?_, ?_⟩
  · rw [hP, hW, ← Tp.split]; exact kaWt_n D hK _ j
  · rw [GlobalTheory.DepthBoundTest.dimY_eq_flag hj, ← Tp.Dp_eq]
    have := Tp.TO_40
    omega
  · rw [hP, Tp.nP_eq]
    have hf : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
    nlinarith

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLogPrimeDepthBoundsLeMulWeightSize
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.PtTie

theorem depth_sum_le_PN : ∀ (D : D7) (large₂ : SizeData₂ D) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ w.n → Real.log (WeightAlgebra.DF w) ≤ 2 * large₂.sc.L → (WeightAlgebra.DF w : ℝ) * (Real.log (WeightAlgebra.DF w) + 2.2) + (c2 D w * Real.log D.host.QS + cHalf w * Real.log D.host.q + cHalf w * Real.log D.host.d) + ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤ WeightAlgebra.PN D large₂ * w.size := by
  intro D large₂ j w _ hlog
  obtain ⟨-, -, hM, hG, hc, -⟩ := GlobalTheory.RunIn.pPow_size D j w
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log (WeightAlgebra.DF w : ℝ) := Real.log_natCast_nonneg _
  have hs : (WeightAlgebra.DF w : ℝ) + 1 ≤ w.size := by
    have e : ((WeightAlgebra.DF w : ℕ) : ℝ) = ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by
      simp [WeightAlgebra.DF, WeightAlgebra.degP, Nat.cast_sum]
    have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by positivity
    unfold WeightFamilies.Wt.size
    linarith
  have hg2 : ∀ i, (2 : ℝ) ≤ D.host.g i := fun i => by exact_mod_cast (D.host.g_prime i).two_le
  have hterm : ∀ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤
      (WeightAlgebra.DF w : ℝ) * Real.log (D.host.g i) := fun i =>
    mul_le_mul_of_nonneg_right (div_le_self hD (by linarith [hg2 i])) (Real.log_natCast_nonneg _)
  have hsum : ∑ i : Fin 2, (WeightAlgebra.DF w : ℝ) / ((D.host.g i : ℝ) - 1) * Real.log (D.host.g i) ≤
      (WeightAlgebra.DF w : ℝ) * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
    rw [Fin.sum_univ_two, Real.log_mul (by linarith [hg2 0]) (by linarith [hg2 1])]
    linarith [hterm 0, hterm 1]
  have hP : 0 ≤ WeightAlgebra.PN D large₂ := by
    unfold WeightAlgebra.PN WeightAlgebra.lamStar
    linarith
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hs hP)
  have h1 := mul_le_mul_of_nonneg_left hlog hD
  unfold WeightAlgebra.PN WeightAlgebra.lamStar
  nlinarith

end GlobalTheory.PtTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaSpansIsLatIn
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

section General

variable {F : Type} [Field F] {K : Type} [Field K] [NumberField K] [Algebra F K] {C : Type} [AddCommGroup C]
  [Module F C] {n : ℕ} (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C)

theorem spanK_fg_of_subset [Module (𝓞 F) C] [IsScalarTower (𝓞 F) F C] (N : Submodule (𝓞 F) C) (hN : N.FG)
    (s : Set C) (hs : s ⊆ N) : (spanK z s).FG := by
  classical
  obtain ⟨t, ht⟩ := hN
  have hle : spanK z s ≤ spanK z (t : Set C) := by
    unfold spanK
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    have hf' : f ∈ Submodule.span (𝓞 F) (t : Set C) := ht ▸ hs hf
    clear hf
    induction hf' using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : z.symm (1 ⊗ₜ[F] (a • x)) =
          (RingOfIntegers.mapRingHom (algebraMap F K) a) • z.symm (1 ⊗ₜ[F] x) := by
        rw [← algebraMap_smul F a x, TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul,
          ← algebraMap_smul K (RingOfIntegers.mapRingHom (algebraMap F K) a)]
        rfl
      beta_reduce
      rw [e]
      exact Submodule.smul_mem _ _ hx
  have hfg : (spanK z (t : Set C)).FG := Submodule.fg_span (t.finite_toSet.image _)
  exact hfg.of_le hle

theorem span_spanK_eq_top (s : Set C) (hs : Submodule.span F s = ⊤) :
    Submodule.span K (spanK z s : Set (Fin n → K)) = ⊤ := by
  have h1 : ∀ f : C, z.symm (1 ⊗ₜ[F] f) ∈ Submodule.span K (spanK z s : Set (Fin n → K)) := by
    intro f
    have hf : f ∈ Submodule.span F s := hs ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (Submodule.subset_span ⟨x, hx, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [TensorProduct.tmul_add, map_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [TensorProduct.tmul_smul, ← algebraMap_smul K, map_smul]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := z.symm.surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    have e : a ⊗ₜ[F] f = a • ((1 : K) ⊗ₜ[F] f) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul]
    exact Submodule.smul_mem _ _ (h1 f)
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ (hx trivial) (hy trivial)

end General

theorem scalOfP_sK_ne_zero {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    {j : ℕ} (p : ℕ) (hp : 0 < p) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (scalOfP B hinj EX p ka wL wF T).sK ≠ 0 := by
  obtain ⟨σ⟩ : Nonempty (B.KO →+* ℂ) := inferInstance
  have h1 := fun w => (GlobalTheory.log_norm_normaliser D B hinj EX j w σ).1
  have h2 := fun a b c => ((GlobalTheory.RunIn.pPow_size D j ka).2.2.2.2.2 a b c).1
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ (h1 _))) (h1 _)) ?_
  · exact Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne')
  · exact Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (h2 _ _ _))

theorem theta_spans_isLatIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra B.KO K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (v : HeightOneSpectrum (𝓞 K)) (i : Bs.J) (z : (Fin (O.nZ i) → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j ka) (act : P → B.Cusp j ka → B.Cusp j ka), FormTie X hinj EX p ka wL wF T O v i z act → 0 < p → WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → Submodule.IsLattice B.KO (B.Mlat j ka) → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt X ka → WeightAlgebra.H2 X (scalOfP B hinj EX p ka wL wF T) ka wL wF → Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v i) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v i) := by
  intro D B P6 j X hinj EX p ka wL wF T K _ _ _ _ Bs Df S P _ _ oc O v i z act ht hp hF hn hD hM hSp h2
  have hle := Formalism.MainNotions.Gaps.T0.theta_le_msup X _ h2 hF rfl hn hD
  refine ⟨⟨?_, ?_⟩, ht.ThK_fg, ?_⟩
  · rw [ht.Th_eq]
    refine spanK_fg_of_subset z (B.Mlat j ka) hM.fg _ fun f hf => ?_
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 (hle hf)
    exact X.inc_inj ka e ▸ hg
  · rw [ht.Th_eq]
    apply span_spanK_eq_top
    rw [eq_top_iff, ← hSp, Submodule.span_le]
    intro g hg
    set c : 𝓞 B.KO := (scalOfP B hinj EX p ka wL wF T).sK *
      ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * ka.n) with hc
    have hc0 : c ≠ 0 := mul_ne_zero (scalOfP_sK_ne_zero B hinj EX p hp ka wL wF T)
      (pow_ne_zero _ (Nat.cast_ne_zero.2
        (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)))
    have hc1 : algebraMap (𝓞 B.KO) B.KO c ≠ 0 := fun h0 => hc0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
    have hmem : c • g ∈ X.Thc (scalOfP B hinj EX p ka wL wF T).sK ka :=
      ⟨_, ⟨g, hg, rfl⟩, by rw [hc, mul_smul]; rfl⟩
    have e : g = (algebraMap (𝓞 B.KO) B.KO c)⁻¹ • (c • g) := by
      rw [← algebraMap_smul B.KO c g, smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.mem_sup_right ⟨_, hmem, rfl⟩))
  · rw [eq_top_iff, ← span_spanK_eq_top z {F | X.inc ka F ∈ thetaPlain X ka wL wF T}]
    · exact Submodule.span_mono ht.ThK_ge
    · rw [eq_top_iff, ← hSp]
      exact Submodule.span_mono fun g hg => Submodule.mem_sup_right ⟨g, hg, rfl⟩

end GlobalTheory.FormTies
end

