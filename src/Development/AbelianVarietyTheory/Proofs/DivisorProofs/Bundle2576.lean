import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2461
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.BergLower

open MeasureTheory ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem le_div_of_mean {β a I v S m J N : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hS0 : S ≠ 0) (hv : v ≠ ⊤)
    (hI : v = 0 → I = 0) (hβ : β * I ≤ a * v) (hJ : J * S = I) (hm : v ≤ m * S) (hN : N ≤ m⁻¹ * J) :
    β ≤ a / N := by
  rw [ENNReal.le_div_iff_mul_le (Or.inr ha0) (Or.inr hat)]
  by_cases h0 : v = 0
  · have hJ0 : J = 0 := by
      rw [hI h0] at hJ
      exact (mul_eq_zero.1 hJ).resolve_right hS0
    rw [hJ0, mul_zero, nonpos_iff_eq_zero] at hN
    simp [hN]
  · have h1 : N * v ≤ I := by
      calc N * v ≤ (m⁻¹ * J) * (m * S) := by gcongr
        _ = (m⁻¹ * m) * (J * S) := by ring
        _ ≤ 1 * I := by
          rw [hJ]
          gcongr
          exact ENNReal.inv_mul_le_one m
        _ = I := one_mul _
    have h2 : β * N * v ≤ a * v := by
      rw [mul_assoc]
      exact le_trans (by gcongr) hβ
    exact (ENNReal.mul_le_mul_iff_left h0 hv).1 h2

theorem pnorm_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

theorem le_bergOn : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  intro D j H Dw l Xo c U dict hL σ hσ G Z y hy β hβ
  classical
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨Kf, th, hr, -, -, hDU, -⟩ := hL.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := Formalism.L2.Pj.dict_dom_of hDU
  have hex : ∀ (X : Data D.host.E D.R.r), ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF := fun X => by
    choose P _ hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ, GlobalTheory.MetricWeightTest.exists_fundSet_orth X (fun τ => hG τ)⟩
  choose x0 hx0 FF hFF using fun k => hex ((U σ).X k)
  obtain ⟨P, hP, hPy, hle⟩ := hβ (x0 y.1) (FF y.1) (hx0 _) (hFF _)
  set la := modelWt (U σ) G with hla
  obtain ⟨hS0, hST, hI⟩ := GlobalTheory.LevGeo.adelicProb_mul_volFund D j H Dw l Xo c U dict hL σ hσ x0 FF
    (fun k => ⟨hx0 k, hFF k⟩)
  set Q : Frame ((U σ).X y.1).Ψ D.R.r → ℂ := ((U σ).X y.1).dom.indicator P with hQ
  have hQP : ∀ x ∈ ((U σ).X y.1).dom, ((U σ).X y.1).pnorm (la y.1) Q x = ((U σ).X y.1).pnorm (la y.1) P x :=
    fun x hx => by unfold Data.pnorm; rw [hQ, Set.indicator_of_mem hx]
  have hQS : Q ∈ ((U σ).X y.1).SS (la y.1) :=
    (GlobalTheory.DomCongr.bddSec_cusp_congr D.host.E D.R.r _ _ P Q (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
  set P' : Formalism.L2.Pj.FDSec (U σ).X := Function.update (fun _ => 0) y.1 Q with hP'
  have hP'y : P' y.1 = Q := Function.update_self _ _ _
  have hP'n : ∀ k, k ≠ y.1 → P' k = 0 := fun k hk => Function.update_of_ne hk _ _
  have hP'S : ∀ k, P' k ∈ ((U σ).X k).SS (la k) := fun k => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact hQS
    · rw [hP'n k hk]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1
  have hP'0 : ∀ k, ∀ x ∉ ((U σ).X k).dom, P' k x = 0 := fun k x hx => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact Set.indicator_of_notMem hx _
    · rw [hP'n k hk]; rfl
  have hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la := Formalism.L2.Pj.holCusp_mem_holSub _ _ hP'S
  have hsf : ∀ k, ((U σ).X k).IsSec (la k) (P' k) := fun k => (hP'S k).1.1
  have hJ := hI (fun k x => ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k) x ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _
      (hsf k).1.continuousOn (hP'0 k)).pow_const 2))
    (fun k γ hγ x hx => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf k) hγ hx])
    (fun k b hb x hx => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf k).2.1 x hx b hb])
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k)
      (cpt ((U σ).X k) (x0 k) z) ^ 2) ∂(muF ((U σ).X k) (x0 k)))
      (fun k _ hk => by simp [hP'n k hk, Formalism.L2.Pj.pnorm_zero])
    (fun h => absurd (Finset.mem_univ _) h), hP'y,
    setLIntegral_congr_fun (hFF y.1).1 (g := fun z => ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P
      (cpt ((U σ).X y.1) (x0 y.1) z) ^ 2)) (fun z hz => by simp only [hQP _ ((hFF y.1).2.1 hz)])] at hJ
  have hM := hI (fun k _ => if k = y.1 then 1 else 0) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, (if k = y.1 then (1 : ℝ≥0∞) else 0)
      ∂(muF ((U σ).X k) (x0 k))) (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl, setLIntegral_one] at hM
  set Cl := classesOver (D.sp.W j) (dict σ) (framesOn (U σ) Z) with hCl
  have hm : ∫⁻ q : AutQ (D.sp.W j), (if (dict σ q.out).1 = y.1 then (1 : ℝ≥0∞) else 0) ∂(muQ1 (D.sp.W j)) ≤
      muQ1 (D.sp.W j) Cl := by
    refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_one_le Cl)
    split_ifs with hq
    · have : q ∈ Cl := by
        have h1 := hdom q.out
        show dict σ q.out ∈ framesOn (U σ) Z
        generalize dict σ q.out = z at hq h1
        obtain ⟨k, x⟩ := z
        obtain rfl : k = y.1 := hq
        exact GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ _ x h1 hy
      simp [this]
    · exact zero_le
  have hN : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 ≤ (muQ1 (D.sp.W j) Cl)⁻¹ *
      ∫⁻ q : AutQ (D.sp.W j), ENNReal.ofReal (((U σ).X (dict σ q.out).1).pnorm (la (dict σ q.out).1)
        (P' (dict σ q.out).1) (dict σ q.out).2 ^ 2) ∂(muQ1 (D.sp.W j)) := by
    have e : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 =
        ∫⁻ q : AutQ (D.sp.W j), ‖ptN la P' (dict σ q.out)‖ₑ ^ 2 ∂(muOn (U σ) (D.sp.W j) (dict σ) Z) := by
      have := eLpNorm_nnreal_pow_eq_lintegral (p := 2) (μ := muOn (U σ) (D.sp.W j) (dict σ) Z)
        (f := fun q : AutQ (D.sp.W j) => ptN la P' (dict σ q.out)) two_ne_zero
      simpa [petE] using this
    rw [e]
    show ∫⁻ q, _ ∂((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl) ≤ _
    rw [lintegral_smul_measure, smul_eq_mul]
    refine mul_le_mul_right
      (le_trans (lintegral_mono' Measure.restrict_le_self le_rfl) (le_of_eq (lintegral_congr fun q => ?_))) _
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _)]
    rfl
  have hpos := pnorm_pos ((U σ).X y.1) (la y.1) y.2.2 hPy
  have hpt : ENNReal.ofReal (ptN la P' ⟨y.1, y.2.1⟩) ^ 2 =
      ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P y.2.1 ^ 2) := by
    rw [ENNReal.ofReal_pow hpos.le]
    show ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) (P' y.1) y.2.1) ^ 2 = _
    rw [hP'y, hQP _ y.2.2]
  refine le_trans ?_ (le_iSup₂_of_le (f := fun P (_ : P ∈ Formalism.L2.Pj.holSub (U σ).X la) =>
    ENNReal.ofReal (ptN la P ⟨y.1, y.2.1⟩) ^ 2 /
      petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2) P' hP'm le_rfl)
  rw [hpt]
  refine le_div_of_mean (ENNReal.ofReal_pos.2 (pow_pos hpos 2)).ne' ENNReal.ofReal_ne_top hS0
    (ne_top_of_le_ne_top hST (Finset.single_le_sum (f := fun k => muF ((U σ).X k) (x0 k) (FF k))
      (fun _ _ => zero_le) (Finset.mem_univ y.1)))
    (fun h => setLIntegral_measure_zero _ _ h) hle hJ ?_ hN
  rw [← hM]
  gcongr

end GlobalTheory.BergLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCorrespondencePolynomialStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_correspondence_polynomial : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A']
    (b : Sp R' ⟶ Sp R) (φ : A'.left ⟶ A.left) (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b φ) (f : A ⟶ A) (f' : A' ⟶ A')
    [IsMonHom f] [IsMonHom f'], φ ≫ f.left = f'.left ≫ φ → ∀ (x : HdR A) (x' : HdR A'), m.Corr x x' →
    ∀ Q : Polynomial R, m.Corr (Polynomial.aeval (push (dp0 R) (𝟙 _) f) Q x) (Polynomial.aeval (push (dp0 R') (𝟙 _) f') (Q.map σ) x') := by
  first | exact @GlobalTheory.DeRham.corr_aeval_push | exact GlobalTheory.DeRham.corr_aeval_push | (intros; apply GlobalTheory.DeRham.corr_aeval_push <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamRankEqCmDegree
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

namespace GlobalTheory.DeRham

theorem hdR_rank_eq_finrank_cm : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔠 : FracId (FR E)) (R : Type)
    [CommRing R] [IsDomain R] (X : Obj (FR E) 𝔠 (Sp R)) (n : ℕ), (HdR X.A ≃ₗ[R] (Fin n → R)) → n = Module.finrank ℚ E := by
  intro H E _ _ _ 𝔠 R _ _ X n e
  letI := X.grp
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim H.1 X.ab X.dim
  haveI := hfin
  haveI := hproj
  let e1 : Module.Dual R (primDR X.A) ≃ₗ[R] (Fin n → R) := e
  let e2 : primDR X.A ≃ₗ[R] Module.Dual R (Fin n → R) :=
    (Module.evalEquiv R (primDR X.A)).trans e1.symm.dualMap
  have hP : ∀ p : PrimeSpectrum R, Module.rankAtStalk (primDR X.A) p = n := by
    intro p
    rw [Module.rankAtStalk_eq_of_equiv e2, Module.rankAtStalk_eq_finrank_of_free,
      Module.finrank_eq_card_basis (Pi.basisFun R (Fin n)).dualBasis, Fintype.card_fin]
    rfl
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have h1 := hrk p
  rw [hP p] at h1
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h3
  rw [h1, ← h3, mul_comm]

end GlobalTheory.DeRham
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationChartPointReductionEqSpecialFibre
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
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem mk_algebraMap_eq_mk_baseMap (K B : Type) [Field K] [CommRing B] [Algebra (DualNumber K) B]
    (d : DualNumber K) :
    Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps}) (algebraMap (DualNumber K) B d) =
      Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})
        (baseMap K B (TrivSqZeroExt.fst d)) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨algebraMap (DualNumber K) B (TrivSqZeroExt.inl d.snd), ?_⟩
  rw [← map_mul, RingHom.comp_apply, ← map_sub]
  congr 1
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem chartPt_red : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l), spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ l = spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i := by
  intro K _ A _ A' _ i hi X Z h y1 m m' hm' him Ω δ n u θ Wo g B _ _ x l hx hxΩ hl
  set I : Ideal B := Ideal.span {algebraMap (DualNumber K) B DualNumber.eps} with hI
  set q : B →+* B ⧸ I := Ideal.Quotient.mk I with hq
  obtain ⟨h1, h2, h3⟩ := hl
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := fun p hp => hxΩ hp
  have hA : (spMap q ≫ l) ≫ A'.hom = (spMap q ≫ x ≫ i) ≫ A'.hom := by
    have e : q.comp (algebraMap (DualNumber K) B) =
        ((q.comp (baseMap K B)).comp (TrivSqZeroExt.fstHom K K K).toRingHom) :=
      RingHom.ext fun d => mk_algebraMap_eq_mk_baseMap K B d
    rw [Category.assoc, h1, Category.assoc, Category.assoc, hi.1.w, ← Category.assoc x, hx, GlobalTheory.DeRham.epsRed]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e]
  have hZ : (spMap q ≫ l) ≫ m' = (spMap q ≫ x ≫ i) ≫ m' := by
    have ha : ⊤ ≤ (spMap q ≫ l ≫ m') ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ h2
    have hb : ⊤ ≤ (spMap q ≫ x ≫ m) ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ hxm
    have e : ev (spMap q ≫ l ≫ m') Ω.1 ha = ev (spMap q ≫ x ≫ m) Ω.1 hb := by
      rw [GlobalTheory.FlagMod.ev_spMap q _ _ h2, GlobalTheory.FlagMod.ev_spMap q _ _ hxm]
      ext f
      simp only [RingHom.comp_apply]
      rw [← valR_eq_ev _ _ h2, ← valR_eq_ev _ _ hxm, h3 f, chartVal, map_add, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl : _ ∈ I), zero_mul, add_zero]
    rw [Category.assoc, Category.assoc, Category.assoc, him,
      ← GlobalTheory.FlagMod.spMap_ev (spMap q ≫ l ≫ m') Ω.2 ha, ← GlobalTheory.FlagMod.spMap_ev (spMap q ≫ x ≫ m) Ω.2 hb, e]
  exact hm'.hom_ext hZ hA

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationClassPullbackEqConstantAddEpsStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformation_class_pullback_eq_constant_add_eps : GlobalTheory.Published.AbelianDeRham → ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (g : ℕ), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → ∀ x : primDR A', ∃ b : primDR A, (liftMor (epsDP K) h).pull x = (constMor A).pull ((fibMor h).pull x) + (DualNumber.eps : DualNumber K) • (constMor A).pull b := by
  first | exact @GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps | exact GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps | (intros; apply GlobalTheory.CechKS.liftMor_pull_eq_const_add_eps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeValueEqHilbertEisensteinValue
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord defTerm)
open GlobalTheory.CMVal (modUnits unitRel)

namespace GlobalTheory.HilbFam.BrVal

theorem card_realEmb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem prod_cpow_ofReal {J : Type} (s : Finset J) (f : J → ℝ) (hf : ∀ i, 0 ≤ f i) (r : ℂ) :
    ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ r = (((∏ i ∈ s, f i : ℝ)) : ℂ) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i)]

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem defTerm_eq (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) :
    defTerm φ k z σ x =
      (∏ i, defCoord φ z x i)⁻¹ ^ k * ((‖∏ i, defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ) := by
  unfold defTerm
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, norm_prod,
    prod_cpow_ofReal _ _ (fun _ => norm_nonneg _)]

theorem defCoord_mul (φ : I → E →+* ℂ) (z : I → ℂ) (a x : E) (i : I) (ha : starRingEnd ℂ (φ i a) = φ i a) :
    defCoord φ z (a * x) i = φ i a * defCoord φ z x i := by
  simp only [defCoord, map_mul, ha]; ring

end GlobalTheory.HilbFam.BrVal

namespace GlobalTheory.HilbFam.BrVal

theorem isGVal_of_isEisValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (k : ℕ) (z : I → ℂ) (G : ℂ), Nonempty I → Even k → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsEisValue φ k Λ z G → IsGVal k L (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) ((((n : ℂ) ^ Module.finrank ℚ (FR E))⁻¹) ^ k * G) := by
  intro E _ _ _ I _ _ φ e θ τ Λ L n k z G hI hk hφ hθ hn hL hG
  obtain ⟨i0⟩ := hI
  set T : (Fin 2 → FR E) → E := fun x ↦ (x 0 : E) * θ + (x 1 : E) with hT
  have hTb : Function.Bijective T := GlobalTheory.HilbFam.EBasis.bijective_pair E (φ i0) θ (by
    rw [hθ i0, UpperHalfPlane.coe_im]; exact (UpperHalfPlane.im_pos τ).ne')
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set B : (Fin 2 → FR E) → E := fun x ↦ (n : E)⁻¹ * T x with hB
  have hBinj : Function.Injective B := fun x y h ↦ hTb.1 (mul_left_cancel₀ (inv_ne_zero hnE) h)
  have hB0 : B 0 = 0 := by simp [hB, hT]
  have hLB : ∀ x, x ∈ L ↔ B x ∈ Λ := by
    intro x
    rw [hL x]
    constructor
    · rintro ⟨y, hy, hny⟩
      have : B x = y := by
        show (n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E)) = y
        rw [← hny, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
      rw [this]; exact hy
    · intro h
      exact ⟨B x, h, by
        show (n : E) * ((n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E))) = _
        rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]⟩
  have hBu : ∀ (u : (OF E)ˣ) (x : Fin 2 → FR E), B (u • x) = algebraMap (OF E) E (u : OF E) * B x := by
    intro u x
    have h0 : ∀ j, (((u • x) j : FR E) : E) = (((u : OF E) : FR E) : E) * ((x j : FR E) : E) := by
      intro j
      rw [Pi.smul_apply, Units.smul_def, Algebra.smul_def]
      rfl
    simp only [hB, hT, h0]
    show _ = (((u : OF E) : FR E) : E) * _
    ring
  have hcoord : ∀ (x : Fin 2 → FR E) (i : I),
      coord (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) x (e i)
        = (n : ℂ) * defCoord φ z (B x) i := by
    intro x i
    have h1 : T x = (n : E) * B x := by simp only [hB]; rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]
    have h2 : defCoord φ z (T x) i = (n : ℂ) * defCoord φ z (B x) i := by
      rw [h1, defCoord_mul φ z _ _ i (by simp)]; simp
    rw [← h2]
    simp only [coord, defCoord, hT, map_add, map_mul, hφ, hθ, Equiv.symm_apply_apply, Complex.conj_ofReal]
    ring
  set b : Emb (FR E) → ℂ := fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ)) with hb
  set a : Emb (FR E) → ℂ := fun j ↦ 1 + z (e.symm j) * 1 with ha
  set d := Module.finrank ℚ (FR E) with hd
  have hcard : Fintype.card I = d := by
    rw [Fintype.card_congr e, hd, ← card_realEmb (FR E)]
  have hprod : ∀ x, ∏ j, coord b a x j = ((n : ℂ) ^ d) * ∏ i, defCoord φ z (B x) i := by
    intro x
    rw [← Equiv.prod_comp e]
    simp only [hcoord, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  set c : ℂ → ℂ := fun σ ↦ (((n : ℂ) ^ d)⁻¹) ^ k * ((((n : ℝ) ^ d : ℝ)) : ℂ) ^ (-2 * σ) with hc
  have hterm : ∀ σ x, gTerm k σ b a x = c σ * defTerm φ k z σ (B x) := by
    intro σ x
    rw [defTerm_eq, gTerm, hprod, hc]
    simp only
    rw [_root_.mul_inv, _root_.mul_pow, norm_mul, norm_pow, Complex.norm_natCast, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
    ring
  have hBne : ∀ x, x ≠ 0 → B x ≠ 0 := fun x hx h ↦ hx (hBinj (h.trans hB0.symm))
  let ι : cls L → modUnits Λ := fun q ↦ ⟨Quotient.mk _ (B q.1.out), B q.1.out, (hLB _).1 q.2.1, hBne _ q.2.2, rfl⟩
  have hinj : Function.Injective ι := by
    intro q1 q2 h
    have h' : Quotient.mk (unitRel (E := E)) (B q1.1.out) = Quotient.mk _ (B q2.1.out) := congrArg Subtype.val h
    obtain ⟨u, hu⟩ := Quotient.exact h'
    rw [← hBu] at hu
    have hx := hBinj hu
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    exact (Quotient.sound (MulAction.mem_orbit_iff.2 ⟨u, hx.symm⟩)).symm
  have hsurj : Function.Surjective ι := by
    rintro ⟨p, y, hy, hy0, hp⟩
    obtain ⟨x, hx⟩ := hTb.2 ((n : E) * y)
    have hBx : B x = y := by
      show (n : E)⁻¹ * T x = y
      rw [hx, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
    have hxL : x ∈ L := (hLB x).2 (hBx ▸ hy)
    have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (hBx ▸ hB0)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x)))
    set q0 := Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x with hq0
    have hmem : q0 ∈ cls L := by
      refine ⟨?_, ?_⟩
      · rw [← hg, Units.smul_def]; exact L.smul_mem _ hxL
      · rw [← hg]; intro h0; exact hx0 ((smul_eq_zero_iff_eq g).1 h0)
    refine ⟨⟨q0, hmem⟩, ?_⟩
    apply Subtype.ext
    show Quotient.mk _ (B q0.out) = p
    rw [← hp, ← hg, hBu g x, hBx]
    exact (Quotient.sound (show (unitRel (E := E)).r y (algebraMap (OF E) E (g : OF E) * y) from ⟨g, rfl⟩)).symm
  have hval : ∀ σ (q : cls L), gTerm k σ b a q.1.out = c σ * defTerm φ k z σ (ι q).1.out := by
    intro σ q
    obtain ⟨u, hu⟩ : (unitRel (E := E)).r (B q.1.out) (ι q).1.out :=
      Quotient.exact (Quotient.out_eq (ι q).1).symm
    rw [hu, ← hBu, ← hterm, GlobalTheory.HilbFam.gTerm_unit_smul (FR E) k σ b a u q.1.out hk]
  have hsum : ∀ σ S, HasSum (fun p : modUnits Λ ↦ defTerm φ k z σ p.1.out) S →
      HasSum (fun q : cls L ↦ gTerm k σ b a q.1.out) (c σ * S) := by
    intro σ S h
    simp only [hval]
    exact ((Equiv.hasSum_iff (Equiv.ofBijective ι ⟨hinj, hsurj⟩)).2 h).mul_left (c σ)
  have hc0 : c 0 = (((n : ℂ) ^ d)⁻¹) ^ k := by simp [hc]
  refine ⟨fun hk2 ↦ ?_, fun hk2 ↦ ?_⟩
  · have hd0 : ∀ x : E, defTerm φ k z 0 x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
      intro x; simp [defTerm]
    rw [← hc0]
    refine hsum 0 G ?_
    simp only [hd0]
    exact hG.1 hk2
  · obtain ⟨H, hHd, hHs, hH0⟩ := hG.2 hk2
    subst hk2
    have hn' : ((((n : ℝ) ^ d : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
    have hcd : Differentiable ℂ c := fun σ ↦
      (differentiableAt_const _).mul (((differentiableAt_const (-2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn'))
    refine ⟨fun σ ↦ c σ * H σ, hcd.differentiableOn.mul hHd, fun σ hσ ↦ hsum σ _ (hHs σ hσ), ?_⟩
    rw [hH0, ← hc0]

end GlobalTheory.HilbFam.BrVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPreDataLawsOfGeneratorValuesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationPreData_laws_of_generator_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R) (O : Type) [CommRing O] [StarRing O]
    [Module O D₀.X] (onB : D₀.P.OAct O), (∀ (a : O) (y : D₀.X), D₀.c (a • y) = D₀.c y ≫ onB.act a) →
    ∀ (w0 : O) (uw : LB.Gen (LB.LinComb D₀.P.L (GlobalTheory.UTau0.w0φ D₀ (onB.act w0)) GlobalTheory.UTau0.w0ε)), uw.IsGen →
    LB.Gen.Corr D₀.P.L _ _ _ _ (LB.pullGen D₀.P.L _ _ uw (eSec D₀.P.A)) (LB.oneGen D₀.P.L) →
    ∀ ψ : ∀ y : D₀.X, LB.Gen (LB.LinComb D₀.P.L (K := PUnit) (fun _ => (D₀.c y).left) (fun _ => -1)),
    GlobalTheory.UTau0.RLaws D₀ onB w0 uw ψ →
    ∃ h : ∀ y, (LB.pullGen D₀.P.L _ _ (ψ y) (jK R)).IsGen,
      letI : Module O ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).X :=
        ‹Module O D₀.X›
      ∃ oa : ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).OAct O,
        oa.onB = onB ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).PsiEven ∧
        ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R).TauBimult ∧
        TraceFormTwistIso ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) oa w0 ∧
        ∀ y, PsiUnitOn ({ D₀ with psi := fun y => LB.pullGen D₀.P.L _ _ (ψ y) (jK R), psi_gen := h } : DegPre R) y
          Set.univ := by
  first | exact @GlobalTheory.UTau0.rlaws_transfer | exact GlobalTheory.UTau0.rlaws_transfer | (intros; apply GlobalTheory.UTau0.rlaws_transfer <;> assumption)
end

