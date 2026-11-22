import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0580
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0530
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0548
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0562
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0551
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0004
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0581
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodEvaluationUnfoldingOfWittDescent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem nonempty_orthDec_zero (D : D7) (S : HSp D) : Nonempty (OrthDec S S (diagSp D 0 ![] 0 0)) :=
  ⟨{ iA := 1
     iB := 0
     isoA := by simp
     isoB := funext fun i => Fin.elim0 i
     orth := funext fun i => Fin.elim0 i
     rank_add := rfl }⟩

private theorem s_finite_of_sigma_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] : SFinite ν :=
  inferInstance

theorem evalBF_of_descent : ∀ D : D7, Descent D → EvalBF D := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ ν₀ 𝓝₀ hν₀ h𝓝₀ h1
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vW.haar
  have := s.vU.unit.1
  have : SigmaCompactSpace (UX D ρ) := inferInstance
  have : IsFiniteMeasureOnCompacts s.vU.ν := inferInstance
  have : IsLocallyFiniteMeasure s.vU.ν := inferInstance
  have : SigmaFinite s.vU.ν := inferInstance
  have : SFinite s.vU.ν := s_finite_of_sigma_finite s.vU.ν
  obtain ⟨hc0, hH0, hI0, hI, hF⟩ := GlobalTheory.T.fourierJacobi_measure_unitriangular_coordinates D ρ J s.vU ν₀ 𝓝₀ hν₀ h𝓝₀ h1
  obtain ⟨o⟩ := nonempty_orthDec_zero D J.W₀
  obtain ⟨⟨hc, hH⟩, -⟩ := GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ (diagSp D 0 ![] 0 0) ρ J.d o J.vN.ν J.vN.𝓝 J.vN.unit
  obtain ⟨hcont, hinv⟩ := GlobalTheory.T.besselUnfolding_evaluationIntegrand_continuous_invariant D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have hrel := GlobalTheory.T.flatPeriod_eq_integral_evaluationPeriods D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have habs := GlobalTheory.T.evaluationForm_absolute_convergence D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have hU := GlobalTheory.T.besselPeriod_thetaLift_unfolding D hD ψ ρ B J s φ G Φ hφ hG hΦ
  rw [funext fun h => (hrel h).2] at hU
  exact GlobalTheory.T.invariant_integral_in_stages_alt (GA D J.W) s.vW.μ (radX J.d ⊔ J.d.emb0.range) (jacGrp J.d) hc0 hc
    (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) J.μR hH0 hI0 (hH _ J.v0.haar) hI (UX D ρ) s.vU.ν (fun u => J.d.levi u.1)
    (J.d.continuous_levi.comp continuous_subtype_val).measurable hF _ hcont.measurable hinv (fun h => (hrel h).1) habs _ hU

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataTopStepStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_data_top_step : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∀ d₀, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (M' : GlobalTheory.FinPl.Lat D.sp.X') (o' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), IsSelfDualC (Yc D (j + 1)) M ∧ IsSelfDualC D.sp.X' M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) (comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h))) ∧ ((omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ≠ 0 → comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d → omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (pk W) j h)) = κ • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h))) := by
  first | exact @GlobalTheory.DatumTopAt.datum_top | exact GlobalTheory.DatumTopAt.datum_top | (intros; apply GlobalTheory.DatumTopAt.datum_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepAdelicIntegralFiniteTwistPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_adelicIntegral_finiteTwistPlaces : ∀ D : D7, ValQ D := by
  first | exact @GlobalTheory.QVal.valQ | exact GlobalTheory.QVal.valQ | (intros; apply GlobalTheory.QVal.valQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteDatumLawRationalPointsHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatumLaw_rationalPoints_half : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ) x y, IsDetRoot _ κ.1 x → IsDetRoot _ κ'.1 y → ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = ((A.chi i α κ : ℂˣ) : ℂ)⁻¹ * ((A.chi (i + 1) γ κ' : ℂˣ) : ℂ) * Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) := by
  first | exact @GlobalTheory.AdForm.RatLaw.law_rat | exact GlobalTheory.AdForm.RatLaw.law_rat | (intros; apply GlobalTheory.AdForm.RatLaw.law_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiPeriodUnfoldingOfWittDescent
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

theorem GlobalTheory.Unf.unfFB_of_descent : ∀ D : D7, Descent D → UnfFB D := by
  intro D hD ψ σ J B s vL Y G Φ hY hG hΦ
  haveI := s.vW.haar
  obtain ⟨hcnt, hdisc, hfd⟩ := GlobalTheory.RationalSubgroupFund.countable_discrete_exists_fundamentalDomain D B.V (GQ B.V ⊓ besGrp B.d B.o) inf_le_left
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  obtain ⟨hcont, hclN, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D σ B
  have hU := B.vN.unit
  have hHR : (semiMeas (flagN B.d) (embA B.d B.o) B.vA.μ B.vN.ν).IsHaarMeasure :=
    (GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L σ B.d B.o B.vN.ν B.vN.𝓝 hU).2.2 B.vA.μ B.vA.haar
  obtain ⟨𝓡, h𝓡, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hcont hclN hnorm huniq hrat B.vA B.vN.ν B.vN.𝓝
    hU.1 hU.2.1 hHR
  obtain ⟨hFc, hFi⟩ := GlobalTheory.T.unfoldedBessel_continuous_leftInvariant D hD ψ σ J B s vL Y G Φ hY hG hΦ
  obtain ⟨hI, hL⟩ := GlobalTheory.T.fourierJacobiPeriod_lift_eq_integral_unfolded D hD ψ σ J B s vL Y G Φ hY hG hΦ 𝓑 h𝓑
  have habs := GlobalTheory.Unf.BesInt.absConv_of_invariant D σ B _ hFc hFi
  have hm : ∀ h : GA D B.V, Measurable fun g : GA D B.V => unfF s vL Y G Φ (g * h) :=
    fun h => (hFc.comp (continuous_mul_right h)).measurable
  have key := GlobalTheory.quot_fubini_mean (GA D B.V) s.vW.μ (besGrp B.d B.o) (GQ B.V ⊓ besGrp B.d B.o) inf_le_right
    (GlobalTheory.BesClosed.besGrp_isClosed D B.V B.V₀ B.A B.L σ B.d B.o) hcnt hdisc B.μR hHR 𝓡 𝓑 h𝓡 h𝓑 (unfF s vL Y G Φ)
    hFc.measurable hFi hI (fun h => ((hint _ (hm h)).1).2 (habs h))
  rw [← hL] at key
  convert key using 2 with h
  have e2 : (∫ r : besGrp B.d B.o in 𝓡, unfF s vL Y G Φ (r * h) ∂B.μR) =
      ∫ h₁ in B.vA.𝓕, ∫ n in B.vN.𝓝, unfF s vL Y G Φ (n.1 * embA B.d B.o h₁ * h) ∂B.vN.ν ∂B.vA.μ :=
    (hint _ (hm h)).2 (habs h)
  rw [e2, BesLev.per, besPer]
  congr 1; funext h₁; congr 1; funext n
  exact (GlobalTheory.T.unfoldedFunction_eq_besselPeriodIntegrand D hD ψ σ J B s vL Y G Φ hΦ h h₁ n).symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf
open ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.UnitAt

variable {D : D7}

theorem incA_mul_mem_intAt {v : Pl D} {c : D.host.E} {N : ℤ} (hN : (N : 𝓞 D.host.F) ∉ v.asIdeal)
    (hint : IsIntegral ℤ (N • c)) : ∀ a ∈ intAt D (· = v), incA D c * a ∈ intAt D (· = v) := by
  intro a ha
  have hNF : (N : D.host.F) ≠ 0 := Int.cast_ne_zero.2 fun h => hN (by rw [h, Int.cast_zero]; exact zero_mem _)
  refine ⟨Ideal.mul_mem_left _ _ ha.1, ?_⟩
  have hc : finPart D (incA D c) = (1 : Af D.host.F) ⊗ₜ[D.host.F] c := rfl
  rw [map_mul, hc, ← AeUnit.idem_mul_finPart D v ha.1, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  refine GlobalTheory.HostAdeleIso.intAE_mul_mem D ?_ ha.2
  refine AddSubgroup.subset_closure ⟨_, AeUnit.inv_smul_singleV_mem v N hN, ⟨N • c, hint⟩, ?_⟩
  exact AeUnit.tmul_eq_inv_smul_tmul N hNF _ c

theorem latA_eq_latV {v : Pl D} {N M : ℕ} (hvN : (N : 𝓞 D.host.F) ∉ v.asIdeal) (hvM : (M : 𝓞 D.host.F) ∉ v.asIdeal)
    (hNI : ∀ a ∈ D.host.AA, ∃ b : 𝓞 D.host.E, algebraMap _ _ b = a * N) (hMI : (M : D.host.E) ∈ D.host.AA)
    (S : HSp D) (L : Lat S) : latA S L (· = v) = latV S L (· = v) := by
  have hN : N ≠ 0 := fun h => hvN (by rw [h, Nat.cast_zero]; exact zero_mem _)
  have hM : M ≠ 0 := fun h => hvM (by rw [h, Nat.cast_zero]; exact zero_mem _)
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨h1, h2⟩ := AlmostAll.smul_inv_mem hvN hα h0
    refine ⟨_, h1, h2, 1, rfl, b • x, L.smul_mem b hx, funext fun i => ?_⟩
    rw [AlmostAll.tmul_eq hN, ← mul_assoc, mul_comm _ a, ← hb, one_mul, Pi.smul_apply, Algebra.smul_def b]
  · refine AddSubgroup.closure_mono ?_
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain rfl : a = 1 := ha
    obtain ⟨h1, h2⟩ := AlmostAll.smul_inv_mem hvM hα h0
    refine ⟨_, h1, h2, (M : D.host.E), hMI, x, hx, funext fun i => ?_⟩
    rw [AlmostAll.tmul_eq hM, one_mul]

theorem notMem_of_coprime {A : Type} [CommRing A] [IsDedekindDomain A] {v : HeightOneSpectrum A} {T N : ℕ}
    (hT : (T : A) ∈ v.asIdeal) (h : Nat.Coprime N T) : (N : A) ∉ v.asIdeal := fun hN => by
  obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom A)
  refine (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top ?_
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hN)) (Ideal.mul_mem_left _ _ (by simpa using hT))

theorem unitAA_of_prime {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {T : ℕ} (hT : T.Prime) (hv : (T : 𝓞 D.host.F) ∈ p.v.asIdeal) (h2 : T ∉ D.host.small) (hq : T ≠ D.host.q)
    (hd : T ≠ D.host.d) (hc : Nat.Coprime (Ideal.absNorm D.host.ccK) T) : p.UnitAA := by
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
  have hint : IsIntegral ℤ D.host.sqrtMinusD := by
    refine IsIntegral.of_pow two_pos ?_
    rw [hsq]
    exact (isIntegral_natCast _).neg
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  have hd0 : (D.host.d : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hdp.ne_zero
  have h0 : D.host.sqrtMinusD ≠ 0 := fun e => by
    rw [e] at hsq
    exact hd0 (by simpa using hsq.symm)
  have hc0 : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hdT : Nat.Coprime D.host.d T := (Nat.coprime_primes hdp hT).2 hd.symm
  refine ⟨fun a ha => ⟨?_, ?_⟩, latA_eq_latV (notMem_of_coprime hv (GlobalTheory.TwV.HalfDiffInt.absNorm_coprime D hT h2 hq hd))
    (notMem_of_coprime hv hc) (fun a ha => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ha) (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D)⟩
  · refine incA_mul_mem_intAt (N := ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : ℤ))
      (by rw [Int.cast_natCast]; exact notMem_of_coprime hv (Nat.Coprime.mul_left hc hdT)) ?_ a ha
    convert hint using 1
    rw [zsmul_eq_mul, Int.cast_natCast, Nat.cast_mul, Host.xi0]
    field_simp
    linear_combination -hsq
  · refine incA_mul_mem_intAt (N := 1)
      (by rw [Int.cast_one]; exact (Ideal.ne_top_iff_one _).1 p.v.isPrime.ne_top) ?_ a ha
    rw [one_smul, Host.xi0, inv_div, div_neg, div_one]
    exact ((isIntegral_natCast _).mul hint).neg

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem unitAA_level {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt (I.rec7 l Z) k)
    (hv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.v.asIdeal) : p.UnitAA := by
  have hT : (B.T u).Prime := l.pr.T_prime u
  have h1 : Nat.Coprime (B.T u) (B.host.QS * B.host.q * B.host.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, B.T_cond u, Nat.gcd_one_left]
  have key : ∀ m, m ∣ B.host.QS * B.host.q * B.host.d → B.T u ≠ m := fun m hm e =>
    (Nat.Prime.coprime_iff_not_dvd hT).1 h1 (e ▸ hm)
  refine unitAA_of_prime p hT hv (UpperTheory.Small.not_mem_of_mod B.host (B.T_cond u)) (key _ ?_) (key _ ?_) ?_
  · exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _
  · exact Dvd.intro_left _ rfl
  · show Nat.Coprime (Ideal.absNorm B.host.ccK) _
    rw [B.ccK_top, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.FinPl.UnitAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRational
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem GlobalTheory.RatHalfDense.tmul_split {F E A : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    (a : E) (α ι : A) (u : F) (N d : ℕ)
    (h : α = ((N * d : ℕ) : F) • algebraMap F A u + ((N * d : ℕ) : F) • ι) :
    a ⊗ₜ[F] α = (algebraMap F E (((N * d : ℕ) : F) * u) * a) ⊗ₜ[F] (1 : A) + N • (((d : E) * a) ⊗ₜ[F] ι) := by
  rw [h, TensorProduct.tmul_add]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one (A := A) u, smul_smul, ← Algebra.smul_def, TensorProduct.smul_tmul]
  · have hd' : (d : E) * a = (d : F) • a := by rw [Algebra.smul_def, map_natCast]
    rw [TensorProduct.tmul_smul, hd', ← TensorProduct.smul_tmul', ← Nat.cast_smul_eq_nsmul F, smul_smul, Nat.cast_mul]

namespace GlobalTheory.RatHalfDense

variable {D : D7}

theorem coe_stdLat (n : ℕ) :
    ((Formalism.L2.Pj.stdLat D.host.E n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, GlobalTheory.LocM.Unim.mem_stdLat, intVec, Set.mem_setOf_eq]
  constructor
  · intro h k
    obtain ⟨c, hc⟩ := h k
    rw [← hc]
    exact c.isIntegral_coe
  · intro h k
    exact ⟨⟨x k, h k⟩, rfl⟩

theorem exists_nsmul_mem_stdHom (S T : HSp D) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
    (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → K • t ∈ stdHom S T := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.LocM.Unim.isLattice_stdLat (E := D.host.E) S.rank) (GlobalTheory.LocM.Unim.isLattice_stdLat (E := D.host.E) T.rank)
  refine ⟨K, hK, fun t h1 h2 => ?_⟩
  have := h t h1 h2
  rw [coe_stdLat, coe_stdLat] at this
  exact this

theorem mul_eq_zero_of_parts {e z : AE D} (he : infPart D e = 0) (hz : finPart D z = 0) : e * z = 0 := by
  rw [Formalism.IndefR.Eqv.infPart_eq_zero_iff_smul] at he
  rw [Formalism.IndefR.Eqv.finPart_eq_zero_iff_smul] at hz
  rw [← he, ← hz, smul_mul_smul_comm]
  have : Formalism.IndefR.Eqv.eFin D * Formalism.IndefR.Eqv.eInf D = 0 := by
    simp only [Formalism.IndefR.Eqv.eFin, Formalism.IndefR.Eqv.eInf, pairA]
    exact Prod.ext (show (0 : Ainf D.host.F) * 1 = 0 from zero_mul _) (show (1 : Af D.host.F) * 0 = 0 from mul_zero _)
  rw [this, zero_smul]

theorem exists_nat_mul_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_rat_add_nsmul (z : EAf D) (N : ℕ) (hN : 0 < N) :
    ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, z = eToEAf D γ + N • w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a α =>
    obtain ⟨d, hd, hda⟩ := exists_nat_mul_isIntegral a
    have hc : ((N * d : ℕ) : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_pos hN hd).ne'
    obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele
      (R := NumberField.RingOfIntegers D.host.F) (K := D.host.F) (((N * d : ℕ) : D.host.F)⁻¹ • α)
    have hα : α = ((N * d : ℕ) : D.host.F) • algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u
        + ((N * d : ℕ) : D.host.F) • (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
    refine ⟨algebraMap D.host.F D.host.E (((N * d : ℕ) : D.host.F) * u) * a,
      ((d : D.host.E) * a) ⊗ₜ (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u), ?_, ?_⟩
    · have h1 : ((d : D.host.E) * a) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨(d : D.host.E) * a, ⟨⟨(d : D.host.E) * a, hda⟩, rfl⟩⟩, rfl⟩)
      have h2 : (1 : D.host.E) ⊗ₜ[D.host.F] (((N * d : ℕ) : D.host.F)⁻¹ • α
          - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨_, hu⟩, rfl⟩)
      have := mul_mem h1 h2
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
    · exact tmul_split a α _ u N d hα
  | add x y hx hy =>
    obtain ⟨γ₁, w₁, hw₁, h₁⟩ := hx
    obtain ⟨γ₂, w₂, hw₂, h₂⟩ := hy
    refine ⟨γ₁ + γ₂, w₁ + w₂, add_mem hw₁ hw₂, ?_⟩
    rw [h₁, h₂, map_add, smul_add]
    abel

theorem exists_half_approx {S T : HSp D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {E₂ : AE D} (hE : IsIdemSum E₂ Q)
    (K : ℕ) (hK : 0 < K) (t : WO S T) (ht : IsHalf E₂ t) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ stdHom S T, IsHalf E₂ u ∧
      t = γ.map (fun a => E₂ * incA D a) + K • u := by
  obtain ⟨c, hc, hlat⟩ := exists_nsmul_mem_stdHom S T
  have hap : ∀ i j, ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      toEAf D (t i j) = eToEAf D γ + (K * c) • w := fun i j => exists_rat_add_nsmul _ (K * c) (Nat.mul_pos hK hc)
  choose γ w hw heq using hap
  choose y hy using fun i j => GlobalTheory.LocMod.exists_toEAf_lift (w i j)
  have hidem := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hE
  let m : WO S T := Matrix.of fun i j => E₂ * y i j
  refine ⟨Matrix.of γ, c • m, hlat m ?_ ?_, ?_, ?_⟩
  · ext i j
    simp only [m, Matrix.map_apply, Matrix.of_apply, map_mul, hinf, zero_mul, Matrix.zero_apply]
  · intro i j
    simp only [m, Matrix.of_apply, map_mul, hy]
    exact mul_mem (GlobalTheory.ExportSeries.toEAf_mem_intAf_of_idem hidem) (hw i j)
  · intro i j
    simp only [m, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    linear_combination ((c : AE D) * y i j) * hidem
  · ext i j
    have hfin : finPart D (t i j - incA D (γ i j) - (K * c) • y i j) = 0 := by
      have h0 : toEAf D (t i j - incA D (γ i j) - (K * c) • y i j) = 0 := by
        rw [map_sub, map_sub, nsmul_eq_mul, map_mul, map_natCast, GlobalTheory.IdemIntegral.toEAf_incA, hy, heq i j,
          nsmul_eq_mul]
        abel
      unfold toEAf at h0
      rw [RingHom.comp_apply] at h0
      exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (h0.trans (map_zero _).symm)
    have hz := mul_eq_zero_of_parts hinf hfin
    rw [mul_sub, mul_sub, sub_sub, sub_eq_zero, ht i j] at hz
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, m, Matrix.of_apply]
    rw [hz]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring

theorem eq_of_rat : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q →
    ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf E₂ (stdHom S T) Φ₁ → IsSBHalf E₂ (stdHom S T) Φ₂ →
    (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      Φ₁ (γ.map fun a => E₂ * incA D a) = Φ₂ (γ.map fun a => E₂ * incA D a)) → Φ₁ = Φ₂ := by
  intro D S T Q E₂ hE Φ₁ Φ₂ h₁ h₂ hrat
  obtain ⟨s₁, k₁, hk₁, inv₁, -⟩ := h₁
  obtain ⟨s₂, k₂, hk₂, inv₂, -⟩ := h₂
  funext t
  by_cases ht : IsHalf E₂ t
  · obtain ⟨γ, u, hu, huh, rfl⟩ := exists_half_approx hE (k₁ * k₂) (Nat.mul_pos hk₁ hk₂) t ht
    have half_smul : ∀ n : ℕ, IsHalf E₂ (n • u) := fun n i j => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, huh i j]
    have e1 : Φ₁ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₁ (γ.map (fun a => E₂ * incA D a)) := by
      rw [mul_smul]
      exact inv₁ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _
    have e2 : Φ₂ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₂ (γ.map (fun a => E₂ * incA D a)) := by
      rw [mul_comm, mul_smul]
      exact inv₂ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _
    rw [e1, e2, hrat]
  · have a1 : Φ₁ t = 0 := by
      by_contra h
      exact ht (s₁ t h)
    have a2 : Φ₂ t = 0 := by
      by_contra h
      exact ht (s₂ t h)
    rw [a1, a2]

end GlobalTheory.RatHalfDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteCellsAtTwistPlacesOfLocalFactorisatiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawFiniteCells_at_twistPlaces_of_localFactorisation : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → t.Is → v.Is → WeilOK (t := t) v → QPin v w → QFin v w := by
  first | exact @GlobalTheory.QFinMain.qFin_of_pin | exact GlobalTheory.QFinMain.qFin_of_pin | (intros; apply GlobalTheory.QFinMain.qFin_of_pin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFiniteIntegralsDoubleStepValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_finiteIntegrals_doubleStep_value : ∀ (D : D7) (c : Comm D) (v : VCom c) (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), c.Is → v.Is → (∀ s, (t s).Is) → (∀ s, PlaceLaws v (w s)) → ContrLaw D → FlatLaw D → BiAct D → ValX t := by
  first | exact @GlobalTheory.ValFin.valX | exact GlobalTheory.ValFin.valX | (intros; apply GlobalTheory.ValFin.valX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamifiedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistRamified_iff_scalarFormsRamified : GlobalTheory.AdForm.TwRam' := by
  first | exact @GlobalTheory.AdForm.ram_iff_scalar_ram | exact GlobalTheory.AdForm.ram_iff_scalar_ram | (intros; apply GlobalTheory.AdForm.ram_iff_scalar_ram <;> assumption)
end

