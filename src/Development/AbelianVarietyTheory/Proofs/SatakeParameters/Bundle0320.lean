import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0313
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0314
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumTypePrimeInvariantFramesCongruentOnStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepDatum_typePrime_invariant_frames_congruent_one : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs →
  ∀ (κ : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))
    (κ' : Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1))),
  κ ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ w - w) ∈ stdAt t.X.E _ P.1) →
  κ' ∈ GLint t.X.E _ P.1 → (∀ w ∈ stdAt t.X.E _ P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (κ' w - w) ∈ stdAt t.X.E _ P.1) →
  ∀ (y : HomE t.X.E (D.R.N (t.m2 + 1)) (D.R.N (t.m2 + 1 + 1))) (y'' : Sp t.X.E (D.R.N (t.m2 + 1))),
  (∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y'' l)) →
  topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P (κ'.symm.toLinearMap ∘ₗ y ∘ₗ κ.toLinearMap) (κ.symm y'') =
    topDat t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P y y'') := by
  first | exact @GlobalTheory.TwV.AwayTopG.topDat_frames_vGs | exact GlobalTheory.TwV.AwayTopG.topDat_frames_vGs | (intros; apply GlobalTheory.TwV.AwayTopG.topDat_frames_vGs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalIsometry
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem funMoved_ptAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG t.X.E (D.R.N i) t.Pr.vGs × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β x x₁ γ hγ hx g hg p hp P v h hv
  have H := funMoved_ratA_act t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)
  have e : ratA D.host.F (A.crd i hi) * x₁.1 = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * x.1) := by
    rw [hx, hg, map_mul, map_mul, map_inv]; group
  rw [e]
  exact H

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelPrimeFunctionalsMoveRationalLatticeAutStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeFunctionals_move_rational_lattice_aut : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG X.E (D.R.N i) SG), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  first | exact @GlobalTheory.TwU.funMoved_ratA_act | exact GlobalTheory.TwU.funMoved_ratA_act | (intros; apply GlobalTheory.TwU.funMoved_ratA_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftedCharactersAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDatumChars

theorem xi_eq_of_heq {D : D7} {C C' : Formalism.L2.Host.CharFrame D} {n : NChoice D} (h : C = C')
    (T : Formalism.L2.Host.TupTied D C n) (T' : Formalism.L2.Host.TupTied D C' n) (hT : HEq T T') : T.xi = T'.xi := by
  subst h; rw [eq_of_heq hT]

theorem weil_chars : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).1 (P.tp.tup (D.nd.mu i) j) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).2 (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹) := by
  intro hL D P X A i j hj
  have hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hlev := X.recR.base.lev
  have hx : X.R.toLevCh.xiH (X.tupT (D.nd.mu i)) = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ, xi_eq_of_heq X.cfEq X.Tp P.tp X.tpEq]
  have hxi := hlev.xi (X.tupT (D.nd.mu i))
  rw [hx] at hxi
  have hm := hlev.mu0 j
  have he := hlev.eta
  have hC : X.R.toLevCh.C = P.cf := X.cfEq
  rw [hC] at hm he
  exact ⟨GlobalTheory.Mem.TupChar.chrEq_mul hm hxi, GlobalTheory.ClassScalarValue.chrEq_mul_inv hm hxi he⟩

end GlobalTheory.WeilDatumChars
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLanglandsSplitQpStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_split_qp : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : GlobalTheory.NPin.Pin hL D) (i : D.nd.Loc) (j : Fin D.R.m), j.1 + 1 = D.nd.j i → ∀ (k : Fin 2) (w : PlE D.host) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w), (∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n), Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) → P.T.e w (rcw n π) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) → D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 (((P.tp.tup (D.nd.mu i) j).loc w).comp (Units.map e.toMonoidHom)))) := by
  first | exact @GlobalTheory.SerChar.locG_muC_eq_rcw | exact GlobalTheory.SerChar.locG_muC_eq_rcw | (intros; apply GlobalTheory.SerChar.locG_muC_eq_rcw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModerateGrowthDefiniteThetaIntegralVectorForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open MeasureTheory Formalism.IndefR.Datum Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
namespace GlobalTheory.ThetaLiftGrowth

theorem modGrowth_thetaIntegral : ∀ {D : D7} (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D)
    (χS χT : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
    IsWeilDatumO ψ V W χS χT om → (∀ τ, (gramAt D V τ).PosDef) →
    ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO V W → ℂ)),
    (∀ x, IsThetaFunO ψ V W (L x)) → ∀ u : GA D V → X, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) →
    GlobalTheory.Grow.ModGrowth W (fun g => ∫ h in 𝓕, thetaKO om h g (L (u h)) ∂ν) := by
  intro D ψ V W χS χT om hom hV ν 𝓕 hν h𝓕 X _ _ _ L hL u hu hinv
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.definite_unitary_cocompact V hV
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  let b := Module.finBasis ℂ X
  have hgr := fun k => GlobalTheory.Core.Rk.ThetaGrowthBoth.thetaKO_modGrowth₂ D ψ V W χS χT om hom (L (b k)) (hL _)
  choose C A hCA using hgr
  have hM : ∀ k, ∃ M : ℝ, ∀ c ∈ K, ‖b.coord k (u c)‖ ≤ M := fun k =>
    hK.exists_bound_of_continuousOn ((b.coord k).continuous_of_finiteDimensional.comp hu).continuousOn
  choose M hM using hM
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓕 hν h𝓕
  have hdec : ∀ h g, thetaKO om h g (L (u h)) = ∑ k, b.coord k (u h) * thetaKO om h g (L (b k)) := by
    intro h g
    conv_lhs => rw [← b.sum_repr (u h)]
    simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply]
  have hθinv : ∀ γ ∈ GQ V, ∀ c g (f : WO V W → ℂ), IsThetaFunO ψ V W f → thetaKO om (γ * c) g f = thetaKO om c g f := by
    intro γ hγ c g f hf
    have e : (γ * c, g) = ((γ, 1) : GA D V × GA D W) * (c, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ hf)
  set H' := max H 1 with hH'
  set N := ∑ k, A k with hN
  set B := ∑ k, |M k| * |C k| with hB
  have hb : ∀ g h, ‖thetaKO om h g (L (u h))‖ ≤ B * (H' * GlobalTheory.Grow.height W g) ^ N := by
    intro g h
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hdec, hB, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, hinv γ hγ c, hθinv γ hγ c g _ (hL _)]
    have h1c := GlobalTheory.Grow.one_le_height V c
    have h1g := GlobalTheory.Grow.one_le_height W g
    have hcH : GlobalTheory.Grow.height V c ≤ H' := (hH c hc).trans (le_max_left _ _)
    have hx1 : 1 ≤ GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g := one_le_mul_of_one_le_of_one_le h1c h1g
    have hxy : GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g ≤ H' * GlobalTheory.Grow.height W g :=
      mul_le_mul_of_nonneg_right hcH (by linarith)
    have hθ : ‖thetaKO om c g (L (b k))‖ ≤ |C k| * (H' * GlobalTheory.Grow.height W g) ^ N := by
      refine (hCA k c g).trans ?_
      refine mul_le_mul (le_abs_self _) ?_ (by positivity) (abs_nonneg _)
      calc (GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g) ^ A k
          ≤ (H' * GlobalTheory.Grow.height W g) ^ A k := pow_le_pow_left₀ (by linarith) hxy _
        _ ≤ (H' * GlobalTheory.Grow.height W g) ^ N :=
          pow_le_pow_right₀ (hx1.trans hxy) (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    calc ‖b.coord k (u c)‖ * ‖thetaKO om c g (L (b k))‖
        ≤ |M k| * (|C k| * (H' * GlobalTheory.Grow.height W g) ^ N) :=
          mul_le_mul ((hM k c hc).trans (le_abs_self _)) hθ (norm_nonneg _) (abs_nonneg _)
      _ = |M k| * |C k| * (H' * GlobalTheory.Grow.height W g) ^ N := by ring
  refine ⟨B * H' ^ N * ν.real 𝓕, N, fun g => ?_⟩
  calc ‖∫ h in 𝓕, thetaKO om h g (L (u h)) ∂ν‖ ≤ B * (H' * GlobalTheory.Grow.height W g) ^ N * ν.real 𝓕 :=
        norm_setIntegral_le_of_norm_le_const hfin fun h _ => hb g h
    _ = B * H' ^ N * ν.real 𝓕 * GlobalTheory.Grow.height W g ^ N := by rw [mul_pow]; ring

end GlobalTheory.ThetaLiftGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiplicitySpaceAllLevelsValuesSmoothCuspidal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct ComplexOrder
open Formalism.IndefR Formalism.IndefR.Mult Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.MinfCusp

theorem minf_val_autCusp : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : Formalism.BasicNotions.TH.HSp D}
    {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} {n : ℕ} (P : principalLevelFrame.RowPsi V n) (M : DSModel V S),
    ∀ T ∈ principalLevelFrame.Minf θ P M, ∀ v : M.Vec, IsAutFunSm θ V (T v) ∧ IsCuspFun V (T v) := by
  intro D θ V S n P M T hT v
  obtain ⟨N, hN⟩ := (principalLevelFrame.mem_Minf (θ := θ) (P := P) (M := M)).1 hT
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M _ _ T).1 hN
  exact ⟨h.aut v, h.cusp v⟩

end GlobalTheory.MinfCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormaliserGLintEqScalarMulGLint
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.NormaliserGLint

open Matrix

theorem exists_unif (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, Formalism.UG.IsUnifV F v ϖ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F), ?_⟩
  unfold Formalism.UG.IsUnifV
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  rfl

theorem mul_entries_mem {L : Type} [Field L] (O : Subring L) {n : ℕ} {A B : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) : ∀ i j, (A * B) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => O.mul_mem (hA i k) (hB k j)

theorem mulVec_entries_mem {L : Type} [Field L] (O : Subring L) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    {z : Fin n → L} (hA : ∀ i j, A i j ∈ O) (hz : ∀ i, z i ∈ O) : ∀ i, (A *ᵥ z) i ∈ O := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => O.mul_mem (hA i k) (hz k)

theorem le_of_zpow_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {p q : ℤ} {w : v.adicCompletion F}
    (hw : w ∈ Formalism.UG.Ov F v) (h : ϖ ^ q = ϖ ^ p * w) : p ≤ q := by
  have hv := congrArg Valued.v h
  rw [map_mul, map_zpow₀, map_zpow₀, hϖ] at hv
  have hw' : Valued.v w ≤ 1 := hw
  have key : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ q ≤
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ p := by
    rw [hv]; exact mul_le_of_le_one_right' hw'
  rw [← WithZero.coe_zpow, ← WithZero.coe_zpow, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zsmul,
    Multiplicative.ofAdd_le] at key
  simp at key
  omega

end GlobalTheory.NormaliserGLint

namespace GlobalTheory.NormaliserGLint

open Matrix

theorem conj_eq_glint_mul_mul :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (N : GL (Fin n) (v.adicCompletion F)),
    (∀ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ z : Fin n → v.adicCompletion F, (∀ i, z i ∈ Formalism.UG.Ov F v) →
      ∃ z' : Fin n → v.adicCompletion F, (∀ i, z' i ∈ Formalism.UG.Ov F v) ∧
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec
            ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z) =
          (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z') →
    ∀ X : Matrix (Fin n) (Fin n) (v.adicCompletion F), ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
      ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X *
            (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro F _ _ v n N hN X
  obtain ⟨ϖ, hϖ⟩ := exists_unif F v
  have hϖO : ϖ ∈ Formalism.UG.Ov F v := by
    change Valued.v ϖ ≤ 1
    rw [hϖ]
    exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1)
  have h0 : ϖ ≠ 0 := by rintro rfl; simp [Formalism.UG.IsUnifV] at hϖ
  obtain ⟨m, -, a, ha, b, hb, hNab⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ N
  set O := Formalism.UG.Ov F v with hO
  have hbe := Formalism.UG.P.cartan_entries_of_mem O b hb
  have hbi := Formalism.UG.P.cartan_entries_of_mem O _ (inv_mem hb)
  have hae := Formalism.UG.P.cartan_entries_of_mem O a ha
  have hai := Formalism.UG.P.cartan_entries_of_mem O _ (inv_mem ha)
  have ha1 : ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have ha2 : (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb2 : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ha1x : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ha1, Matrix.one_mul]
  have ha2x : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ha2, Matrix.one_mul]
  have key : ∀ i j : Fin n, i ≠ j → m i ≤ m j := by
    intro i j hij
    set E : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.single i j 1 with hE
    have hsq : E * E = 0 := by rw [hE]; simp [Matrix.single_mul_single_of_ne, hij.symm]
    have hEmem : ∀ r s, E r s ∈ O := by
      intro r s
      simp only [hE, Matrix.single_apply]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    have h1mem : ∀ r s, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) r s ∈ O := by
      intro r s
      rw [Matrix.one_apply]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    have hAB : ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (1 + E) *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) *
        ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (1 - E) *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1 := by
      have hpm : (1 + E) * (1 - E) = 1 := by
        rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
      simp only [Matrix.mul_assoc, ha1x]
      rw [← Matrix.mul_assoc (1 + E), hpm, Matrix.one_mul, ha2]
    obtain ⟨g, hg, hgA⟩ := Formalism.UG.P.cartan_exists_glint O _ _ hAB
      (mul_entries_mem O (mul_entries_mem O hae fun r s => O.add_mem (h1mem r s) (hEmem r s)) hai)
      (mul_entries_mem O (mul_entries_mem O hae fun r s => O.sub_mem (h1mem r s) (hEmem r s)) hai)
    have hz : ∀ k, (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
        Pi.single j 1) k ∈ O := mulVec_entries_mem O hbi fun k => by
      rw [Pi.single_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    obtain ⟨z', hz', hEq⟩ := hN g hg _ hz
    rw [hgA, hNab] at hEq
    have hL := congrArg (fun w => ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w) hEq
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, ha1x, hb2, Matrix.mul_one] at hL
    have hi := congrFun hL i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hi
    rw [← Matrix.mulVec_mulVec] at hi
    simp only [Formalism.UG.diagPow, Matrix.mul_diagonal, Matrix.mulVec_diagonal, Matrix.add_apply,
      Matrix.one_apply_ne hij, hE, Matrix.single_apply_same, zero_add, one_mul] at hi
    exact le_of_zpow_eq hϖ (mulVec_entries_mem O hbe hz' i) hi
  obtain ⟨c, hc, hD⟩ : ∃ c : v.adicCompletion F, c ≠ 0 ∧
      Formalism.UG.diagPow F v ϖ m = c • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rcases n with _ | k
    · exact ⟨1, one_ne_zero, by ext i; exact i.elim0⟩
    · refine ⟨ϖ ^ (m 0), zpow_ne_zero _ h0, ?_⟩
      ext i j
      simp only [Formalism.UG.diagPow, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs with h
      · subst h
        have hm : m i = m 0 := by
          rcases eq_or_ne i 0 with rfl | hi
          · rfl
          · exact le_antisymm (key i 0 hi) (key 0 i hi.symm)
        rw [hm, mul_one]
      · rw [mul_zero]
  refine ⟨(a * b)⁻¹, inv_mem (mul_mem ha hb), a * b, mul_mem ha hb, ?_⟩
  have hNc : (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      c • ((a * b : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [hNab, hD, Units.val_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hNi : ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    have h1 : ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1 := by
      rw [hNc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    calc _ = ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
          ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
            (c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
          rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hNi, hNc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.NormaliserGLint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceSecondStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_eigen_good_place_second : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv : InertDatum D.host.E D.R.nV v Pp), NG.OverPl Pp v → ∃ h0 : Formalism.UG.GU Dv.σw D.R.nV → ℂ, h0 ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw D.R.nV) ∧ ∀ (f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (y' : (X.R.HV j (X.tupT (D.nd.mu i))).H) (c : ℂ), X.R.extV j (X.tupT (D.nd.mu i)) y' = X.fn hμ j f' → (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real (hj ▸ f')) = (P.M.loc i).real (hj ▸ f')) → heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real (hj ▸ f')) = c • (P.M.loc i).real (hj ▸ f') → h Pp (Finsupp.single d 1) y' = c • y' := by
  first | exact @GlobalTheory.InertTransport.main | exact GlobalTheory.InertTransport.main | (intros; apply GlobalTheory.InertTransport.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalCoordsConjUnitaryStandardFormStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalCoords_conj_unitary_standard_form : ∀ (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (crd γ : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E) = J → γ ∈ UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J → cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  first | exact @GlobalTheory.unitary_conj_orthonormal | exact GlobalTheory.unitary_conj_orthonormal | (intros; apply GlobalTheory.unitary_conj_orthonormal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimensionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parts_give_dimension : ∀ D : D7, GlobalTheory.NRows.PartsGive D := by
  first | exact @GlobalTheory.NRows.Parts.main | exact GlobalTheory.NRows.Parts.main | (intros; apply GlobalTheory.NRows.Parts.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PublishedInputsCombinedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.published_inputs_combined : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.TotallyDisjointProductIrreducible → GlobalTheory.Published.MoyPrasadJacquetIso → GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.CaraianiTempered → GlobalTheory.Published.TemperedProductOfSquareIntegrable → GlobalTheory.Published.EssSquareIntegrableSegments → GlobalTheory.Published.GelfandKazhdanDual → GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.ClozelPurity → GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.HeckeLAdicCharacterAbove → GlobalTheory.Published.AlgebraicCharacterWD → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.NRows.Hypotheses₂ := by
  first | exact @GlobalTheory.NRows.HypothesesBridge.main | exact GlobalTheory.NRows.HypothesesBridge.main | (intros; apply GlobalTheory.NRows.HypothesesBridge.main <;> assumption)
end

