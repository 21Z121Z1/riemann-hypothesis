import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatBFSource
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.Unf.FB GlobalTheory.FinPl.HandInvPf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem qS_xZero {S S₀ T T₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ ρ) (c : skewA D ρ) (w : Mx D ρ ρ) :
    d.qS T c (xZero d' ⬝ w) = 0 := by
  have h : adj (xZero d' ⬝ w) ⬝ (gA T ⬝ (xZero d' ⬝ w)) = 0 := by
    rw [xZero, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj d'.jX), d'.gram_XX,
      Matrix.zero_mul, Matrix.mul_zero]
  rw [← cenS_nC, ← neg_inj, LinkPoint.neg_cenS_eq, h, Matrix.zero_mul, trace_zero, map_zero, neg_zero]

set_option maxHeartbeats 1000000 in

theorem flatBF_source {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {n : GA D B.V} (hn : n ∈ flagN B.d) :
    flatBF s (s.om (n, 1) Ψ) = psiBes ψ B.d 1 (vecB B.o B.ζ) n • flatBF s Ψ := by
  have hψ := s.weil.std
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp B.d hn
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  have hfl : psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.levi u * (B.d.nB b * B.d.nC c)) =
      psiUni ψ u * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) := by
    rw [psiBes_mul B.d ψ 1 _ (B.d.levi_mem_NFlag hu) (mul_mem (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c)),
      psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c), psiBes_nC, mul_one, psiBes_levi]
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]
    exact Finset.prod_eq_one fun i _ => (hu i i).2
  have hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod J.W.rank u = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]
  have h1 := s.weil.om_pres (B.d.nC c, 1) Ψ hΨ
  have h2 := s.weil.om_pres (B.d.nB b, 1) _ h1
  have e : s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ =
      s.om (B.d.levi u, 1) (s.om (B.d.nB b, 1) (s.om (B.d.nC c, 1) Ψ)) := by
    rw [← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]
  let u' : UX D ρ := ⟨u, hu⟩
  have key : ∀ v : UX D ρ,
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1)
          (yZero B.V₀ ρ (vecB B.o B.ζ)) =
        psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) •
          evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
    intro v
    have ex : xZero J.d ⬝ v.1.1 ⬝ u.1 = xZero J.d ⬝ (v * u').1.1 := by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    have t1 := (FS _ h2).levi u (xZero J.d ⬝ v.1.1)
    rw [hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex] at t1
    have t2 := (FS _ h1).unip b (xZero J.d ⬝ (v * u').1.1)
    rw [Matrix.mul_assoc (xZero J.d)] at t2
    have t3 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
        ψ (B.d.qS J.W c (xZero J.d ⬝ (v * u').1.1)) • B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) :=
      (FS _ hΨ).centre c _
    rw [qS_xZero, AddChar.map_zero_eq_one, one_smul] at t3
    have t4 := (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _ (MV (xZero J.d ⬝ (v * u').1.1))).1
      ((v * u').1.1 ⬝ b) (yZero B.V₀ ρ (vecB B.o B.ζ))
    have t5 : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ ((v * u').1.1 ⬝ b))) =
        psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) := by
      refine (psi_yZero ψ B.d J.d _ _).trans ?_
      rw [psiBes_nB, psiBes_nB, ← Matrix.mulVec_mulVec, dotProduct_mulVec (ell D ρ) (v * u').1.1, ell_vecMul (v * u').2]
    rw [t5] at t4
    unfold evalAt
    rw [e, t1, t2, t3]
    exact t4
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have hmul : ∀ v : UX D ρ, psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u := fun v => by
    rw [← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul,
      psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]
  have hu1 : psiUni ψ u * star (psiUni ψ u) = 1 := mul_star_psi hψ _
  funext w
  rw [hfl]
  simp only [Pi.smul_apply, smul_eq_mul]
  change ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν = _ *
    ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ v.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν
  conv_rhs => rw [← integral_mul_right_eq_self _ u', ← integral_const_mul]
  congr 1
  funext v
  rw [key, hmul, star_mul']
  simp only [Pi.smul_apply, smul_eq_mul]
  generalize evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) _ _ = z
  linear_combination (-(star (psiUni ψ v.1) * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) * z)) * hu1

theorem flatBF_bes {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Φ : WO B.V J.W → ℂ}
    (hΦ : IsThetaFunO ψ B.V J.W Φ) {n : GA D B.V} (hn : n ∈ flagN B.d) (a : GA D B.A) (g : GA D B.V) (h : GA D J.W) :
    flatBF s (s.om (n * embA B.d B.o a * g, h) Φ) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) n • s.om₀ (B.o.emb (a, 1), 1) (flatBF s (s.om (g, h) Φ)) := by
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have hΨ := s.weil.om_pres (g, h) Φ hΦ
  have c := GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ _ B J s om' hom' _ hΨ a 1 (one_mem _) 1
  have p1 : psiFlag ψ J.d 1 = 1 := by
    have := psiFlag_levi_mul ψ J.d 1 (one_mem (stabX J.d))
    rw [map_one, mul_one] at this
    rw [this, psiUni, Units.val_one, upSum_one, psiE_zero]
  rw [map_one, mul_one, p1, star_one, one_smul, opA, jacT_one, id, show s.om₀ (1, 1) = 1 from map_one _,
    Module.End.one_apply] at c
  rw [← c, ← flatBF_source s (s.weil.om_pres _ _ hΨ) hn, ← om_mul, ← om_mul, one_mul, one_mul]

theorem om_rat_line {V₀ A L S : HSp D} (o : OrthDec V₀ A L) {χ χ' : (AE D)ˣ →* Circle} {om : Om V₀ S}
    (hom : IsWeilDatumO ψ V₀ S χ χ' om) {γ : GA D A} (hγ : γ ∈ GQ A) {f : WO V₀ S → ℂ} (hf : IsThetaFunO ψ V₀ S f) (y : WO L S) :
    om (o.emb (γ, 1), 1) f ((o.resS S).symm (0, y)) = f ((o.resS S).symm (0, y)) := by
  have hact : actO V₀ S (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) = (o.resS S).symm (0, y) := by
    apply (o.resS S).injective
    rw [o.resS_actO, AddEquiv.apply_symm_apply]
    simp only [actO_eq, inv_one, mt_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]
  have h0 : ∀ F : WO V₀ S → ℂ, ∀ p, heisO ψ V₀ S p F 0 = F p := fun F p => by
    rw [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  have h1 := congrFun (hom.om_heis (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) f hf) 0
  rw [hact, h0] at h1
  rw [← h1, hom.om_aut _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf _), h0]

theorem handBF_move {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') {φ : GA D B.A → ℂ} (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g) {Ξ : WO B.V₀ J.W₀ → ℂ}
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (c : ℂ) (hc : c * star c = 1) (a : GA D B.A) :
    handBF s l (star c • rTrans a φ) (c • s.om₀ (B.o.emb (a, 1), 1) Ξ) = handBF s l φ Ξ := by
  funext h w
  unfold handBF
  congr 1
  rw [← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund
    (fun h₀ => φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) ?_ a]
  · congr 1
    funext x
    rw [map_smul, ← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, rTrans]
    linear_combination (φ (x * a) * s.om₀ (B.o.emb (x * a, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) * hc
  · intro γ hγ x
    have e : s.om₀ (B.o.emb (γ * x, 1), h) Ξ = s.om₀ (B.o.emb (γ, 1), 1) (s.om₀ (B.o.emb (x, 1), h) Ξ) := by
      rw [← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    simp only [hφ γ hγ]
    rw [e, om_rat_line B.o s.weil₀ hγ (s.weil₀.om_pres _ _ hΞ)]

theorem hand_right {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Φ₁ : WO B.V J.W → ℂ) {Φ₂ : WO J.W B'.V → ℂ}
    (hΦ₂ : IsThetaFunO ψ J.W B'.V Φ₂) (φ : GA D B.A → ℂ) (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V)
    {n : GA D B'.V} (hn : n ∈ flagN B'.d) (a : GA D B'.A) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (n * embA B'.d B'.o a * h₂) =
      star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) • rTrans a (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) := by
  have hD : Descent D := GlobalTheory.Desc.weil_data_descend D
  have hΨ₂ := s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂
  have e : flatFB s₂ (s₂.om (h₁, n * embA B'.d B'.o a * h₂) Φ₂) = star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) •
      s₂.om₀ (1, B'.o.emb (a, 1)) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := by
    have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B' s₂ _ hΨ₂ 1 a
    rw [map_one] at c
    rw [← c, ← GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B' s₂ _ (s₂.weil.om_pres _ _ hΨ₂) n hn, ← om_mul, ← om_mul, one_mul, one_mul]
  unfold Chain.hand
  rw [e, handFB_smul_om]

theorem hand_left {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {Φ₁ : WO B.V J.W → ℂ} (Φ₂ : WO J.W B'.V → ℂ)
    (hΦ₁ : IsThetaFunO ψ B.V J.W Φ₁) {φ : GA D B.A → ℂ} (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V) {n : GA D B.V} (hn : n ∈ flagN B.d) (a : GA D B.A) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ (star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • rTrans a φ) (n * embA B.d B.o a * g) h₁ h₂ =
      Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ := by
  have hΞ := (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁)
  unfold Chain.hand
  rw [flatBF_bes s₁ hΦ₁ hn, handBF_move s₁ l hφ hΞ (psiBes ψ B.d 1 (vecB B.o B.ζ) n) (mul_star_psi s₁.weil.std _)]

theorem biLift_last {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {χA χz χS : (AE D)ˣ →* Circle} {om₁ : Om V₀ S} {oma : Om A S} {omz : Om L S}
    (h₁ : IsWeilDatumO ψ V₀ S (χA * χz) χS om₁) (ha : IsWeilDatumO ψ A S χA χS oma) (hz : IsWeilDatumO ψ L S χz χS omz)
    (omb : Om S X) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : ∀ γ ∈ GQ A, ∀ g, φ (γ * g) = φ g) {Ξ : WO V₀ S → ℂ}
    (hΞ : IsThetaFunO ψ V₀ S Ξ) (Φ₂ : WO S T → ℂ) (c : ℂ) (hc : c * star c = 1) (a : GA D A) :
    GlobalTheory.SeeSaw.biLift oma omb vA vS (star c • rTrans a φ) (GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂) =
      GlobalTheory.SeeSaw.biLift oma omb vA vS φ (GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂) := by
  have hsrc := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ h₁.std V₀ A L o S
  have e0 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) =
      Φ₂ (o''.resT S v).1 • fun u => Ξ ((o.resS S).symm (u, GlobalTheory.FinPl.kap τ S (o''.resT S v).2)) := fun v => rfl
  have e1 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) =
      c • oma (a, 1) fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v := fun v => by
    funext u
    have k := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz a 1 1 Ξ hΞ (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)).2 u
    rw [show omz (1, 1) = 1 from map_one _] at k
    simp only [Module.End.one_apply] at k
    rw [e0, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.lastBi, OrthDec.boxT, k]
    ring
  funext h₂
  unfold GlobalTheory.SeeSaw.biLift
  congr 1
  funext h
  rw [← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A vA.μ vA.𝓕 vA.haar vA.fund
    (fun h₀ => φ h₀ * omb (h, h₂) (fun v => oma (h₀, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) ?_ a]
  · congr 1
    funext x
    have e2 : (fun v => oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) 0) =
        c • fun v => oma (x * a, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 := by
      funext v
      rw [e1, map_smul, ← om_mul, mul_one]
      rfl
    rw [e2, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, rTrans]
    linear_combination (φ (x * a) * omb (h, h₂) (fun v => oma (x * a, h)
      (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) * hc
  · intro γ hγ x
    have e : ∀ v, oma (γ * x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 =
        oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 := fun v => by
      have k := ha.om_aut γ hγ 1 (one_mem _) _
        (ha.om_pres (x, h) _ ((hsrc.slice_theta Ξ hΞ).1 (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)))
      rw [← om_mul, one_mul] at k
      rw [e0, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, k]
    simp only [hφ γ hγ, e]

end GlobalTheory.BesMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatScal

noncomputable section

open GlobalTheory.LocMod (Place Frame IsOne)
open GlobalTheory.SplitWeil (SB)
open GlobalTheory.SplitFlip (Grid Edge oppositePath gdet)
open GlobalTheory.FlatPlace

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def xiEdge (ξ : kˣ →* ℂˣ) : Edge → kˣ →* ℂˣ
  | .theta _ _ => ξ
  | .ex _ _ => 1

theorem kappa_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ) (b : Edge) (X : ℕ × ℕ) :
    Γ.kappa b X = ({Γ with mu := μ₀} : Grid k).kappa b X * xiEdge ξ b := by
  cases b with
  | theta i j =>
    show Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) = μ₀ (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) * ξ
    rw [h, mul_div_right_comm]
  | ex i j =>
    show Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) = Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) * 1
    rw [mul_one]

def xiPart (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) : ℂˣ :=
  ((oppositePath Γ.m).map fun b => xiEdge ξ b (gdet (g b.src)) * (xiEdge ξ b (gdet (g b.tgt)))⁻¹).prod

theorem charFactor_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ)
    (g : Γ.VertexGroup) :
    charFactor Γ g = charFactor ({Γ with mu := μ₀} : Grid k) g * xiPart Γ ξ g := by
  simp only [charFactor, xiPart, kappa_split Γ μ₀ ξ h, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  simp only [MonoidHom.mul_apply, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem xiPart_mem (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) (H : Subgroup ℂˣ) (hH : ∀ x, ξ x ∈ H) :
    xiPart Γ ξ g ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  have e : ∀ u, xiEdge ξ b u ∈ H := fun u => by
    cases b with
    | theta _ _ => exact hH u
    | ex _ _ => exact H.one_mem
  exact H.mul_mem (e _) (H.inv_mem (e _))

theorem prod_edgeFactor (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod = ((charFactor Γ ε : ℂˣ) : ℂ) := by
  rw [charFactor, ← Units.coeHom_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  have ha : ∀ X (z : ℂ), GlobalTheory.SplitFlip.apow (gdet (GlobalTheory.SplitFlip.Assignment.one.read (ε X))) z = 1 := fun X z => by
    refine GlobalTheory.SplitFlip.apow_of_valuation_eq_one ?_ z
    rw [show GlobalTheory.SplitFlip.Assignment.one.read (ε X) = GlobalTheory.SplitFlip.invT (ε X) from rfl, GlobalTheory.SplitFlip.gdet_invT,
      Units.val_inv_eq_inv_val, map_inv₀, GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X), inv_one]
  simp only [Grid.edgeFactor, ha, mul_one, Function.comp, Units.coeHom_apply, Units.val_mul]

theorem charFactor_eq_one (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _)
    (hrow : ∀ i < Γ.m, ε (i, Γ.m) = 1 ∧ ε (i + 1, Γ.m) = 1)
    (hμ : ∀ j < Γ.m, IsUnram (Γ.mu (j + 1))) (hη : IsUnram Γ.eta) : charFactor Γ ε = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · show Γ.kappa _ (i, Γ.m) (gdet (ε (i, Γ.m))) * (Γ.kappa _ (i + 1, Γ.m) (gdet (ε (i + 1, Γ.m))))⁻¹ = 1
    have g1 : ∀ n, gdet (1 : GL (Fin n) k) = 1 := fun _ => map_one _
    rw [(hrow i hi).1, (hrow i hi).2, g1, g1, map_one, map_one, inv_one, mul_one]
  · have hu : ∀ X, Γ.kappa (.theta Γ.m j) X (gdet (ε X)) = 1 := fun X => by
      have hv := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X)
      show (Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2)) (gdet (ε X)) = 1
      rw [MonoidHom.div_apply, MonoidHom.pow_apply, hμ j hj _ hv, hη _ hv, one_pow, div_one]
    show Γ.kappa _ _ (gdet (ε _)) * (Γ.kappa _ _ (gdet (ε _)))⁻¹ = 1
    rw [hu, hu, inv_one, mul_one]

end Local

section Grid0

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

variable (G : GridData L sc) in

def grid0 (w : Pl D.host.E) : Grid (Kw w) where
  m := D.R.m
  r := D.R.r
  t := D.R.t
  s := sLen D
  mu j := (muBase L j).loc w
  chi i := (G.ch.chiH i).loc w
  eta := L.C.eta.loc w

variable (G : GridData L sc) in
open Classical in

def eps0 (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j ∈ idx D then GlobalTheory.SplitFlip.diagGL fun a =>
    if Odd j ∧ topRank (grid0 G w) j + (D.R.m - 1 - j) / 2 ≤ a.1 then Units.map (Int.castRingHom (Kw w)).toMonoidHom (-1) else 1
    else 1

variable (G : GridData L sc) in

def stair0 (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j + 2 ≤ D.R.m then stair (grid0 G w) (unifAt w) (cosExp G w) j else 1

theorem elt_stair (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i + 1))) :
    (repsAt G t w).elt β = (stair0 G w : (locGrid G t w).VertexGroup) := by
  have hb : β = fun i : Fin _ => DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i.1 + 1)) := funext hβ
  subst hb
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hi : i = D.R.m
  · subst hi
    have e1 : (stair0 G w : (locGrid G t w).VertexGroup) (D.R.m, j) =
        if j + 2 ≤ D.R.m then stair (locGrid G t w) (unifAt w) (cosExp G w) j else 1 := onColumn_apply (G := grid0 G w) _ j
    rw [e1]
    split_ifs with hj
    · exact through_elt _ hj
    · exact elt_eq_one t w _ (by omega)
  · show onColumn (G := locGrid G t w) _ (i, j) = onColumn (G := grid0 G w) _ (i, j)
    rw [onColumn, onColumn, dif_neg (show ¬ (i, j).1 = (locGrid G t w).m from hi),
      dif_neg (show ¬ (i, j).1 = (grid0 G w).m from hi)]
    rfl

end Grid0

open Classical in

theorem scal : Big fun ch => ScalP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  refine ⟨fun w => if w ∈ ch.G.pl.W0 then
      ((charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w) : ℂˣ) : ℂ) else 1,
    fun t w => (xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
      if w ∈ ch.G.pl.W0 then xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w) else 1)⁻¹,
    fun t w => ?_, fun w hw => if_neg hw, fun t w hw β hβ => ?_⟩
  · have hH : ∀ x, (R.toLevCh.xiH t).loc w x ∈ xiVals R.toLevCh t := fun x => Subgroup.subset_closure ⟨w, x, rfl⟩
    refine inv_mem (mul_mem (xiPart_mem _ _ _ _ hH) ?_)
    split_ifs
    · exact xiPart_mem _ _ _ _ hH
    · exact one_mem _
  · have hmu : ∀ j, (locGrid ch.G t w).mu j = (fun j => (muBase R.toLevCh j).loc w) j * (R.toLevCh.xiH t).loc w :=
      fun j => MonoidHom.ext fun _ => rfl
    have hsplit := charFactor_split (locGrid ch.G t w) _ _ hmu
    dsimp only
    unfold zetaLoc
    rw [prod_edgeFactor _ _ (epsV_mem t w)]
    by_cases h0 : w ∈ ch.G.pl.W0
    · have hk : keepAt ch.G w = false := by simp [keepAt, h0]
      rw [hk, if_pos h0, if_pos h0, elt_stair ch.G t w β (hβ h0)]
      have key : charFactor (locGrid ch.G t w) (epsV ch.G t w) * charFactor (locGrid ch.G t w) (stair0 ch.G w) =
          (charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w)) *
          ((xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
            xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w))⁻¹)⁻¹ := by
        rw [inv_inv, hsplit (epsV ch.G t w), hsplit (stair0 ch.G w)]
        exact mul_mul_mul_comm _ _ _ _
      simp only [Bool.false_eq_true, if_false]
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.val_mul]
      exact congrArg Units.val key
    · have hk : keepAt ch.G w = true := by simp [keepAt, h0]
      rw [hk, if_neg h0, if_neg h0, if_pos rfl]
      have ha : w.under (𝓞 D.host.F) ∉ ch.G.pl.S0 := by
        rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, b⟩ | ⟨a, -, -⟩
        · exact absurd (by rw [b]; exact Finset.mem_image_of_mem ch.G.pl.w a) h0
        · exact a
      have hoff : ∀ i j, i ≠ D.R.m → epsV ch.G t w (i, j) = 1 := fun i j hi => by
        show onColumn (G := locGrid ch.G t w) _ (i, j) = 1
        rw [onColumn, dif_neg (show ¬ (i, j).1 = (locGrid ch.G t w).m from hi)]
      have h1 : charFactor ({locGrid ch.G t w with mu := fun j => (muBase R.toLevCh j).loc w} : Grid (Kw w))
          (epsV ch.G t w) = 1 := by
        refine charFactor_eq_one _ _ (epsV_mem t w) (fun i hi => ⟨hoff i _ (Nat.ne_of_lt hi), ?_⟩) (fun j hj => ?_) ?_
        · by_cases e : i + 1 = D.R.m
          · show epsV ch.G t w (i + 1, D.R.m) = 1
            rw [show (i + 1, D.R.m) = (D.R.m, D.R.m) by rw [e]]
            exact epsV_eq_one t w (by omega)
          · exact hoff _ _ e
        · replace hj : j < D.R.m := hj
          show IsUnram ((muBase R.toLevCh (j + 1)).loc w)
          rw [muBase, dif_pos hj]
          refine GlobalTheory.FunObj.Good.isUnram_loc.2 ((R.toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun k hk => ?_)
          refine ha (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
          have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
            show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
            rw [map_natCast]; exact hk
          fin_cases k
          · exact Or.inl this
          · exact Or.inr (Or.inl this)
        · exact GlobalTheory.FunObj.Good.isUnram_loc.2 (R.toLevCh.C.isEta.unr w)
      simp only [hsplit (epsV ch.G t w), h1, one_mul, mul_one, Units.val_inv_eq_inv_val, inv_inv]

end

end GlobalTheory.FlatScal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedLocalTotalTensorFixedByInnerVertexLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedLocalTotalTensor_fixed_by_innerVertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} (Φ : G.Datum), t ∈ U → ∀ {μ₀ : T}, L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → ∀ (w : Pl D.host.E), w ∈ locPl G t → ∀ (j : ℕ), j + 1 < D.R.m →
    ∀ (κ : GL (Fin ((locGrid G t w).rank (j + 1, D.R.m))) (Kw w)), κ ∈ givenLevel G t w (j + 1, D.R.m) →
    (locGrid G t w).pathAct .one (oppositePath D.R.m) (Pi.mulSingle (j + 1, D.R.m) κ) (Tflip W S.B t Φ w) =
      Tflip W S.B t Φ w := by
  first | exact @GlobalTheory.FlipVertexInv.main | exact GlobalTheory.FlipVertexInv.main | (intros; apply GlobalTheory.FlipVertexInv.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKSubmoduleInfimumAndIrreducibleSupremumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_finite_dim_stable : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  first | exact @GlobalTheory.CuspGK.mem_iSup_irr | exact GlobalTheory.CuspGK.mem_iSup_irr | (intros; apply GlobalTheory.CuspGK.mem_iSup_irr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianCompactActionEigenStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_compact_action_eigen : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  first | exact @GlobalTheory.FockVacStab.isGauss_of_acts | exact GlobalTheory.FockVacStab.isGauss_of_acts | (intros; apply GlobalTheory.FockVacStab.isGauss_of_acts <;> assumption)
end

