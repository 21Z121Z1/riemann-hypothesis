import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProductMeanContinuousPeriodicDualVariable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistThetaMean

variable {D : D7}

theorem isoPart_add (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a b : Mx D W.rank r) :
    isoPart V W C (a + b) = isoPart V W C a + isoPart V W C b :=
  Matrix.add_mul _ _ _

theorem isoPart_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {γ : Mx D W.rank r}
    (hγ : γ ∈ ratMx D W.rank r) : isoPart V W C γ ∈ ratL W V := by
  obtain ⟨g, rfl⟩ := hγ
  refine ⟨g * (adj D C * V.gram), ?_⟩
  show (g * (adj D C * V.gram)).map (incA D) = g.map (incA D) * (adj D C * V.gram).map (incA D)
  exact Matrix.map_mul

theorem isoPart_continuous (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    Continuous (isoPart V W C) :=
  continuous_id.matrix_mul continuous_const

theorem midPart_continuous (V V' W : HSp D) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) :
    Continuous (midPart V V' W B) :=
  continuous_id.matrix_mul continuous_const

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean

theorem integral_continuous_of_bounded {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (k : X × Y → ℂ) (hk : Continuous k) (b : ℝ) (hb : ∀ q, ‖k q‖ ≤ b) :
    Continuous (fun p => ∫ y, k (p, y) ∂ν) ∧ ∀ p, ‖∫ y, k (p, y) ∂ν‖ ≤ b * ν.real Set.univ := by
  refine ⟨continuous_of_dominated (bound := fun _ => b) (fun p => ?_) (fun p => ?_) (integrable_const _) ?_,
    fun p => norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => hb _)⟩
  · exact (hk.comp (Continuous.prodMk_right p)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hb _
  · exact Filter.Eventually.of_forall fun y => hk.comp (Continuous.prodMk_left y)

end GlobalTheory.TwistThetaMean

namespace GlobalTheory.TwistThetaMean

open TopologicalSpace in

theorem mean_continuous_periodic : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ P G, IsThetaFunO ψ V W P → IsThetaFunO ψ V W G → Continuous (fun t : Mx D W.rank r => ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) ∧ ∀ γ ∈ ratMx D W.rank r, ∀ t : Mx D W.rank r, (∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' (γ + t) + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = ∫ y' in 𝓨, ∫ x in 𝓕', P (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B _hs C' _h1 _h2 _h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' h𝓕' P G hP hG
  haveI hAE : SecondCountableTopology (AE D) := (Formalism.IndefR.Eqv.ae_facts D).2.2.2.1
  haveI hM : SecondCountableTopology (Mx D W.rank r) :=
    inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin r → AE D))
  haveI hM2 : SecondCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    @instSecondCountableTopologyProd _ _ _ _ hM hM
  haveI : FirstCountableTopology (Mx D W.rank r × Mx D W.rank r) :=
    SecondCountableTopology.to_firstCountableTopology _
  haveI : FirstCountableTopology (Mx D W.rank r) := SecondCountableTopology.to_firstCountableTopology _
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V'
  haveI : Countable (ratL W V') := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') := ⟨by
    rw [Measure.restrict_apply_univ]
    exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WO V' W) (ratL W V') hK hKc μ' h𝓕'⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by
    rw [Measure.restrict_apply_univ, hY.2.2]; exact ENNReal.one_lt_top⟩
  obtain ⟨b1, hb1⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hP
  obtain ⟨b2, hb2⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG
  have hh : Continuous fun w => P w * star (G w) := hP.cont.mul hG.cont.star
  have hhb : ∀ w, ‖P w * star (G w)‖ ≤ b1 * b2 := fun w => by
    rw [norm_mul, norm_star]
    exact mul_le_mul (hb1 w) (hb2 w) (norm_nonneg _) ((norm_nonneg _).trans (hb1 w))
  have hu : Continuous fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2 :=
    (((isoPart_continuous V W C').comp (continuous_fst.comp continuous_fst)).add
      ((isoPart_continuous V W C).comp (continuous_snd.comp continuous_fst))).add
      ((midPart_continuous V V' W B).comp continuous_snd)
  obtain ⟨hin, hinb⟩ := integral_continuous_of_bounded (μ'.restrict 𝓕')
    (fun q : (Mx D W.rank r × Mx D W.rank r) × WO V' W =>
      P (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2) *
        star (G (isoPart V W C' q.1.1 + isoPart V W C q.1.2 + midPart V V' W B q.2))) (hh.comp hu) (b1 * b2)
    (fun q => hhb _)
  refine ⟨?_, ?_⟩
  · exact (integral_continuous_of_bounded (μ.restrict 𝓨)
      (fun q : Mx D W.rank r × Mx D W.rank r => ∫ x in 𝓕',
        P (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x) *
          star (G (isoPart V W C' q.1 + isoPart V W C q.2 + midPart V V' W B x)) ∂μ') hin _ hinb).1
  · intro γ hγ t
    have key : ∀ y x, P (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' (γ + t) + isoPart V W C y + midPart V V' W B x)) =
        P (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) *
        star (G (isoPart V W C' t + isoPart V W C y + midPart V V' W B x)) := fun y x => by
      rw [isoPart_add, add_assoc (isoPart V W C' γ) (isoPart V W C' t),
        add_assoc (isoPart V W C' γ) (isoPart V W C' t + isoPart V W C y)]
      exact GlobalTheory.ThetaSchur.prod_periodic hψ hP hG (isoPart_rat V W C' hγ) _
    simp_rw [key]

end GlobalTheory.TwistThetaMean
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionInvariantRationalLeviScaling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviRes

local infixl:70 " ⬝ " => HMul.hMul

variable {D : D7}

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat M) = GlobalTheory.MixModel.rat Mᴴ := by
  rw [← GlobalTheory.MixModel.cT_sig]
  ext i j
  simp [GlobalTheory.MixModel.adj, GlobalTheory.MixModel.rat, Formalism.UG.cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem symplOH_add_right (S T : HSp D) (x y z : WO S T) :
    symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_add, map_add]

theorem symplOH_mul_rat (V W : HSp D) {s t : ℕ} (X : Matrix (Fin s) (Fin V.rank) D.host.E)
    (Y : Matrix (Fin t) (Fin V.rank) D.host.E) (hXY : X * V.gram⁻¹ * Yᴴ = 0) (q : Mx D W.rank s) (a : Mx D W.rank t) :
    symplOH V W (q ⬝ GlobalTheory.MixModel.rat X) (a ⬝ GlobalTheory.MixModel.rat Y) = 0 := by
  have hz : GlobalTheory.MixModel.rat X ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.rat Yᴴ = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hXY, GlobalTheory.MixModel.rat_zero]
  have hre : GlobalTheory.MixModel.giA V ⬝ (GlobalTheory.MixModel.adj (a ⬝ GlobalTheory.MixModel.rat Y) ⬝ (GlobalTheory.MixModel.gA W ⬝ (q ⬝ GlobalTheory.MixModel.rat X)))
      = (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.rat Yᴴ ⬝ (GlobalTheory.MixModel.adj a ⬝ GlobalTheory.MixModel.gA W ⬝ q)) ⬝ GlobalTheory.MixModel.rat X := by
    rw [GlobalTheory.MixModel.adj_mul, adj_rat]
    simp only [Matrix.mul_assoc]
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, hre, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero, map_zero]

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem iso_iso (hs : IsIsoSplit V V' C B) : (adj D C * V.gram) * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, h0]

theorem iso_mid (hs : IsIsoSplit V V' C B) :
    (adj D C * V.gram) * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * B = 0 := hs.orth
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul]

theorem periodic (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ} {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ y : Mx D W.rank r,
      f (isoPart V W C (γ + y) + midPart V V' W B x) = f (isoPart V W C y + midPart V V' W B x) := by
  intro γ hγ y
  obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
  have e1 : ∀ z : Mx D W.rank r, isoPart V W C z = z ⬝ GlobalTheory.MixModel.rat (adj D C * V.gram) := fun z => rfl
  have e2 : midPart V V' W B x = (x : Mx D W.rank V'.rank) ⬝ GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) := rfl
  have h0 : symplOH V W (GlobalTheory.MixModel.rat γ0 ⬝ GlobalTheory.MixModel.rat (adj D C * V.gram))
      (isoPart V W C y + midPart V V' W B x) = 0 := by
    rw [symplOH_add_right, e1, e2,
      symplOH_mul_rat V W (adj D C * V.gram) (adj D C * V.gram) (iso_iso hs) (GlobalTheory.MixModel.rat γ0) y,
      symplOH_mul_rat V W (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (iso_mid hs) (GlobalTheory.MixModel.rat γ0) x,
      add_zero]
  have hq : f (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram)) + (isoPart V W C y + midPart V V' W B x)) =
      ψ (-(symplOH V W (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram))) (isoPart V W C y + midPart V V' W B x))) *
        f (isoPart V W C y + midPart V V' W B x) :=
    hf.quasi (γ0 * (adj D C * V.gram)) (isoPart V W C y + midPart V V' W B x)
  rw [e1 (GlobalTheory.MixModel.rat γ0 + y), Matrix.add_mul, add_assoc, ← e1 y, ← GlobalTheory.MixModel.rat_mul, hq,
    GlobalTheory.MixModel.rat_mul, h0, neg_zero, AddChar.map_zero_eq_one, one_mul]

end Split

theorem mt_unitary (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a) ⬝ GlobalTheory.MixModel.gA V ⬝ Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.gA V := by
  rw [Matrix.mul_assoc]
  exact GlobalTheory.MixModel.mt_unitary V a

theorem mt_mul (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_mul_mt (S T : HSp D) (g : GA D S) (w : WO S T) :
    actO S T g 1 (HMul.hMul (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g)) = w := by
  rw [GlobalTheory.MixModel.actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.mul_one]

private lemma rat_adj_mul_gram_eq (V : HSp D) {s : ℕ} (B : Matrix (Fin V.rank) (Fin s) D.host.E) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) = GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) ⬝ GlobalTheory.MixModel.gA V := by
  rw [GlobalTheory.MixModel.rat_mul, adj_rat, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig, GlobalTheory.MixModel.gA]

private lemma gA_mul_mt_eq_adj_mt_inv_mul (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.gA V ⬝ Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) ⬝ GlobalTheory.MixModel.gA V := by
  calc GlobalTheory.MixModel.gA V ⬝ Formalism.L2.Theta.mt V a
      = (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) ⬝ GlobalTheory.MixModel.gA V ⬝ Formalism.L2.Theta.mt V a⁻¹) ⬝ Formalism.L2.Theta.mt V a := by
        rw [mt_unitary]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) ⬝ GlobalTheory.MixModel.gA V ⬝ (Formalism.L2.Theta.mt V a⁻¹ ⬝ Formalism.L2.Theta.mt V a) := by
        rw [Matrix.mul_assoc]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) ⬝ GlobalTheory.MixModel.gA V := by
        rw [← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem form_fix (V : HSp D) {s : ℕ} (a : GA D V) (B : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) ⬝ Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.rat (adj D B * V.gram) := by
  have hinv : Formalism.L2.Theta.mt V a⁻¹ ⬝ GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv]

theorem form_scale (V : HSp D) {s : ℕ} (a : GA D V) (C : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C) :
    GlobalTheory.MixModel.rat (adj D C * V.gram) ⬝ Formalism.L2.Theta.mt V a =
      incA D (1 / 2) • GlobalTheory.MixModel.rat (adj D C * V.gram) := by
  have h2 : incA D (1 / 2) * (2 : AE D) = 1 := by
    rw [← map_ofNat (incA D) 2, ← map_mul]
    norm_num
  have hinv : Formalism.L2.Theta.mt V a⁻¹ ⬝ GlobalTheory.MixModel.rat C = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
    calc Formalism.L2.Theta.mt V a⁻¹ ⬝ GlobalTheory.MixModel.rat C
        = (incA D (1 / 2) * (2 : AE D)) • (Formalism.L2.Theta.mt V a⁻¹ ⬝ GlobalTheory.MixModel.rat C) := by rw [h2, one_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ ⬝ ((2 : AE D) • GlobalTheory.MixModel.rat C)) := by
        rw [mul_smul, Matrix.mul_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ ⬝ (Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat C)) := by rw [h]
      _ = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
        rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  have hc : cA D (incA D (1 / 2)) = incA D (1 / 2) := GlobalTheory.MixModel.cA_half
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv,
    GlobalTheory.MixModel.adj_smul, hc, Matrix.smul_mul]

theorem res_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ a : GA D V, a ∈ GQ V → HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ l : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (a, 1) f) = l • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hcov
  refine ⟨1, fun f hf => ?_⟩
  have hC' : Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C := haC
  have hB' : Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := haB
  have hsub : ∀ w : WO V W,
      ω (a, 1) f w = f (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a)) := by
    intro w
    have h1 := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω a haQ 1 (one_mem _) f hf
      (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a))
    rwa [actO_mul_mt] at h1
  have hiso : ∀ y : Mx D W.rank r,
      HMul.hMul (isoPart V W C y : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
        isoPart V W C (incA D (1 / 2) • y) := by
    intro y
    show y ⬝ GlobalTheory.MixModel.rat (adj D C * V.gram) ⬝ Formalism.L2.Theta.mt V a =
      (incA D (1 / 2) • y) ⬝ GlobalTheory.MixModel.rat (adj D C * V.gram)
    rw [Matrix.mul_assoc, form_scale V a C hC', Matrix.mul_smul, Matrix.smul_mul]
  rw [one_smul]
  funext x
  have hmid : HMul.hMul (midPart V V' W B x : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
      midPart V V' W B x := by
    show (x : Mx D W.rank V'.rank) ⬝ GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) ⬝ Formalism.L2.Theta.mt V a =
      (x : Mx D W.rank V'.rank) ⬝ GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram)
    rw [Matrix.mul_assoc V'.gram⁻¹ (adj D B) V.gram, GlobalTheory.MixModel.rat_mul]
    simp only [Matrix.mul_assoc]
    rw [form_fix V a B hB']
  calc res V V' W C B μ 𝓨 (ω (a, 1) f) x
      = ∫ y in 𝓨, f (isoPart V W C (incA D (1 / 2) • y) + midPart V V' W B x) ∂μ := by
        show ∫ y in 𝓨, ω (a, 1) f (isoPart V W C y + midPart V V' W B x) ∂μ = _
        congr 1
        funext y
        rw [hsub, Matrix.add_mul, hiso, hmid]
    _ = ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B x) ∂μ :=
        GlobalTheory.UnipMean.mean_smul hcov (c := 1 / 2) (by norm_num)
          (fun y => f (isoPart V W C y + midPart V V' W B x)) (periodic hs hf x)
    _ = res V V' W C B μ 𝓨 f x := rfl

end GlobalTheory.LeviRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentIntegralsPureTensorVanishOfLocalStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local : ∀ (D : D7) (V : HSp D) (𝔉 : IsoFlag V) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ)
    (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w) →
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    (∀ (ν : Measure (NLoc 𝔉 v)) [ν.IsHaarMeasure] (x y : GLoc D.sp.cm.sig V.gram v),
      ∫ n : NLoc 𝔉 v, ff v (x * n * y) ∂ν = 0) →
    UnipIntegralsVanish 𝔉 (tensor D.sp.cm.sig V.gram fa ff) := by
  first | exact @GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor | exact GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor | (intros; apply GlobalTheory.TestConstTerm.unipIntegralsVanish_tensor <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU Formalism.UG

section Generic

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem htOf_le_mul {R : Type} [CommRing R] {N : Matrix n n R → ℝ≥0} {N₁ : Matrix m m R → ℝ≥0} {c : ℝ≥0}
    (hc : 1 ≤ c) (X : GL n R) (x : GL m R) (h1 : N (X : Matrix n n R) ≤ c * max 1 (N₁ (x : Matrix m m R)))
    (h2 : N ((X⁻¹ : GL n R) : Matrix n n R) ≤ c * max 1 (N₁ ((x⁻¹ : GL m R) : Matrix m m R))) :
    htOf N X ≤ c * htOf N₁ x := by
  refine max_le (one_le_mul_of_one_le_of_one_le hc (one_le_htOf _ _)) (max_le ?_ ?_)
  · exact h1.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (le_htOf _ _)))
  · exact h2.trans (mul_le_mul' le_rfl (max_le (one_le_htOf _ _) (inv_le_htOf _ _)))

theorem bc_val_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R} (h : (X : Matrix n n R) = A + B * (x : Matrix m m R) * C) :
    ((bc φ X : GL n R') : Matrix n n R') = A.map φ + B.map φ * ((bc φ x : GL m R') : Matrix m m R') * C.map φ := by
  show (X : Matrix n n R).map φ = A.map φ + B.map φ * (x : Matrix m m R).map φ * C.map φ
  rw [h, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem bc_inv_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) {X : GL n R} {x : GL m R}
    (h : ((X⁻¹ : GL n R) : Matrix n n R) = A + B * ((x⁻¹ : GL m R) : Matrix m m R) * C) :
    (((bc φ X)⁻¹ : GL n R') : Matrix n n R') =
      A.map φ + B.map φ * (((bc φ x)⁻¹ : GL m R') : Matrix m m R') * C.map φ := by
  simp only [← map_inv]
  exact bc_val_aff φ A B C h

theorem map_aff {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (A : Matrix n n R) (B : Matrix n m R)
    (C : Matrix m n R) (y : Matrix m m R) : (A + B * y * C).map φ = A.map φ + B.map φ * y.map φ * C.map φ := by
  rw [Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul]

theorem opNorm_add_le (a b : Matrix n n ℂ) : opNorm (a + b) ≤ opNorm a + opNorm b := by
  unfold opNorm; rw [map_add]; exact nnnorm_add_le _ _

theorem exists_opNorm_mul_mul_le (B : Matrix n m ℂ) (C : Matrix m n ℂ) :
    ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ, opNorm (B * y * C) ≤ K * opNorm y := by
  let L : (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
    { toFun := fun T => Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (B * (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ)).symm T * C)
      map_add' := fun S T => by simp only [map_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r T => by simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖₊, fun y => ?_⟩
  have e : opNorm (B * y * C) = ‖Lc (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) y)‖₊ := by
    show _ = ‖L _‖₊
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, StarAlgEquiv.symm_apply_apply]
    rfl
  rw [e]
  exact Lc.le_opNNNorm _

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem normFin_add_le (v : HeightOneSpectrum (𝓞 F)) {p q : Type} [Fintype p] [Fintype q]
    (a b : Matrix p q (Fv F v ⊗[F] E)) : normFin F v (a + b) ≤ max (normFin F v a) (normFin F v b) :=
  (normFin_le_iff F v).2 fun i j =>
    (absFin_add_le F v _ _).trans (max_le_max (absFin_le_normFin F v a i j) (absFin_le_normFin F v b i j))

theorem normFin_aff_le (v : HeightOneSpectrum (𝓞 F)) (A : Matrix n n (Fv F v ⊗[F] E)) (B : Matrix n m (Fv F v ⊗[F] E))
    (C : Matrix m n (Fv F v ⊗[F] E)) (y : Matrix m m (Fv F v ⊗[F] E)) :
    normFin F v (A + B * y * C) ≤
      max 1 (max (normFin F v A) (normFin F v B * normFin F v C)) * max 1 (normFin F v y) := by
  set M := max 1 (max (normFin F v A) (normFin F v B * normFin F v C))
  have h1 : (1 : ℝ≥0) ≤ M := le_max_left _ _
  refine (normFin_add_le F v _ _).trans (max_le ?_ ?_)
  · exact (le_max_left _ _ |>.trans (le_max_right 1 _) : normFin F v A ≤ M).trans (le_mul_of_one_le_right' (le_max_left _ _))
  · calc normFin F v (B * y * C) ≤ normFin F v B * normFin F v y * normFin F v C :=
          (normFin_mul_le F v _ _).trans (mul_le_mul' (normFin_mul_le F v _ _) le_rfl)
      _ = (normFin F v B * normFin F v C) * normFin F v y := by ring
      _ ≤ M * max 1 (normFin F v y) :=
          mul_le_mul' ((le_max_right _ _).trans (le_max_right _ _)) (le_max_right _ _)

theorem exists_normInf_aff_le (w : InfinitePlace F) (A : Matrix n n (w.Completion ⊗[F] E))
    (B : Matrix n m (w.Completion ⊗[F] E)) (C : Matrix m n (w.Completion ⊗[F] E)) :
    ∃ c : ℝ≥0, 1 ≤ c ∧ ∀ y : Matrix m m (w.Completion ⊗[F] E),
      normInf F w (A + B * y * C) ≤ c * max 1 (normInf F w y) := by
  classical
  have hK : ∀ τ : EmbOver E w, ∃ K : ℝ≥0, ∀ y : Matrix m m ℂ,
      opNorm (B.map (infEmb τ) * y * C.map (infEmb τ)) ≤ K * opNorm y := fun τ =>
    exists_opNorm_mul_mul_le _ _
  choose K hK using hK
  refine ⟨1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ), le_self_add, fun y => (normInf_le_iff F w).2 fun τ => ?_⟩
  have hy : opNorm (y.map (infEmb τ)) ≤ max 1 (normInf F w y) :=
    ((normInf_le_iff F w).1 le_rfl τ).trans (le_max_right _ _)
  have hs : opNorm (A.map (infEmb τ)) + K τ ≤ 1 + ∑ τ, (opNorm (A.map (infEmb τ)) + K τ) :=
    (Finset.single_le_sum (f := fun τ => opNorm (A.map (infEmb τ)) + K τ) (fun _ _ => zero_le)
      (Finset.mem_univ τ)).trans le_add_self
  have e := map_aff (infEmb τ) A B C y
  rw [e]
  refine (opNorm_add_le _ _).trans ?_
  have h3 := hK τ (y.map (infEmb τ))
  refine (add_le_add le_rfl h3).trans ?_
  calc opNorm (A.map (infEmb τ)) + K τ * opNorm (y.map (infEmb τ))
      ≤ opNorm (A.map (infEmb τ)) * max 1 (normInf F w y) + K τ * max 1 (normInf F w y) :=
        add_le_add (le_mul_of_one_le_right' (le_max_left _ _)) (mul_le_mul' le_rfl hy)
    _ = (opNorm (A.map (infEmb τ)) + K τ) * max 1 (normInf F w y) := by rw [add_mul]
    _ ≤ _ := mul_le_mul' hs le_rfl

theorem eventually_normFin_rect_le_one {p q : Type} [Fintype p] [Fintype q] (y : Matrix p q (AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, normFin F v (y.map (compFin F E v)) ≤ 1 := by
  simp only [normFin_le_iff, Filter.eventually_all]
  exact fun i j => eventually_absFin_le_one F (y i j)

theorem exists_heightGL_aff_le (A : Matrix n n (AF F ⊗[F] E)) (B : Matrix n m (AF F ⊗[F] E))
    (C : Matrix m n (AF F ⊗[F] E)) :
    ∃ K : ℝ≥0, ∀ (X : GL n (AF F ⊗[F] E)) (x : GL m (AF F ⊗[F] E)),
      (X : Matrix n n (AF F ⊗[F] E)) = A + B * (x : Matrix m m (AF F ⊗[F] E)) * C →
      ((X⁻¹ : GL n (AF F ⊗[F] E)) : Matrix n n (AF F ⊗[F] E)) =
        A + B * ((x⁻¹ : GL m (AF F ⊗[F] E)) : Matrix m m (AF F ⊗[F] E)) * C →
      heightGL F X ≤ K * heightGL F x := by
  have hw := fun w : InfinitePlace F =>
    exists_normInf_aff_le F w (A.map (compInf F E w)) (B.map (compInf F E w)) (C.map (compInf F E w))
  choose cw hcw1 hcw using hw
  set cv : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (max (normFin F v (A.map (compFin F E v)))
    (normFin F v (B.map (compFin F E v)) * normFin F v (C.map (compFin F E v)))) with hcv
  have hfin : (Function.mulSupport cv).Finite := by
    have h := ((eventually_normFin_rect_le_one F A).and (eventually_normFin_rect_le_one F B)).and
      (eventually_normFin_rect_le_one F C)
    refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
    refine max_eq_left (max_le hv'.1.1 ?_)
    exact mul_le_one' hv'.1.2 hv'.2
  refine ⟨(∏ w, cw w) * ∏ᶠ v, cv v, fun X x h1 h2 => ?_⟩
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib hfin (finite_mulSupport_htFin F x)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) (hfin.union (finite_mulSupport_htFin F x) |>.subset
      (Function.mulSupport_mul _ _)) fun v => ?_)
  · refine htOf_le_mul (hcw1 w) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact hcw w _
    · rw [bc_inv_aff _ _ _ _ h2]; exact hcw w _
  · refine htOf_le_mul (le_max_left _ _) _ _ ?_ ?_
    · rw [bc_val_aff _ _ _ _ h1]; exact normFin_aff_le F v _ _ _ _
    · rw [bc_inv_aff _ _ _ _ h2]; exact normFin_aff_le F v _ _ _ _

end GlobalTheory.EmbHeight

namespace GlobalTheory.EmbHeight

open scoped NNReal
open GlobalTheory.AdelicU

theorem unitaryAdelicHeight_wittEmbedding_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀,
    height S (d.emb0 g) ≤ C * height S₀ g := by
  intro D S S₀ ρ d
  obtain ⟨K, hK⟩ := exists_heightGL_aff_le D.host.F (d.jX ⬝ d.pX + d.jY ⬝ d.pY) d.j0 d.p0
  refine ⟨K, fun g => ?_⟩
  have h1 : ∀ g : GA D S₀, mt S (d.emb0 g) = (d.jX ⬝ d.pX + d.jY ⬝ d.pY) + d.j0 ⬝ mt S₀ g ⬝ d.p0 := fun g => by
    rw [d.unitaryMatrix_wittCoreEmbedding, add_right_comm]
  have h := hK (matHom S (d.emb0 g)) (matHom S₀ g) (h1 g) (by
    rw [← map_inv, ← map_inv]
    exact h1 g⁻¹)
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ (K : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.EmbHeight

end
end

