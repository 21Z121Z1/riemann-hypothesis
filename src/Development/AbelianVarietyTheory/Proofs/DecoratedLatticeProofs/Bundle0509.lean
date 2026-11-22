import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0498
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0499
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOfMemPartW
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableContAut

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniform
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.SigConv

variable {D : D7}

theorem mt_jX_eq {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    mt V n ⬝ d.jX = d.jX ⬝ blockX d n := by
  obtain ⟨T, b, -, h1, -⟩ := exists_blocks d hn
  have e3 : blockX d n = 1 + T := by
    rw [blockX, h1, Matrix.mul_add, d.pX_jX, cancel₂ d.pX_jX, Matrix.one_mul]
  rw [e3, h1, Matrix.mul_add, Matrix.mul_one]

theorem blockX_mul_inv {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    blockX d n ⬝ blockX d n⁻¹ = 1 := by
  have h1 := mt_jX_eq d (inv_mem hn)
  have h2 := mt_jX_eq d hn
  have h3 : d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹) = d.jX := by
    rw [← Matrix.mul_assoc, ← h2, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
      Matrix.one_mul]
  have h4 : d.pX ⬝ (d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹)) = d.pX ⬝ d.jX := by rw [h3]
  rwa [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h4

theorem blockX_rat {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ B : Matrix (Fin ρ) (Fin ρ) D.host.E, rat B = blockX d γ :=
  mem_ratMx.1 (ratMx_mul (rat_mem d.qX) (ratMx_mul ((mem_GQ_iff V γ).1 hγ) (rat_mem d.e)))

def sumAbs (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)
    (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ) : ENNReal :=
  ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS Ψ x‖ₑ

end GlobalTheory.Unf.SigConv

open GlobalTheory.Unf.SigConv in

theorem GlobalTheory.Unf.sum_term_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h, ∀ n ∈ flagN d, ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n * g, h) Φ) x‖ₑ ≤ ENNReal.ofReal (C * (height V g * quotHeight W h) ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.mixedCoordinate_absSum_weilTranslate_moderateGrowth D ψ V W χV χW om hW V₀ ρ d vS Φ hΦ
  have hT := fun Ψ (hΨ : IsThetaFunO ψ V W Ψ) => GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ

  have hA : ∀ g h, sumAbs ψ d W vS (om (g, h) Φ) ≤ ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
    intro g h
    refine le_trans ?_ (hC g h 0)
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E =>
        (⟨rat x, rat_mem x⟩ : ratMx D W.rank ρ))
      (fun x y hxy => rat_injective (congrArg Subtype.val hxy))
      (fun y : ratMx D W.rank ρ => ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) y 0‖ₑ)

  have hB : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ γ ∈ GQ V, γ ∈ flagN d →
      sumAbs ψ d W vS (om (γ, 1) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ γ hQ hN
    obtain ⟨B, hB⟩ := blockX_rat d hQ
    have key : ∀ x, term ψ d W vS (om (γ, 1) Ψ) x = term ψ d W vS Ψ (x * B) :=
      fun x => (hT Ψ hΨ).2.1 γ hQ hN x (x * B) (by rw [rat_mul, hB])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => x * B) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : x * B = y * B := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => (rat z : Mx D W.rank ρ) ⬝ blockX d γ⁻¹) hxy'
    simp only [rat_mul, hB, Matrix.mul_assoc, blockX_mul_inv d hN, Matrix.mul_one] at h5
    exact h5

  have hD : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ δ ∈ GQ W,
      sumAbs ψ d W vS (om (1, δ⁻¹) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ δ hQ
    obtain ⟨M, hM⟩ := mem_ratMx.1 ((mem_GQ_iff W δ).1 hQ)
    have key : ∀ x, term ψ d W vS (om (1, δ⁻¹) Ψ) x = term ψ d W vS Ψ (M * x) :=
      fun x => (hT Ψ hΨ).2.2.1 δ⁻¹ (inv_mem hQ) x (M * x)
        (by rw [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => M * x) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : M * x = M * y := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => mt W δ⁻¹ ⬝ (rat z : Mx D W.rank ρ)) hxy'
    simp only [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul] at h5
    exact h5

  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨c, hc⟩ := exists_height_le_of_isCompact V (hK.image continuous_subtype_val)
  set c' := max c 1 with hc'
  set C₀ := max C 0 with hC₀
  have hc'1 : 1 ≤ c' := le_max_right _ _
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set C' := C₀ * c' ^ A with hC'
  have hC'0 : 0 ≤ C' := mul_nonneg hC₀0 (pow_nonneg (zero_le_one.trans hc'1) _)

  have hN : ∀ g h, ∀ n ∈ flagN d, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * height W h) ^ A) := by
    intro g h n hn
    obtain ⟨γ, hγ, k, hk, hnk⟩ := hcov ⟨n, hn⟩
    have hγQ : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have hn' : n = γ.1 * k.1 := congrArg Subtype.val hnk
    have hp : ((n * g, h) : GA D V × GA D W) = (γ.1, 1) * (k.1 * g, h) := by
      rw [hn']; ext <;> simp [mul_assoc]
    have hom : om (n * g, h) Φ = om (γ.1, 1) (om (k.1 * g, h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    refine (hB _ (hW.om_pres _ _ hΦ) γ.1 hγQ γ.2).trans ((hA _ _).trans (ENNReal.ofReal_le_ofReal ?_))
    have hk' : height V k.1 ≤ c' := (hc _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
    have hkg : height V (k.1 * g) ≤ c' * height V g :=
      (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right hk' (height_pos V g).le)
    have hx0 : 0 ≤ height V (k.1 * g) * height W h := mul_nonneg (height_pos V _).le (height_pos W h).le
    have hx : height V (k.1 * g) * height W h ≤ c' * (height V g * height W h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkg (height_pos W h).le
    calc C * (height V (k.1 * g) * height W h) ^ A ≤ C₀ * (height V (k.1 * g) * height W h) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 _)
      _ ≤ C₀ * (c' * (height V g * height W h)) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx _) hC₀0
      _ = C' * (height V g * height W h) ^ A := by rw [mul_pow, hC', mul_assoc]
  refine ⟨C', A, fun g h n hn => ?_⟩

  have hδ : ∀ δ : GQ W, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * max (height W (δ.1 * h)) 0) ^ A) := by
    intro δ
    rw [max_eq_left (height_pos W _).le]
    have hp : ((n * g, h) : GA D V × GA D W) = (1, δ.1⁻¹) * (n * g, δ.1 * h) := by
      ext <;> simp [← mul_assoc]
    have hom : om (n * g, h) Φ = om (1, δ.1⁻¹) (om (n * g, δ.1 * h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    exact (hD _ (hW.om_pres _ _ hΦ) δ.1 δ.2).trans (hN g _ n hn)
  let φ : ℝ → ENNReal := fun t => ENNReal.ofReal (C' * (height V g * max t 0) ^ A)
  have hmono : Monotone φ := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC'0
    apply pow_le_pow_left₀ (mul_nonneg (height_pos V g).le (le_max_right _ _))
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) (height_pos V g).le
  have hcont : Continuous φ := by
    refine ENNReal.continuous_ofReal.comp ?_
    fun_prop
  have hinf := hmono.map_ciInf_of_continuousAt (g := fun δ : GQ W => height W (δ.1 * h)) hcont.continuousAt
    ⟨1, by rintro _ ⟨_, rfl⟩; exact one_le_height W _⟩
  have hq : ENNReal.ofReal (C' * (height V g * quotHeight W h) ^ A) = φ (quotHeight W h) := by
    simp only [φ, max_eq_left (quotHeight_pos W h).le]
  change sumAbs ψ d W vS (om (n * g, h) Φ) ≤ _
  rw [hq, quotHeight, hinf]
  exact le_iInf hδ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionTrivialAfterFlagUnipotentFixing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf

open GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction

variable {D : D7}

theorem form_mulVec_mulVec (S : HSp D) {k l : ℕ} (M : Mx D S.rank k) (N : Mx D S.rank l) (x : Fin k → AE D)
    (y : Fin l → AE D) :
    form S (M *ᵥ x) (N *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj N ⬝ (gA S ⬝ M)) *ᵥ x) := by
  have h : (fun i => cA D ((N *ᵥ y) i)) = (N.map (cA D)) *ᵥ fun i => cA D (y i) := by
    funext i
    exact RingHom.map_mulVec (cA D) N y i
  rw [form, h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec _ (adj N), adj,
    Matrix.vecMul_transpose]

theorem form_act_act (S : HSp D) (g : GA D S) (x y : VA S) : form S (act S g x) (act S g y) = form S x y := by
  rw [act, act, form_mulVec_mulVec, mt_unitary, form]

theorem act_vecX_of_mem_Nfix {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (j : Fin ρ) (a : Fin ρ → AE D)
    (ha : ∀ i, j < i → a i = 0) {m : GA D V} (hm : m ∈ Nfix d j) : act V m (vecX d a) = vecX d a := by
  have hm' : ∀ i : Fin ρ, i ≤ j → ∀ k, (mt V m ⬝ d.jX : Mx D V.rank ρ) k i = d.jX k i := by
    intro i hi k
    have h1 := (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hm).2) ⟨i, hi⟩
    have h2 := congrFun (congrFun (mem_fixer.1 h1) k) 0
    simpa [Matrix.mul_apply, Matrix.submatrix_apply] using h2
  rw [act, vecX, Matrix.mulVec_mulVec]
  funext k
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ≤ j
  · rw [hm' i hi k]
  · rw [ha i (not_le.1 hi), mul_zero, mul_zero]

theorem rat_mulVec_ratVec {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (a : Fin n → D.host.E) :
    rat x *ᵥ ratVec a = ratVec (x *ᵥ a) := by
  funext i
  exact (RingHom.map_mulVec (incA D) x a i).symm

theorem transv_trivial_after_Nfix : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W), IsWeilDatumO ψ V W χV χW om → ∀ (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ), IsThetaFunO ψ V W Ψ → ∀ (j : Fin ρ) (a : Fin ρ → D.host.E), (∀ i, j < i → a i = 0) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.VA V) (u : GA D V), GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v = 0 → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.IsTransv V (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.vecX d (GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a)) v u → ∀ x : Matrix (Fin W.rank) (Fin ρ) D.host.E, x *ᵥ a = 0 → ∀ m ∈ Nfix d j, ∀ n : GA D V, term ψ d W vS (om (m * u * n, 1) Ψ) x = term ψ d W vS (om (m * n, 1) Ψ) x := by
  intro D hD ψ V V₀ W ρ d χV χW om hW vS Ψ hΨ j a ha v u hv hu x hx m hm n
  obtain ⟨-, hConj, hTriv⟩ := GlobalTheory.T.transvectionLemma_of_wittCoreDescent D hD
  have ha' : ∀ i, j < i → ratVec a i = 0 := fun i hi => by simp [ratVec, ha i hi]
  have hmw : act V m (vecX d (ratVec a)) = vecX d (ratVec a) := act_vecX_of_mem_Nfix d j _ ha' hm
  have hc := hConj V V₀ ρ d (ratVec a) v hv u m hu
  rw [hmw] at hc
  have hv' : form V (vecX d (ratVec a)) (act V m v) = 0 := by
    rw [← hmw, form_act_act, hv]
  have hx' : rat x *ᵥ ratVec a = 0 := by
    rw [rat_mulVec_ratVec, hx]
    funext i
    simp [ratVec]
  have e : ((m * u * n, (1 : GA D W)) : GA D V × GA D W) = (m * u * m⁻¹, 1) * (m * n, 1) := by
    ext
    · simp [mul_assoc]
    · simp
  have key := hTriv V V₀ W ρ d ψ χV χW om hW vS.μ vS.𝓕 vS.covol a (act V m v) hv' (m * u * m⁻¹) hc (rat x) hx'
    (om (m * n, 1) Ψ) (hW.om_pres _ _ hΨ)
  rw [term, term, e, map_mul, Module.End.mul_apply]
  exact congrFun key 0

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryPsiValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiColChar

open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil

theorem chr_unif_congr {k : Type} [Field k] [ValuativeRel k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {t : kˣ} (ht : IsUnif t)
    {p y : k} (hp : valuation k ((t : k) - p) < valuation k (t : k)) (hy : valuation k y ≤ 1) :
    ψ (((t⁻¹ : kˣ) : k) * y) = ψ (p⁻¹ * y) := by
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  have hpv : valuation k p = valuation k (t : k) := by
    refine Valuation.map_eq_of_sub_lt _ ?_
    rwa [Valuation.map_sub_swap]
  have p0 : p ≠ 0 := fun e => by
    rw [e, map_zero] at hpv
    exact tp.ne hpv
  have h1 : valuation k (((t : k) - p) * (t : k)⁻¹) ≤ valuation k (t : k) := (ht _).1 (by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ tp, one_mul]
    exact hp)
  have triv : ψ (((t : k) - p) * (t : k)⁻¹ * p⁻¹ * y) = 1 := (hψ 1).2 (by simp) _ (by
    rw [map_one, map_mul, map_mul _ _ p⁻¹, map_inv₀, hpv]
    refine mul_le_one' ?_ hy
    rw [mul_inv_le_iff₀ tp, one_mul]
    exact h1)
  have e : p⁻¹ * y = ((t⁻¹ : kˣ) : k) * y + ((t : k) - p) * (t : k)⁻¹ * p⁻¹ * y := by
    have := t.ne_zero
    rw [Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [e, AddChar.map_add_eq_mul, triv, mul_one]

theorem weil_unif_eq_exp {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {ψ : AddChar k Circle}
    (hψ : HasConductor ψ 1) {Ψ : AddChar (AF D.host.F) ℂ} (hΨ : IsStdChar D Ψ (-1)) (hc : (ofSplit q).IsChar Ψ ψ)
    {p : ℕ} (hp : p.Prime) (hN : Ideal.absNorm PP.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2)
    {t : kˣ} (ht : IsUnif t) (htp : valuation k ((t : k) - (p : k)) < valuation k (t : k))
    {s : 𝓞 D.host.E} (hs : D.host.xi0 * (s : D.host.E) = 1) {z : 𝓞 D.host.E} {b : ℤ} (hz : z - s * b ∈ PP.asIdeal) :
    (ψ (((t⁻¹ : kˣ) : k) * (ofSplit q).pr (z : D.host.E)) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  obtain ⟨hv, hi, -⟩ := place_facts q h
  have h1 : valuation k (prO q z - prO q (s * b)) < 1 := by
    rw [← map_sub, ← prO_lt q h]
    exact hz
  rw [← prO_apply, GlobalTheory.LevelUnif.chr_near hψ ht h1, chr_unif_congr hψ ht htp (prO_le q h _), hc,
    ← GlobalTheory.SplitDegOneChar.psiE_sec_pr_eq_exp D k q PP p hp hN hsq hv hi Ψ hΨ ((b : D.host.E) / (p : D.host.E)) b
      (by rw [sub_self]; exact ⟨0, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)]
  have e1 : ((p : k))⁻¹ * prO q (s * b) = q.pr (incA D ((s : D.host.E) * ((b : D.host.E) / (p : D.host.E)))) := by
    change _ = (q.pr.comp (incA D)) _
    rw [map_mul, map_mul, map_div₀, map_intCast, map_intCast, map_natCast]
    change _ = prO q s * _
    ring
  rw [e1]
  change psiE Ψ (incA D D.host.xi0 * q.sec (q.pr _)) = psiE Ψ (q.sec (q.pr (incA D _)))
  rw [q.sec_pr, q.sec_pr, mul_left_comm, ← map_mul, ← mul_assoc D.host.xi0, hs, one_mul]

theorem columnCharacter_reduction_eq_exp {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok)
    (G : Formalism.L2.Forms.GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG)
    (hpsi : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ n : ℕ,
      G.psi0 j v h (n : Formalism.L2.Forms.kv B.host.F v) = B.embLL (I.Ch.psi0 w (n : 𝓞 B.fields.E ⧸ w.1.asIdeal)))
    (P : HeightOneSpectrum (𝓞 B.host.E)) (hPP : P ∈ (B.primes X).vGs) (j : Fin 2)
    (h : (B.host.g j : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal) (z : 𝓞 B.host.E)
    (w : (P.under (𝓞 B.host.F)).adicCompletionIntegers B.host.F)
    (hw : (w : (P.under (𝓞 B.host.F)).adicCompletion B.host.F) =
      G.phi j _ h ((z : B.host.E) ⊗ₜ[B.host.F] (1 : (P.under (𝓞 B.host.F)).adicCompletion B.host.F)))
    {s : 𝓞 B.host.E} (hs : B.host.xi0 * (s : B.host.E) = 1) (hsP : s ∉ P.asIdeal) :
    (Formalism.L2.Col.qOf P).Prime ∧ ∃ b : ℤ, z - s * b ∈ P.asIdeal ∧ G.psi0 j _ h (IsLocalRing.residue _ w) =
      Complex.exp (2 * Real.pi * Complex.I * b / ((Formalism.L2.Col.qOf P : ℕ) : ℂ)) := by
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨P', hP, ρ, hPu, hres⟩ := TC.GLev0.exists_w (X := X) G hG j _ h
  have hwP : P' = P := TC.GLev0.vGs_inj (X := X) hPP (TC.GLev0.mem_vGs.2 ⟨j, hP⟩) hPu
  subst hwP
  have hq : Formalism.L2.Col.qOf P' = B.host.g j := hPr.vG_norm j _ hP
  refine ⟨by rw [hq]; exact hPr.g_prime j, ?_⟩
  obtain ⟨n, hn⟩ := TC.GLev0.exists_natCast (X := X) hPP (Ideal.Quotient.mk _ z)
  obtain ⟨b, hb⟩ := TC.GLev0.exists_natCast (X := X) hPP (Formalism.L2.Col.redP P' B.host.xi0 * n)
  have hred := Formalism.L2.Col.reduction_spec P' (a := B.host.xi0) (r := 1) hsP (by rw [map_one, mul_comm]; exact hs)
  refine ⟨b, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_mul, Int.cast_natCast, map_natCast, hb, ← mul_assoc, hred, map_one, one_mul, hn]
  obtain ⟨hh, e⟩ := hres (Formalism.UG.inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (z : B.host.E)) (Ideal.Quotient.mk _ z)
    (by rw [adAt_inclE]; exact hasRes_coe _ z)
  have ew : w = ⟨_, hh⟩ := Subtype.ext hw
  have e2 : IsLocalRing.residue _ w = (n : Formalism.L2.Forms.kv B.host.F _) := by
    rw [ew]
    exact e.trans ((congrArg ρ hn.symm).trans (map_natCast ρ n))
  have e3 := hpsi j _ h ⟨_, hPP⟩ rfl n
  have e4 := hI.weil ⟨_, hPP⟩ (n : _) (b : ℤ) ((hb.symm).trans (Int.cast_natCast b).symm)
  rw [e2]
  exact e3.trans e4

theorem psi_uniformizer_eq_psi_zero : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ (i : Fin a.n) (j : Fin 2) (h : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).asIdeal) (z : 𝓞 (I.rec7 l Z).host.E) (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletionIntegers (I.rec7 l Z).host.F), (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F) = (F0 W u).gl.phi j _ h ((z : (I.rec7 l Z).host.E) ⊗ₜ[(I.rec7 l Z).host.F] (1 : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F)) → ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) : ℂ) = (F0 W u).gl.psi0 j _ h (IsLocalRing.residue _ w) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ i j h z w hw
  obtain ⟨hS⟩ := hA.tr.std
  have hR := (ha.tie row col).2
  have hPP : (a.pl i).1 ∈ (B.primes X).vGs := (hA.lev.2.1 _).1 (a.pl i).2
  have hid := (hR.idem i).1
  have hsq := GlobalTheory.LevelUnif.norm_notMem_sq (D := I.rec7 l Z) (hA.lev.1.1 _ (a.pl i).2)
  have hu := GlobalTheory.LevelUnif.unif_of_read (D := I.rec7 l Z) _ _ _ hR hA.lev.1 i
  obtain ⟨s, hs⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer (I.rec7 l Z).host
  have hsP : s ∉ (a.pl i).1.asIdeal := fun hm => by
    have h1 := (prO_lt (a.G i).q hid s).1 hm
    have h2 := xi_unit (a.G i).q (a.G i).unit (GlobalTheory.LocMod.Witness.xi_ne _)
    have h3 : (ofSplit (a.G i).q).xi * prO (a.G i).q s = 1 :=
      (((a.G i).q.pr.comp (incA (I.rec7 l Z))).map_mul _ _).symm.trans
        ((congrArg ((a.G i).q.pr.comp (incA (I.rec7 l Z))) hs).trans (map_one _))
    have h4 := congrArg (valuation (a.G i).k) h3
    rw [map_mul, h2, one_mul, map_one] at h4
    exact h1.ne h4
  obtain ⟨hp, b, hz, e⟩ := columnCharacter_reduction_eq_exp I hA.tr.ok (F0 W u).gl (hS u).gl.piG (hS u).gl.psi (a.pl i).1 hPP j h z w hw hs hsP
  exact (weil_unif_eq_exp (a.G i).q hid (a.G i).S.cond W.Q.stdChar (a.G i).char hp rfl hsq (a.G i).S.unif hu
    hs hz).trans e.symm

end GlobalTheory.FamTraceChiColChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowChoiceValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

namespace GlobalTheory.LevUnif

theorem unif_of_gRead : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u) (row : ∀ t, RowCh (pk W) (lvP W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), GRead (a.fam row col) a.G a.pl → ∀ n : Fin a.n, valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a row col hR n
  exact GlobalTheory.LevelUnif.unif_of_read (D := I.rec7 l Z) _ _ _ hR hW.lev.1 n

end GlobalTheory.LevUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeIndexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_tuple_free_index : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : QJ a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : QJ a t), J.Reads → ∀ i, ¬ GlobalTheory.PenBridge.plF J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), GlobalTheory.PenBridge.rd J j hj g i ∈ KO (J.G i).k _ := by
  first | exact @GlobalTheory.PenBridge.rd_mem_KO_off_twist | exact GlobalTheory.PenBridge.rd_mem_KO_off_twist | (intros; apply GlobalTheory.PenBridge.rd_mem_KO_off_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainThetaLiftUpSpanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedChain_thetaLiftUpSpan : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ D : D7, LevelLawQ D → UpSpanQ D := by
  first | exact @GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of | exact GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of | (intros; apply GlobalTheory.ChainTw.UpSpanTw.upSpanQ_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataUnitShiftRelationStatement
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_data_unit_shift_relation : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), ∀ u (f : FamCh W u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : ∀ t, (ι → 𝓀[k]ˣ) → (f.t t).Col 0 → (f.t t).Col 0), RamUnitary D → f.c.Is → (∀ t, (f.t t).Is ∧ (f.t t).KBack ∧ (f.t t).TailRd ∧ LiftS o (f.t t) ∧ ReadS o (f.t t) ε (S₀ t)) → o.I.Nodup → (∀ i, i ∈ o.I) → (Function.Injective fun i => (o.p i).v) → (∀ t, Nonempty ((f.t t).Ch 0)) → (∀ t φ, col0 f t φ ∈ (f.t t).Ram 0 ∧ ∀ α y, (f.t t).rd 0 α (col0 f t φ) y = (chart0 (F0 W u)).rd W.Q.Rl.θ (D.eMu u φ).1 y) → (∀ t, ∀ ψ ∈ (f.t t).Ram 0, ∃ φ, ψ = col0 f t φ) → LinkComm f := by
  first | exact @GlobalTheory.MiTop.linkComm_of_laws | exact GlobalTheory.MiTop.linkComm_of_laws | (intros; apply GlobalTheory.MiTop.linkComm_of_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.UnrAll

theorem unrCorr_all : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun _ => True) := by
  intro _hDec hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw _
  by_cases hc : Formalism.IndefR.Lev.IsConjPl w w
  · exact GlobalTheory.DownInert.unrCorr_inert hHowe D G Pl0 T A Ks R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
  · exact GlobalTheory.SplitCorr.unrCorr_split D G Pl0 T A Ks R F hG hFull i t h hh s c y hy h1 h2 B B' hB hB' w hw hc

end GlobalTheory.UnrAll
end

