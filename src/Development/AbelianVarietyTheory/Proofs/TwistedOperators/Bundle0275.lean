import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicMeanThetaProductConjEqRestrictionProduc
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanProd

variable {D : D7}

local infixl:70 " ⬝ " => HMul.hMul

theorem symplOH_iso_mid {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (q₀ : Matrix (Fin W.rank) (Fin r) D.host.E) (a : Mx D W.rank r) (x : WO V' W) :
    symplOH V W (isoPart V W C (q₀.map (incA D))) (isoPart V W C a + midPart V V' W B x) = 0 := by
  set P : Mx D r V.rank := GlobalTheory.MixModel.rat (adj D C * V.gram) with hP
  set Q : Mx D V'.rank V.rank := GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) with hQ
  have hG := GlobalTheory.MixModel.gram_conjTranspose V
  have hG' := GlobalTheory.MixModel.gramInv_conjTranspose V'
  have hU := GlobalTheory.MixModel.gram_isUnit_det V
  have hC0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hO : adj D C * V.gram * B = 0 := hs.orth
  have k1 : P ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj P = 0 := by
    rw [hP, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (Cᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * C = 0 at hC0
      rw [Matrix.conjTranspose_mul, hG, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc (Cᴴ * V.gram),
        ← Matrix.mul_assoc V.gram⁻¹, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, hC0]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have k2 : P ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj Q = 0 := by
    rw [hP, hQ, ← GlobalTheory.MixModel.rat_conjTranspose, GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
      change Cᴴ * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * Bᴴ * V.gram)ᴴ = 0
      change Cᴴ * V.gram * B = 0 at hO
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hG, hG', Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc (Cᴴ * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ hU, Matrix.one_mul, ← Matrix.mul_assoc, hO, Matrix.zero_mul]
    rw [this, GlobalTheory.MixModel.rat_zero]
  have e1 : isoPart V W C (q₀.map (incA D)) = GlobalTheory.MixModel.rat q₀ ⬝ P := rfl
  have e2 : isoPart V W C a + midPart V V' W B x = a ⬝ P + x ⬝ Q := rfl
  have k3 : P ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q) = 0 := by
    rw [GlobalTheory.MixModel.adj_add, GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_mul, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, k1, k2, Matrix.zero_mul, Matrix.zero_mul, add_zero]
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, e1, e2]
  have e3 : GlobalTheory.MixModel.giA V ⬝ (GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q) ⬝ (GlobalTheory.MixModel.gA W ⬝ (GlobalTheory.MixModel.rat q₀ ⬝ P))) =
      (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q) ⬝ GlobalTheory.MixModel.gA W ⬝ GlobalTheory.MixModel.rat q₀) ⬝ P := by
    simp only [Matrix.mul_assoc]
  rw [e3, Matrix.trace_mul_comm]
  have e4 : P ⬝ (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q) ⬝ GlobalTheory.MixModel.gA W ⬝ GlobalTheory.MixModel.rat q₀) =
      (P ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj (a ⬝ P + x ⬝ Q)) ⬝ (GlobalTheory.MixModel.gA W ⬝ GlobalTheory.MixModel.rat q₀) := by
    simp only [Matrix.mul_assoc]
  rw [e4, k3, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem iso_periodic {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ}
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ a,
      f (isoPart V W C (γ + a) + midPart V V' W B x) = f (isoPart V W C a + midPart V V' W B x) := by
  rintro _ ⟨q₀, rfl⟩ a
  have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
  have hadd : isoPart V W C (q₀.map (incA D) + a) = isoPart V W C (q₀.map (incA D)) + isoPart V W C a :=
    Matrix.add_mul _ _ _
  have hrat : ratW W V (q₀ * (adj D C * V.gram)) = isoPart V W C (q₀.map (incA D)) := Matrix.map_mul
  rw [e3, hadd, add_assoc, ← hrat, hf.quasi, hrat, symplOH_iso_mid hs, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.IsoMeanProd

namespace GlobalTheory.IsoMeanProd

theorem mean_iso_mul_star : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ ∂μ = ∫ x in 𝓕', res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) ∂μ' := by
  intro D V V' W r C B hs ψ hψ μ 𝓨 hμ μ' 𝓕' hμ' h𝓕' F G hF hG
  have hμ1 : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (WO V' W) := ⟨rfl⟩
  haveI hfin1 : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hμ.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (μ'.restrict 𝓕') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (GlobalTheory.Size.measure_dom hμ' h𝓕').2⟩
  haveI hsf1 : SigmaFinite (μ.restrict 𝓨) := @IsFiniteMeasure.toSigmaFinite _ _ _ hfin1
  haveI : SFinite (μ.restrict 𝓨) := @instSFiniteOfSigmaFinite _ _ _ hsf1
  haveI : SigmaFinite (μ'.restrict 𝓕') := inferInstance
  haveI : SFinite (μ'.restrict 𝓕') := inferInstance
  obtain ⟨cF, hcF⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hF
  obtain ⟨cG, hcG⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hG
  have ciso : Continuous (fun y : Mx D W.rank r => isoPart V W C y) := continuous_id.matrix_mul continuous_const
  have cmid : Continuous (fun x : WO V' W => midPart V V' W B x) := continuous_id.matrix_mul continuous_const
  obtain ⟨H, hH⟩ : ∃ H : Mx D W.rank r → Mx D W.rank r → WO V' W → ℂ, H = fun y y' x =>
      F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) := ⟨_, rfl⟩
  have hHb : ∀ y y' x, ‖H y y' x‖ ≤ cF * cG := by
    intro y y' x
    rw [hH, norm_mul, norm_star]
    exact mul_le_mul (hcF _) (hcG _) (norm_nonneg _) ((norm_nonneg _).trans (hcF 0))
  have hHc : Continuous fun p : Mx D W.rank r × Mx D W.rank r × WO V' W => H p.1 p.2.1 p.2.2 := by
    rw [hH]
    exact (hF.cont.comp ((ciso.comp (continuous_fst.add continuous_snd.fst)).add (cmid.comp continuous_snd.snd))).mul
      (continuous_star.comp (hG.cont.comp ((ciso.comp continuous_snd.fst).add (cmid.comp continuous_snd.snd))))
  have hint : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X)
      [IsFiniteMeasure ν] (g : X → ℂ), Continuous g → (∀ z, ‖g z‖ ≤ cF * cG) → Integrable g ν :=
    fun ν _ g hg hb => Integrable.of_bound hg.aestronglyMeasurable _ (Filter.Eventually.of_forall hb)
  have hI1 : ∀ y, Integrable (Function.uncurry fun y' x => H y y' x) ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) :=
    fun y => hint _ _ (hHc.comp (continuous_const.prodMk continuous_id)) fun z => hHb _ _ _
  have hI3 : Integrable (fun q : (Mx D W.rank r × WO V' W) × Mx D W.rank r => H q.1.1 q.2 q.1.2)
      (((μ.restrict 𝓨).prod (μ'.restrict 𝓕')).prod (μ.restrict 𝓨)) :=
    hint _ _ (hHc.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))) fun z => hHb _ _ _
  have hI2 : Integrable (Function.uncurry fun y x => ∫ y', H y y' x ∂(μ.restrict 𝓨))
      ((μ.restrict 𝓨).prod (μ'.restrict 𝓕')) := hI3.integral_prod_left
  have hI4 : ∀ x, Integrable (Function.uncurry fun y y' => H y y' x) ((μ.restrict 𝓨).prod (μ.restrict 𝓨)) :=
    fun x => hint _ _ (hHc.comp (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))) fun z => hHb _ _ _
  have step4 : ∀ x y', ∫ y in 𝓨, H y y' x ∂μ =
      res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) := by
    intro x y'
    rw [hH]
    simp only
    rw [integral_mul_const]
    congr 1
    exact GlobalTheory.MixModel.covolOne_integral_add hμ1 (fun a => F (isoPart V W C a + midPart V V' W B x))
      (iso_periodic hs hF x) y'
  have step5 : ∀ x, ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ =
      res V V' W C B μ 𝓨 F x * star (res V V' W C B μ 𝓨 G x) := by
    intro x
    rw [integral_const_mul]
    congr 1
    exact integral_conj
  have e0 : ∀ y y' x, F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) = H y y' x := by
    intro y y' x; rw [hH]
  simp only [e0]
  calc ∫ y in 𝓨, ∫ y' in 𝓨, ∫ x in 𝓕', H y y' x ∂μ' ∂μ ∂μ
      = ∫ y in 𝓨, ∫ x in 𝓕', ∫ y' in 𝓨, H y y' x ∂μ ∂μ' ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => integral_integral_swap (hI1 y))
    _ = ∫ x in 𝓕', ∫ y in 𝓨, ∫ y' in 𝓨, H y y' x ∂μ ∂μ ∂μ' := integral_integral_swap hI2
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, ∫ y in 𝓨, H y y' x ∂μ ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => integral_integral_swap (hI4 x))
    _ = ∫ x in 𝓕', ∫ y' in 𝓨, res V V' W C B μ 𝓨 F x * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ ∂μ' :=
        integral_congr_ae (Filter.Eventually.of_forall fun x =>
          integral_congr_ae (Filter.Eventually.of_forall fun y' => step4 x y'))
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => step5 x)

end GlobalTheory.IsoMeanProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteLeOfGKStableDiscreteSeriesModel
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HCModIrred

open GlobalTheory.TypeSum Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace

section Model

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mem_of_dense (h : Std ε σ) {W : Submodule ℂ H} (hd : Dense (W : Set H))
    (hW : ∀ w ∈ W, IsKFin ε σ w) (hK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W) {v : H} (hv : IsKFin ε σ v) :
    v ∈ W := by
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  have havgW : ∀ e : KG ε → ℂ, Continuous e → ∀ x ∈ W, kAvg ε σ e x ∈ W := by
    intro e he x hx
    obtain ⟨S, hS, hxS, hKS⟩ := hW x hx
    haveI := hS
    haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W
    have hKSW : IsKStableOn ε σ (S ⊓ W) := fun g hg y hy =>
      Submodule.mem_inf.2 ⟨hKS g hg y (Submodule.mem_inf.1 hy).1, hK g hg y (Submodule.mem_inf.1 hy).2⟩
    exact (Submodule.mem_inf.1 (c4 e he _ inferInstance hKSW x (Submodule.mem_inf.2 ⟨hxS, hx⟩))).2
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ W := by
    intro e he hc w
    obtain ⟨m, b, c, -, -, -, hbc⟩ := kAvg_finite_rank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (W ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right W F
    have hcl : IsClosed (Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (W : Set H) ⊆ Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact havgW e hc x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hd w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hKS⟩ := hv
  haveI := hS
  haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ W).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hKS⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hKS y hyS, hrange _ hk hc y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

theorem inner_exp_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {W : Submodule ℂ H} (hW : ∀ w ∈ W, IsKFin ε σ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hXg : inG ε X) (hX : ∀ w ∈ W, dRep σ X w ∈ W)
    {a : H} (ha : a ∈ W) {y : H} (hy : y ∈ Wᗮ) (t : ℝ) :
    ⟪y, σ (NormedSpace.exp (t • X)) a⟫_ℂ = 0 := by
  have hXl : X ∈ GlobalTheory.SmoothGlob.lieSet ε := hXg
  have hsplit : ∀ s t : ℝ, NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
    intro s t
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left t |>.smul_right (s - t))]
    congr 1
    rw [← add_smul]; congr 1; ring
  have hderiv : ∀ v, IsKFin ε σ v → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (σ (NormedSpace.exp (t • X)) (dRep σ X v)) t := by
    intro v hv t
    have han := (hHC.analytic hU hI hv).analytic_exp (one_mem_UJ ε) hXg 0
    simp only [one_mul] at han
    have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (dRep σ X v) 0 :=
      han.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s - t) • X)) v) (dRep σ X v) t := by
      have := HasDerivAt.comp_sub_const (f := fun s : ℝ => σ (NormedSpace.exp (s • X)) v) t t (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((σ (NormedSpace.exp (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show σ (NormedSpace.exp (s • X)) v = σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((s - t) • X)) v)
    rw [hsplit s t, sigma_mul hU (exp_mem_UJ hXl t) (exp_mem_UJ hXl (s - t))]
  have hmem : ∀ k : ℕ, (dRep σ X)^[k] a ∈ W := by
    intro k
    induction k with
    | zero => exact ha
    | succ k ih => rw [Function.iterate_succ_apply']; exact hX _ ih
  let f : ℕ → ℝ → ℂ := fun k s => ⟪y, σ (NormedSpace.exp (s • X)) ((dRep σ X)^[k] a)⟫_ℂ
  have hf : ∀ k s, HasDerivAt (f k) (f (k + 1) s) s := by
    intro k s
    have h := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hderiv _ (hW _ (hmem k)) s)
    simp only [f, Function.iterate_succ_apply']
    exact h
  have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [iteratedDeriv_succ, ih]; funext s; exact (hf k s).deriv
  have hA : AnalyticOnNhd ℝ (f 0) Set.univ := by
    intro s _
    have := ((hHC.analytic hU hI (hW a ha)).clm ((innerSL ℂ y).restrictScalars ℝ)).analytic_exp (one_mem_UJ ε) hXg s
    simp only [one_mul] at this
    exact this
  have h0 : ∀ k, f k 0 = 0 := by
    intro k
    simp only [f, zero_smul, NormedSpace.exp_zero, sigma_one hU]
    exact Submodule.inner_left_of_mem_orthogonal (hmem k) hy
  have htop : analyticOrderAt (f 0) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro m
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)]
    intro i _
    rw [hit, h0]
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.mp htop) (Set.mem_univ t)

theorem dense_of_stable (hHC : GlobalTheory.Published.HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {W : Submodule ℂ H} (hW : ∀ w ∈ W, IsKFin ε σ w)
    (hX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W) (hK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W) (h0 : W ≠ ⊥) :
    Dense (W : Set H) := by
  have hexp : ∀ X, inG ε X → ∀ x ∈ W.topologicalClosure, σ (NormedSpace.exp X) x ∈ W.topologicalClosure := by
    intro X hXg x hx
    have hW1 : ∀ a ∈ W, σ (NormedSpace.exp X) a ∈ W.topologicalClosure := by
      intro a ha
      rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
      intro y hy
      have := inner_exp_eq_zero hHC hU hI hW hXg (hX X hXg) ha hy 1
      rwa [one_smul] at this
    have hcl : IsClosed ((σ (NormedSpace.exp X)) ⁻¹' (W.topologicalClosure : Set H)) :=
      (Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)
    exact closure_minimal (fun a ha => hW1 a ha) hcl hx
  have hKc : ∀ k ∈ Kset ε, ∀ x ∈ W.topologicalClosure, σ k x ∈ W.topologicalClosure := fun k hk x hx =>
    map_mem_closure (σ k).continuous hx (hK k hk)
  have hinv : ∀ g ∈ UJset ε, ∀ x ∈ W.topologicalClosure, σ g x ∈ W.topologicalClosure := by
    intro g hg x hx
    obtain ⟨k, P, hk, hP, rfl⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 g hg
    have hPl : P ∈ GlobalTheory.SmoothGlob.lieSet ε := hP.1
    have hPe : NormedSpace.exp P ∈ UJset ε := by simpa using exp_mem_UJ hPl 1
    rw [sigma_mul hU (K_le_UJ hk) hPe]
    exact hKc k hk _ (hexp P hP.1 x hx)
  rcases hI _ (Submodule.isClosed_topologicalClosure W) hinv with h | h
  · exact absurd (le_bot_iff.1 (h ▸ W.le_topologicalClosure)) h0
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

end Model

open Formalism.IndefR.Mult in

theorem kFin_le_of_stable : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S) (τ : D.what₂.Tau) (W : Submodule ℂ (M.H τ)), W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →
    (∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W) → W ≠ ⊥ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ W := by
  intro hHC D V S M τ W hWk hX hK h0
  obtain ⟨hc, -, hU, hI, -⟩ := M.ds τ
  haveI := hc
  have hfr : IsUnit (M.fr τ) := M.fr_unit τ
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hW : ∀ w ∈ W, IsKFin (M.ε τ) (M.σ τ) w := fun w hw => hWk hw
  have hX' : ∀ X, inG (M.ε τ) X → ∀ w ∈ W, dRep (M.σ τ) X w ∈ W := by
    intro X hXg w hw
    have hXg' : Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X = 0 := hXg
    have hmem : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
      show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
      rw [← M.fr_gram τ]
      have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
      calc ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Jm (M.ε τ) * M.fr τ) +
            (M.fr τ)ᴴ * Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ)
          = (M.fr τ)ᴴ * Xᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Jm (M.ε τ) * M.fr τ +
            (M.fr τ)ᴴ * Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * X * M.fr τ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (M.fr τ)ᴴ * (Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X) * M.fr τ := by
            rw [h1, Matrix.mul_nonsing_inv _ hd]
            simp only [Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hXg']; simp
    have e : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w := by
      unfold dRep
      congr 1
      funext t
      rw [DSModel.rep, GlobalTheory.SmVec.exp_conj_inv hfr X t]
      congr 2
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [← e]
    exact hX _ hmem w hw
  have hK' : ∀ k ∈ Kset (M.ε τ), ∀ w ∈ W, M.σ τ k w ∈ W := by
    intro k hk w hw
    have e : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    have hm : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
      show M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
      rw [e]; exact hk
    have := hK _ hm w hw
    rwa [DSModel.rep, e] at this
  have hdense := dense_of_stable hHC hU hI hW hX' hK' h0
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  intro v hv
  exact mem_of_dense hstd hdense hW hK' hv

end GlobalTheory.HCModIrred

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyIntegrableExtChar
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special

theorem integrableOn_translate {n : ℕ} (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure]
    (Θ' : SUJ ε → ℂ) (h : LocallyIntegrable Θ' μ') (c : SUJ ε) {K : Set (SUJ ε)} (hK : IsCompact K) :
    IntegrableOn (fun g => Θ' (c * g)) K μ' := by
  have h1 : IntegrableOn Θ' ((fun g => c * g) '' K) μ' :=
    h.integrableOn_isCompact (hK.image (continuous_const.mul continuous_id))
  have h2 := ((measurePreserving_mul_left μ' c).integrableOn_comp_preimage
    (MeasurableEquiv.mulLeft c).measurableEmbedding).2 h1
  exact h2.mono_set (Set.subset_preimage_image _ _)

theorem integrableOn_avgChar {n : ℕ} [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure]
    (m : ℤ) (Θ' : SUJ ε → ℂ) (h : LocallyIntegrable Θ' μ') {K : Set (SUJ ε)} (hK : IsCompact K) :
    IntegrableOn (avgChar ε m Θ') K μ' := by
  unfold avgChar
  exact (integrable_finset_sum _ fun j _ => (integrableOn_translate ε μ' Θ' h _ hK).const_mul _).const_mul _

theorem locallyIntegrable_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), LocallyIntegrable Θ' μ' → AEStronglyMeasurable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) → LocallyIntegrable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
  intro n _ ε μ' _ m Θ' h hm
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  rw [locallyIntegrable_iff]
  intro K hK
  have hP : IsCompact (scalarMul ε ⁻¹' K) := by
    have := (isProperMap_iff_tendsto_cocompact.2 ⟨hsc, GlobalTheory.SqIntSU.scalarMul_proper ε⟩)
    exact this.isCompact_preimage hK
  have hK' : IsCompact (Prod.snd '' (scalarMul ε ⁻¹' K)) := hP.image continuous_snd
  have hmr := hm.restrict (s := K)
  rw [IntegrableOn]
  rw [Measure.restrict_map hsc.measurable hK.measurableSet] at hmr ⊢
  rw [integrable_map_measure hmr hsc.measurable.aemeasurable]
  have hz : Integrable (fun z : Circle => (z : ℂ) ^ m) circleHaar := by
    have hc : Continuous (fun z : Circle => (z : ℂ) ^ m) :=
      (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).zpow₀ m fun z => Or.inl (Circle.coe_ne_zero z)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 := hz.mul_prod (integrableOn_avgChar ε μ' m Θ' h hK')
  have h2 : IntegrableOn (fun p : Circle × SUJ ε => (p.1 : ℂ) ^ m * avgChar ε m Θ' p.2)
      (Set.univ ×ˢ (Prod.snd '' (scalarMul ε ⁻¹' K))) (circleHaar.prod μ') := by
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
    exact h1
  have h3 := h2.mono_set (t := _) (s := scalarMul ε ⁻¹' K) fun p hp => ⟨trivial, p, hp, rfl⟩
  have e : extChar ε m Θ' ∘ scalarMul ε = fun p : Circle × SUJ ε => (p.1 : ℂ) ^ m * avgChar ε m Θ' p.2 := by
    funext p
    exact extChar_scalarMul ε m Θ' p.1 p.2
  rw [e]
  exact h3

end GlobalTheory.ExtChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaximalCompactActsOnFockVectorsBySubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCompact_acts_on_fockVectors_by_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ g h, IsAtTau θ S τ (BS τ * κS * (BS τ)⁻¹) g → IsAtTau θ T τ (BT τ * κT * (BT τ)⁻¹) h → ∀ c : ℂ, om (g, h) f = c • f → ∀ P, om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = c • pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  first | exact @GlobalTheory.FockCompact.om_pureTensorO_compact | exact GlobalTheory.FockCompact.om_pureTensorO_compact | (intros; apply GlobalTheory.FockCompact.om_pureTensorO_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKFinOfMemLowT
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
  MeasureTheory NumberField Matrix

namespace GlobalTheory.KFiniteDetermined

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_kFin_of_mem_lowT {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {v : M.sm τ} (hv : v ∈ lowT M τ) : (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ :=
  (sSup_le (a := GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) fun A hA _ hw => ⟨A, hA.1, hw, hA.2.1⟩) hv

theorem restrInj : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.RestrInj D :=
  fun D θ hθ V S M J χ T hT h0 =>
    GlobalTheory.LowTypeDetermined.eq_zero_of_lowT D V S M θ hθ (GlobalTheory.LowTypeRestriction.lowT_ne_bot M) J χ T hT
      fun v => h0 _ fun τ => mem_kFin_of_mem_lowT M τ (v τ).2

end GlobalTheory.KFiniteDetermined
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowthSobolevSize_rightTranslate_polyBound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (d N : ℕ), ∃ (C : NNReal) (m : ℕ), ∀ h ∈ GinfC V, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V d N (rTr V h φ) ≤ (C : ENNReal) * ENNReal.ofReal (GlobalTheory.Grow.height V h ^ m) * GlobalTheory.Size.growthSob θ V d N φ := by
  first | exact @GlobalTheory.Size.Translate.growthSob_rTr_le | exact GlobalTheory.Size.Translate.growthSob_rTr_le | (intros; apply GlobalTheory.Size.Translate.growthSob_rTr_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSatakeLeOfUnitarySphericalGLStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_satake_le_of_unitary_spherical_GL : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (B : Multiset ℂˣ), GlobalTheory.LGrp.IsIrrSmooth ρ → GlobalTheory.LGrp.IsUnitarisable ρ → HasSatGL w ρ B → ∀ b ∈ B, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) := by
  first | exact @GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL | exact GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL | (intros; apply GlobalTheory.LFun.SatBoundGL.norm_le_of_hasSatGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reductionTrivial_of_conjugatePlace_selfDual : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank), IsSelfDualC V L → ∀ β : GL (Fin V.rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame β L → ∀ k : GA D V, Lev.finE V k ∈ Formalism.L2.DIV.St β → ∀ (PP PP' : Formalism.L2.DIV.Pl D.host.E), Formalism.IndefR.Lev.IsConjPl PP' PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V k) = 1 → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  first | exact @GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj | exact GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj | (intros; apply GlobalTheory.ConjPlaceRedGen.redFn_eq_one_of_conj <;> assumption)
end

