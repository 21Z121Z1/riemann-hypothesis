import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0199
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0257

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankFacGen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal

noncomputable section
namespace GlobalTheory.TowerCT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem vol : ∀ (D : D7) (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → κ 𝓝 ≠ ⊤ := by
  intro D V r C hC κ 𝓝 hκ h𝓝
  have hint : IntegrableOn (fun _ : NI V C => (1 : ℂ)) 𝓝 κ := by
    have key : ∀ N : Subgroup (GA D V),
        N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => (1 : ℂ)) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => 1) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) κ 𝓝 hκ h𝓝
  rcases (integrableOn_const_iff (C := (1 : ℂ))).1 hint with h | h
  · exact absurd h (by simp)
  · exact h.ne

theorem cusp : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    ∀ (ν : Measure (GA D W)), ν.IsHaarMeasure → ∀ F : GA D W → ℂ, GlobalTheory.Grow.RapidDec W F → IsCuspFun W F →
    ∀ Γ : Subgroup (GA D W), Γ ≤ GQ W → (∀ γ ∈ Γ, ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) →
    (∀ n ∈ NI W L, n ∈ GQ W → n ∈ Γ) → ∀ K : GA D W → ℂ, Measurable K → (∀ n ∈ NI W L, ∀ h, K (n * h) = K h) →
    (∀ γ ∈ Γ, ∀ h, K (γ * h) = K h) → ∀ 𝓖 : Set (GA D W), IsFundamentalDomain Γ 𝓖 ν →
    IntegrableOn (fun h => K h * F h) 𝓖 ν → ∫ h in 𝓖, K h * F h ∂ν = 0 := by
  intro D W s L hL ν hν F hF hcusp Γ hle hnorm hin K hKm hKn hKγ 𝓖 h𝓖 hint
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hcl := GlobalTheory.CuspDecay.Model.isClosed_NI W hL
  have : LocallyCompactSpace (NI W L) := hcl.locallyCompactSpace
  have hQ : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  let i : NIQ W L → GQ W := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ W => z.1) h))
  have : DiscreteTopology (NIQ W L) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ W L) := hi.countable
  have : SecondCountableTopology (NI W L) := TopologicalSpace.Subtype.secondCountableTopology _
  let κ : Measure (NI W L) := Measure.haar
  obtain ⟨𝓝, h𝓝⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ W L) κ
  have hκ : κ.IsHaarMeasure := inferInstance
  have hΓ : Countable Γ := (Subgroup.inclusion_injective hle).countable
  have e : Γ.subgroupOf (NI W L) = NIQ W L := by
    ext n
    exact ⟨fun h => hle h, fun h => hin _ n.2 h⟩
  have h𝓝' : IsFundamentalDomain (Γ.subgroupOf (NI W L)) 𝓝 κ := by
    rw [e]
    exact h𝓝
  exact GlobalTheory.T.unfolding_zero_mean_normalized_subgroup (GA D W) ν Γ (NI W L) hΓ hcl hnorm κ 𝓝 hκ h𝓝' (vol D W s L hL κ 𝓝 hκ h𝓝) K F hKm
    hF.2.1.measurable hKn hKγ (fun γ hγ h => hF.1 γ (hle hγ) h) (fun h => hcusp s L hL κ 𝓝 hκ h𝓝 h) 𝓖 h𝓖 hint

theorem rankFacGen {K : Type} [Field K] {a b : ℕ} (y : Matrix (Fin a) (Fin b) K) (hy : y ≠ 0) :
    ∃ (s : ℕ) (L : Matrix (Fin a) (Fin s) K) (m : Matrix (Fin s) (Fin b) K) (m' : Matrix (Fin b) (Fin s) K),
      0 < s ∧ LinearIndependent K L.transpose ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  classical
  let U : Submodule K (Fin a → K) := Submodule.span K (Set.range y.transpose)
  let s := Module.finrank K U
  let bs : Module.Basis (Fin s) K U := Module.finBasisOfFinrankEq K U rfl
  have hcol : ∀ j, y.transpose j ∈ U := fun j => Submodule.subset_span ⟨j, rfl⟩
  let L : Matrix (Fin a) (Fin s) K := Matrix.of fun i k => (bs k : Fin a → K) i
  let m : Matrix (Fin s) (Fin b) K := Matrix.of fun k j => bs.repr ⟨y.transpose j, hcol j⟩ k
  have hym : y = L * m := by
    ext i j
    have h := bs.sum_repr ⟨y.transpose j, hcol j⟩
    have h2 := congrArg (fun u : U => (u : Fin a → K) i) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    simp only [Matrix.mul_apply, L, m, Matrix.of_apply]
    rw [show y i j = y.transpose j i from rfl, ← h2]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hLi : LinearIndependent K L.transpose := by
    have : LinearIndependent K fun k => (bs k : Fin a → K) := bs.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    exact this
  have hrk : y.rank = s := by
    rw [Matrix.rank_eq_finrank_span_cols]
    rfl
  have hs : 0 < s := by
    refine Nat.pos_of_ne_zero fun h => hy ?_
    have hU : U = ⊥ := Submodule.finrank_eq_zero.1 h
    ext i j
    have := hcol j
    rw [hU, Submodule.mem_bot] at this
    exact congrFun this i
  have hle : s ≤ m.rank := by
    calc s = y.rank := hrk.symm
      _ = (L * m).rank := by rw [← hym]
      _ ≤ m.rank := Matrix.rank_mul_le_right _ _
  have hm : m.rank = s := le_antisymm ((Matrix.rank_le_height m)) hle
  have hsurj : Function.Surjective m.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    have : Module.finrank K (LinearMap.range m.mulVecLin) = s := hm
    simpa using this
  obtain ⟨g, hg⟩ := m.mulVecLin.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  refine ⟨s, L, m, LinearMap.toMatrix' g, hs, hLi, hm, ?_, hym⟩
  have : Matrix.toLin' (m * LinearMap.toMatrix' g) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    exact hg
  apply Matrix.toLin'.injective
  rw [this, Matrix.toLin'_one]

theorem rankFac : ∀ (D : D7) (W : HSp D) (r : ℕ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), y ≠ 0 →
    adj D y * W.gram * y = 0 → ∃ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E)
      (m' : Matrix (Fin r) (Fin s) D.host.E), IsIsoFrame W L ∧ m.rank = s ∧ m * m' = 1 ∧ y = L * m := by
  intro D W r y hy hiso
  obtain ⟨s, L, m, m', hs, hL, hm, hmm, e⟩ := rankFacGen y hy
  refine ⟨s, L, m, m', ⟨hs, hL, ?_⟩, hm, hmm, e⟩
  have hLy : L = y * m' := by rw [e, Matrix.mul_assoc, hmm, Matrix.mul_one]
  have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) L = adj D m' * adj D y := by
    rw [hLy]
    simp only [adj, Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  rw [hc]
  calc adj D m' * adj D y * W.gram * L = adj D m' * (adj D y * W.gram * y) * m' := by
        rw [hLy]
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hiso, Matrix.mul_zero, Matrix.zero_mul]

theorem fub {N H Y : Type} [MeasurableSpace N] [MeasurableSpace H] [Countable Y]
    (κ : Measure N) (ν : Measure H) [SFinite κ] [SFinite ν] (𝓝 : Set N) (𝓕 : Set H)
    (T : Y → N → H → ℂ) (hT : ∀ y, Measurable (Function.uncurry (T y))) (Θ : N → H → ℂ)
    (F : H → ℂ) (hF : Measurable F) (hs : ∀ n h, HasSum (fun y => T y n h) (Θ n h))
    (hb : ∫⁻ n in 𝓝, ∫⁻ h in 𝓕, (∑' y, ‖T y n h‖ₑ) * ‖F h‖ₑ ∂ν ∂κ ≠ ⊤) :
    IntegrableOn (fun n => ∫ h in 𝓕, Θ n h * F h ∂ν) 𝓝 κ ∧
    (∑' y, ∫⁻ h in 𝓕, ‖(∫ n in 𝓝, T y n h ∂κ) * F h‖ₑ ∂ν) ≠ ⊤ ∧
    HasSum (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν)
      (∫ n in 𝓝, ∫ h in 𝓕, Θ n h * F h ∂ν ∂κ) := by
  set P := (κ.restrict 𝓝).prod (ν.restrict 𝓕) with hP
  let G : Y → N × H → ℂ := fun y p => T y p.1 p.2 * F p.2
  have hGm : ∀ y, Measurable (G y) := fun y => (hT y).mul (hF.comp measurable_snd)
  have hGe : ∀ y, Measurable fun p => ‖G y p‖ₑ := fun y => (hGm y).enorm
  have hlin : ∫⁻ p, ∑' y, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rw [hP, lintegral_prod _ (Measurable.ennreal_tsum hGe).aemeasurable]
    convert hb using 6 with n _ h
    simp only [G, enorm_mul]
    rw [ENNReal.tsum_mul_right]
  have hsum : ∑' y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := by
    rwa [← lintegral_tsum fun y => (hGe y).aemeasurable]
  have hfin : ∀ y, ∫⁻ p, ‖G y p‖ₑ ∂P ≠ ⊤ := fun y => ENNReal.ne_top_of_tsum_ne_top hsum y
  have hGi : ∀ y, Integrable (G y) P := fun y =>
    ⟨(hGm y).aestronglyMeasurable, lt_top_iff_ne_top.2 (hfin y)⟩
  have hsp : ∀ p : N × H, HasSum (fun y => G y p) (Θ p.1 p.2 * F p.2) := fun p => (hs p.1 p.2).mul_right _
  have hΘm : Measurable fun p : N × H => Θ p.1 p.2 * F p.2 :=
    measurable_of_tendsto_metrizable' Filter.atTop (f := fun (s : Finset Y) p => ∑ y ∈ s, G y p)
      (fun s => Finset.measurable_sum _ fun y _ => hGm y) (tendsto_pi_nhds.2 hsp)
  have hle : ∀ p : N × H, ‖Θ p.1 p.2 * F p.2‖ₑ ≤ ∑' y, ‖G y p‖ₑ := fun p =>
    le_of_tendsto' ((continuous_enorm.tendsto _).comp (hsp p)) fun s =>
      (enorm_sum_le s _).trans (ENNReal.sum_le_tsum s)
  have hΘi : Integrable (fun p : N × H => Θ p.1 p.2 * F p.2) P :=
    ⟨hΘm.aestronglyMeasurable, ((lintegral_mono hle).trans_lt (lt_top_iff_ne_top.2 hlin))⟩
  have hnorm : Summable fun y => ∫ p, ‖G y p‖ ∂P := by
    have e : ∀ y, ∫ p, ‖G y p‖ ∂P = (∫⁻ p, ‖G y p‖ₑ ∂P).toReal := fun y => by
      rw [integral_norm_eq_lintegral_enorm (hGm y).aestronglyMeasurable]
    simp only [e]
    exact ENNReal.summable_toReal hsum
  have hS := hasSum_integral_of_summable_integral_norm hGi hnorm
  have eT : (fun p => ∑' y, G y p) = fun p : N × H => Θ p.1 p.2 * F p.2 := funext fun p => (hsp p).tsum_eq
  rw [eT, hP, integral_prod _ (by rw [← hP]; exact hΘi)] at hS
  refine ⟨hΘi.integral_prod_left, ?_, ?_⟩
  · refine ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum fun y => ?_)
    rw [hP, lintegral_prod_symm _ (hGe y).aemeasurable]
    refine lintegral_mono fun h => ?_
    simp only [G, enorm_mul]
    rw [lintegral_mul_const _ ((hT y).of_uncurry_right.enorm)]
    exact mul_le_mul' (enorm_integral_le_lintegral_enorm _) le_rfl
  · have e : (fun y => ∫ h in 𝓕, (∫ n in 𝓝, T y n h ∂κ) * F h ∂ν) =
        fun y => ∫ p, G y p ∂(κ.restrict 𝓝).prod (ν.restrict 𝓕) := funext fun y => by
      rw [integral_prod_symm _ (by rw [← hP]; exact hGi y)]
      refine integral_congr_ae (.of_forall fun h => ?_)
      simp only [G]
      rw [integral_mul_const]
    rw [e]
    exact hS

end GlobalTheory.TowerCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadica
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FrameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

local infixl:70 " ⋆ₘ " => HMul.hMul

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem mt_mul (W : HSp D) (g h : GA D W) : Formalism.L2.Theta.mt W (g * h) = Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g⁻¹ * Formalism.L2.Theta.mt W g = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W g⁻¹ = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_frame (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (n : GA D W) (hn : n ∈ NI W L) :
    Formalism.L2.Theta.mt W n ⋆ₘ L.map (incA D) = L.map (incA D) := by
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    have h1 : (Formalism.L2.Theta.mt W g - 1) ⋆ₘ L.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one => simp [Formalism.L2.Theta.mt]
  | mul x y _ _ hx hy => rw [mt_mul, Matrix.mul_assoc, hy, hx]
  | inv x _ hx =>
    calc Formalism.L2.Theta.mt W x⁻¹ ⋆ₘ L.map (incA D)
        = Formalism.L2.Theta.mt W x⁻¹ ⋆ₘ (Formalism.L2.Theta.mt W x ⋆ₘ L.map (incA D)) := by rw [hx]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem mt_conj_sub_one (W : HSp D) (γ m : GA D W) : Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1 =
    Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W m - 1) * Formalism.L2.Theta.mt W γ⁻¹ := by
  rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]

theorem conj_sub_one_kills_frame_of_fixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (γ m : GA D W)
    (hΓiL : Formalism.L2.Theta.mt W γ⁻¹ ⋆ₘ L.map (incA D) = L.map (incA D))
    (h1 : (Formalism.L2.Theta.mt W m - 1) ⋆ₘ L.map (incA D) = 0) :
    (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) ⋆ₘ L.map (incA D) = 0 := by
  rw [mt_conj_sub_one, Matrix.mul_assoc, hΓiL, Matrix.mul_assoc, h1, Matrix.mul_zero]

theorem rowFrame_mul_conj_sub_one_eq_zero_of_fixed (W : HSp D) {s : ℕ} (P : Matrix (Fin s) (Fin W.rank) D.host.E) (γ m : GA D W)
    (hPΓ : P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ = P.map (incA D))
    (h2 : P.map (incA D) ⋆ₘ (Formalism.L2.Theta.mt W m - 1) = 0) :
    P.map (incA D) ⋆ₘ (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) = 0 := by
  rw [mt_conj_sub_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPΓ, h2, Matrix.zero_mul]

theorem conj_unipotentRadical_kernelCondition_of_rationalFixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (P : Matrix (Fin s) (Fin W.rank) D.host.E)
    (γ m : GA D W) (γ₀ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hγ₀ : Formalism.L2.Theta.mt W γ = γ₀.map (incA D)) (hγγi : γ₀ * γi = 1) (hPγi : P * γi = P)
    (hΓL : Formalism.L2.Theta.mt W γ ⋆ₘ L.map (incA D) = L.map (incA D))
    (h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a)
    (x : Fin W.rank → D.host.E) (hx : P *ᵥ x = 0) : ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
  have hy : P *ᵥ (γi *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, hPγi]; exact hx
  obtain ⟨a, ha⟩ := h3 _ hy
  refine ⟨a, ?_⟩
  have hyb : (fun i => incA D ((γi *ᵥ x) i)) = γi.map (incA D) *ᵥ (fun i => incA D (x i)) := by
    funext i; exact RingHom.map_mulVec (incA D) γi x i
  have hxb : Formalism.L2.Theta.mt W γ *ᵥ (fun i => incA D ((γi *ᵥ x) i)) = fun i => incA D (x i) := by
    rw [hyb, Matrix.mulVec_mulVec, hγ₀, ← Matrix.map_mul, hγγi, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hxi : Formalism.L2.Theta.mt W γ⁻¹ *ᵥ (fun i => incA D (x i)) = fun i => incA D ((γi *ᵥ x) i) := by
    rw [← hxb, Matrix.mulVec_mulVec, mt_inv_mul, Matrix.one_mulVec]
  rw [mt_conj_sub_one, ← Matrix.mulVec_mulVec, hxi, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hΓL]

theorem stab : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) →
      γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧
    (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) →
      n₀ * L = L) := by
  intro D W s L _
  refine ⟨?_, fun n hn n₀ hn₀ => ?_⟩
  swap
  · apply Matrix.map_injective (incA_injective D)
    show (n₀ * L).map (incA D) = L.map (incA D)
    rw [Matrix.map_mul, ← hn₀]
    exact mt_mul_frame W L n hn
  intro γ hγ γ₀ hγ₀ hL
  obtain ⟨g, hg, e⟩ := hγ
  have hg0 : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = γ₀ := by
    apply Matrix.map_injective (incA_injective D)
    show (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = γ₀.map (incA D)
    rw [← hγ₀]
    exact congrArg Units.val e

  obtain ⟨σ, hσ⟩ : ∃ σ : D.host.E →+* D.host.E, σ = (D.sp.cm.sig : D.host.E →+* D.host.E) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = W.gram := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin s) (Fin W.rank) D.host.E, P = Formalism.UG.cT σ L * G := ⟨_, rfl⟩
  obtain ⟨γi, hγi⟩ : ∃ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E, γi = (g⁻¹ : GL (Fin W.rank) D.host.E).1 :=
    ⟨_, rfl⟩
  have hγγi : γ₀ * γi = 1 := by rw [← hg0, hγi]; exact Units.mul_inv g
  have hU : Formalism.UG.cT σ γ₀ * G * γ₀ = G := by rw [← hg0, hσ, hG]; exact hg
  have hPγ : P * γ₀ = P := by
    calc P * γ₀ = Formalism.UG.cT σ (γ₀ * L) * G * γ₀ := by rw [hL, hP]
      _ = Formalism.UG.cT σ L * (Formalism.UG.cT σ γ₀ * G * γ₀) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hU, hP]
  have hPγi : P * γi = P := by
    calc P * γi = P * γ₀ * γi := by rw [hPγ]
      _ = P := by rw [Matrix.mul_assoc, hγγi, Matrix.mul_one]

  have hΓL : Formalism.L2.Theta.mt W γ ⋆ₘ L.map (incA D) = L.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hL]
  have hΓiL : Formalism.L2.Theta.mt W γ⁻¹ ⋆ₘ L.map (incA D) = L.map (incA D) := by
    calc Formalism.L2.Theta.mt W γ⁻¹ ⋆ₘ L.map (incA D)
        = Formalism.L2.Theta.mt W γ⁻¹ ⋆ₘ (Formalism.L2.Theta.mt W γ ⋆ₘ L.map (incA D)) := by rw [hΓL]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have hPΓ : P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ = P.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hPγ]
  have hPΓi : P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ⁻¹ = P.map (incA D) := by
    calc P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ⁻¹
        = P.map (incA D) ⋆ₘ Formalism.L2.Theta.mt W γ ⋆ₘ Formalism.L2.Theta.mt W γ⁻¹ := by rw [hPΓ]
      _ = P.map (incA D) := by rw [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

  have key : NI W L ≤ (NI W L).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun m hm => ?_
    have h1 : (Formalism.L2.Theta.mt W m - 1) ⋆ₘ L.map (incA D) = 0 := hm.1
    have h2 : P.map (incA D) ⋆ₘ (Formalism.L2.Theta.mt W m - 1) = 0 := by
      have := hm.2.1
      rw [hP, hσ, hG]; exact this
    have h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
      rw [hP, hσ, hG]; exact hm.2.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨conj_sub_one_kills_frame_of_fixed W L γ m hΓiL h1, ?_, ?_⟩
    · have := rowFrame_mul_conj_sub_one_eq_zero_of_fixed W P γ m hPΓ h2
      rw [hP, hσ, hG] at this; exact this
    · intro x hx
      rw [← hG, ← hσ, ← hP] at hx
      exact conj_unipotentRadical_kernelCondition_of_rationalFixed W L P γ m γ₀ γi hγ₀ hγγi hPγi hΓL h3 x hx
  intro n hn
  exact key hn

end GlobalTheory.FrameStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMatrixSandwichMemCompletedIdealLatticeHo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.TwistHatMx

theorem homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (h : Matrix (Fin m) (Fin n) D.host.E) (hh : h ∈ homLat Λ Λ') : q * h * j ∈ homLat M M' := by
  intro y hy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact hq _ (hh _ (hj _ hy))

theorem smul_homLat_conj {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Matrix (Fin m) (Fin n) D.host.E) (hx : x ∈ 𝔪 • homLat Λ Λ') : q * x * j ∈ 𝔪 • homLat M M' := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro c hc h hh
    rw [Matrix.mul_smul, Matrix.smul_mul]
    exact Submodule.smul_mem_smul hc (homLat_conj j q hj hq h hh)
  · intro a b ha hb
    rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _ ha hb

theorem gen_conj {D : D7} {m n m' n' : ℕ} (a : AF D.host.F) (x : Matrix (Fin m) (Fin n) D.host.E) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) :
    rat q * (Matrix.of fun i k => a ⊗ₜ[D.host.F] x i k) * rat j = Matrix.of fun i k => a ⊗ₜ[D.host.F] (q * x * j) i k := by
  have e : ∀ {r s : ℕ} (y : Matrix (Fin r) (Fin s) D.host.E), (Matrix.of fun i k => a ⊗ₜ[D.host.F] y i k) = (a ⊗ₜ[D.host.F] (1 : D.host.E)) • rat y := by
    intro r s y
    ext i k
    simp [rat, inclR, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, e, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [rat, Matrix.map_mul]

theorem rat_conj_mem_hatMx {D : D7} {m n m' n' : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {M : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {M' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)} (𝔪 : Ideal (𝓞 D.host.E)) (j : Matrix (Fin n) (Fin n') D.host.E) (q : Matrix (Fin m') (Fin m) D.host.E) (hj : ∀ y ∈ M, j *ᵥ y ∈ Λ) (hq : ∀ t ∈ Λ', q *ᵥ t ∈ M') (x : Mx D m n) (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : rat q * x * rat j ∈ hatMx (𝔪 • homLat M M') := by
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, y, hy, rfl⟩ := hw
    rw [gen_conj]
    exact AddSubgroup.subset_closure ⟨α, hα, q * y * j, smul_homLat_conj 𝔪 j q hj hq y hy, rfl⟩
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Matrix.mul_add, Matrix.add_mul]
    exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha =>
    rw [Matrix.mul_neg, Matrix.neg_mul]
    exact AddSubgroup.neg_mem _ ha

end GlobalTheory.TwistHatMx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeVacuumAndLiftVector
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.ReVec

theorem L_lat : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (LT : Set (Fin T.rank → D.host.E)) (u : WO (reS S b) T), u ∈ latO (reS S b) T (L0c D (reS S b)) LT (fun _ => True) ↔ reW S T b u ∈ latO S T (L0c D S) LT (fun _ => True) := GlobalTheory.T.mem_completedLattice_reframeHomMatrix_iff

theorem L_sympl : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x y : WO (reS S b) T), symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y) := GlobalTheory.T.symplecticFormOnHoms_reframeHomMatrix

theorem L_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := GlobalTheory.T.isSmoothThetaFunction_reframeFunctionOnHoms

theorem L_fock : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ → (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := GlobalTheory.T.isFockVacuumAt_reframeFunctionOnHoms

theorem L_norm : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ), AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := GlobalTheory.T.reF_norm_one_of_norm_one_covolOne

theorem L_thetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → (∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) e Λ' c (reF S T b f₀) (fun x => Φ (reW S T b x)) (reF S T b f) := GlobalTheory.T.isThetaAtSplitPlace_reframe

theorem L_frMap : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (x : WO (reS S b) T), frMapAdj (reS S b) T (frPinvGL S b * βS) βT x = frMapAdj S T βS βT (reW S T b x) := GlobalTheory.T.frameAdjointMap_reframedHermitianSpace

theorem L_frame : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := GlobalTheory.T.isFrame_frameChangeInverseGL_mul

theorem pi_eq_stdL' (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) = stdL E n := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx a trivial)
    have : (Pi.single a (x a) : Fin n → E) = b • (Pi.single a 1 : Fin n → E) := by
      rw [← Pi.single_smul, ← hb, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩ j -
    by_cases h : j = a
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · simp [h]

theorem L_std : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), StdFrame.OrthFrame (reS S b) → L0c D (reS S b) = (stdL D.host.E (reS S b).rank : Set (Fin (reS S b).rank → D.host.E)) := by
  intro D S b hO
  ext x
  rw [SetLike.mem_coe, ← pi_eq_stdL', Submodule.mem_pi]
  exact (hO.mem_iff x).trans ⟨fun k a _ => k a, fun k a => k a trivial⟩

theorem reframe_thPVecOf : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), StdFrame.OrthFrame (reS S b) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Lt D.host.E S.rank) (ΛT : Set (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (f₀ f : WO S T → ℂ), (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → IsThPVecOf ψ θ S T (fun _ => 1) sT (ΛS : Set (Fin S.rank → D.host.E)) ΛT βS βT Pg Q ξ f₀ f → ∃ βS' : GL (Fin (reS S b).rank) (Lev.EAf D), Formalism.L2.DIV.IsFrame βS' (stdL D.host.E (reS S b).rank) ∧ IsThPVecOf ψ θ (reS S b) T (fun _ => 1) sT (stdL D.host.E (reS S b).rank : Set (Fin (reS S b).rank → D.host.E)) ΛT βS' βT Pg Q ξ (reF S T b f₀) (reF S T b f) := by
  intro D S T b hO ψ θ sT ΛS ΛT βS βT Pg Q ξ f₀ f hΛ hfr hv
  have hL := L_std D S b hO
  refine ⟨frPinvGL S b * βS, L_frame D S b βS ΛS hO hΛ hfr, ?_⟩
  rw [← hL]
  rw [hΛ] at hv
  obtain ⟨⟨hstd, hvac⟩, e, he, hth⟩ := hv
  have hs := L_sympl D S T b
  have hlat := L_lat D S T b ΛT
  refine ⟨⟨hstd, ?_⟩, e, he, ?_⟩
  · exact
      { inf := hvac.inf
        theta := L_theta D ψ S T b hs f₀ hvac.theta
        lat := ⟨fun u hu => by
            rw [heisO_reF S T b ψ hs, reW_nsmul, hvac.lat.1 _ ((hlat u).1 hu)],
          fun e' he' u hu hh => by
            rw [heisO_reF S T b ψ hs, hvac.lat.2 e' he' _ ((hlat u).1 hu) ((isHalf_reW_iff S T b e' u).2 hh)]⟩
        fock := fun τ => L_fock D ψ θ S T b hvac.inf hs τ (sT τ) f₀ (hvac.fock τ)
        norm := L_norm D S T b f₀ hvac.norm }
  · refine (congrArg (fun Φ => IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) (cA D e)
      (latO (reS S b) T (L0c D (reS S b)) ΛT fun _ => True) 1 (reF S T b f₀) Φ (reF S T b f)) ?_).mpr
      (L_thetaAt D ψ S T b (cA D e) _ _ 1 f₀ _ f hs hlat hth)
    funext x
    simp only [L_frMap D S T b βS βT x]
    rw [isHalf_reW_iff S T b (cA D e) x]
    exact if_congr Iff.rfl rfl rfl

end GlobalTheory.AdSpan.ReVec

end
end

