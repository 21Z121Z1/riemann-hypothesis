import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0806
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0789
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0591
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0683
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0676
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0808
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0809
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0048
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLatticeOfIsUnf
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open Limits

namespace GlobalTheory.ShFam.Hor.LogCh

theorem kernel_lattice_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (g : ℕ) (x : GlobalTheory.CxPts (genStr Z) σ) (ex : (Fin g → ℂ) → (Over.mk (x.1 ≫ genι Z) ⟶ Z.t.G)), Inner x → IsExpAt Z.t (x.1 ≫ genι Z) ex → IsHolTo Set.univ (fun w => (ex w).left) → Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) = g ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ Submodule.span ℝ {w | ex w = 1} = ⊤ ∧ (∀ v w, ex v = 1 → ex w = 1 → ∃ m : ℤ, (hermForm Hm v w).im = m) ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm v w).im : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ U _hσ hU g x ex hx hex hhol
  obtain ⟨y, hy⟩ := hx.exists_lift
  obtain ⟨W₀⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ _ U hU
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]
    exact x.2
  obtain ⟨i, P, hP, hu⟩ := W₀.F.onto (y ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, OpenReg.spMap_comp])
  obtain ⟨e', he', hhol', hker, hweil⟩ := exists_pushed_exp E H Dw l Xo c O β Z _ _ _ W₀.F y i P (x.1 ≫ genι Z) hP hu
    (by rw [← hy, Category.assoc])
  obtain ⟨L, hL⟩ := exp_eq_comp_linearEquiv E H Z.X Z.t (x.1 ≫ genι Z) g _ ex e' hex hhol he' hhol'
  have hg : W₀.g = g := by
    have := L.finrank_eq
    simpa using this
  obtain ⟨Hm₀, hH₀, hpos₀, hEF⟩ := hP.2.2.2.2
  obtain ⟨Hm, hH, hpos, hform⟩ := exists_hermForm_transport _ _ L Hm₀ hH₀ hpos₀
  have hkerex : ∀ w, ex w = 1 ↔ ∃ a, w = L (P a) := by
    intro w
    constructor
    · intro h
      have h' : e' (L.symm w) = 1 := by rw [hL, L.apply_symm_apply, h]
      obtain ⟨a, ha⟩ := (hker _).1 h'
      exact ⟨a, by rw [ha, L.apply_symm_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [← hL]
      exact (hker _).2 ⟨a, rfl⟩
  refine ⟨?_, Hm, hH, hpos, ?_, ?_, ?_⟩
  · rw [← hg, ← Fintype.card_congr W₀.e, Fintype.card_fin]
  · have hset : {w | ex w = 1} = (L.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      ext w
      simp only [Set.mem_setOf_eq, hkerex, Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨P a, ⟨a, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    rw [hset, Submodule.span_image, hP.2.2.2.1, Submodule.map_top, LinearMap.range_eq_top]
    exact L.surjective
  · intro v w hv hw
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    exact ⟨(W₀.F.Di i).EF a b, by rw [hform, hEF]⟩
  · intro k v w ζ hk hv hw hζ
    obtain ⟨a, rfl⟩ := (hkerex v).1 hv
    obtain ⟨b, rfl⟩ := (hkerex w).1 hw
    rw [← L.map_smul, ← L.map_smul, ← hL, ← hL]
    refine hweil k a b ζ hk ?_
    rw [hζ, hform, hEF, Complex.ofReal_intCast]

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormCoordinateLtOneInPrimitiveCell
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem orbMark_coord_lt_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  intro E _ _ _ H φ hφ X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvsum X _ _ _ m δ h hli hprim
    β _ _ hβ1 c hc hβsum j
  obtain ⟨p, -, hpos, hcells⟩ :=
    GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv (fun i => (ht i).1) hvsum β hβ1
  rcases (hc j).lt_or_eq with hcj | hcj
  · obtain ⟨i, hti, d, hd, hpd, hcd⟩ := (hcells m δ h hli c hc hβsum).2 j hcj
    have hpi := (hpos i hti).2.2.1
    have hδj := GlobalTheory.T.isPrimitiveBalancedForm_primitive_among_intForms H.bar (δ j) (h.mem j) (hprim j)
    have hd1 := (GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray (p i) (δ j) d hd hpi hδj hpd).2
    rw [hcd, hd1, mul_one]
    exact (ht i).2
  · rw [← hcj]; exact zero_lt_one

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPeriodMatrixIntVecContinuousBoundary
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PeriodFrame

theorem combMat_mulVec_eq_sum {g r : ℕ} (l : Fin r → Fin g → ℂ) (φ : Matrix (Fin g) (Fin r) ℚ) (v : Fin g → ℂ) :
    combMat l φ *ᵥ v = ∑ m, (∑ i, (φ i m : ℂ) * v i) • l m := by
  ext k
  simp only [combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem exists_nat_mul_int {r : ℕ} (u : Fin r → ℚ) : ∃ N : ℕ, 0 < N ∧ ∀ m, ∃ k : ℤ, (N : ℚ) * u m = k := by
  refine ⟨∏ m, (u m).den, Finset.prod_pos fun m _ => (u m).den_pos, fun m => ?_⟩
  refine ⟨(∏ j ∈ Finset.univ.erase m, (u j).den : ℕ) * (u m).num, ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ m)]
  push_cast
  rw [_root_.mul_assoc, _root_.mul_comm ((u m).den : ℚ), Rat.mul_den_eq_num]

end GlobalTheory.PeriodFrame

theorem GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous : ∀ (n a g r₀ r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (rk D : ℕ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → Mᵀ = -M → φ * M.map (Int.cast : ℤ → ℚ) * (α * c.map (Int.cast : ℤ → ℚ))ᵀ = 1 → (∀ i : Fin g, i.val < rk → ∀ m, ((α * c.map (Int.cast : ℤ → ℚ)) * M.map (Int.cast : ℤ → ℚ) * (c.map (Int.cast : ℤ → ℚ))ᵀ) i m = 0) → 0 < D → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → ∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 1) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).mulVec (fun j => (v j : ℂ)) = F (logExp a s) := by
  intro n a g r₀ r K ζ lam M c α φ rk D hK hζa hζK hζ0 hlam hζc hM hφ hrk hD hdet v hv hsupp F hF heq
  set u : Fin r → ℚ := fun m => ∑ i, φ i m * (v i : ℚ) with hu
  obtain ⟨N, hN0, hNint⟩ := GlobalTheory.PeriodFrame.exists_nat_mul_int u
  choose kk hkk using hNint
  set W : (Fin n → ℂ) → Fin g → ℂ := fun z => ((N : ℂ) / D) • (GlobalTheory.PeriodFrame.combMat (ζ z) α *ᵥ F z) with hW
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hζc0 : ContinuousAt ζ 0 := (hζa 0 h0).continuousAt
  have hFc0 : ContinuousAt F 0 := hF.continuousAt (Metric.isOpen_ball.mem_nhds h0)
  have hWc : ContinuousAt W 0 := by
    have h1 : ∀ m k, ContinuousAt (fun z => ζ z m k) 0 := fun m k =>
      (continuous_apply k).continuousAt.comp ((continuous_apply m).continuousAt.comp hζc0)
    have h2 : ∀ i, ContinuousAt (fun z => F z i) 0 := fun i => (continuous_apply i).continuousAt.comp hFc0
    refine continuousAt_pi.2 fun k => ?_
    simp only [hW, GlobalTheory.PeriodFrame.combMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hlK : ∀ᶠ b in 𝓝 (0 : Fin n → ℂ), ∀ j, ζ b j ∈ K b := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with b hb using hζK b hb
  have hev := IsLatFam.eventually_intComb hK h0 hζc0 hlK hζ0 (W 0)
  have ht : Filter.Tendsto (fun z => (z, W z)) (𝓝 (0 : Fin n → ℂ)) (𝓝 ((0 : Fin n → ℂ), W 0)) :=
    (continuousAt_id.prodMk hWc).tendsto
  have hev2 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧
      (W z ∈ K z → ∃ m : Fin r₀ → ℤ, W z = ∑ j, m j • ζ z j) :=
    Filter.Eventually.and (Metric.isOpen_ball.mem_nhds h0 : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), z ∈ Metric.ball (0 : Fin n → ℂ) 1)
      (ht.eventually hev)
  set s : ℝ → Fin n → ℂ := fun R k => if (k : ℕ) < a then -(R : ℂ) else 0 with hs
  have hsdom : ∀ R : ℝ, 0 < R → s R ∈ logDom n a := by
    intro R hR k
    by_cases hk : (k : ℕ) < a
    · simp [hs, hk, hR]
    · simp [hs, hk]
  have hslim : Filter.Tendsto (fun R => logExp a (s R)) Filter.atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun k => ?_
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hs, hk, if_true, Pi.zero_apply]
      have h3 : Filter.Tendsto (fun R : ℝ => ((Real.exp (-R) : ℝ) : ℂ)) Filter.atTop (𝓝 ((0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      simpa [Complex.ofReal_exp] using h3
    · simp [logExp, hs, hk]
  obtain ⟨R, ⟨hzb, hzK⟩, hR0⟩ := ((hslim.eventually hev2).and (Filter.eventually_gt_atTop 0)).exists
  have hs0 := hsdom R hR0
  have he := heq (s R) hs0 hzb
  have hWz : W (logExp a (s R)) = ∑ m, ((kk m : ℤ) : ℂ) • lam (s R) m := by
    have hP := hdet (s R) hs0
    have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have hsm : ∀ (c : ℂ) (A : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ), (c • A) *ᵥ x = c • (A *ᵥ x) := by
      intro c A x; ext p; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, _root_.mul_assoc]
    simp only [hW]
    rw [← he, GlobalTheory.PeriodFrame.perTau, Matrix.mulVec_mulVec, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hP, Matrix.one_mul, hsm, smul_smul,
      GlobalTheory.PeriodFrame.combMat_mulVec_eq_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
    congr 1
    have h4 := congrArg (Rat.cast : ℚ → ℂ) (hkk m)
    push_cast [hu] at h4
    rw [← h4]
    field_simp

  have hWK : W (logExp a (s R)) ∈ K (logExp a (s R)) :=
    ((hlam (s R) hs0).2 _).2 ⟨kk, by rw [hWz]; exact Finset.sum_congr rfl fun m _ => Int.cast_smul_eq_zsmul ℂ _ _⟩
  obtain ⟨mm, hmm⟩ := hzK hWK
  have hcomb : ∑ j, kk j • lam (s R) j = ∑ j, (∑ i, mm i * c i j) • lam (s R) j := by
    have e1 : ∑ j, kk j • lam (s R) j = W (logExp a (s R)) := by
      rw [hWz]; exact Finset.sum_congr rfl fun m _ => (Int.cast_smul_eq_zsmul ℂ _ _).symm
    rw [e1, hmm]
    simp only [hζc (s R) hs0, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
  have hkc : ∀ j, kk j = ∑ i, mm i * c i j := by
    have hli := (hlam (s R) hs0).1
    have h5 := Fintype.linearIndependent_iff.1 hli (fun j => ((kk j - ∑ i, mm i * c i j : ℤ) : ℝ)) (by
      simp only [Int.cast_smul_eq_zsmul, sub_smul, Finset.sum_sub_distrib, hcomb, sub_self])
    intro j
    have h6 := h5 j
    have h7 : kk j - ∑ i, mm i * c i j = 0 := by exact_mod_cast h6
    exact sub_eq_zero.1 h7
  set cq := c.map (Int.cast : ℤ → ℚ) with hcq
  set Mq := M.map (Int.cast : ℤ → ℚ) with hMq
  set vq : Fin g → ℚ := fun i => (v i : ℚ) with hvq
  set mq : Fin r₀ → ℚ := fun i => (mm i : ℚ) with hmq
  have hvec : Matrix.vecMul ((N : ℚ) • vq) φ = Matrix.vecMul mq cq := by
    ext j
    have h6 := hkk j
    rw [hkc j] at h6
    push_cast at h6
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, hcq, hvq, hmq, Matrix.map_apply]
    rw [← h6, hu, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hskew : cq * (Mq * (α * cq)ᵀ) = -((α * cq) * Mq * cqᵀ)ᵀ := by
    have hMt : Mqᵀ = -Mq := by
      ext i j
      have h := congrFun (congrFun hM i) j
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
      simp [hMq, Matrix.transpose_apply, h]
    rw [Matrix.transpose_mul (α * cq * Mq), Matrix.transpose_transpose, Matrix.transpose_mul (α * cq) Mq, hMt]
    simp [Matrix.neg_mul, Matrix.mul_neg]
  have hfin := congrArg (fun x => Matrix.vecMul x (Mq * (α * cq)ᵀ)) hvec
  simp only [Matrix.vecMul_vecMul] at hfin
  rw [show φ * (Mq * (α * cq)ᵀ) = 1 by rw [← Matrix.mul_assoc, hφ], Matrix.vecMul_one, hskew] at hfin
  apply hv
  funext i
  by_cases hi : i.val < rk
  · have h7 := congrFun hfin i
    have h8 : Matrix.vecMul mq (-((α * cq) * Mq * cqᵀ)ᵀ) i = 0 := by
      simp only [Matrix.vecMul, dotProduct, Matrix.neg_apply, Matrix.transpose_apply, hrk i hi, neg_zero, mul_zero,
        Finset.sum_const_zero]
    rw [h8] at h7
    simp only [Pi.smul_apply, smul_eq_mul, hvq] at h7
    have hN : (N : ℚ) ≠ 0 := by exact_mod_cast hN0.ne'
    have h9 := (mul_eq_zero.1 h7).resolve_left hN
    simpa using h9
  · exact hsupp i (not_lt.1 hi)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrthonormalFramesSameComponentNearChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalFrames_same_component_near_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ (n : ℕ) (ch : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr Z) σ) (Fin n → ℂ)), IsHolTo ch.target (fun z => (ch.symm z).1) → ∀ (k₀ : U.Comp) (x₀ : (U.X k₀).dom), cxPt Z (U.un k₀ x₀) ∈ ch.source → ∃ B : Set (Fin n → ℂ), IsOpen B ∧ ch (cxPt Z (U.un k₀ x₀)) ∈ B ∧ ∀ z ∈ B, ∀ (k : U.Comp) (x : (U.X k).dom), cxPt Z (U.un k x) = ch.symm z → k = k₀ := by
  first | exact @GlobalTheory.HodgeSmooth.chart_comp_locconst | exact GlobalTheory.HodgeSmooth.chart_comp_locconst | (intros; apply GlobalTheory.HodgeSmooth.chart_comp_locconst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodChartRescaleBallToUnitPolydisc
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.HodgeChart

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram in

theorem periodChart_rescale_ball : ∀ (n a g rk : ℕ) (ha : a ≤ n) (ρ : ℝ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ → ρ ≤ 1 → rk ≤ g → (∀ j k, DifferentiableOn ℂ (fun z => τ₀ z j k) (Metric.ball 0 ρ)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (τ₀ z).IsSymm) → (∀ i, ((B i).map (Int.cast : ℤ → ℝ)).PosSemidef) → (∀ i (j k : Fin g), (rk ≤ j.val ∨ rk ≤ k.val) → B i j k = 0) → (((∑ i, B i).map (Int.cast : ℤ → ℝ)).submatrix (Subtype.val : {j : Fin g // j.val < rk} → Fin g) Subtype.val).PosDef → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (((τ₀ z).map Complex.im).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) Subtype.val).PosDef) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B ∧ ∀ z : Fin n → ℂ, (∀ i : Fin a, z (Fin.castLE ha i) ≠ 0) → GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha (fun u => τ₀ (ρ • u) + ∑ i, (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) • (B i).map (Int.cast : ℤ → ℂ)) B (ρ⁻¹ • z) = GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z := by
  intro n a g rk ha ρ τ₀ B hr hr1 hrk hholo hsymm hpsd hsupp htoric habel
  set cst : ℂ := (((Real.log ρ : ℝ) : ℂ) / (2 * Real.pi * Complex.I)) with hcst
  have him : cst.im = -Real.log ρ / (2 * Real.pi) := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have e : cst = ((-Real.log ρ / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hcst]; push_cast; field_simp; rw [Complex.I_sq]; ring
    rw [e, Complex.im_ofReal_mul, Complex.I_im, _root_.mul_one]
  have hBs : ∀ i (j k : Fin g), B i k j = B i j k := fun i j k => by
    have := (hpsd i).isHermitian.apply j k
    simp at this
    exact_mod_cast this
  have hmaps : ∀ z ∈ polydisc n 1, ρ • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
    intro u hu
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    have : ‖u‖ < 1 := (pi_norm_lt_iff one_pos).2 hu
    calc ρ * ‖u‖ < ρ * 1 := by gcongr
      _ = ρ := _root_.mul_one ρ
  have hdiff : DifferentiableOn ℂ (fun z : Fin n → ℂ => ρ • z) (polydisc n 1) :=
    ((differentiable_id.const_smul (ρ : ℂ)).differentiableOn).congr fun u _ => by
      funext k; simp [Complex.real_smul]
  refine ⟨⟨hrk, fun j k => ?_, fun z hz => ?_, hpsd, hsupp, htoric, fun z hz => ?_⟩, fun u hu => ?_⟩
  · have h1 := (hholo j k).comp hdiff hmaps
    refine (h1.add (differentiableOn_const (∑ i, cst * (B i j k : ℂ)))).congr fun z _ => ?_
    simp [Matrix.add_apply, Matrix.sum_apply, Function.comp]
  · refine Matrix.IsSymm.ext fun j k => ?_
    have := (hsymm _ (hmaps z hz)).apply j k
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, hBs, this]
  · have h1 := habel _ (hmaps z hz)
    convert h1 using 1
    ext ⟨j, hj⟩ ⟨k, hk⟩
    simp [Matrix.sum_apply, hsupp _ j k (Or.inl hj)]
  · have hρu : ρ • (ρ⁻¹ • u) = u := smul_inv_smul₀ hr.ne' u
    ext j k
    have hu' : ∀ i : Fin a, tlog ((ρ⁻¹ • u) (Fin.castLE ha i)) = Real.log ρ / (2 * Real.pi) + tlog (u (Fin.castLE ha i)) := by
      intro i
      rw [Pi.smul_apply, tlog, tlog, norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le,
        Real.log_mul (inv_pos.2 hr).ne' (norm_ne_zero_iff.2 (hu i)), Real.log_inv]
      ring
    simp only [hodgeGram, imPeriod, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply,
      hu', hρu, Complex.add_im, Complex.im_sum, smul_eq_mul]
    push_cast
    simp only [Complex.smul_im, Complex.intCast_im, Complex.intCast_re, smul_eq_mul, him, add_mul, Finset.sum_add_distrib]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, mul_zero, add_zero, him]
    push_cast
    simp only [zero_add]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring

end GlobalTheory.LieBase.HodgeChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscCoverLatticeBasisRealHolomorphic
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShFam.Hor.LogCh

theorem latBasis_logCover_real_holo : ∀ (n a g r : ℕ) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ), IsLatFam (Metric.ball 0 1) K → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → r = 2 * g ∧ (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s)) ∧ ∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a) := by
  intro n a g r K lam hK hlam hB

  have hne : (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0) ∈ logDom n a := by
    intro k
    by_cases h : (k : ℕ) < a <;> simp [h]
  obtain ⟨hOpen, -, hAn, hMaps⟩ := GlobalTheory.logDom_chart_props n a

  have hmem : ∀ s ∈ logDom n a, ∀ j, lam s j ∈ K (logExp a s) := by
    intro s hs j
    refine ((hB s hs).2.2 _).2 ⟨Pi.single j 1, ?_⟩
    simp [Pi.single_apply]
  have hreal : ∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) := by
    intro s hs
    obtain ⟨hli, hsp, hK'⟩ := hB s hs
    have hspanK : Submodule.span ℝ (K (logExp a s)) = ⊤ := by
      rw [eq_top_iff, ← hsp]
      exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hmem s hs j)
    exact (GlobalTheory.LatReal.isRealBasis_of_isLatFam n g r (Metric.ball 0 1) K (logExp a s) (lam s) hK
      (hMaps hs) hspanK hli hK').1
  refine ⟨?_, hreal, ?_⟩
  · set s₀ := (fun k : Fin n => if (k : ℕ) < a then (-1 : ℂ) else 0)
    have hli := hreal s₀ hne
    have hsp := (hB s₀ hne).2.1
    have h1 := linearIndependent_iff_card_eq_finrank_span.1 hli
    rw [Set.finrank, hsp, finrank_top, Fintype.card_fin] at h1
    rw [h1, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  · intro j k
    have hF := IsLatFam.pullback_analytic n n g (Metric.ball 0 1) (logDom n a) K (logExp a) hK hOpen
      (fun s _ => hAn s) hMaps
    intro s₀ hs₀
    have hnhds : logDom n a ∈ 𝓝 s₀ := hOpen.mem_nhds hs₀
    obtain ⟨ζ, hζ0, hζa, hev⟩ := hF.2.2.2 s₀ hs₀ (lam s₀ j) (hmem s₀ hs₀ j)
    have hc : ContinuousAt (fun s => (s, lam s j)) s₀ :=
      continuousAt_id.prodMk ((continuous_apply j).continuousAt.comp (hlam.continuousAt hnhds))
    have hev' : ∀ᶠ s in 𝓝 s₀, (lam s j ∈ K (logExp a s) ↔ lam s j = ζ s) := by
      have := hc.tendsto.eventually hev
      simpa [hζ0] using this
    have heq : (fun s => lam s j) =ᶠ[𝓝 s₀] ζ := by
      filter_upwards [hev', hnhds] with s h1 h2
      exact h1.1 (hmem s h2 j)
    have hd : DifferentiableAt ℂ (fun s => lam s j) s₀ :=
      hζa.differentiableAt.congr_of_eventuallyEq heq
    exact (differentiableAt_pi.1 hd k).differentiableWithinAt

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalFormsLinkedConstructionStatesIdentifiedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalForms_linkedConstructionStates_identified : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) → (∀ u, HEq (γ u) u) → FormsCl (sideAt x g hg a) (sideAt x' g' hg' a') ι eK γ := by
  first | exact @GlobalTheory.HeightCounting.SerMove.FormsMove.formsCl_of_link | exact GlobalTheory.HeightCounting.SerMove.FormsMove.formsCl_of_link | (intros; apply GlobalTheory.HeightCounting.SerMove.FormsMove.formsCl_of_link <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionToLocalLanglandsAStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_to_local_langlands_A : PrN → PhtCmp → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SA hL := by
  first | exact @GlobalTheory.HeightCounting.Up.sa_of_prN | exact GlobalTheory.HeightCounting.Up.sa_of_prN | (intros; apply GlobalTheory.HeightCounting.Up.sa_of_prN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeAmpleCanonicalTrivialLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_ample_canonical_trivial_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [CharZero O], IsIntegrallyClosed O → ∀ (t : SAB H (Sp O)), IsProper t.G.hom → GlobalTheory.LN.PolAt t (Out.jK O) → Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic | exact GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic | (intros; apply GlobalTheory.PolLocal.relAmple_kTriv_of_polAt_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesisStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_local_of_hypothesis : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalTheory.TypeLeaf.SerLoc D' := by
  first | exact @GlobalTheory.SerThird.main | exact GlobalTheory.SerThird.main | (intros; apply GlobalTheory.SerThird.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideReadHeckeOfAdmissibleTwistStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_read_hecke_of_admissible_twist : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ParaShape (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) := by
  first | exact @GlobalTheory.XPara.paraShape_export | exact GlobalTheory.XPara.paraShape_export | (intros; apply GlobalTheory.XPara.paraShape_export <;> assumption)
end

