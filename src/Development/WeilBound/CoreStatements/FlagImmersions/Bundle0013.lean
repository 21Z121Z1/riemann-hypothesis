import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.CoordsOrbit
section
noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

namespace Pot

theorem log_norm_an {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀)
    (h0 : F t₀ ≠ 0) : ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, Real.log ‖F t‖ = (G t).re := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have e1 : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
  refine ⟨fun t => Complex.log (F t / F t₀) + (Real.log ‖F t₀‖ : ℂ), (hH.clog e1).add analyticAt_const, ?_⟩
  filter_upwards [hF.continuousAt.eventually_ne h0] with t ht
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 ht) (norm_ne_zero_iff.2 h0)]
  ring

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem val_an {n : ℕ} {B : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo B z)
    (hall : ∀ q : X, genPt ξ ⤳ q) {t₀ : Fin n → ℂ} (ht : t₀ ∈ B) {a : Ω} {r : ℂ} (h : ValAt ξ (z t₀) a r) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u t₀ ∧ ∀ᶠ t in 𝓝 t₀, ValAt ξ (z t) a (u t) := by
  obtain ⟨h0, s, rfl, -⟩ := h
  obtain ⟨U, hU, f, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg : centre ξ ∈ U := h0.mem_open U.isOpen hU
  have hn : {b ∈ B | ⊤ ≤ z b ⁻¹ᵁ U} ∈ 𝓝 t₀ := (hz U f).1.mem_nhds ⟨ht, (SheetDecomposition.CovSch.top_le_iff _ _).2 hU⟩
  refine ⟨fun b => valAt' (z b) U f, GlobalTheory.SCV.analyticAt_of_differentiableOn (hz U f).2 hn, ?_⟩
  filter_upwards [hn] with t h1
  have h2 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h1.2
  rw [SheetDecomposition.CovSch.valAt'_eq _ _ h2, SheetDecomposition.CovSch.genMap_germ' ⟨centre (z t₀), h0⟩ U hU hg f]
  exact SheetDecomposition.CovSch.valAt_sec (hall _) U h2 hg f

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem coords_orbit {z : Sp ℂ ⟶ X} {w w' : (Σ k, J k) → ℂ} (h : CoordsAt ξ y z w') (hs : SameOrbit w w') :
    CoordsAt ξ y z w := by
  obtain ⟨a, ha, rfl⟩ := hs
  refine ⟨fun k => (h.1 k).imp fun i hi => (IsUnit.mk0 _ (ha k)).mul hi, fun k i hi => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 k i (isUnit_of_mul_isUnit_right hi)
  refine ⟨h1, fun j => (h2 j).imp fun r hr => ⟨hr.1, ?_⟩⟩
  show a k * w' ⟨k, j⟩ = r * (a k * w' ⟨k, i⟩)
  rw [hr.2]
  ring

theorem log_h_smul (A : HermLine J) (a : K → ℂ) (ha : ∀ k, a k ≠ 0) {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => a p.1 * w p) = ∑ k, (A.a k : ℝ) * Real.log ‖a k‖ + Real.log (A.h w) := by
  have h1 : ∀ k, ‖a k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (ha k))
  rw [A.smul a w ha, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => h1 k) (A.pos w hw).ne',
    Real.log_prod fun k _ => h1 k]
  simp only [Real.log_zpow]

theorem log_orbit {I : Type} (s : Finset I) (A : HermLine J) (B : I → HermLine J) (hd : A.a = -∑ i ∈ s, (B i).a)
    {w w' : (Σ k, J k) → ℂ} (hs : SameOrbit w w') (hw : ∀ k, ∃ i, w' ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ i ∈ s, Real.log ((B i).h w) = Real.log (A.h w') + ∑ i ∈ s, Real.log ((B i).h w') := by
  obtain ⟨a, ha, rfl⟩ := hs
  simp only [log_h_smul _ a ha hw, hd, Finset.sum_add_distrib, Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem log_h_an {n : ℕ} {B : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo B z)
    (hall : ∀ q : X, genPt ξ ⤳ q) {t₀ : Fin n → ℂ} (ht : t₀ ∈ B) (A : HermLine J) (e₀ T : Ω)
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hγ : ∀ p, AnalyticAt ℂ (fun t => γ t p) t₀) {ν : (Fin n → ℂ) → ℝ}
    (hν : ∀ᶠ t in 𝓝 t₀, 0 < ν t ∧ SecNorm ξ y A e₀ (z t) (γ t) T (ν t)) :
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, -Real.log (A.h (γ t)) = Real.log (ν t) + (G t).re := by
  obtain ⟨p0, h0⟩ := hν.self_of_nhds
  obtain ⟨c, hc⟩ := h0.exists_chart
  obtain ⟨u₀, hu₀, e0⟩ := h0.2.2 c hc
  obtain ⟨u, hu, hue⟩ := val_an hz hall ht hu₀
  let F : (Fin n → ℂ) → ℂ := fun t => u t * ∏ k, γ t ⟨k, c k⟩ ^ A.a k
  have hF : AnalyticAt ℂ F t₀ := hu.mul (Finset.analyticAt_fun_prod _ fun k _ => (hγ _).zpow (hc k))
  have hcn : ∀ᶠ t in 𝓝 t₀, ∀ k, γ t ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hγ _).continuousAt.eventually_ne (hc k)
  have hev : ∀ᶠ t in 𝓝 t₀, ν t * A.h (γ t) = ‖F t‖ := by
    filter_upwards [hν, hue, hcn] with t h1 h2 h3
    obtain ⟨u', hu', e⟩ := h1.2.2.2 c h3
    rw [e, CxVal.unique hu' h2]
    simp only [F, norm_mul, norm_prod, norm_zpow]
  have hF0 : F t₀ ≠ 0 := by
    rw [← norm_ne_zero_iff, ← hev.self_of_nhds]
    exact (mul_pos p0 (A.pos _ fun k => ⟨c k, hc k⟩)).ne'
  obtain ⟨G, hG, hGe⟩ := log_norm_an hF hF0
  refine ⟨fun t => -G t, hG.neg, ?_⟩
  filter_upwards [hν, hev, hcn, hGe] with t h1 h2 h3 h4
  rw [Complex.neg_re, ← h4, ← h2, Real.log_mul h1.1.ne' (A.pos _ fun k => ⟨c k, h3 k⟩).ne']
  ring

theorem holo_comp {e e' : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {A : FinHolAtlas e M}
    {B : FinHolAtlas e' N} {ψ : M → N} (hψ : HoloMap A B ψ) (k : Fin A.n) {t : Fin e → ℂ} (ht : t ∈ (A.chart k).target)
    {W : Set N} {f : N → ℂ} (hf : B.HoloOn W f) (hW : ψ ((A.chart k).symm t) ∈ W) :
    AnalyticAt ℂ (fun t' => f (ψ ((A.chart k).symm t'))) t := by
  obtain ⟨j, hj⟩ := B.cover (ψ ((A.chart k).symm t))
  have h1 := hψ.2 k j t ⟨ht, hj⟩
  have h2 := hf j (B.chart j (ψ ((A.chart k).symm t))) ⟨(B.chart j).map_source hj, by
    show (B.chart j).symm _ ∈ W
    rwa [(B.chart j).left_inv hj]⟩
  have h3 := AnalyticAt.comp (f := B.chart j ∘ ψ ∘ (A.chart k).symm) (x := t) h2 h1
  refine h3.congr ?_
  have hc : ContinuousAt (fun t' => ψ ((A.chart k).symm t')) t :=
    hψ.1.continuousAt.comp ((A.chart k).continuousAt_symm ht)
  filter_upwards [hc.eventually_mem ((B.chart j).open_source.mem_nhds hj)] with t' h
  simp only [Function.comp_apply, (B.chart j).left_inv h]

end Pot

open Pot in
theorem potLoc : PotLoc := by
  intro E _ _ _ H D l Xo c Y S RM Sys Fx Or ψ k V z tr ν hψ hπ hV hVt hpt t₁ ht₁ p
  classical
  obtain ⟨τ, i⟩ := p
  let w : _ → Or.Re.R.X := fun t => ψ ((Sys.A.chart k).symm t)
  let γ : _ → (Σ k, RM.ι k) → ℂ := fun t => Or.Re.R.lift (w t₁) (w t)
  have hwc : ∀ t ∈ V, ContinuousAt w t := fun t ht =>
    hψ.1.continuousAt.comp ((Sys.A.chart k).continuousAt_symm (hVt ht))
  let B := V ∩ w ⁻¹' Or.Re.R.U (w t₁)
  have hB : IsOpen B := (continuousOn_of_forall_continuousAt hwc).isOpen_inter_preimage hV (Or.Re.R.isOpen_U _)
  have ht₁B : t₁ ∈ B := ⟨ht₁, Or.Re.R.mem_U _⟩
  have hγ : ∀ t ∈ B, ∀ q, AnalyticAt ℂ (fun t => γ t q) t := fun t ht q =>
    holo_comp hψ k (hVt ht.1) (Or.Re.R.holo (w t₁) q) ht.2
  have horb : ∀ t ∈ B, SameOrbit (γ t) (Or.Re.R.lift (w t) (w t)) := fun t ht => Or.Re.R.compat _ _ _ ⟨ht.2, Or.Re.R.mem_U _⟩
  have hco : ∀ t ∈ B, CoordsAt Or.𝔐.ξ RM.y (z t) (γ t) := fun t ht => coords_orbit (hpt t ht.1).2.1 (horb t ht)
  have hz : IsHolTo B z := GlobalTheory.T.holomorphic_coords_of_generic_point _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie Or.𝔐.all _ B γ z hB
    (differentiableOn_pi.2 fun q t ht => (hγ t ht q).differentiableAt.differentiableWithinAt) hco
  have hop : ∀ t ∈ V, Or.Re.π (w t) ∈ Sys.open' := fun t ht => by
    rw [hπ]
    exact (hpt t ht).1
  have hin : ∀ t ∈ V, Or.𝔐.Interior (z t) := fun t ht => (Or.interior (w t) (z t) (hpt t ht).2.1).2 (hop t ht)
  have hroot : ∀ r : RootIx D, ∃ G : _ → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
      -Real.log ((Or.sing r).h (γ t)) = Real.log (ν r t ^ HodgeCpt.rootSgn D r) + (G t).re := fun r => by
    refine log_h_an (y := RM.y) hz Or.𝔐.all ht₁B (Or.sing r) (Or.e r) (tr r ^ HodgeCpt.rootSgn D r) (hγ t₁ ht₁B) ?_
    filter_upwards [hB.mem_nhds ht₁B] with t ht
    exact ⟨zpow_pos ((hpt t ht.1).2.2 r).pos _, Or.hodge r (z t) (γ t) (hco t ht) (hin t ht.1) _ _ ((hpt t ht.1).2.2 r)⟩
  choose G hG hGe using hroot
  obtain ⟨W, hW, hwW, G₀, hG₀, e₀⟩ := Or.Re.ref_pot (some (τ, i)) (w t₁) trivial
  have hG₀a : AnalyticAt ℂ (fun t => G₀ (w t)) t₁ := holo_comp hψ k (hVt ht₁) hG₀ hwW
  refine ⟨fun t => ∑ j ∈ Finset.Iic i, G (τ, j) t - G₀ (w t),
    (Finset.analyticAt_fun_sum _ fun j _ => hG _).sub hG₀a, ?_⟩
  filter_upwards [hB.mem_nhds ht₁B, (hwc t₁ ht₁).eventually_mem (hW.mem_nhds hwW),
    (Filter.eventually_all_finset (Finset.Iic i)).2 fun j _ => hGe (τ, j)] with t ht htW h3
  have e1 : Real.log ((Or.Re.ref (some (τ, i))).h (γ t)) -
      (Sys.th (some (τ, i))).φ (Or.Re.π (w t₁)) (Or.Re.π (w t)) = (G₀ (w t)).re := e₀ (w t) htW
  have e2 := Or.fund_sing τ i (w t) (hop t ht.1)
  have e3 := log_orbit (Finset.Iic i) (Or.Re.ref (some (τ, i))) (fun j => Or.sing (τ, j))
    (by rw [Or.fund_deg]; simp only [Or.sing_deg]) (horb t ht) (Or.Re.R.mem _ _ (Or.Re.R.mem_U _)).1
  have e4 : ∑ j ∈ Finset.Iic i, -Real.log ((Or.sing (τ, j)).h (γ t)) =
      ∑ j ∈ Finset.Iic i, ((HodgeCpt.rootSgn D (τ, j) : ℝ) * Real.log (ν (τ, j) t) + (G (τ, j) t).re) :=
    Finset.sum_congr rfl fun j hj => by rw [h3 j hj, Real.log_zpow]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at e4
  simp only [w, hπ] at e1 e2
  show (Sys.th (some (τ, i))).φ _ _ + Sys.ph (some (τ, i)) _ = _
  rw [Complex.sub_re, Complex.re_sum]
  simp only [w] at e3 ⊢
  linarith

end RootFieldNumerics
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.DifferentiableAtAffCoord
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights.LowerBoundFree (torusSmul)
open ReciprocityTheory.AnForm

namespace RootFieldNumerics.Levi

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem tangent_decomp (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, γ t' ∈ mcPts (mCoordIdeal y))
    (himm : ∀ u c, fderiv ℂ γ t u = torusSmul c (γ t) → u = 0) (v : (Σ k, J k) → ℂ)
    (hv : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) v) :
    ∃ (u : Fin e → ℂ) (c : K → ℂ), v = fderiv ℂ γ t u + torusSmul c (γ t) := by
  classical
  have hz := hpts.self_of_nhds
  have hdim := finrank_tanSub_pC_le Ω y _ hP hsm hz
  have hzI : ∀ f ∈ pC (mCoordIdeal y), eval (γ t) f = 0 := by
    have h := hz
    rw [mcPts_eq_pC] at h
    exact h.2
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  have hcone : ∀ x, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) x →
      x ∈ tanSub (pC (mCoordIdeal y)) (γ t) := by
    intro x hx f hf
    have hle : pC (mCoordIdeal y) ≤ tanIdeal (γ t) x := by
      rw [pC, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨hz.2 g hg, hx g hg⟩
    exact (hle hf).2
  let L₁ : (Fin e → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ := (fderiv ℂ γ t).toLinearMap
  let L₂ : (K → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ :=
    { toFun := fun c => torusSmul c (γ t)
      map_add' := fun c c' => by funext q; simp only [torusSmul, Pi.add_apply]; ring
      map_smul' := fun r c => by
        funext q; simp only [torusSmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let L := L₁.coprod L₂
  have hL : ∀ u c, L (u, c) = fderiv ℂ γ t u + torusSmul c (γ t) := fun _ _ => rfl
  have hrange : LinearMap.range L ≤ tanSub (pC (mCoordIdeal y)) (γ t) := by
    rintro _ ⟨⟨u, c⟩, rfl⟩
    rw [hL]
    refine Submodule.add_mem _ (hcone _ ?_) fun f hf => (le_tanIdeal_torusSmul hPh hzI c hf).2
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.G1.isConeTangent_of_sheet le_rfl hγ hpts u
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, c⟩ h
    rw [hL] at h
    have hu : u = 0 := himm u (fun k => -c k) (by
      funext q
      have h1 := congrFun h q
      simp only [torusSmul, Pi.add_apply, Pi.zero_apply] at h1 ⊢
      linear_combination h1)
    subst hu
    have h2 : torusSmul c (γ t) = 0 := by simpa using h
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := hz.1 k
      have h3 : c k * γ t ⟨k, i⟩ = 0 := congrFun h2 ⟨k, i⟩
      exact (mul_eq_zero.mp h3).resolve_right hi
    rw [hc]
    rfl
  have hfr : Module.finrank ℂ (LinearMap.range L) = e + Fintype.card K := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have heq := Submodule.eq_of_le_of_finrank_le hrange (by rw [hfr]; exact hdim)
  have hvr : v ∈ LinearMap.range L := heq ▸ hcone v hv
  obtain ⟨⟨u, c⟩, huc⟩ := hvr
  exact ⟨u, c, huc.symm⟩

theorem differentiableAt_affCoord (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    DifferentiableAt ℂ (affCoord p) z := by
  refine differentiableAt_pi.2 fun q => ?_
  have h1 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v q) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) q).analyticAt z
  have h2 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v ⟨q.1, p q.1⟩) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨q.1, p q.1⟩).analyticAt z
  exact (h1.div h2 (hp q.1)).differentiableAt

theorem affCoord_torus (p : (k : K) → J k) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    affCoord p (torusSmul c z) = affCoord p z := by
  funext q
  simp only [affCoord, torusSmul]
  exact mul_div_mul_left _ _ (hc q.1)

theorem fderiv_affCoord_torus (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) (b : K → ℂ) :
    fderiv ℂ (affCoord p) z (torusSmul b z) = 0 := by
  have h1 : HasDerivAt (fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) (torusSmul b z) 0 := by
    refine hasDerivAt_pi.2 fun q => ?_
    have := (((hasDerivAt_id (0 : ℂ)).mul_const (b q.1)).cexp).mul_const (z q)
    simpa [torusSmul] using this
  have h0 : torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z = z := by
    funext q; simp [torusSmul]
  have h2 : HasFDerivAt (affCoord p) (fderiv ℂ (affCoord p) z)
      (torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z) := by
    rw [h0]; exact (differentiableAt_affCoord p z hp).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℂ) h1
  have h4 : (affCoord p ∘ fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) = fun _ => affCoord p z := by
    funext s
    exact affCoord_torus p _ (fun k => Complex.exp_ne_zero _) z
  rw [h4] at h3
  exact h3.unique (hasDerivAt_const _ _)

theorem levi_torus {e : ℕ} (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, ∀ k, ∃ i, γ t' ⟨k, i⟩ ≠ 0) (hφ : ContDiffAt ℝ 2 φ (γ t)) (u : Fin e → ℂ) (b : K → ℂ) :
    levi φ (γ t) (fderiv ℂ γ t u + torusSmul b (γ t)) = levi (φ ∘ γ) t u := by
  let ℓ : (Unit → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ()
  let lin : (Unit → ℂ) → Fin e → ℂ := fun s => t + ℓ s • u
  have hlin : HasFDerivAt lin (ℓ.smulRight u) 0 := by
    have := (ℓ.smulRight u).hasFDerivAt (x := 0)
    exact this.const_add t
  have hlinA : AnalyticAt ℂ lin 0 := analyticAt_const.add ((ℓ.smulRight u).analyticAt 0)
  have hl0 : lin 0 = t := by simp [lin]
  have hγ' : AnalyticAt ℂ γ (lin 0) := by rw [hl0]; exact hγ
  let Γ : (Unit → ℂ) → (Σ k, J k) → ℂ := fun s => torusSmul (fun k => Complex.exp (ℓ s * b k)) (γ (lin s))
  have hΓ0 : Γ 0 = γ t := by
    funext q; simp [Γ, torusSmul, hl0]
  have hγl : AnalyticAt ℂ (γ ∘ lin) 0 := hγ'.comp hlinA
  have hΓA : AnalyticAt ℂ Γ 0 := by
    refine analyticAt_pi_iff.2 fun q => ?_
    exact (((ℓ.analyticAt 0).mul analyticAt_const).cexp').mul (analyticAt_pi_iff.1 hγl q)
  have hΓd : fderiv ℂ Γ 0 (fun _ => 1) = fderiv ℂ γ t u + torusSmul b (γ t) := by
    have hg : HasFDerivAt (γ ∘ lin) ((fderiv ℂ γ t).comp (ℓ.smulRight u)) 0 := by
      have h1 : HasFDerivAt γ (fderiv ℂ γ t) (lin 0) := by rw [hl0]; exact hγ.differentiableAt.hasFDerivAt
      exact h1.comp 0 hlin
    funext q
    have h1 := (hasFDerivAt_pi'.1 hΓA.differentiableAt.hasFDerivAt q)
    have h2 := (((ℓ.hasFDerivAt (x := 0)).mul_const (b q.1)).cexp).mul (hasFDerivAt_pi'.1 hg q)
    have h3 := congrArg (fun L => L (fun _ => 1)) (h1.unique h2)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply] at h3
    rw [h3]
    simp [ℓ, hl0, torusSmul]
    ring
  have hφγ : ContDiffAt ℝ 2 (φ ∘ γ) t := hφ.comp t (hγ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have e1 := levi_comp (φ := φ) (τ := Γ) (z := 0) (fun _ => 1) hΓA (by rw [hΓ0]; exact hφ)
  rw [hΓ0, hΓd] at e1
  have e2 := levi_comp (φ := φ ∘ γ) (τ := lin) (z := 0) (fun _ => 1) hlinA (by rw [hl0]; exact hφγ)
  rw [hl0, hlin.fderiv] at e2
  have e3 : (ℓ.smulRight u) (fun _ => 1) = u := by simp [ℓ]
  rw [e3] at e2
  rw [← e1, ← e2]
  let G : (Unit → ℂ) → ℂ := fun s => ∑ k, (d k : ℂ) * (ℓ s * b k)
  have hG : AnalyticAt ℂ G 0 :=
    Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ((ℓ.analyticAt 0).mul analyticAt_const)
  have hev : φ ∘ Γ =ᶠ[𝓝 0] fun s => ((φ ∘ γ) ∘ lin) s + 1 * (G s).re := by
    have ht : Tendsto lin (𝓝 0) (𝓝 t) := by rw [← hl0]; exact hlinA.continuousAt
    filter_upwards [ht.eventually hpts] with s hs
    simp only [Function.comp_apply, Γ]
    rw [hhom _ _ (fun k => Complex.exp_ne_zero _) hs, add_comm, one_mul]
    congr 1
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.norm_exp, Real.log_exp]
  have hc1 : ContDiffAt ℝ 2 ((φ ∘ γ) ∘ lin) 0 :=
    ContDiffAt.comp 0 (by rw [hl0]; exact hφγ) (hlinA.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hc2 : ContDiffAt ℝ 2 (fun s => (G s).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0 (hG.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hG]
  simp

theorem levi_nonneg (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y) {B : Ideal (MRing J)} (hB : B = ⊤)
    (R : AnLogRes (mCoordIdeal y) B e) (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (hφ : ∀ z : (Σ k, J k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 φ z)
    (hpsh : ∀ x j, x ∈ (R.A.chart j).source → ∀ u,
      0 ≤ levi (fun t => φ (R.lift x ((R.A.chart j).symm t))) (R.A.chart j x) u)
    (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal y)) (w : (Σ k, J k) → ℂ)
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) z w) : 0 ≤ leviForm φ z w := by
  classical
  have hno : ∀ z : (Σ k, J k) → ℂ, z ∉ mcPts B := fun z hz => by
    subst hB
    simpa using hz.2 1 Submodule.mem_top
  obtain ⟨x, c, hc, hx⟩ := R.surj z hz (hno z)
  obtain ⟨j, hj⟩ := R.A.cover x
  let γ₀ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => R.lift x ((R.A.chart j).symm t)
  let γ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => torusSmul (fun k => (c k)⁻¹) (γ₀ t)
  have hci : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hsx : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmemO : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsx]; exact R.mem_U x⟩
  have hO := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hmemO
  have hγ₀A : AnalyticAt ℂ γ₀ (R.A.chart j x) := analyticAt_pi_iff.2 fun q => R.holo x q j _ hmemO
  have hγA : AnalyticAt ℂ γ (R.A.chart j x) :=
    analyticAt_pi_iff.2 fun q => analyticAt_const.mul (analyticAt_pi_iff.1 hγ₀A q)
  have hγz : γ (R.A.chart j x) = z := by
    funext q
    simp only [γ, γ₀, torusSmul, hsx, hx]
    rw [← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have h0pts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ₀ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hO] with t ht using R.mem x _ ht.2
  have hpts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [h0pts] with t ht
    exact mcPts_smul hP.2.1.2.1 _ hci ht
  choose p hp using hz.1
  have himm : ∀ u b, fderiv ℂ γ (R.A.chart j x) u = torusSmul b (γ (R.A.chart j x)) → u = 0 := by
    intro u b hub
    have hp' : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0 := fun k => by
      rw [hx]; exact mul_ne_zero (hc k) (hp k)
    have hk := R.immersion x (hno _) p hp' j hj
    have hfun : (fun t => affCoord p (R.lift x ((R.A.chart j).symm t))) = affCoord p ∘ γ := by
      funext t
      exact (affCoord_torus p _ hci _).symm
    rw [hfun, fderiv_comp _ (by rw [hγz]; exact differentiableAt_affCoord p z hp) hγA.differentiableAt] at hk
    have : u ∈ (⊥ : Submodule ℂ (Fin e → ℂ)) := by
      rw [← hk]
      show fderiv ℂ (affCoord p) (γ (R.A.chart j x)) (fderiv ℂ γ (R.A.chart j x) u) = 0
      rw [hub, hγz]
      exact fderiv_affCoord_torus p z hp b
    exact this
  obtain ⟨u, b, hub⟩ := tangent_decomp Ω y e hP hsm γ _ hγA hpts himm w (by rw [hγz]; exact hw)
  have h1 := levi_torus φ d hhom γ _ hγA (hpts.mono fun t ht => ht.1) (by rw [hγz]; exact hφ z hz.1) u b
  rw [← hub, hγz] at h1
  show 0 ≤ levi φ z w
  rw [h1]
  have hev : φ ∘ γ =ᶠ[𝓝 (R.A.chart j x)] fun t => φ (γ₀ t) +
      1 * ((fun _ : Fin e → ℂ => ((∑ k, d k * Real.log ‖(c k)⁻¹‖ : ℝ) : ℂ)) t).re := by
    filter_upwards [h0pts] with t ht
    simp only [Function.comp_apply, γ]
    rw [hhom _ _ hci ht.1, Complex.ofReal_re, one_mul, add_comm]
  have hc1 : ContDiffAt ℝ 2 (fun t => φ (γ₀ t)) (R.A.chart j x) :=
    (hφ _ h0pts.self_of_nhds.1).comp _ (hγ₀A.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 contDiffAt_const, levi_re_analytic analyticAt_const]
  simpa using hpsh x j hj u

end RootFieldNumerics.Levi
end
end

