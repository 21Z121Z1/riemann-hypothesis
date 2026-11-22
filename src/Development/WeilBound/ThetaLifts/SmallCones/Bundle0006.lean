import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.ConeUnf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0072
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0070
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdeleRingCocompactDiscreteNumberFieldStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.IsFrPlane
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0334
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0004
import Development.WeilBound.ThetaLifts.TowerModels.PlaneReal

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeLaw
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem levi_one (H : Plane E d d₁) : IsLevi (σ := σ) (W := W) (W₁ := W₁) H 1 1 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat_one']

theorem absE_ne (l : (AE F E)ˣ) : (absE F E l : ℝ) ≠ 0 := by
  have : absE F E l * absE F E l⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact_mod_cast left_ne_zero_of_mul_eq_one this

theorem absE_pos (l : (AE F E)ˣ) : 0 < (absE F E l : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg _) (absE_ne l).symm

structure LawsT (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Ten F E n d) (w : (AE F E)ˣ → ℂ) (ι : (AE F E)ˣ → (AE F E)ˣ) : Prop where
  one : ι 1 = 1
  w1 : w 1 = 1
  uni : ∀ m ∈ unip σ X H, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) (om (m, 1) Ψ)) = e (M.co.rho B.ψ (u 1) Ψ)
  tor : ∀ l g₁ p h₁ p', IsLevi H (ι l) g₁ p → IsLevi H' 1 h₁ p' → ∀ Ψ ∈ schA F (Fin n × Fin d),
    (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) • e (M.co.rho B.ψ (u 1) (om (p, p') Ψ)) =
      w l • om₀ (g₁, h₁) (e (M.co.rho B.ψ (u l) Ψ))

structure Laws (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (om₀ : Rep σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (u : (AE F E)ˣ → Ten F E n d) (ν χ : Chr F E) (z : ℕ) (ι : (AE F E)ˣ → (AE F E)ˣ) : Prop
    extends LawsT B M om om₀ H H' e u (fun l => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ι where
  torW : ∀ t h₁ p', IsLevi H' t h₁ p' → ∃ s : (AE F E)ˣ, ∀ l, ∀ Ψ ∈ schA F (Fin n × Fin d),
    e (M.co.rho B.ψ (u l) (om (1, p') Ψ)) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) *
      ((ν s : ℂ) * ((absE F E s : ℝ) : ℂ) ^ z)) • om₀ (1, h₁) (e (M.co.rho B.ψ (u (l * s)) Ψ))

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁}
  {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν χ : Chr F E} {z : ℕ}
  {ι : (AE F E)ˣ → (AE F E)ˣ} {w : (AE F E)ˣ → ℂ} {χX χW : Chr F E} {r s r' s' r₀ s₀ r₀' s₀' : ℕ}

theorem LawsT.theta (h : LawsT B M om om₀ H H' e u w ι) {l g₁ p h₁ p'} (h1 : IsLevi H (ι l) g₁ p) (h2 : IsLevi H' 1 h₁ p') {Ψ}
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) :
    thetaSum F (e (M.co.rho B.ψ (u 1) (om (p, p') Ψ))) * (((absE F E (ι l) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) =
      theta om₀ (e (M.co.rho B.ψ (u l) Ψ)) g₁ h₁ * w l := by
  have := congrArg (thetaSum F) (h.tor l g₁ p h₁ p' h1 h2 Ψ hΨ)
  rw [thetaSum_smul', thetaSum_smul'] at this
  rw [mul_comm, this, mul_comm]
  rfl

theorem LawsT.rat (h : LawsT B M om om₀ H H' e u w ι) (hD : StabDec) (hTB : ThetaBasic) (hp : IsPair B M χX χW om r s r' s')
    (hp₀ : IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀') {j₀ j₁} (hH : H.IsAdapted σ B X X₁ j₀ j₁)
    (hs : ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u 1) Ψ) ∈ schA F (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (y) {δ} (hδ : δ ∈ ratU σ X.J) (hx : mat δ *ᵥ incV F H.x = incV F H.x) (g) :
    thv B M om e (u 1) Φ y (δ * g) = thv B M om e (u 1) Φ y g := by
  obtain ⟨m, hm, g₁, p, hp1, rfl, hr⟩ := (hD F E σ B n n₁ X X₁ H j₀ j₁ r s hp.base (Or.inl hp.herm) hH).1 δ 1 (by simpa using hx)
  have hΨ := pair_pres hp (g, y) hΦ
  have e1 : om (m * p * g, y) Φ = om (m, 1) (om (p, 1) (om (g, y) Φ)) := by simp [om_mul, mul_assoc]
  have e2 := h.theta (l := 1) (by rwa [h.one]) (levi_one (W₁ := W₁) H') hΨ
  have e3 := ((hTB F E σ B _ _ X₁ W₁ M₀ χX χW om₀ _ _ _ _ hp₀).1 _ (hs _ hΨ)).2.1 g₁ (hr hδ) 1 (one_mem _) 1 1
  simp only [h.one, h.w1, map_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, mul_one, Circle.coe_one, one_pow] at e2 e3
  unfold thv
  rw [e1, h.uni m hm _ (pair_pres hp _ hΨ), e2, e3]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, ← Prod.one_eq_mk]

theorem Laws.coneI_law [μ.IsMulRightInvariant] [MeasurableMul (AE F E)ˣ] (h : Laws B M om om₀ H H' e u ν χ z ι)
    (hp : IsPair B M χX χW om r s r' s') {K : Subgroup (UA σ X.J)} (μK : Measure K) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    {t h₁ p} (hl : IsLevi H' t h₁ p) (y) :
    coneI B M om M₀ om₀ e K μK μ u ν z (om (1, p * y) Φ) 1 =
      (χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, y) Φ) h₁ := by
  obtain ⟨s, hs⟩ := h.torW t h₁ p hl
  unfold coneI
  rw [← integral_const_mul]
  congr 1
  funext k
  rw [← integral_mul_right_eq_self (fun l => M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) (om (1, y) Φ)))) h₁ * (ν l : ℂ) *
    ((absE F E l : ℝ) : ℂ) ^ z) s, ← integral_const_mul]
  congr 1
  funext l
  have e1 : om (k.1, 1) (om (1, p * y) Φ) = om (1, p) (om (k.1, 1) (om (1, y) Φ)) := by simp [om_mul]
  rw [e1, hs l _ (pair_pres hp _ (pair_pres hp _ hΦ))]
  simp only [Model.I, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta, map_smul, thetaSum_smul', om_mul, Prod.mk_mul_mk, mul_one, one_mul, integral_const_mul,
    map_mul, Circle.coe_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_pow]
  ring

end Core

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.UnfMod
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.Doubling (absE)

noncomputable section

namespace PositivityTheory.ThKCT.Unf

theorem lattice_one {V Λ : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddRightInvariant]
    (h0 : μ ≠ 0) [AddCommGroup Λ] [Countable Λ] (j : Λ →+ V) {C : Set V} (hC : MeasurableSet C) (hf : μ C ≠ ⊤)
    (cov : ∀ y, ∃ l, y + j l ∈ C) (fin : ∀ y, {l | y + j l ∈ C}.Finite) (T : V →+ V) (hT : Measurable T) (t : Λ ≃ Λ)
    (ht : ∀ l, T (j l) = j (t l)) {c : ℝ≥0} (hc : μ.map T = c • μ) : c = 1 := by
  let S : V → ℝ≥0∞ := fun y => ∑' l, C.indicator 1 (y + j l)
  have hi : Measurable (C.indicator (1 : V → ℝ≥0∞)) := measurable_one.indicator hC
  have hS : Measurable S := Measurable.tsum fun l => hi.comp (measurable_add_const _)
  have S1 : ∀ y, 1 ≤ S y := fun y => by
    obtain ⟨l, hl⟩ := cov y
    exact le_trans (by simp [hl]) (ENNReal.le_tsum l)
  have S2 : ∀ y, S y ≠ ⊤ := fun y => by
    simp only [S]
    rw [tsum_eq_sum (s := (fin y).toFinset) fun l hl => Set.indicator_of_notMem (by simpa using hl) _]
    exact ENNReal.sum_ne_top.2 fun l _ => by by_cases h : y + j l ∈ C <;> simp [h]
  have S3 : ∀ y l, S (y + j l) = S y := fun y l => by
    simp only [S, add_assoc, ← map_add]
    exact (Equiv.addLeft l).tsum_eq fun m => C.indicator 1 (y + j m)
  let β : V → ℝ≥0∞ := fun y => C.indicator 1 y * (S y)⁻¹
  have hβ : Measurable β := hi.mul hS.inv
  have b1 : ∀ y, ∑' l, β (y + j l) = 1 := fun y => by
    simp only [β, S3]
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_inv_cancel (zero_lt_one.trans_le (S1 y)).ne' (S2 y)
  have b2 : ∀ y, ∑' l, β (T (y + j l)) = 1 := fun y => by
    simp only [map_add, ht]
    exact (t.tsum_eq fun l => β (T y + j l)).trans (b1 _)
  have half : ∀ f g : V → ℝ≥0∞, Measurable f → Measurable g → (∀ y, ∑' l, g (y + j l) = 1) →
      ∫⁻ y, f y ∂μ = ∑' l, ∫⁻ y, f y * g (y + j l) ∂μ := fun f g h1 h2 h3 => by
    rw [← lintegral_tsum (f := fun l y => f y * g (y + j l)) fun l => (h1.mul (h2.comp (measurable_add_const _))).aemeasurable]
    simp only [ENNReal.tsum_mul_left, h3, mul_one]
  have e : ∫⁻ y, β (T y) ∂μ = ∫⁻ y, β y ∂μ := by
    rw [half (fun y => β (T y)) β (hβ.comp hT) hβ b1, half β (fun y => β (T y)) hβ (hβ.comp hT) b2, ← (Equiv.neg Λ).tsum_eq]
    refine tsum_congr fun l => ?_
    rw [← lintegral_add_right_eq_self _ (j l)]
    simp [mul_comm]
  rw [← lintegral_map hβ hT, hc, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul] at e
  have n0 : ∫⁻ y, β y ∂μ ≠ 0 := fun h => h0 (by
    rw [← Measure.measure_univ_eq_zero, ← lintegral_one, half _ β measurable_const hβ b1]
    simp [lintegral_add_right_eq_self β, h])
  have n1 : ∫⁻ y, β y ∂μ ≠ ⊤ := ne_top_of_le_ne_top hf (by
    rw [← lintegral_indicator_one hC]
    exact lintegral_mono fun y => mul_le_of_le_one_right' (ENNReal.inv_le_one.2 (S1 y)))
  exact_mod_cast (ENNReal.mul_left_inj n0 n1).1 (e.trans (one_mul _).symm)

theorem eq_one_of_bdd {T : Type} [Group T] (φ : T →* ℝ≥0) {b : ℝ≥0} (h : ∀ t, φ t ≤ b) (t : T) : φ t = 1 := by
  have k : ∀ t, φ t ≤ 1 := fun t => not_lt.1 fun h1 => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b h1
    exact absurd (h (t ^ n)) (by rw [map_pow]; exact not_le.2 hn)
  refine le_antisymm (k t) ?_
  calc 1 = φ t * φ t⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ φ t := mul_le_of_le_one_right' (k _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem absE_flow (h : IsCMExt F E σ) {τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ} (hτ : IsFlow τ) (x : ℝ) :
    (absE F E (τ (Multiplicative.ofAdd x)) : ℝ) = Real.exp (2 * Module.finrank ℚ F * x) := by
  obtain ⟨-, θ, hθ, hv⟩ := hτ
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have e := GlobalTheory.CompanionTheory.SW.FChi.norm_tmul_one h.2.2.1 (AF F) (pairA F (θ (Real.exp x)) 1)
  rw [← hv] at e
  simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf, e, map_pow]
  have e1 : ∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.AdelicU.evFin F v (pairA F (θ (Real.exp x)) 1) = 1 := fun v =>
    map_one (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)
  have e2 : ∀ w : InfinitePlace F, ‖GlobalTheory.AdelicU.evInf F w (pairA F (θ (Real.exp x)) 1)‖ = Real.exp x := fun w => by
    have := Complex.ringHom_eq_ofReal_of_continuous (f := (InfinitePlace.Completion.extensionEmbedding w).comp
      ((Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp θ))
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_apply w).comp hθ))
    have h2 := congrArg (fun f : ℝ →+* ℂ => ‖f (Real.exp x)‖) this
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]
    refine Eq.trans h2 ?_
    simp
  simp only [e1, one_pow, nnnorm_one, finprod_one, mul_one, NNReal.coe_prod, NNReal.coe_pow, nnnorm_pow, coe_nnnorm, e2,
    Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  rw [← pow_mul, ← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem modulus (h : IsCMExt F E σ) (M : ℕ) (μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (μA : Measure (AF F))
    (hW : μW.IsAddHaarMeasure) (hA : μA.IsAddHaarMeasure) : ∃ χ : (AF F ⊗[F] E)ˣ →* ℝ≥0, Continuous χ ∧
      (∀ a : (AF F ⊗[F] E)ˣ, (μW.prod μA).map (fun p => (sigR (AF F) σ (a : AF F ⊗[F] E) • p.1,
        Algebra.norm (AF F) (a : AF F ⊗[F] E) * p.2)) = χ a • μW.prod μA) ∧ ∀ a, χ a * absE F E a ^ (M + 1) = 1 := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ h (AF F)
  have := hB 1 M
  have : BorelSpace (AF F) := ⟨rfl⟩
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable F := Function.Injective.countable (Module.finBasis ℚ F).equivFun.injective
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ h
  obtain ⟨χ, χc, χ1, χ2⟩ := GlobalTheory.T.modulus_character_unit_action_product F E σ h τ hτ M μW μA hW hA
  obtain ⟨ω, hω, hid⟩ := GlobalTheory.T.adelic_units_decomposition_flow_compact F E σ h τ hτ
  obtain ⟨⟨CW, hCW, cW⟩, fW, -⟩ := GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ h 1 M
  obtain ⟨⟨CA, hCA, cA⟩, fA, -⟩ := GlobalTheory.T.adele_ring_cocompact_discrete_number_field F
  have rt : ∀ X Y : Fin 1 → Fin M → E, ratTup (F := F) (AF F) (X + Y) = ratTup (AF F) X + ratTup (AF F) Y :=
    fun X Y => funext fun a => funext fun i => map_add _ _ _
  have rat : ∀ (l : Eˣ) (a : (AF F ⊗[F] E)ˣ), (a : AF F ⊗[F] E) = inclR (AF F) (l : E) → χ a = 1 := fun l a hl => by
    have hs : σ l ≠ 0 := (map_ne_zero σ).2 l.ne_zero
    have hn : Algebra.norm F (l : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 l.ne_zero
    let j : (Fin 1 → Fin M → E) × F →+ (Fin 1 → Fin M → AF F ⊗[F] E) × AF F :=
      (AddMonoidHom.mk' _ rt).prodMap (algebraMap F (AF F)).toAddMonoidHom
    refine lattice_one (μW.prod μA) (NeZero.ne _) j (hCW.prod hCA).measurableSet (hCW.prod hCA).measure_lt_top.ne
      (fun y => ?_) (fun y => ?_) ((DistribSMul.toAddMonoidHom _ (sigR (AF F) σ (a : AF F ⊗[F] E))).prodMap
        (AddMonoidHom.mulLeft (Algebra.norm (AF F) (a : AF F ⊗[F] E)))) ?_
      ((MulAction.toPerm (Units.mk0 _ hs)).prodCongr (Equiv.mulLeft₀ _ hn)) (fun l' => Prod.ext ?_ ?_) (χ1 a)
    · obtain ⟨X, hX⟩ := cW y.1
      obtain ⟨r, hr⟩ := cA y.2
      exact ⟨-(X, r), by rw [map_neg, ← sub_eq_add_neg]; exact ⟨hX, hr⟩⟩
    · refine ((fW _ (hCW.image (continuous_add_left (-y.1)))).prod (fA _ (hCA.image (continuous_add_left (-y.2))))).subset ?_
      exact fun l' hl' => ⟨⟨_, hl'.1, neg_add_cancel_left _ _⟩, ⟨_, hl'.2, neg_add_cancel_left _ _⟩⟩
    · exact ((continuous_const_smul _ : Continuous fun x : Fin 1 → Fin M → AF F ⊗[F] E => (_ : AF F ⊗[F] E) • x).prodMap (continuous_const.mul continuous_id : Continuous fun x : AF F => _ * x)).measurable
    · funext b i
      show sigR (AF F) σ (a : AF F ⊗[F] E) * inclR (AF F) (l'.1 b i) = inclR (AF F) (σ l * l'.1 b i)
      rw [hl, map_mul]; rfl
    · show Algebra.norm (AF F) (a : AF F ⊗[F] E) * algebraMap F (AF F) l'.2 = algebraMap F (AF F) (Algebra.norm F (l : E) * l'.2)
      rw [hl, map_mul]
      exact congrArg (· * _) (GlobalTheory.Doubling.norm_inclR _)
  have hc : Continuous fun a => χ a * absE F E a ^ (M + 1) := χc.mul (GlobalTheory.Doubling.continuous_absE.pow _)
  obtain ⟨b, hb⟩ := (hω.image hc).bddAbove
  refine ⟨χ, χc, χ1, eq_one_of_bdd (χ * (powMonoidHom (M + 1)).comp (absE F E)) (b := b) fun a => ?_⟩
  obtain ⟨l, a', x, j, hl, hx, rfl⟩ := hid a
  have e1 : absE F E a' = 1 := by
    rw [← GlobalTheory.Doubling.absE_inclR (F := F) l]
    exact congrArg _ (Units.ext hl)
  have e2 : χ (τ (Multiplicative.ofAdd (j : ℝ))) * absE F E (τ (Multiplicative.ofAdd (j : ℝ))) ^ (M + 1) = 1 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, NNReal.coe_pow, χ2, absE_flow h hτ, ← Real.exp_nat_mul, ← Real.exp_add, NNReal.coe_one, Real.exp_eq_one_iff]
    push_cast
    ring
  rw [map_mul, map_mul]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, powMonoidHom_apply, rat l a' hl, e1, e2, one_pow, one_mul]
  exact hb ⟨x, hx, rfl⟩

end PositivityTheory.ThKCT.Unf
end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.UnipEx
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr
open GlobalTheory.Doubling (absE)

theorem unipEx_of : UnipEx := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have G := PositivityTheory.ThKEnd.Grp.unipGood hB.cm (hY.imp (·.herm) (·.skew)) (det_ne hY)
    ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, (h.isUnit_det (det_ne hY).isUnit).ne_zero⟩
  refine ⟨G.ex, G.cov, G.closed, G.right, ?_, fun u hu => ⟨(mem_unip.1 hu).1, ?_⟩, ?_⟩
  · choose m h1 h2 using exists_levi hB.cm h
    let lev : (AE F E)ˣ × UA σ Y₁.J →* UA σ Y.J := MonoidHom.mk' (fun z => m z.1 z.2)
      fun a b => levi_uniq h (h1 _ _) (levi_mul (h1 _ _) (h1 _ _))
    have hc : Continuous (cA σ : AE F E → AE F E) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
    have c1 : Continuous fun z => mat (lev z) := by
      have e : (fun z => mat (lev z)) = fun z => _ := funext fun z => h2 z.1 z.2
      rw [e]
      refine (continuous_const.matrix_mul (continuous_matrix fun i j => ?_)).matrix_mul continuous_const
      rcases i with i | i <;> rcases j with j | j
      · exact (PositivityTheory.ThKEnd.Grp.continuous_mat.comp continuous_snd).matrix_elem i j
      · exact continuous_const
      · exact continuous_const
      · fin_cases i <;> fin_cases j
        exacts [Units.continuous_val.comp continuous_fst, continuous_const, continuous_const,
          hc.comp (Units.continuous_coe_inv.comp continuous_fst)]
    refine ⟨lev, Continuous.subtype_mk (f := fun z => (lev z).1) (Units.continuous_iff.2 ⟨c1, ?_⟩) _, h1,
      fun t g p hp => levi_uniq h hp (h1 t g)⟩
    have e : (fun z => mat (lev z)⁻¹) = (fun z => mat (lev z)) ∘ fun z => z⁻¹ := funext fun z => by simp
    exact (e ▸ c1.comp continuous_inv : Continuous fun z => mat (lev z)⁻¹)
  · exact h.ad.fix_y (PositivityTheory.ThKG.Tow.Levi.cA_cA hB.cm) u.2 (mem_unip.1 hu).1
  · obtain ⟨t, ht⟩ : ∃ t, absE F E t = ((4 : ℝ≥0) ^ Fintype.card (InfinitePlace F))⁻¹ := ⟨_, GlobalTheory.Eis.Conv.absE_halfE F E σ hB.cm⟩
    refine ⟨t⁻¹, ?_⟩
    rw [map_inv, ht, inv_inv, NNReal.coe_pow]
    exact one_lt_pow₀ (by norm_num) Fintype.card_ne_zero

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.WittOf
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix NNReal
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr

theorem sig_val {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {A : Matrix (Fin n) (Fin r ⊕ Fin s) ℂ}
    (hA : Aᵀ * M * A.map star = Matrix.fromBlocks 1 0 0 (-1)) (u : Fin r ⊕ Fin s → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (A *ᵥ u) =
      ((∑ i, Complex.normSq (u (Sum.inl i)) - ∑ i, Complex.normSq (u (Sum.inr i)) : ℝ) : ℂ) := by
  have e : star (A *ᵥ u) = A.map star *ᵥ star u := funext fun i => RingHom.map_mulVec (starRingEnd ℂ) A u i
  rw [e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
  simp [Matrix.fromBlocks_mulVec, dotProduct, Matrix.neg_mulVec, Complex.mul_conj, sub_eq_add_neg]

theorem aniso {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) {x : Fin n → ℂ}
    (hx : x ⬝ᵥ M *ᵥ star x = 0) : x = 0 := by
  obtain ⟨hn, A, hA⟩ := h
  obtain ⟨A', -, h1⟩ := PositivityTheory.ThKG.Tow.Pln.frame_inv hn hA
  have e : x = A *ᵥ (A' *ᵥ x) := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  generalize A' *ᵥ x = u at e
  rw [e, sig_val hA, Complex.ofReal_eq_zero] at hx
  have : u = 0 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_sub, neg_eq_zero] at hx
      ext (i | i)
      · exact i.elim0
      · exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 hx i (Finset.mem_univ _))
    · simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] at hx
      ext (i | i)
      · exact Complex.normSq_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _).1 hx i (Finset.mem_univ _))
      · exact i.elim0
  rw [e, this, Matrix.mulVec_zero]

theorem witt_of : Witt := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  refine ⟨fun h0 x hx => ?_, fun n₁ H h1 h2 => ?_⟩
  · obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have e := congrArg (B.emb w).1 hx
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hB.cm.2.2.2, map_zero] at e
    have := aniso (hX.sig w) h0 (x := fun i => (B.emb w).1 (x i)) e
    exact funext fun i => (B.emb w).1.injective ((congrFun this i).trans (map_zero _).symm)
  · obtain ⟨c, hc, hσ⟩ := PositivityTheory.ThKF.exists_scale hB.cm (-1)
    have f : ∀ x, form σ X.J x x = 0 → form σ (c • X.J) x x = 0 := fun x hx => by
      rw [form, Matrix.smul_mulVec, dotProduct_smul]
      exact smul_eq_zero_of_right _ hx
    have key := fun x : IsoV σ X => PositivityTheory.ThKEnd.Grp.wittVec F E σ hB.cm n (c • X.J)
      (fun i j => by simp [hσ, hX.herm])
      (by rw [Matrix.det_smul]; exact mul_ne_zero (pow_ne_zero _ hc) (det_ne (Or.inl hX))) x.1 H.x x.2.1 h1 (f _ x.2.2) (f _ h2)
    choose g g1 g2 using key
    have g3 : ∀ x, (g x).1ᵀ * X.J * (g x).1.map σ = X.J := fun x => smul_right_injective _ hc (by
      have := g1 x
      rwa [Matrix.mul_smul, Matrix.smul_mul] at this)
    have key : ∀ x, ∃ p : UA σ X.J, mat p = incM F (g x).1 := fun x =>
      PositivityTheory.ThKG.Tow.Levi.exists_UA (g' := incM F (g x)⁻¹.1)
        (by rw [← PositivityTheory.ThKEnd.Grp.incM_mul, Units.mul_inv, PositivityTheory.ThKEnd.Grp.incM_one])
        (by
          conv_rhs => rw [← g3 x]
          rw [PositivityTheory.ThKEnd.Grp.incM_mul, PositivityTheory.ThKEnd.Grp.incM_mul, PositivityTheory.ThKEnd.Grp.incM_conj]
          rfl)
    choose γ hγ using key
    exact ⟨γ, fun x => ⟨mem_ratU.2 ⟨_, hγ x⟩, by rw [hγ, PositivityTheory.ThKEnd.Grp.incM_mulVec, g2]⟩⟩

end PositivityTheory.ThKCT

end
end

