import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveElementPowersIndepStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_element_powers_indep : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | exact GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | (intros; apply GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModulesGlueCoverStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_modules_glue_cover : ∀ (R E : Type) [CommRing R] [AddCommGroup E] [Module R E] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  ∀ (F : J → Type) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [∀ i, Module (Localization.Away (f i)) (F i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (F i)] [∀ i, Module.Finite (Localization.Away (f i)) (F i)]
    [∀ i, Module.Projective (Localization.Away (f i)) (F i)] (φ : ∀ i, E →ₗ[R] F i),
    (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (φ i)) → Module.Finite R E ∧ Module.Projective R E := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover | exact GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover | (intros; apply GlobalTheory.CompanionTheory.Ggeo.finite_projective_of_isLocalizedModule_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_stalk_closed {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (U : X.Opens) (hp : p.1 ∈ U)
    (hη : genPt ξ ∈ U) (r : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp r) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := U) hp p.2
  have h2 := congr(($h).hom r)
  have e : ∀ x, genMap ξ p x =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes p.2).hom x) := fun _ => rfl
  rw [e]
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem stalk_eq_germ_div_of_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (b : X.presheaf.stalk x.1) :
    ∃ r t : Γ(X, U), b * X.presheaf.germ U x.1 x.2 t = X.presheaf.germ U x.1 x.2 r ∧
      IsUnit (X.presheaf.germ U x.1 x.2 t) := by
  have hl := hU.isLocalization_stalk x
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj (hU.primeIdealOf x).asIdeal.primeCompl b
  exact ⟨r, t.1, hrt, IsLocalization.map_units (X.presheaf.stalk x.1)
    (M := (hU.primeIdealOf x).asIdeal.primeCompl) t⟩

theorem regAt_isLocalRing_isFractionRing_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ →
      ∀ p : Cpt ξ, IsLocalRing (regAt ξ p) ∧ IsFractionRing (regAt ξ p) Ω ∧
        Nonempty (X.presheaf.stalk p.1 ≃+* regAt ξ p) := by
  intro X Ω _ ξ hξ p
  have hsurj : Function.Surjective (genMap ξ p).rangeRestrict := (genMap ξ p).rangeRestrict_surjective
  have hinj : Function.Injective (genMap ξ p).rangeRestrict := fun a b h =>
    hξ.inj p (congrArg Subtype.val h)
  have e : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict ⟨hinj, hsurj⟩
  have hloc : IsLocalRing (regAt ξ p) :=
    IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict hsurj
  refine ⟨hloc, ?_, ⟨e⟩⟩
  apply IsFractionRing.of_field
  intro a
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p.1) trivial
  have hη : genPt ξ ∈ U := p.2.mem_open U.2 hpU
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = a :=
    hξ.bij.2 a
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨⟨_, X.presheaf.germ U p.1 hpU r, rfl⟩, ⟨_, X.presheaf.germ U p.1 hpU t, rfl⟩, ?_⟩
  show _ = genMap ξ p (X.presheaf.germ U p.1 hpU r) / genMap ξ p (X.presheaf.germ U p.1 hpU t)
  rw [genMap_germ_eq_stalk_closed ξ p U hpU hη, genMap_germ_eq_stalk_closed ξ p U hpU hη, eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionExtendsFromStalkPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_extends_from_stalk_pullback : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ X) (p : X) (y₀ : Y), π y₀ = p → ∀ (c : Z ⟶ pullback π (X.fromSpecStalk p)) [IsClosedImmersion c] (s : Γ(Z, ⊤)), ∃ (W : Y.Opens) (f : Γ(Y, W)), y₀ ∈ W ∧ ((c ≫ pullback.fst π (X.fromSpecStalk p)).app W).hom f = Z.presheaf.map (homOfLE (le_top : (c ≫ pullback.fst π (X.fromSpecStalk p)) ⁻¹ᵁ W ≤ ⊤)).op s := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension | exact GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension | (intros; apply GlobalTheory.CompanionTheory.Ggeo.LocalLift.exists_open_extension <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SiegelLimitImagBound
section
open Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.PeriodLimitSeq

open GlobalTheory.CompanionTheory.PeriodLimit

theorem int_seq_const (a : ℕ → ℤ) (L : ℂ) (h : Tendsto (fun m => (a m : ℂ)) atTop (𝓝 L)) :
    ∃ N : ℤ, L = N ∧ ∀ᶠ m in atTop, a m = N := by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 h (1 / 2) (by norm_num)
  have key : ∀ m ≥ M, a m = a M := by
    intro m hm
    have h2 : dist (a m : ℂ) (a M : ℂ) < 1 := by
      calc dist (a m : ℂ) (a M : ℂ) ≤ dist (a m : ℂ) L + dist (a M : ℂ) L :=
            dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add (hM m hm) (hM M le_rfl)
        _ = 1 := by norm_num
    rw [Complex.dist_eq, ← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs] at h2
    have h3 : |a m - a M| < 1 := by exact_mod_cast h2
    exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h3)
  have hev : ∀ᶠ m in atTop, a m = a M := eventually_atTop.2 ⟨M, key⟩
  refine ⟨a M, ?_, hev⟩
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun m hm => by simp [hm]))

theorem mulVec_expand {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (A : Matrix (Fin g) (Fin g) ℂ)
    (t : ℂ) (v : Fin g → ℤ) (k : Fin g) :
    ((A + t • Bs.map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k
      = (A *ᵥ (fun k => (v k : ℂ))) k + t * (((Bs *ᵥ v) k : ℤ) : ℂ) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem im_mulVec_lemma {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) (k : Fin g) :
    ((M *ᵥ (fun k => (v k : ℂ))) k).im = ((M.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

theorem freq_ker {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ)
    (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ)
    (hσ : Tendsto σs atTop (𝓝 σ)) (ht : Tendsto (fun m => (t m).im) atTop atTop)
    (hτ : ∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ)))
    (hy : Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y))
    (v : Fin g → ℤ) (hv : ∃ᶠ m in atTop, vs m = v) :
    Bs *ᵥ v = 0 ∧ ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k := by
  have hyk : ∀ k, Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k)
      atTop (𝓝 (y k)) := fun k => tendsto_pi_nhds.1 hy k
  have hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (v k : ℂ))) k) atTop
      (𝓝 ((σ *ᵥ (fun k => (v k : ℂ))) k)) := by
    intro k
    have hc : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (v k : ℂ))) k) :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    exact (hc.tendsto σ).comp hσ
  have htpos : ∀ᶠ m in atTop, 0 < (t m).im := ht.eventually_gt_atTop 0
  have hid : ∀ m, vs m = v → ∀ k,
      (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im + (t m).im * (((Bs *ᵥ v) k : ℤ) : ℝ) := by
    intro m hm k
    rw [Pi.add_apply, hm, hτ m, mulVec_expand]
    simp [Complex.mul_im]
  have hker : Bs *ᵥ v = 0 := by
    funext k
    have hf : Tendsto (fun m => ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im) atTop (𝓝 0) :=
      (((Complex.continuous_im.tendsto _).comp (hyk k)).sub
        ((Complex.continuous_im.tendsto _).comp (hσk k))).div_atTop ht
    have hfreq : ∃ᶠ m in atTop, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im = (((Bs *ᵥ v) k : ℤ) : ℝ) := by
      refine (hv.and_eventually htpos).mono fun m hm => ?_
      rw [hid m hm.1 k, add_sub_cancel_left]
      exact mul_div_cancel_left₀ _ hm.2.ne'
    have h0 := tendsto_nhds_unique_of_frequently_eq hf tendsto_const_nhds hfreq
    show (Bs *ᵥ v) k = 0
    exact_mod_cast h0.symm
  refine ⟨hker, fun k => ?_⟩
  rw [← im_mulVec_lemma σ v k]
  have hfreq2 : ∃ᶠ m in atTop,
      (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im := by
    refine hv.mono fun m hm => ?_
    rw [hid m hm k, hker]
    simp
  exact tendsto_nhds_unique_of_frequently_eq ((Complex.continuous_im.tendsto _).comp (hyk k))
    ((Complex.continuous_im.tendsto _).comp (hσk k)) hfreq2

private theorem cast_mulVec_lemma_2 {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (v k : ℝ)) = fun k => (((Bs *ᵥ v) k : ℤ) : ℝ) := by
  funext k
  simp [Matrix.mulVec, dotProduct]

theorem unique_value {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ)
    (c : ℝ) (hc : 0 < c) (y : Fin g → ℂ)
    (hpos : ∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 →
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v))
    (v v' : Fin g → ℤ) (hk : Bs *ᵥ v = 0) (hk' : Bs *ᵥ v' = 0)
    (hi : ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k)
    (hi' : ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v' k : ℝ))) k) : v = v' := by
  obtain ⟨w, hw⟩ : ∃ w : Fin g → ℝ, w = (fun k => (v k : ℝ)) - (fun k => (v' k : ℝ)) := ⟨_, rfl⟩
  have hBw : Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, cast_mulVec_lemma_2, cast_mulVec_lemma_2, hk, hk']
    funext k
    simp
  have hSw : (σ.map Complex.im) *ᵥ w = 0 := by
    funext k
    have e1 := hi k
    have e2 := hi' k
    rw [hw, Matrix.mulVec_sub, Pi.sub_apply, Pi.zero_apply, ← e1, ← e2, sub_self]
  have h1 := hpos w hBw
  rw [hSw, dotProduct_zero] at h1
  have h3 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
  have h5 : w ⬝ᵥ w ≤ 0 := by
    by_contra hne
    have := mul_pos hc (not_le.1 hne)
    linarith
  have h4 : w = 0 := dotProduct_self_eq_zero.1 (le_antisymm h5 h3)
  funext k
  have h6 := congrFun h4 k
  rw [hw] at h6
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h6
  exact_mod_cast h6

theorem limit_seq : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ) (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (c : ℝ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ), 0 < c → Tendsto σs atTop (𝓝 σ) → Tendsto (fun m => (t m).im) atTop atTop → (∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ))) → (∀ m, ((τs m).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v)) → Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y) → ∃ u v : Fin g → ℤ, Bs *ᵥ v = 0 ∧ y = (fun k => (u k : ℂ)) + σ *ᵥ (fun k => (v k : ℂ)) ∧ ∀ᶠ m in atTop, us m = u ∧ vs m = v := by
  intro g Bs σ σs τs t c us vs y hc hσ ht hτ hpsd hposσ hy
  have huniq : ∀ w w' : Fin g → ℤ, (∃ᶠ m in atTop, vs m = w) → (∃ᶠ m in atTop, vs m = w') →
      w = w' := by
    intro w w' hw hw'
    obtain ⟨hk, hi⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w hw
    obtain ⟨hk', hi'⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w' hw'
    exact unique_value Bs σ c hc y hposσ w w' hk hk' hi hi'
  have hS : Tendsto (fun m => ∑ k, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ)) :
      Fin g → ℂ)) k).im ^ 2) atTop (𝓝 (∑ k, (y k).im ^ 2)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((Complex.continuous_im.tendsto _).comp (tendsto_pi_nhds.1 hy k)).pow 2
  have hbd : ∀ᶠ m in atTop,
      vs m ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2} := by
    filter_upwards [hS.eventually_lt_const (lt_add_one _)] with m hm
    have h1 := sq_mul_sum_sq_le ((τs m).map Complex.im) hc (hpsd m) (fun k => (vs m k : ℝ))
    simp only [im_period (τs m) (us m) (vs m)] at h1
    show ∑ k, (vs m k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2
    rw [le_div_iff₀ (pow_pos hc 2)]
    linarith
  have hfin := finite_sum_sq_le (g := g) ((∑ k, (y k).im ^ 2 + 1) / c ^ 2)
  have hall : ∀ᶠ m in atTop, ∀ w ∈ {w ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤
      (∑ k, (y k).im ^ 2 + 1) / c ^ 2} | ¬ ∃ᶠ n in atTop, vs n = w}, vs m ≠ w := by
    rw [Filter.eventually_all_finite (hfin.subset (Set.sep_subset _ _))]
    intro w hw
    exact Filter.not_frequently.1 hw.2
  have hev : ∀ᶠ m in atTop, ∃ᶠ n in atTop, vs n = vs m := by
    filter_upwards [hbd, hall] with m hm1 hm2
    by_contra hne
    exact hm2 (vs m) ⟨hm1, hne⟩ rfl
  obtain ⟨m0, hm0⟩ := hev.exists
  have hv_ev : ∀ᶠ m in atTop, vs m = vs m0 := by
    filter_upwards [hev] with m hm
    exact huniq _ _ hm hm0
  obtain ⟨hker, -⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy (vs m0) hv_ev.frequently
  have hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop
      (𝓝 ((σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) := by
    intro k
    have hc' : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (vs m0 k : ℂ))) k) :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    exact (hc'.tendsto σ).comp hσ
  have hu : ∀ k, Tendsto (fun m => (us m k : ℂ)) atTop
      (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) := by
    intro k
    have h1 : Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k
        - (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop
        (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) :=
      (tendsto_pi_nhds.1 hy k).sub (hσk k)
    refine h1.congr' ?_
    filter_upwards [hv_ev] with m hm
    rw [Pi.add_apply, hm, hτ m, mulVec_expand, hker]
    simp
  choose u hu1 hu2 using fun k => int_seq_const (fun m => us m k) _ (hu k)
  refine ⟨u, vs m0, hker, ?_, ?_⟩
  · funext k
    simp only [Pi.add_apply]
    rw [← hu1 k]
    ring
  · have hall2 : ∀ᶠ m in atTop, ∀ k, us m k = u k := Filter.eventually_all.2 hu2
    filter_upwards [hall2, hv_ev] with m h1 h2
    exact ⟨funext h1, h2⟩

end GlobalTheory.CompanionTheory.PeriodLimitSeq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompatStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_map_localization_compat : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (A₀ : Subalgebra ℤ Ω₀)
    (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁), (∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) → φ.Smooth →
    ∀ h : Ω₀, h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀) → h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
      S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)) →
      T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω)) →
      ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | exact GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SubspaceContainsUnitStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subspace_contains_unit : ∀ (k : Type) [Field k] [IsAlgClosed k] (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R]
    (U : Submodule k R), (∀ x : R →ₐ[k] k, ∃ t ∈ U, x t ≠ 0) → ∃ w ∈ U, IsUnit w := by
  first | exact @GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | exact GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point | (intros; apply GlobalTheory.CompanionTheory.FiniteAlgebraUnit.exists_isUnit_mem_of_forall_point <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionLiftIsClosedImmersion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem isClosedImmersion_torsion_lift {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsSeparated G.hom]
    (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (x : Spec (CommRingCat.of R) ⟶ X) (N : ℕ) (i : Γ.G.left ⟶ G.left)
    (h : Γ.IsTorsionAlong G x N i) :
    IsClosedImmersion (pullback.lift i Γ.G.hom h.isOver : Γ.G.left ⟶ pullback G.hom x) := by
  obtain ⟨i', hi'⟩ : ∃ i' : Γ.G.left ⟶ pullback G.hom x, i' = pullback.lift i Γ.G.hom h.isOver :=
    ⟨_, rfl⟩
  rw [← hi']
  have i'fst : i' ≫ pullback.fst G.hom x = i := by rw [hi']; exact pullback.lift_fst _ _ _
  have i'snd : i' ≫ pullback.snd G.hom x = Γ.G.hom := by rw [hi']; exact pullback.lift_snd _ _ _
  let PO : Over X := Over.mk (pullback.snd G.hom x ≫ x)
  let u : PO ⟶ G := Over.homMk (pullback.fst G.hom x) pullback.condition
  obtain ⟨f, hfdef⟩ : ∃ f : pullback G.hom x ⟶ G.left, f = (u ^ N).left := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : pullback G.hom x ⟶ G.left, g = (1 : PO ⟶ G).left := ⟨_, rfl⟩
  have hf : f ≫ G.hom = pullback.snd G.hom x ≫ x := by rw [hfdef]; exact Over.w (u ^ N)
  have hg : g ≫ G.hom = pullback.snd G.hom x ≫ x := by rw [hgdef]; exact Over.w (1 : PO ⟶ G)
  have hfg : f ≫ G.hom = g ≫ G.hom := hf.trans hg.symm

  let jq : pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) ⟶ pullback G.hom x :=
    pullback.snd _ _
  haveI : IsClosedImmersion jq := inferInstance
  have l1 : pullback.lift f g hfg ≫ pullback.fst G.hom G.hom = f := pullback.lift_fst _ _ _
  have l2 : pullback.lift f g hfg ≫ pullback.snd G.hom G.hom = g := pullback.lift_snd _ _ _
  have cond := pullback.condition (f := pullback.diagonal G.hom) (g := pullback.lift f g hfg)
  have jqf : jq ≫ f = pullback.fst _ _ := by
    have := congrArg (· ≫ pullback.fst G.hom G.hom) cond
    simpa [jq, l1] using this.symm
  have jqg : jq ≫ g = pullback.fst _ _ := by
    have := congrArg (· ≫ pullback.snd G.hom G.hom) cond
    simpa [jq, l2] using this.symm
  have jqeq : jq ≫ f = jq ≫ g := jqf.trans jqg.symm

  have key : i' ≫ f = i' ≫ g := by
    let g₀ : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
    have h0 : g₀ ^ N = 1 := (h.kernel Γ.G g₀).2 ⟨𝟙 _, by simp [g₀]⟩
    let ψ : Over.mk (Γ.G.hom ≫ x) ⟶ PO :=
      Over.homMk i' (by simp [PO, reassoc_of% i'snd])
    have h1 : ψ ≫ u = g₀ := by
      ext1
      simpa [ψ, u, g₀] using i'fst
    have h2 : ψ ≫ u ^ N = ψ ≫ 1 := by rw [MonObj.comp_pow, h1, h0, MonObj.comp_one]
    have h3 : i' ≫ (u ^ N).left = i' ≫ (1 : PO ⟶ G).left := congrArg (fun m => m.left) h2
    rw [hfdef, hgdef]
    exact h3
  let b : Γ.G.left ⟶ pullback (pullback.diagonal G.hom) (pullback.lift f g hfg) :=
    pullback.lift (i' ≫ f) i' (by
      apply pullback.hom_ext
      · simp [l1]
      · simp [l2, key])
  have bjq : b ≫ jq = i' := pullback.lift_snd _ _ _

  let Qs : Over (Spec (CommRingCat.of R)) := Over.mk (jq ≫ pullback.snd G.hom x)
  let g' : Over.mk (Qs.hom ≫ x) ⟶ G := Over.homMk (jq ≫ pullback.fst G.hom x)
    (by simp [Qs, pullback.condition])
  have hg' : g' ^ N = 1 := by
    let φ : Over.mk (Qs.hom ≫ x) ⟶ PO := Over.homMk jq (by simp [PO, Qs])
    have h1 : φ ≫ u = g' := by
      ext1
      simp [φ, u, g']
    have h2 : φ ≫ u ^ N = φ ≫ 1 := by
      apply Over.OverMorphism.ext
      change jq ≫ (u ^ N).left = jq ≫ (1 : PO ⟶ G).left
      rw [← hfdef, ← hgdef]
      exact jqeq
    rw [← h1, ← MonObj.comp_pow, h2, MonObj.comp_one]
  obtain ⟨y, hy⟩ := (h.kernel Qs g').1 hg'
  have hyl : y.left ≫ i = jq ≫ pullback.fst G.hom x := hy
  have hys : y.left ≫ Γ.G.hom = jq ≫ pullback.snd G.hom x := Over.w y
  have yi' : y.left ≫ i' = jq := by
    apply pullback.hom_ext
    · simp [i'fst, hyl]
    · simp [i'snd, hys]
  have ab : y.left ≫ b = 𝟙 _ := by
    rw [← cancel_mono jq]
    simp [bjq, yi']
  have ba : b ≫ y.left = 𝟙 _ := by
    have e : (Over.homMk (b ≫ y.left) (by
        change (b ≫ y.left) ≫ Γ.G.hom = Γ.G.hom
        rw [Category.assoc, hys, ← Category.assoc, bjq, i'snd]) : Γ.G ⟶ Γ.G) = 𝟙 Γ.G := by
      apply h.inj Γ.G
      change (b ≫ y.left) ≫ i = 𝟙 _ ≫ i
      rw [Category.assoc, hyl, ← Category.assoc, bjq, i'fst, Category.id_comp]
    exact congrArg (fun m => m.left) e
  haveI : IsIso b := ⟨y.left, ba, ab⟩
  rw [← bjq]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

private theorem eq_specMap_comp_of_apply_eq {X : Scheme.{0}} {B K Ω : Type} [CommRing B] [Field K]
    [Field Ω] (h : X ⟶ Spec (CommRingCat.of B)) (β : B →+* K)
    (hβ : ∀ x : K, ∃ r u : B, β u ≠ 0 ∧ x * β u = β r)
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ h = Spec.map (CommRingCat.ofHom β))
    (k : K →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ X)
    (hy : y ≫ h = Spec.map (CommRingCat.ofHom (k.comp β)))
    (a : Spec (CommRingCat.of Ω)) (b : Spec (CommRingCat.of K)) (hab : y a = s b) :
    y = Spec.map (CommRingCat.ofHom k) ≫ s := by
  have hpt : ∀ (L : Type) [Field L] (p q : Spec (CommRingCat.of L)), p = q := by
    intro L _ p q
    let p' : PrimeSpectrum L := p
    let q' : PrimeSpectrum L := q
    exact (PrimeSpectrum.ext ((Ideal.eq_bot_of_prime p'.asIdeal).trans
      (Ideal.eq_bot_of_prime q'.asIdeal).symm) : p' = q')
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top (s b))
  haveI := hW.isOpenImmersion_fromSpec
  have hrange : ∀ {Y : Scheme.{0}} (e : Y ⟶ X) (z : Y), (∀ z', z' = z) → e z ∈ W →
      Set.range e ⊆ Set.range hW.fromSpec := by
    intro Y e z hz he
    rintro _ ⟨z', rfl⟩
    rw [hW.range_fromSpec, hz z']
    exact he
  have hyW := hrange y a (fun z' => hpt Ω z' a) (by rw [hab]; exact hbW)
  have hsW := hrange s b (fun z' => hpt K z' b) hbW
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec y hyW)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec s hsW)
  obtain ⟨α, hα⟩ := Spec.map_surjective (hW.fromSpec ≫ h)
  have hσβ : α ≫ σ = CommRingCat.ofHom β := Spec.map_injective (by
    rw [Spec.map_comp, hσ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hs])
  have hψβ : α ≫ ψ = CommRingCat.ofHom (k.comp β) := Spec.map_injective (by
    rw [Spec.map_comp, hψ, hα, ← Category.assoc, IsOpenImmersion.lift_fac, hy])
  have hpts : (Spec.map ψ) a = (Spec.map σ) b := by
    apply (Scheme.Hom.isOpenEmbedding hW.fromSpec).injective
    rw [← Scheme.Hom.comp_apply (Spec.map ψ) hW.fromSpec a,
      ← Scheme.Hom.comp_apply (Spec.map σ) hW.fromSpec b, hψ, hσ, IsOpenImmersion.lift_fac,
      IsOpenImmersion.lift_fac, hab]
  have hker : ∀ x, σ.hom x = 0 → ψ.hom x = 0 := by
    intro x hx
    let a' : PrimeSpectrum Ω := a
    let b' : PrimeSpectrum K := b
    have ha : a'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have hb : b'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    have e := congrArg PrimeSpectrum.asIdeal hpts
    have hmem : x ∈ PrimeSpectrum.asIdeal ((Spec.map σ) b) := by
      rw [Spec.map_apply]
      change σ.hom x ∈ b'.asIdeal
      rw [hb, Ideal.mem_bot]
      exact hx
    rw [← e, Spec.map_apply] at hmem
    change ψ.hom x ∈ a'.asIdeal at hmem
    rwa [ha, Ideal.mem_bot] at hmem
  have hψσ : ψ = σ ≫ CommRingCat.ofHom k := by
    apply CommRingCat.hom_ext
    ext x
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    obtain ⟨r, u, hu, hxu⟩ := hβ (σ.hom x)
    have hσα : ∀ z, σ.hom (α.hom z) = β z := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hσβ, CommRingCat.hom_ofHom]
    have hψα : ∀ z, ψ.hom (α.hom z) = k (β z) := fun z => by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, hψβ, CommRingCat.hom_ofHom,
        RingHom.comp_apply]
    have h0 : ψ.hom (x * α.hom u - α.hom r) = 0 := hker _ (by
      rw [map_sub, map_mul, hσα, hσα, hxu, sub_self])
    rw [map_sub, map_mul, hψα, hψα, sub_eq_zero] at h0
    have hku : k (β u) ≠ 0 := (map_ne_zero k).mpr hu
    apply mul_right_cancel₀ hku
    rw [h0, ← map_mul, hxu]
  calc y = IsOpenImmersion.lift hW.fromSpec y hyW ≫ hW.fromSpec :=
        (IsOpenImmersion.lift_fac _ _ _).symm
    _ = Spec.map ψ ≫ hW.fromSpec := by rw [hψ]
    _ = Spec.map (CommRingCat.ofHom k) ≫ s := by
        rw [hψσ, Spec.map_comp, Category.assoc, hσ, IsOpenImmersion.lift_fac]

theorem QFGroup.exists_eq_comp_pt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
    (Ω : Type) [Field Ω] (k : FractionRing R →+* Ω) (y : Spec (CommRingCat.of Ω) ⟶ Γ.G.left),
    y ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (k.comp (algebraMap R (FractionRing R)))) →
    ∃ t, y = Spec.map (CommRingCat.ofHom k) ≫ (Γ.pt t).left := by
  intro R _ _ T _ Γ
  cases Γ
  rename_i pt _ pt_onto _
  dsimp only
  intro Ω _ k y hy
  let a0 : Spec (CommRingCat.of Ω) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum Ω)
  obtain ⟨t, x, hx⟩ := pt_onto (y a0) (by
    rw [← Scheme.Hom.comp_apply y _ a0, hy, Spec.map_apply]
    change Ideal.comap (k.comp (algebraMap R (FractionRing R))) (⊥ : Ideal Ω) = ⊥
    exact Ideal.comap_bot_of_injective _ (k.injective.comp (IsFractionRing.injective R (FractionRing R))))
  refine ⟨t, eq_specMap_comp_of_apply_eq _ (algebraMap R (FractionRing R)) ?_ (pt t).left
    (Over.w (pt t)) k y hy a0 x hx.symm⟩
  intro z
  obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) z
  exact ⟨n, d, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2, hnd⟩

end GlobalTheory.CompanionTheory.Ar.BT
end

