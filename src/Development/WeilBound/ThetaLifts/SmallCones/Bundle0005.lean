import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0004
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0003
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0001
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.InertDef

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeEx
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem int_prod {α β : Type} [TopologicalSpace α] [TopologicalSpace β] [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α]
    [BorelSpace β] [SecondCountableTopology α] [SecondCountableTopology β] (μ : Measure α) (ν : Measure β) [SFinite ν]
    {θ : α × β → ℂ} (hθ : Continuous θ) {w : α → ℂ} (hw : Continuous w) {a : α → ℝ} (ha : ∀ l, ‖w l‖ = a l)
    (hfin : ∫⁻ l, (∫⁻ g, ‖θ (l, g)‖ₑ ∂ν) * ENNReal.ofReal (a l) ∂μ < ⊤) : Integrable (fun x => θ x * w x.1) (μ.prod ν) := by
  have hc : Continuous fun x : α × β => θ x * w x.1 := hθ.mul (hw.comp continuous_fst)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hc.measurable.enorm.aemeasurable]
  convert hfin using 3 with l
  simp only [enorm_mul]
  rw [lintegral_mul_const' _ _ (by simp), ← ha, ofReal_norm_eq_enorm]

section Core

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure LineOK (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (M₀ : Model σ X₁ W₁) (om₀ : Rep σ X₁ W₁)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Ten F E n d) (ν : Chr F E) (z : ℕ)
    (S : Submodule ℂ (Fn F n d)) : Prop where
  le : ∀ Ψ ∈ S, Ψ ∈ schA F (Fin n × Fin d)
  stab : ∀ x, ∀ Ψ ∈ S, om x Ψ ∈ S
  sch : ∀ l, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (u l) Ψ) ∈ schA F (Fin n₁ × Fin d₁)
  th : ∀ g h, ∃ l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁), ∀ Φ ∈ schA F _, l Φ = theta om₀ Φ g h
  int : ∀ Ψ ∈ S, ∀ h₁, Integrable (fun x : (AE F E)ˣ × UA σ X₁.J =>
    theta om₀ (e (M.co.rho B.ψ (u x.1) Ψ)) x.2 h₁ * ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z)) (μ.prod (M₀.μ.restrict M₀.dom))
  lam : ∀ Ψ ∈ schA F (Fin n × Fin d), ∃ Ψ₁ ∈ schA F (Fin n₁ × Fin d₁), ∀ l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
    Integrable (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) μ ∧
    l₁ Ψ₁ = ∫ l, l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ

variable {B : Base F E} {M : Model σ X W} {om : Rep σ X W} {M₀ : Model σ X₁ W₁} {om₀ : Rep σ X₁ W₁}
  {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {μ : Measure (AE F E)ˣ} {u : (AE F E)ˣ → Ten F E n d} {ν : Chr F E} {z : ℕ}
  {S : Submodule ℂ (Fn F n d)}

theorem LineOK.theta_sum (h : LineOK B M om M₀ om₀ e μ u ν z S) {m : ℕ} (c : Fin m → ℂ) {Ψ : Fin m → Fn F n₁ d₁}
    (hΨ : ∀ i, Ψ i ∈ schA F (Fin n₁ × Fin d₁)) (g h₁) : theta om₀ (∑ i, c i • Ψ i) g h₁ = ∑ i, c i * theta om₀ (Ψ i) g h₁ := by
  obtain ⟨l, -, hl⟩ := h.th g h₁
  rw [← hl _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΨ i)), map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hl _ (hΨ i), smul_eq_mul]

theorem LineOK.val_sum (h : LineOK B M om M₀ om₀ e μ u ν z S) {m : ℕ} (c : Fin m → ℂ) {Ψ : Fin m → Fn F n d} (hΨ : ∀ i, Ψ i ∈ S)
    (l g h₁) : theta om₀ (e (M.co.rho B.ψ (u l) (∑ i, c i • Ψ i))) g h₁ =
      ∑ i, c i * theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ := by
  rw [rho_linear, map_sum]
  simp only [map_smul]
  exact h.theta_sum c (fun i => h.sch l _ (h.le _ (hΨ i))) g h₁

theorem LineOK.coneI_eq [SFinite μ] [SFinite M₀.μ] (h : LineOK B M om M₀ om₀ e μ u ν z S) {K : Subgroup (UA σ X.J)} (μK : Measure K)
    {Φ : Fn F n d} {m : ℕ} {Ψ : Fin m → Fn F n d} {c : Fin m → K → ℂ} (hΨ : ∀ i, Ψ i ∈ S) (hc : ∀ i, Integrable (c i) μK)
    (hd : ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i) (h₁ : UA σ W₁.J) :
    coneI B M om M₀ om₀ e K μK μ u ν z Φ h₁ = M₀.I om₀ (cone B M om e K μK μ u ν z Φ) h₁ := by
  choose Λ hΛ hΛ' using fun i => h.lam (Ψ i) (h.le _ (hΨ i))
  have h1 : cone B M om e K μK μ u ν z Φ = ∑ i, (∫ k, c i k ∂μK) • Λ i := by
    funext y
    have e1 : ∀ k : K, ∫ l, e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ =
        ∑ i, c i k * Λ i y := fun k => by
      have e2 := fun i => hΛ' i _ (ev_adm y)
      simp only [LinearMap.proj_apply] at e2
      simp only [hd, rho_linear, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [integral_finset_sum _ fun i _ => by simpa only [mul_assoc] using (e2 i).1.const_mul (c i k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(e2 i).2, ← integral_const_mul]
      simp only [mul_assoc]
    simp only [cone, e1, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finset_sum _ fun i _ => (hc i).mul_const _]
    simp only [integral_mul_const]
  have h2 : ∀ i g, theta om₀ (Λ i) g h₁ =
      ∫ l, theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ∂μ := fun i g => by
    obtain ⟨l, hl, hl'⟩ := h.th g h₁
    rw [← hl' _ (hΛ i), (hΛ' i l hl).2]
    simp only [hl' _ (h.sch _ _ (h.le _ (hΨ i))), mul_assoc]
  have h3 : ∀ i, IntegrableOn (fun g => theta om₀ (Λ i) g h₁) M₀.dom M₀.μ := fun i => by
    simp only [h2]
    exact (h.int _ (hΨ i) h₁).integral_prod_right
  set T : Fin m → ℂ := fun i => M₀.I om₀ (Λ i) h₁ with hT
  have h4 : ∀ i, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) ∂μ = T i := fun i => by
    simp only [hT, Model.I, h2]
    rw [← integral_integral_swap (h.int _ (hΨ i) h₁)]
    simp only [integral_mul_const]
  have h5 : ∀ i, Integrable (fun l => M₀.I om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) h₁ * ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) μ :=
    fun i => by
      have := (h.int _ (hΨ i) h₁).integral_prod_left
      simpa only [integral_mul_const, Model.I] using this
  have h6 : ∀ k : K, ∫ l, M₀.I om₀ (e (M.co.rho B.ψ (u l) (om (k.1, 1) Φ))) h₁ * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ =
      ∑ i, c i k * T i := fun k => by
    rw [← Finset.sum_congr rfl fun i _ => congrArg (c i k * ·) (h4 i)]
    simp only [← integral_const_mul]
    rw [← integral_finset_sum _ fun i _ => (h5 i).const_mul _]
    refine integral_congr_ae ?_
    have : ∀ᵐ l ∂μ, ∀ i, Integrable (fun g => theta om₀ (e (M.co.rho B.ψ (u l) (Ψ i))) g h₁ *
        ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z)) (M₀.μ.restrict M₀.dom) :=
      ae_all_iff.2 fun i => (h.int _ (hΨ i) h₁).prod_right_ae
    filter_upwards [this] with l hl
    simp only [Model.I, hd, h.val_sum _ hΨ, mul_assoc, ← integral_mul_const, ← integral_const_mul, Finset.sum_mul]
    rw [integral_finset_sum _ fun i _ => (hl i).const_mul _]
  rw [h1]
  simp only [coneI, h6]
  rw [integral_finset_sum _ fun i _ => (hc i).mul_const _]
  simp only [integral_mul_const, Model.I, h.theta_sum _ hΛ]
  rw [integral_finset_sum _ fun i _ => (h3 i).const_mul _]
  simp only [integral_const_mul, hT, Model.I]

end Core

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.GenAnisoOf
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}

theorem dom_change (hG : GrpTop) (hE : EpsOf) (hB : B.IsGood σ) {r s : ℕ} (hX : X.IsHerm σ B r s)
    {m m' : Measure (UA σ X.J)} {D D' : Set (UA σ X.J)} (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure)
    (hd : IsFundamentalDomain (ratU σ X.J) D m) (hd' : IsFundamentalDomain (ratU σ X.J) D' m') :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ φ : UA σ X.J → ℂ, (∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g) →
      ∫ g in D, φ g ∂m = c * ∫ g in D', φ g ∂m' := by
  obtain ⟨b1, b2, b3, b4, -⟩ := hG F E σ hB.cm n X.J (hE F E σ B hB n X r s (Or.inl hX)).1
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hc : m = Measure.haarScalarFactor m m' • m' := Measure.isMulLeftInvariant_eq_smul m m'
  have hpos : 0 < Measure.haarScalarFactor m m' := Measure.haarScalarFactor_pos_of_isHaarMeasure m m'
  have hac : m ≪ m' := by
    rw [hc]; exact Measure.smul_absolutelyContinuous
  have hd'' : IsFundamentalDomain (ratU σ X.J) D' m := hd'.mono hac
  refine ⟨((Measure.haarScalarFactor m m' : NNReal) : ℂ), ?_, fun φ hφ => ?_⟩
  · exact_mod_cast hpos.ne'
  · have h1 : ∫ g in D, φ g ∂m = ∫ g in D', φ g ∂m := hd.setIntegral_eq hd'' fun γ g => hφ γ γ.2 g
    rw [h1]
    conv_lhs => rw [hc]
    rw [Measure.restrict_smul, integral_smul_nnreal_measure]
    simp [NNReal.smul_def]

theorem isLevi_one : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 1 :=
  ⟨by rw [mat_one', Matrix.one_mulVec, Units.val_one, one_smul],
    by rw [mat_one', Matrix.one_mulVec, inv_one, Units.val_one, map_one, one_smul],
    by rw [mat_one', mat_one', Matrix.one_mul, Matrix.mul_one]⟩

theorem weil_bound (hW : WeilConv) {M : Model σ X W} {χX χW om r s r' s'} (hp : IsPair B M χX χW om r s r' s')
    (hr : d + 2 * min r s < 2 * n ∨ min r s = 0) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ (C : ℝ) (k : ℕ), ∀ h, ∫⁻ g in M.dom, ‖theta om Φ g h‖ₑ ∂M.μ ≤ ENNReal.ofReal (C * (ht h : ℝ) ^ k) := by
  obtain ⟨h1, C, k, h2⟩ := (hW F E σ B n d X W M χX χW om r s r' s' hp hr).1 Φ hΦ
  refine ⟨C, k, fun h => ?_⟩
  rw [← ofReal_integral_norm_eq_lintegral_enorm (h1 h)]
  exact ENNReal.ofReal_le_ofReal (h2 h)

theorem zero_term (hM : MixW) (hT : ThetaBasic) {M : Model σ X W} {M₁ : Model σ X W₁} {χX χW om om₁ r s r' s' r₁ s₁ i₀ i₁}
    (hp : IsPair B M χX χW om r s r' s') (hp₁ : IsPair B M₁ χX χW om₁ r s r₁ s₁) (hH : H'.IsAdapted σ B W W₁ i₀ i₁)
    {e} (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) {c : ℂ} (hc : ∀ φ : UA σ X.J → ℂ, (∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g) →
      ∫ g in M.dom, φ g ∂M.μ = c * ∫ g in M₁.dom, φ g ∂M₁.μ) (C₀ : ℂ) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    HasLaw W₁ H' χX ((n : ℝ) / 2) (fun h => ∫ g in M.dom, C₀ * thetaSum F (e (om (g, h) Φ)) ∂M.μ) ∧
      ∀ h₁ p, IsLevi H' 1 h₁ p → ∀ h, ∫ g in M.dom, C₀ * thetaSum F (e (om (g, p * h) Φ)) ∂M.μ =
        C₀ * c * M₁.I om₁ (e (om (1, h) Φ)) h₁ := by
  have key : ∀ g t h₁ p, IsLevi H' t h₁ p → ∀ h, thetaSum F (e (om (g, p * h) Φ)) =
      (χX t : ℂ) * (((absE F E t : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * theta om₁ (e (om (1, h) Φ)) g h₁ := fun g t h₁ p hl h => by
    have := hM F E σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hH hp₁ e he g t h₁ p hl 1 (one_mem _) _
      (pair_pres hp (1, h) hΦ)
    rw [om_mul, Prod.mk_mul_mk, mul_one, one_mul] at this
    rw [this, thetaSum_smul', theta]
  have key1 : ∀ g h₁ p, IsLevi H' 1 h₁ p → ∀ h, thetaSum F (e (om (g, p * h) Φ)) = theta om₁ (e (om (1, h) Φ)) g h₁ :=
    fun g h₁ p hl h => by rw [key g 1 h₁ p hl h]; simp
  refine ⟨fun t m hl h => ?_, fun h₁ p hl h => ?_⟩
  · simp only [key _ t 1 m hl h, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    have := key1 g 1 1 isLevi_one h
    rw [one_mul] at this
    simp only [this]
    ring
  · obtain ⟨-, t2, -⟩ := (hT F E σ B n d₁ X W₁ M₁ χX χW om₁ r s r₁ s₁ hp₁).1 _ (he.maps _ (pair_pres hp (1, h) hΦ))
    simp only [key1 _ h₁ p hl h]
    rw [integral_const_mul, hc _ fun γ hγ g => by simpa using t2 γ hγ 1 (one_mem _) g h₁, mul_assoc, Model.I]

theorem genAniso_of (hK : CTKernel) (hF : CTFub) (hM : MixW) (hW : WeilConv) (hT : ThetaBasic) (hWi : Witt) (hG : GrpTop)
    (hE : EpsOf) : GenAniso := by
  intro F E _ _ _ _ _ σ B n d d₁ X W W₁ H' i₀ i₁ r s r' s' r₁ s₁ X' M M₁ hX hrs hH e he
  subst hX
  by_cases h0 : ∃ χX χW om om₁, IsPair B M χX χW om r s r' s' ∧ IsPair B M₁ χX χW om₁ r s r₁ s₁
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₁ h1 h2 => absurd ⟨χX, χW, om, om₁, h1, h2⟩ h0⟩
  obtain ⟨_, _, _, _, q, q₁⟩ := h0
  obtain ⟨C₀, hC₀, h1, -⟩ := hK F E σ B n d d₁ X' W W₁ M M₁ H' i₀ i₁ hH q₁.good e he
  obtain ⟨c, hc0, hc⟩ := dom_change hG hE q.base q.herm q.good.haar q₁.good.haar q.good.dom q₁.good.dom
  refine ⟨C₀ * c, mul_ne_zero hC₀ hc0, fun χX χW om om₁ hp hp₁ Φ hΦ => ?_⟩
  obtain ⟨z1, z2⟩ := zero_term hM hT hp hp₁ hH he hc C₀ hΦ
  exact ⟨_, (hF F E σ B n d X' W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ (weil_bound hW hp (Or.inr hrs) hΦ) _
    (h1 ((hWi F E σ B n X' r s hp.base hp.herm).1 hrs) χX χW om r s r' s' hp Φ hΦ)).2, z1, z2⟩

theorem genBig_of (hK : CTKernel) (hF : CTFub) (hA : ConeA) (hM : MixW) (hW : WeilConv) (hT : ThetaBasic) (hWi : Witt)
    (hG : GrpTop) (hE : EpsOf) : GenBig := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' M₁ e₀ e g₁ g₀ he₀ he z hz K μK μ hI hμK hμ
  by_cases h0 : ∃ χX χW om, IsPair B M χX χW om (r + 1) (s + 1) (r' + 1) (s' + 1)
  swap
  · exact ⟨1, 1, one_ne_zero, one_ne_zero, fun χX χW om _ _ h1 => absurd ⟨χX, χW, om, h1⟩ h0⟩
  obtain ⟨_, _, _, q⟩ := h0
  obtain ⟨C₀, hC₀, -, h1⟩ := hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' g₁ e₀ he₀
  obtain ⟨C₁, hC₁, h2⟩ := h1 n₁ X₁ H j₀ j₁ M₀ hH g₀ e he
  obtain ⟨κ, hκ, h3⟩ := hA F E σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' e he z hz K μK μ hI hμK hμ
  obtain ⟨c, hc0, hc⟩ := dom_change hG hE q.base q.herm q.good.haar g₁.haar q.good.dom g₁.dom
  obtain ⟨γ, hγ⟩ := (hWi F E σ B n X _ _ q.base q.herm).2 n₁ H (adapted_x_ne hH) hH.xx
  refine ⟨C₀ * c, C₁ * κ, mul_ne_zero hC₀ hc0, mul_ne_zero hC₁ hκ, fun χX χW om om₁ om₀ hp hp₁ hp₀ Φ hΦ hfin => ?_⟩
  obtain ⟨z1, z2⟩ := zero_term hM hT hp hp₁ hH' he₀ hc C₀ hΦ
  obtain ⟨a1, a2, a3⟩ := h3 χX χW om om₀ hp hp₀ Φ hΦ hfin
  obtain ⟨f1, f2⟩ := hF F E σ B n d X W M χX χW om _ _ _ _ hp d₁ W₁ H' i₀ i₁ hH' Φ hΦ
    (weil_bound hW hp (Or.inl (by omega)) hΦ) _ fun g => (h2 γ hγ χX χW om _ _ _ _ hp Φ hΦ g).2
  refine ⟨_, fun h => C₁ * κ * coneI B M om M₀ om₀ e K μK μ (shiftA H H') χW⁻¹ z (om (1, h) Φ) 1, ?_, z1,
    fun t m hl h => ?_, fun h₁ p hl h => ⟨?_, z2 h₁ p hl h⟩⟩
  · convert f2 using 1
    funext h
    obtain ⟨-, b2, b3⟩ := a1 γ hγ h
    have b4 := b2.const_mul C₁
    have b5 := (f1 h).sub b4
    rw [Pi.add_apply, mul_assoc, ← b3, ← integral_const_mul, ← integral_add _ b4]
    · rfl
    · refine b5.congr (Eventually.of_forall fun g => ?_)
      exact add_sub_cancel_right _ _
  · simp only [a2 t 1 m hl h]
    ring
  · simp only [a2 1 h₁ p hl h, a3]
    simp

end PositivityTheory.ThKCT
end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.IwaGlob
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Euler
open PositivityTheory.ThKG.Tow.Levi (hf hf_apply hf_mulVec iso_of_hf exists_move piInf_incl piInf_cA iso_map_piInf exists_lift exists_inf ad_ext)
open PositivityTheory.ThK (latW KAt)

namespace IwaG

theorem exists_loc {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (hθ : IsCartan M θ)
    {v : Fin n → ℂ} (hv0 : v ≠ 0) (hvv : hf M v v = 0) {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g * g' = 1)
    (h2 : gᵀ * M * g.map star = M) :
    ∃ (p p' : Matrix (Fin n) (Fin n) ℂ) (t : ℂ), t ≠ 0 ∧ p * p' = 1 ∧ pᵀ * M * p.map star = M ∧ p *ᵥ v = t • v ∧
      Commute (p' * g) θ := by
  have hd := cartan_det hθ
  obtain ⟨c1, c2, c3⟩ := hθ
  have hgv : g *ᵥ (g' *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  obtain ⟨κ, t, ht, k1, k2, k3⟩ := exists_move hM c1 c2 c3 hv0 (v' := g' *ᵥ v)
    (fun h => hv0 (by rw [← hgv, h, Matrix.mulVec_zero])) hvv (by rw [← h2, ← hf_mulVec, hgv, hvv])
  have hκ : IsUnit κ.det := by
    have e := congrArg Matrix.det k1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at e
    refine IsUnit.mk0 _ fun h => hd ?_
    rw [h, zero_mul, zero_mul] at e
    exact e.symm
  have h1' := mul_eq_one_comm.1 h1
  refine ⟨g * κ, κ⁻¹ * g', t, ht, ?_, iso_of_hf fun x y => ?_, ?_, ?_⟩
  · rw [mul_assoc, ← mul_assoc κ, Matrix.mul_nonsing_inv _ hκ, one_mul, h1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hf_mulVec, h2, hf_mulVec, k1]
  · rw [← Matrix.mulVec_mulVec, k3, Matrix.mulVec_smul, hgv]
  · rw [mul_assoc, h1', mul_one]
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det κ).2 hκ
    rw [← Matrix.coe_units_inv]
    exact k2.units_inv_left

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {n r s : ℕ} {X : Spc F E n} {x : Fin n → E} {v : Pl F}

theorem compFin_smul (u : Pl F) (a : AF F) (z : AE F E) : compFin F E u (a • z) = evFin F u a • compFin F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F u) a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem compInf_smul (u : InfinitePlace F) (a : AF F) (z : AE F E) : compInf F E u (a • z) = evInf F u a • compInf F E u z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F u) a b)
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def LocIwa (σ : E →ₐ[F] E) (X : Spc F E n) (x : Fin n → E) : Prop :=
  ∀ (v : Pl F) (g : UA σ X.J), g ∈ UAt σ X (evFin F v) → ∃ p ∈ UAt σ X (evFin F v), ∃ k ∈ KAt σ X v, ∃ t : (AE F E)ˣ,
    mat p *ᵥ incV F x = t.1 • incV F x ∧ g = p * k

theorem map_one' {S : Type} [CommRing S] (f : AE F E →+* S) : (1 : Matrix (Fin n) (Fin n) (AE F E)).map f = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem exists_arch (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hx : x ≠ 0) (h0 : form σ X.J x x = 0) (g : UA σ X.J) :
    ∃ (p : UA σ X.J) (t : (AE F E)ˣ), mat p *ᵥ incV F x = t.1 • incV F x ∧
      ∀ w, Commute ((mat (p⁻¹ * g)).map (piInf (B.emb w))) (X.θ w) := by
  have hσ := hB.cm
  choose p p' t ht h1 h2 h3 h4 using fun w => exists_loc (M := X.J.map (B.emb w).1)
    (fun i j => by rw [Matrix.map_apply, ← hσ.2.2.2, hX.herm, Matrix.map_apply]) (hX.cartan w)
    (v := fun i => (B.emb w).1 (x i))
    (fun h => hx (funext fun i => (B.emb w).1.injective ((congrFun h i).trans (map_zero _).symm)))
    (by
      have e := congrArg (B.emb w).1 h0
      simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ.2.2.2, map_zero] at e
      exact e)
    (g := (mat g).map (piInf (B.emb w))) (g' := (mat g⁻¹).map (piInf (B.emb w)))
    (by rw [← Matrix.map_mul, show mat g * mat g⁻¹ = 1 from g.1.mul_inv, map_one'])
    (by
      rw [← iso_map_piInf (fun τ z => piInf_cA hσ τ z), show (mat g)ᵀ * incM F X.J * (mat g).map (cA σ) = incM F X.J from g.2]
      exact Matrix.ext fun i j => piInf_incl _ _)
  obtain ⟨q, q1, q2⟩ := exists_lift hσ B.emb X.J p p' h1 h2
  obtain ⟨a, a1, a2⟩ := exists_inf hσ B.emb t
  obtain ⟨b, b1, b2⟩ := exists_inf hσ B.emb fun w => (t w)⁻¹
  have hab : a * b = 1 := ad_ext hσ B.emb (fun w => by rw [map_mul, a1, b1, mul_inv_cancel₀ (ht w), map_one])
    fun v => by rw [map_mul, a2, b2, mul_one, map_one]
  refine ⟨q, ⟨a, b, hab, (mul_comm _ _).trans hab⟩, funext fun i => ad_ext hσ B.emb (fun w => ?_) fun v => ?_, fun w => ?_⟩
  · have e : piInf (B.emb w) ∘ incV F x = fun i => (B.emb w).1 (x i) := funext fun i => piInf_incl _ _
    rw [RingHom.map_mulVec, q1, e, h3, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, a1]
    exact congrArg _ (congrFun e i).symm
  · rw [RingHom.map_mulVec, q2, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, a2, one_mul]
    rfl
  · have e : (mat q⁻¹).map (piInf (B.emb w)) = p' w := by
      have e1 : (mat q⁻¹).map (piInf (B.emb w)) * p w = 1 := by
        rw [← q1, ← Matrix.map_mul, show mat q⁻¹ * mat q = 1 from q.1.inv_mul, map_one']
      exact left_inv_eq_right_inv e1 (h1 w)
    rw [mat_mul, Matrix.map_mul, e]
    exact h4 w

theorem latW_le : latW X v ≤ latHat X := AddSubgroup.closure_mono (by
  rintro _ ⟨a, ha, hi, y, hy, rfl⟩
  have e : idem v * a = a := at_iff.1 ha
  have := idem_mem hi
  rw [e] at this
  exact ⟨a, this.1, this.2, y, hy, rfl⟩)

theorem idem_latW {z : Fin n → AE F E} (hz : z ∈ latHat X) : idem v • z ∈ latW X v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, hi, y, hy, rfl⟩ := hz
    exact AddSubgroup.subset_closure ⟨idem v * a, at_iff.2 (by rw [smul_eq_mul, ← mul_assoc, idem_sq]), by
      rw [map_mul, ev_self, one_mul]; exact hi v, y, hy, by rw [smul_smul]; rfl⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact neg_mem ha

theorem int_of_KAt {k : UA σ X.J} (hk : k ∈ KAt σ X v) : IntAt v k := fun z hz h =>
  have h1 : z ∈ latW X v := at_iff.1 h ▸ idem_latW hz
  ⟨latW_le (hk.2 z h1).1, latW_le (hk.2 z h1).2⟩

variable (F) in

def eInf : AF F := ((1, 0) : Ainf F × Af F)

theorem eInf_smul {z : Fin n → AE F E} (hz : z ∈ latHat X) : eInf F • z = 0 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, -, y, -, rfl⟩ := hz
    have h1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
    have : eInf F * a = 0 := Prod.ext ((one_mul a.1).trans h1) (zero_mul a.2)
    rw [smul_smul, this, zero_smul]
  | zero => rw [smul_zero]
  | add a b _ _ ha hb => rw [smul_add, ha, hb, add_zero]
  | neg a _ ha => rw [smul_neg, ha, neg_zero]

theorem glue (hL : X.L.IsLattice E) {z : Fin n → AE F E} (h0 : eInf F • z = 0) (h : ∀ v : Pl F, idem v • z ∈ latHat X) :
    z ∈ latHat X := by
  obtain ⟨m, y, -, hy⟩ := lat_gen (Y := X) hL
  choose a a1 a2 using fun v => (hy _).1 (h v)
  let b : Fin m → AF F := fun i => ((0, ⟨fun v => evFin F v (a v i), Eventually.of_forall fun v => (a1 v i).2 v⟩) : Ainf F × Af F)
  have hb : ∀ v i, evFin F v (b i) = evFin F v (a v i) := fun _ _ => rfl
  refine (hy _).2 ⟨b, fun i => ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => (a1 v i).2 v⟩,
    funext fun j => Supp.adTens_ext (fun w => ?_) fun v => ?_⟩
  · have e := congrArg (compInf F E w) (congrFun h0 j)
    rw [Pi.smul_apply, compInf_smul, show evInf F w (eInf F) = 1 from rfl, one_smul, Pi.zero_apply, map_zero] at e
    rw [e, Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [Pi.smul_apply, compInf_smul, show evInf F w (b i) = 0 from rfl, zero_smul]
  · have e := congrArg (compFin F E v) (congrFun (a2 v) j)
    rw [Pi.smul_apply, compFin_smul, ev_self, one_smul] at e
    rw [← e, Finset.sum_apply, Finset.sum_apply, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, Pi.smul_apply, compFin_smul, compFin_smul, hb]

theorem stab_of_int (hL : X.L.IsLattice E) {A : Matrix (Fin n) (Fin n) (AE F E)}
    (h : ∀ v, ∀ z ∈ latHat X, At (evFin F v) z → A *ᵥ z ∈ latHat X) {z : Fin n → AE F E} (hz : z ∈ latHat X) :
    A *ᵥ z ∈ latHat X :=
  glue hL (by rw [← Matrix.mulVec_smul, eInf_smul hz, Matrix.mulVec_zero]) fun v => by
    rw [← Matrix.mulVec_smul]
    exact h v _ (latW_le (idem_latW hz)) (at_iff.2 (by rw [smul_smul, idem_sq]))

theorem piInf_loc {p : UA σ X.J} (hp : p ∈ UAt σ X (evFin F v)) {w : InfinitePlace F} (τ : EmbOver E w) :
    (mat p).map (piInf τ) = 1 := by
  rw [← map_one' (piInf τ)]
  ext i j
  have e : idem v • (mat p - 1) i j = (mat p - 1) i j := congrFun (congrFun (at_iff.1 hp) i) j
  rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, ← Matrix.sub_apply, ← e, piInf,
    RingHom.comp_apply, compInf_smul, show evInf F w (idem v) = 0 from rfl, zero_smul, map_zero]

theorem exists_fin (B : Base F E) (hl : LocIwa σ X x) (S : Finset (Pl F)) :
    ∀ g : UA σ X.J, (∀ v ∉ S, IntAt v g) → ∃ (p : UA σ X.J) (t : (AE F E)ˣ), mat p *ᵥ incV F x = t.1 • incV F x ∧
      (∀ w, (mat p⁻¹).map (piInf (B.emb w)) = 1) ∧ ∀ v, IntAt v (p⁻¹ * g) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact fun g h => ⟨1, 1, by simp [mat_one], fun w => map_one' _, fun v => by simpa using h v (by simp)⟩
  | insert v S hv ih =>
    intro g h
    have hg : prj v g ∈ UAt σ X (evFin F v) := at_iff.2 (cut_eq.1 (congrArg mat (mem_loc.1 (prj_mem g))))
    obtain ⟨p, hp, k, hk, t, ht, e⟩ := hl v _ hg
    have hp' : p⁻¹ ∈ locGrp σ X v := inv_mem (Subgroup.subset_closure hp)
    obtain ⟨q, t', h1, h2, h3⟩ := ih (p⁻¹ * g) fun u hu => by
      by_cases c : u = v
      · subst c
        rw [← int_prj, map_mul, mem_loc.1 hp', e, inv_mul_cancel_left]
        exact int_of_KAt hk
      · exact (int_mul_ne c hp' g).2 (h u (by simp [c, hu]))
    refine ⟨p * q, t' * t, ?_, fun w => ?_, fun u => by rw [mul_inv_rev, mul_assoc]; exact h3 u⟩
    · rw [mat_mul, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, ht, smul_smul, Units.val_mul]
    · rw [mul_inv_rev, mat_mul, Matrix.map_mul, h2, piInf_loc (at_iff.2 (cut_eq.1 (congrArg mat (mem_loc.1 hp')))), mul_one]

theorem iwa_glob {n₁ : ℕ} {H : Plane E n n₁} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hx : H.x ≠ 0)
    (h0 : form σ X.J H.x H.x = 0) (hl : LocIwa σ X H.x) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) (g : UA σ X.J) :
    ∃ (p k : UA σ X.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k := by
  obtain ⟨q, t, h1, h2⟩ := exists_arch hB hX hx h0 g
  have hf : ∀ᶠ v in cofinite, IntAt v (q⁻¹ * g) := by
    filter_upwards [ae_mulVec hX.lat (mat (q⁻¹ * g)), ae_mulVec hX.lat (mat (q⁻¹ * g)⁻¹)] with v a b z hz h
    exact ⟨a z hz h, b z hz h⟩
  obtain ⟨p, t', e1, e2, e3⟩ := exists_fin B hl (Set.Finite.toFinset hf) (q⁻¹ * g) fun v hv =>
    not_not.1 fun c => hv ((Set.Finite.mem_toFinset hf).2 c)
  refine ⟨q * p, p⁻¹ * (q⁻¹ * g), t' * t, (hK _).2 ⟨fun w => ?_, fun z hz => ⟨?_, ?_⟩⟩, ?_, by group⟩
  · rw [mat_mul, Matrix.map_mul, e2, one_mul]
    exact h2 w
  · exact stab_of_int hX.lat (fun v z hz h => (e3 v z hz h).1) hz
  · exact stab_of_int hX.lat (fun v z hz h => (e3 v z hz h).2) hz
  · rw [mat_mul, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_smul, h1, smul_smul, Units.val_mul]

end IwaG

end PositivityTheory.ThKCT

end
end

