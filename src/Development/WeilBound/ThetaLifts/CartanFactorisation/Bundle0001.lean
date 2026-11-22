import Mathlib

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight
section
noncomputable section

namespace PositivityTheory.ThKF.L2

open MeasureTheory
open scoped ComplexConjugate Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

def Inv (Γ : Subgroup G) (F : G → ℂ) : Prop := ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x

theorem fd_right (h : IsFundamentalDomain Γ 𝓕 μ) (g : G) : IsFundamentalDomain Γ ((fun x => x * g) '' 𝓕) μ := by
  have := h.smul_of_comm (MulOpposite.op g)
  simpa [← Set.image_smul] using this

theorem emb (g : G) : MeasurableEmbedding fun x : G => x * g := (Homeomorph.mulRight g).measurableEmbedding

theorem integral_right {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : IsFundamentalDomain Γ 𝓕 μ) (F : G → E)
    (hF : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) (g : G) : ∫ x in 𝓕, F (x * g) ∂μ = ∫ x in 𝓕, F x ∂μ := by
  rw [← (measurePreserving_mul_right μ g).setIntegral_image_emb (emb g) F 𝓕]
  exact (fd_right h g).setIntegral_eq h fun γ x => hF γ γ.2 x

theorem integrableOn_right {E : Type} [NormedAddCommGroup E] (h : IsFundamentalDomain Γ 𝓕 μ) (F : G → E)
    (hF : ∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) (hi : IntegrableOn F 𝓕 μ) (g : G) : IntegrableOn (fun x => F (x * g)) 𝓕 μ := by
  have h1 : IntegrableOn F ((fun x => x * g) '' 𝓕) μ :=
    ((fd_right h g).integrableOn_iff h fun γ x => hF γ γ.2 x).2 hi
  exact ((measurePreserving_mul_right μ g).integrableOn_image (emb g)).1 h1

omit [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [Countable Γ] [IsTopologicalGroup G] [Group G] in
theorem integrableOn_mul {f g : G → ℂ} (hf : Continuous f) (hg : Continuous g)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (g2 : IntegrableOn (fun x => ‖g x‖ ^ 2) 𝓕 μ) :
    IntegrableOn (fun x => conj (f x) * g x) 𝓕 μ := by
  refine Integrable.mono' (f2.add g2) ((Complex.continuous_conj.comp hf).mul hg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Complex.norm_conj, Pi.add_apply]
  nlinarith [sq_nonneg (‖f x‖ - ‖g x‖), norm_nonneg (f x), norm_nonneg (g x)]

theorem form_right (h : IsFundamentalDomain Γ 𝓕 μ) {f g : G → ℂ} (hf : Inv Γ f) (hg : Inv Γ g) (a : G) :
    ∫ x in 𝓕, conj (f (x * a)) * g (x * a) ∂μ = ∫ x in 𝓕, conj (f x) * g x ∂μ :=
  integral_right h (fun x => conj (f x) * g x) (fun γ hγ x => by rw [hf γ hγ, hg γ hγ]) a

omit [μ.IsMulRightInvariant] in
theorem eq_zero (h : IsFundamentalDomain Γ 𝓕 μ) {f : G → ℂ} (hc : Continuous f) (hf : Inv Γ f)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (h0 : ∫ x in 𝓕, conj (f x) * f x ∂μ = 0) : f = 0 := by
  have e : ∫ x in 𝓕, conj (f x) * f x ∂μ = ((∫ x in 𝓕, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.conj_mul']
  rw [e, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg (fun x => by positivity) f2] at h0
  have hm : MeasurableSet {x | f x ≠ 0} := (isOpen_ne_fun hc continuous_const).measurableSet
  have h1 : μ ({x | f x ≠ 0} ∩ 𝓕) = 0 := by
    rw [← Measure.restrict_apply hm]
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 h0)
    simpa using hx
  have h2 : μ {x | f x ≠ 0} = 0 := h.measure_zero_of_invariant _ (fun γ => by
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    change f ((γ⁻¹ : Γ) * x) ≠ 0 ↔ f x ≠ 0
    rw [hf _ (γ⁻¹).2]) h1
  have h3 := (isOpen_ne_fun hc continuous_const).eq_empty_of_measure_zero h2
  funext x
  by_contra hx
  exact (h3 ▸ hx : x ∈ (∅ : Set G))

theorem integral_deriv [SFinite μ] (h : IsFundamentalDomain Γ 𝓕 μ) (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    {F F₁ : G → ℂ} (c₁ : Continuous F₁) (hF : Inv Γ F) (hF₁ : Inv Γ F₁) (iF : IntegrableOn F 𝓕 μ)
    (iF₁ : IntegrableOn F₁ 𝓕 μ) (hd : ∀ x, HasDerivAt (fun t : ℝ => F (x * γ (Multiplicative.ofAdd t))) (F₁ x) 0) :
    ∫ x in 𝓕, F₁ x ∂μ = 0 := by
  have cg : Continuous fun t : ℝ => γ (Multiplicative.ofAdd t) := hγ.comp continuous_ofAdd
  have hd' : ∀ x s, HasDerivAt (fun t : ℝ => F (x * γ (Multiplicative.ofAdd t))) (F₁ (x * γ (Multiplicative.ofAdd s))) s := by
    intro x s
    have h1 := hd (x * γ (Multiplicative.ofAdd s))
    have h2 : HasDerivAt (fun t : ℝ => t - s) 1 s := (hasDerivAt_id s).sub_const s
    have h3 := HasDerivAt.scomp s (by simpa using h1) h2
    simp only [one_smul] at h3
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    show F _ = F (x * γ (Multiplicative.ofAdd s) * γ (Multiplicative.ofAdd (t - s)))
    rw [mul_assoc, ← map_mul, ← ofAdd_add, add_sub_cancel]
  have ftc : ∀ x, ∫ s in (0 : ℝ)..1, F₁ (x * γ (Multiplicative.ofAdd s)) = F (x * γ (Multiplicative.ofAdd 1)) - F x := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd' x s)
      ((c₁.comp (continuous_const.mul cg)).intervalIntegrable _ _)]
    simp
  have cj : Continuous fun p : ℝ × G => F₁ (p.2 * γ (Multiplicative.ofAdd p.1)) :=
    c₁.comp (continuous_snd.mul (cg.comp continuous_fst))
  have ij : Integrable (Function.uncurry fun (s : ℝ) (x : G) => F₁ (x * γ (Multiplicative.ofAdd s)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (μ.restrict 𝓕)) := by
    refine (integrable_prod_iff cj.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall fun s =>
      integrableOn_right h F₁ hF₁ iF₁ (γ (Multiplicative.ofAdd s)), ?_⟩
    have : (fun s : ℝ => ∫ x in 𝓕, ‖F₁ (x * γ (Multiplicative.ofAdd s))‖ ∂μ) = fun _ => ∫ x in 𝓕, ‖F₁ x‖ ∂μ :=
      funext fun s => integral_right h (fun x => ‖F₁ x‖) (fun g hg x => by rw [hF₁ g hg]) _
    simp only
    rw [this]
    exact integrable_const _
  have sw := integral_integral_swap ij
  have l : ∫ s in Set.Ioc (0 : ℝ) 1, ∫ x in 𝓕, F₁ (x * γ (Multiplicative.ofAdd s)) ∂μ = ∫ x in 𝓕, F₁ x ∂μ := by
    simp [integral_right h F₁ hF₁]
  have r : ∫ x in 𝓕, (∫ s in Set.Ioc (0 : ℝ) 1, F₁ (x * γ (Multiplicative.ofAdd s))) ∂μ = 0 := by
    simp only [← intervalIntegral.integral_of_le zero_le_one, ftc]
    rw [integral_sub (integrableOn_right h F hF iF _) iF, integral_right h F hF, sub_self]
  rw [← l, sw, r]

theorem skew [SFinite μ] (h : IsFundamentalDomain Γ 𝓕 μ) (γ : Multiplicative ℝ →* G) (hγ : Continuous γ)
    {f f₁ g g₁ : G → ℂ} (cf : Continuous f) (cf₁ : Continuous f₁) (cg : Continuous g) (cg₁ : Continuous g₁)
    (hf : Inv Γ f) (hf₁ : Inv Γ f₁) (hg : Inv Γ g) (hg₁ : Inv Γ g₁)
    (f2 : IntegrableOn (fun x => ‖f x‖ ^ 2) 𝓕 μ) (f₁2 : IntegrableOn (fun x => ‖f₁ x‖ ^ 2) 𝓕 μ)
    (g2 : IntegrableOn (fun x => ‖g x‖ ^ 2) 𝓕 μ) (g₁2 : IntegrableOn (fun x => ‖g₁ x‖ ^ 2) 𝓕 μ)
    (df : ∀ x, HasDerivAt (fun t : ℝ => f (x * γ (Multiplicative.ofAdd t))) (f₁ x) 0)
    (dg : ∀ x, HasDerivAt (fun t : ℝ => g (x * γ (Multiplicative.ofAdd t))) (g₁ x) 0) :
    ∫ x in 𝓕, conj (f₁ x) * g x ∂μ + ∫ x in 𝓕, conj (f x) * g₁ x ∂μ = 0 := by
  have i1 := integrableOn_mul cf₁ cg f₁2 g2
  have i2 := integrableOn_mul cf cg₁ f2 g₁2
  rw [← integral_add i1 i2]
  refine integral_deriv h γ hγ (F := fun x => conj (f x) * g x)
    (((Complex.continuous_conj.comp cf₁).mul cg).add ((Complex.continuous_conj.comp cf).mul cg₁))
    (fun a ha x => by simp only [hf a ha, hg a ha]) (fun a ha x => by simp only [hf a ha, hg a ha, hf₁ a ha, hg₁ a ha])
    (integrableOn_mul cf cg f2 g2) (i1.add i2) fun x => ?_
  have h1 : HasDerivAt (fun t : ℝ => conj (f (x * γ (Multiplicative.ofAdd t)))) (conj (f₁ x)) 0 :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (df x)
  have := h1.fun_mul (dg x)
  simp only [ofAdd_zero, map_one, mul_one] at this
  exact this

end PositivityTheory.ThKF.L2

end
end

-- bundled from Development.WeilBound.ThetaLifts.CartanFactorisation.SpanOrbitStab
section
noncomputable section

namespace PositivityTheory.ThKF.Abs

open scoped InnerProductSpace

variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem orth_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (z : U) (hz : z ∈ Yᗮ) : κ k z ∈ Yᗮ := by
  rw [Submodule.mem_orthogonal] at hz ⊢
  intro y hy
  have e : y = κ k (κ k⁻¹ y) := by rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [e, hi]
  exact hz _ (hY _ _ hy)

theorem proj_equiv {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (Y : Submodule ℂ U) [FiniteDimensional ℂ Y] (hY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y) (k : K) (x : U) :
    Y.starProjection (κ k x) = κ k (Y.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (hY _ _ (Y.starProjection_apply_mem x))
  rw [← map_sub]
  exact orth_stab κ hi Y hY k _ (Y.sub_starProjection_mem_orthogonal x)

theorem span_orbit_stab {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) (k : K) :
    ∀ y ∈ Submodule.span ℂ (Set.range fun k => κ k x), κ k y ∈ Submodule.span ℂ (Set.range fun k => κ k x) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y h => obtain ⟨k', rfl⟩ := h; exact Submodule.subset_span ⟨k * k', by simp⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

def orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : Submodule ℂ U := Submodule.span ℂ (Set.range fun k => κ k x)

theorem mem_orb {K : Type} [Group K] (κ : K →* Module.End ℂ U) (x : U) : x ∈ orb κ x := Submodule.subset_span ⟨1, by simp⟩

def homs {K : Type} [Group K] (κ : K →* Module.End ℂ U) (W : Submodule ℂ U) : Submodule ℂ (U →ₗ[ℂ] U) where
  carrier := {L | (∀ x, L x ∈ W) ∧ ∀ k x, L (κ k x) = κ k (L x)}
  add_mem' := fun {a b} ha hb => ⟨fun x => add_mem (ha.1 x) (hb.1 x), fun k x => by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨fun x => by simp, fun k x => by simp⟩
  smul_mem' := fun c a ha => ⟨fun x => W.smul_mem c (ha.1 x), fun k x => by simp [ha.2]⟩

def ck (H : Submodule ℂ (U →ₗ[ℂ] U)) : Submodule ℂ U where
  carrier := {z | ∀ L ∈ H, L z = 0}
  add_mem' := fun {a b} ha hb L hL => by rw [map_add, ha L hL, hb L hL, add_zero]
  zero_mem' := fun L _ => map_zero L
  smul_mem' := fun c a ha L hL => by rw [map_smul, ha L hL, smul_zero]

theorem fd_orth {K : Type} [Group K] (κ : K →* Module.End ℂ U) (W : Submodule ℂ U) [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ (homs κ W)] : FiniteDimensional ℂ ↥(ck (homs κ W))ᗮ := by
  let ev : ↥(ck (homs κ W))ᗮ →ₗ[ℂ] (homs κ W →ₗ[ℂ] W) :=
    { toFun := fun z => { toFun := fun L => ⟨L.1 z, L.2.1 z⟩, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      map_add' := fun a b => LinearMap.ext fun L => Subtype.ext (map_add L.1 a.1 b.1)
      map_smul' := fun c a => LinearMap.ext fun L => Subtype.ext (map_smul L.1 c a.1) }
  refine Module.Finite.of_injective ev ((injective_iff_map_eq_zero ev).2 fun z hz => ?_)
  have h1 : z.1 ∈ ck (homs κ W) := fun L hL => congrArg Subtype.val (LinearMap.congr_fun hz ⟨L, hL⟩)
  exact Subtype.ext (inner_self_eq_zero.1 (z.2 _ h1))

theorem split {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (W V : Submodule ℂ U) [FiniteDimensional ℂ V] (sV : ∀ k, ∀ y ∈ V, κ k y ∈ V) (u : U) (uV : u ∈ V) :
    ∃ y ∈ V, ∃ z ∈ V, y ∈ (ck (homs κ W))ᗮ ∧ z ∈ ck (homs κ W) ∧ u = y + z := by
  have sZ' : ∀ k, ∀ z ∈ ck (homs κ W), κ k z ∈ ck (homs κ W) := fun k z hz L hL => by rw [hL.2, hz L hL, map_zero]
  obtain ⟨A, hA⟩ : ∃ A, A = V ⊓ ck (homs κ W) := ⟨_, rfl⟩
  have : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le (S₂ := V) (hA ▸ inf_le_left)
  have mA : ∀ y, y ∈ A ↔ y ∈ V ∧ y ∈ ck (homs κ W) := fun y => by rw [hA]; rfl
  have sA : ∀ k, ∀ y ∈ A, κ k y ∈ A := fun k y hy => (mA _).2 ⟨sV k y ((mA _).1 hy).1, sZ' k y ((mA _).1 hy).2⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = V ⊓ Aᗮ := ⟨_, rfl⟩
  have : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le (S₂ := V) (hY ▸ inf_le_left)
  have mY : ∀ y, y ∈ Y ↔ y ∈ V ∧ y ∈ Aᗮ := fun y => by rw [hY]; rfl
  have sY : ∀ k, ∀ y ∈ Y, κ k y ∈ Y := fun k y hy =>
    (mY _).2 ⟨sV k y ((mY _).1 hy).1, orth_stab κ hi A sA k y ((mY _).1 hy).2⟩
  have hz := (mA _).1 (A.starProjection_apply_mem u)
  have hy : u - A.starProjection u ∈ Y := (mY _).2 ⟨sub_mem uV hz.1, A.sub_starProjection_mem_orthogonal u⟩
  refine ⟨_, ((mY _).1 hy).1, _, hz.1, fun z hz' => ?_, hz.2, (sub_add_cancel _ _).symm⟩
  have h1 : Y.starProjection z ∈ ck (homs κ W) := fun L hL =>
    hz' (L ∘ₗ (Y.starProjection : U →ₗ[ℂ] U)) ⟨fun x => hL.1 _, fun k x => by
      show L (Y.starProjection (κ k x)) = κ k (L (Y.starProjection x))
      rw [proj_equiv κ hi Y sY, hL.2]⟩
  have h2 := (mY _).1 (Y.starProjection_apply_mem z)
  have h3 : Y.starProjection z = 0 := inner_self_eq_zero.1 (h2.2 _ ((mA _).2 ⟨h2.1, h1⟩))
  have h4 := Y.sub_starProjection_mem_orthogonal z
  rw [h3, sub_zero] at h4
  rw [inner_eq_zero_symm]
  exact h4 _ hy

theorem exists_e {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hf : ∀ x, FiniteDimensional ℂ (orb κ x)) (f : U) (hH : FiniteDimensional ℂ (homs κ (orb κ f))) :
    ∃ Z Z' : Submodule ℂ U, FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z = Z'ᗮ ∧
      ∀ S : Submodule ℂ U, (∀ k, ∀ y ∈ S, κ k y ∈ S) → ∀ u ∈ S, ∃ y ∈ S, ∃ z ∈ S, y ∈ Z ∧ z ∈ Z' ∧ u = y + z := by
  have := hf f
  refine ⟨_, ck (homs κ (orb κ f)), fd_orth κ _, fun z hz => ?_, rfl, fun S hS u hu => ?_⟩
  · have h0 : (orb κ f).starProjection z = 0 := hz ((orb κ f).starProjection : U →ₗ[ℂ] U)
      ⟨fun x => (orb κ f).starProjection_apply_mem x, fun k x => proj_equiv κ hi (orb κ f) (span_orbit_stab κ f) k x⟩
    have h1 := (orb κ f).sub_starProjection_mem_orthogonal z
    rw [h0, sub_zero] at h1
    rw [inner_eq_zero_symm]
    exact h1 f (mem_orb κ f)
  · have := hf u
    have VS : orb κ u ≤ S := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hS k u hu)
    obtain ⟨y, hy, z, hz, h⟩ := split κ hi (orb κ f) (orb κ u) (span_orbit_stab κ u) u (mem_orb κ u)
    exact ⟨y, VS hy, z, VS hz, h⟩

def Proj (St : Submodule ℂ U → Prop) : Prop :=
  ∀ f : U, ∃ Z Z' : Submodule ℂ U, FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z = Z'ᗮ ∧
    ∀ S : Submodule ℂ U, St S → ∀ u ∈ S, ∃ y ∈ S, ∃ z ∈ S, y ∈ Z ∧ z ∈ Z' ∧ u = y + z

theorem compl {St : Submodule ℂ U → Prop} (h : Proj St) (S : Submodule ℂ U) (hS : St S) (f : U) :
    ∃ a ∈ S, f - a ∈ Sᗮ := by
  obtain ⟨Z, Z', hZ, hf, e, hd⟩ := h f
  let A : Submodule ℂ U := S ⊓ Z
  haveI : FiniteDimensional ℂ A := Submodule.finiteDimensional_of_le (S₂ := Z) inf_le_right
  have ha := A.starProjection_apply_mem f
  refine ⟨_, ha.1, fun u hu => ?_⟩
  obtain ⟨y, hy, z, -, hyZ, hz, rfl⟩ := hd S hS u hu
  have h1 : f - A.starProjection f ∈ Z'ᗮ := e ▸ sub_mem hf ha.2
  rw [inner_add_left, A.sub_starProjection_mem_orthogonal f y ⟨hy, hyZ⟩, h1 z hz, add_zero]

theorem simple {St : Submodule ℂ U → Prop} (h : Proj St) (hinf : ∀ s : Set (Submodule ℂ U), (∀ S ∈ s, St S) → St (sInf s))
    (horth : ∀ S, St S → St Sᗮ) (N : Submodule ℂ U) (hN : St N) (hne : N ≠ ⊥) :
    ∃ S, St S ∧ S ≤ N ∧ S ≠ ⊥ ∧ ∀ P, St P → P ≤ S → P = ⊥ ∨ P = S := by
  classical
  obtain ⟨f, hfN, hf0⟩ := (Submodule.ne_bot_iff N).1 hne
  obtain ⟨Z, Z', hZ, hf, e, hd⟩ := h f
  have ex : ∃ m, ∃ S, St S ∧ S ≤ N ∧ S ⊓ Z ≠ ⊥ ∧ Module.finrank ℂ ↥(S ⊓ Z) = m :=
    ⟨_, N, hN, le_rfl, (Submodule.ne_bot_iff _).2 ⟨f, ⟨hfN, hf⟩, hf0⟩, rfl⟩
  obtain ⟨S₀, h0, h0N, h0ne, h0r⟩ := Nat.find_spec ex
  have hmin : ∀ P, St P → P ≤ S₀ → P ⊓ Z = ⊥ ∨ P ⊓ Z = S₀ ⊓ Z := fun P hP hle => by
    by_cases hb : P ⊓ Z = ⊥
    · exact Or.inl hb
    · haveI : FiniteDimensional ℂ ↥(S₀ ⊓ Z) := Submodule.finiteDimensional_of_le (S₂ := Z) inf_le_right
      refine Or.inr (Submodule.eq_of_le_of_finrank_le (inf_le_inf_right _ hle) ?_)
      rw [h0r]
      exact Nat.find_min' ex ⟨P, hP, hle.trans h0N, hb, rfl⟩
  let S := sInf {P | St P ∧ S₀ ⊓ Z ≤ P}
  have hS : St S := hinf _ fun P hP => hP.1
  have hS0 : S ≤ S₀ := sInf_le ⟨h0, inf_le_left⟩
  have hZS : S₀ ⊓ Z ≤ S := le_sInf fun P hP => hP.2
  have inf2 : ∀ P Q, St P → St Q → St (P ⊓ Q) := fun P Q hP hQ => by
    rw [← sInf_pair]; exact hinf _ (by rintro _ (rfl | rfl) <;> assumption)
  refine ⟨S, hS, hS0.trans h0N, fun hb => h0ne (le_bot_iff.1 (hb ▸ hZS)), fun P hP hle => ?_⟩
  rcases hmin P hP (hle.trans hS0) with hb | hb
  · left
    have h2 : S₀ ⊓ Z ≤ Pᗮ := fun x hx u hu => by
      obtain ⟨y, hy, z, -, hyZ, hz, rfl⟩ := hd P hP u hu
      have y0 : y = 0 := by
        have : y ∈ P ⊓ Z := ⟨hy, hyZ⟩
        rwa [hb, Submodule.mem_bot] at this
      have hx' : x ∈ Z'ᗮ := e ▸ hx.2
      rw [y0, zero_add]
      exact hx' z hz
    have h3 : S ≤ Pᗮ := sInf_le ⟨horth P hP, h2⟩
    exact (Submodule.eq_bot_iff _).2 fun x hx => inner_self_eq_zero.1 (h3 (hle hx) x hx)
  · exact Or.inr (le_antisymm hle (sInf_le ⟨hP, hb ▸ inf_le_left⟩))

theorem eq_bot {St : Submodule ℂ U → Prop} (h : Proj St) (hinf : ∀ s : Set (Submodule ℂ U), (∀ S ∈ s, St S) → St (sInf s))
    (horth : ∀ S, St S → St Sᗮ) (N : Submodule ℂ U) (hN : St N)
    (hu : ∀ M, Maximal (fun P => St P ∧ P ≠ ⊤) M → N ≤ M) : N = ⊥ := by
  by_contra hne
  obtain ⟨S, hS, hSN, hS0, hs⟩ := simple h hinf horth N hN hne
  have nle : ¬ S ≤ Sᗮ := fun hle => hS0 ((Submodule.eq_bot_iff _).2 fun x hx => inner_self_eq_zero.1 (hle hx x hx))
  refine nle (hSN.trans (hu _ ⟨⟨horth S hS, fun ht => nle (ht ▸ le_top)⟩, fun P hP hle => ?_⟩))
  have hPS : St (P ⊓ S) := by
    rw [← sInf_pair]; exact hinf _ (by rintro _ (rfl | rfl); exacts [hP.1, hS])
  rcases hs _ hPS inf_le_right with hb | hb
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := compl h S hS x
    have : a ∈ P ⊓ S := ⟨by simpa using P.sub_mem hx (hle hxa), ha⟩
    rw [hb, Submodule.mem_bot] at this
    simpa [this] using hxa
  · exfalso
    refine hP.2 (eq_top_iff.2 fun x _ => ?_)
    obtain ⟨a, ha, hxa⟩ := compl h S hS x
    have : a ∈ P := (by rw [hb]; exact ha : a ∈ P ⊓ S).1
    simpa using P.add_mem (hle hxa) this

end PositivityTheory.ThKF.Abs

end
end

