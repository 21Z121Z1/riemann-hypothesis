import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralOfContinuous
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory.CxForm GlobalTheory.ChartGlue

namespace GlobalTheory.LineForm.FnMul

section Chart

variable {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}

theorem lintegral_chartMeas (e : OpenPartialHomeomorph M (V n)) {ρ f : M → ℝ≥0∞} (hf : Measurable f)
    (hρ : AEMeasurable (ρ ∘ e.symm) (volume.restrict e.target)) :
    ∫⁻ y, f y ∂chartMeas e ρ = ∫⁻ v in e.target, f (e.symm v) * ρ (e.symm v) := by
  have h0 : AEMeasurable e.symm (volume.restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  have h : AEMeasurable e.symm ((volume.restrict e.target).withDensity (ρ ∘ e.symm)) :=
    h0.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [chartMeas, lintegral_map' hf.aemeasurable h,
    lintegral_withDensity_eq_lintegral_mul₀ hρ (g := fun v => f (e.symm v)) (hf.comp_aemeasurable h0)]
  exact lintegral_congr fun v => mul_comm _ _

theorem ofReal_mul_eq (a b : ℝ) : ENNReal.ofReal (a * b) =
    ENNReal.ofReal a * ENNReal.ofReal b + ENNReal.ofReal (-a) * ENNReal.ofReal (-b) := by
  rcases le_total 0 a with ha | ha
  · rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_of_nonpos (neg_nonpos.2 ha), zero_mul, add_zero]
  · rw [← neg_mul_neg, ENNReal.ofReal_mul (neg_nonneg.2 ha), ENNReal.ofReal_of_nonpos ha, zero_mul, zero_add]

variable [SecondCountableTopology M] (A : HolAtlas M n)

def glue (r : A.ι → V n → ℝ) : Measure M := glueMeas A.e fun i y => ENNReal.ofReal (r i (A.e i y))

theorem setLIntegral_glue {r : A.ι → V n → ℝ} (hr : ∀ i, ContinuousOn (r i) (A.e i).target)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    {f : M → ℝ≥0∞} (hf : Measurable f) (i : A.ι) {S : Set M} (hS : MeasurableSet S) (h : S ⊆ (A.e i).source) :
    ∫⁻ y in S, f y ∂glue A r =
      ∫⁻ v in (A.e i).target, S.indicator f ((A.e i).symm v) * ENNReal.ofReal (r i v) := by
  have h1 : (glue A r).restrict S = (chartMeas (A.e i) fun y => ENNReal.ofReal (r i (A.e i y))).restrict S :=
    (Measure.restrict_congr_meas hS).2 fun t ht htm =>
      glueMeas_apply A.e (fun i y => ENNReal.ofReal (r i (A.e i y))) A.holo (fun i j y hi hj => by
        rw [hc i j y hi hj, ENNReal.ofReal_mul (by positivity)]) i htm (ht.trans h)
  have h2 : ∀ᵐ v ∂volume.restrict (A.e i).target, ENNReal.ofReal (r i v) =
      ENNReal.ofReal (r i (A.e i ((A.e i).symm v))) :=
    (ae_restrict_iff' (A.e i).open_target.measurableSet).2 (.of_forall fun v hv => by rw [(A.e i).right_inv hv])
  rw [h1, ← lintegral_indicator hS, lintegral_chartMeas _ (ρ := fun y => ENNReal.ofReal (r i (A.e i y))) (hf.indicator hS)
    (((ENNReal.continuous_ofReal.comp_continuousOn (hr i)).aemeasurable
      (A.e i).open_target.measurableSet).congr h2)]
  refine lintegral_congr_ae ?_
  filter_upwards [h2] with v hv
  rw [hv]

theorem glue_mul {r : A.ι → V n → ℝ} (hr : ∀ i, ContinuousOn (r i) (A.e i).target)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    {g : M → ℝ} (hg : Continuous g) :
    glue A (fun i v => g ((A.e i).symm v) * r i v) =
      (glue A r).withDensity (fun y => ENNReal.ofReal (g y)) +
        (glue A fun i v => -r i v).withDensity fun y => ENNReal.ofReal (-g y) := by
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS h => ?_
  have m1 : Measurable fun y => ENNReal.ofReal (g y) := hg.measurable.ennreal_ofReal
  have m2 : Measurable fun y => ENNReal.ofReal (-g y) := hg.neg.measurable.ennreal_ofReal
  have h0 : AEMeasurable (A.e i).symm (volume.restrict (A.e i).target) :=
    (A.e i).continuousOn_symm.aemeasurable (A.e i).open_target.measurableSet
  have e0 := setLIntegral_glue A (r := fun i v => g ((A.e i).symm v) * r i v)
    (fun i => (hg.comp_continuousOn (A.e i).continuousOn_symm).mul (hr i))
    (fun i j y hi hj => by
      simp only [(A.e i).left_inv hi, (A.e j).left_inv hj, hc i j y hi hj]; ring)
    (f := fun _ => 1) measurable_const i hS h
  rw [setLIntegral_one] at e0
  rw [e0, Measure.add_apply, withDensity_apply _ hS, withDensity_apply _ hS,
    setLIntegral_glue A hr hc m1 i hS h,
    setLIntegral_glue A (r := fun i v => -r i v) (fun i => (hr i).neg)
      (fun i j y hi hj => by simp only [hc i j y hi hj]; ring) m2 i hS h,
    ← lintegral_add_left' (f := fun v => S.indicator (fun y => ENNReal.ofReal (g y)) ((A.e i).symm v) *
      ENNReal.ofReal (r i v)) (((m1.indicator hS).comp_aemeasurable h0).mul
      ((ENNReal.continuous_ofReal.comp_continuousOn (hr i)).aemeasurable (A.e i).open_target.measurableSet))]
  refine lintegral_congr fun v => ?_
  by_cases hv : (A.e i).symm v ∈ S
  · simp only [Function.comp_apply, indicator_of_mem hv, one_mul, ofReal_mul_eq]
  · simp only [Function.comp_apply, indicator_of_notMem hv, zero_mul, add_zero]

end Chart

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem dens_loc_fn_mul (g : M → ℝ) (ψ : A.Fld) (i : A.ι) (v : V n) :
    (dens (A.loc (A.fn g * ψ) i v)).re = g ((A.e i).symm v) * (dens (A.loc ψ i v)).re := by
  have key : ∀ x : A.Pt, (dens ((A.fn g * ψ) x)).re = g x.pt * (dens (ψ x)).re := fun x => by
    rw [Pi.mul_apply, HolAtlas.fn, ← Algebra.smul_def, ← Complex.re_ofReal_mul]
    simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]
  unfold HolAtlas.loc
  split_ifs with h
  · exact key _
  · simp [dens]

theorem dens_compat {ψ : A.Fld} (hψ : A.IsForm ψ) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) :
    (dens (A.loc ψ i (A.e i y))).re = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * (dens (A.loc ψ j (A.e j y))).re := by
  have h1 := A.loc_crd ψ (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd ψ (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hψ.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  erw [h1, h2, h3, dens_pull]
  rw [Complex.re_ofReal_mul]
  rfl

end GlobalTheory.LineForm.FnMul

namespace GlobalTheory.LineForm

open GlobalTheory.LineForm.FnMul

theorem integral_fn_mul : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (g : M → ℝ),
    Continuous g → ∀ ψ : A.Fld, A.IsForm ψ → A.integral (A.fn g * ψ) = wInt A g ψ := by
  intro M _ _ _ _ _ _ n A g hg ψ hψ
  set r : A.ι → V n → ℝ := fun i v => (dens (A.loc ψ i v)).re with hr
  have rc : ∀ i, ContinuousOn (r i) (A.e i).target := fun i =>
    Complex.continuous_re.comp_continuousOn ((hψ.smooth i Finset.univ).continuousOn.div_const _)
  have rt := dens_compat A hψ
  have nc : ∀ i, ContinuousOn (fun v => -r i v) (A.e i).target := fun i => (rc i).neg
  have nt : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      -r i (A.e i y) = ‖transDet (A.e i) (A.e j) y‖ ^ 2 * -r j (A.e j y) := fun i j y hi hj => by
    simp only [hr, rt i j y hi hj]; ring
  have p1 : A.part ψ 1 = glue A r := by simp [HolAtlas.part, glue, hr]
  have p2 : A.part ψ (-1) = glue A fun i v => -r i v := by simp [HolAtlas.part, glue, hr]
  have q1 : A.part (A.fn g * ψ) 1 = glue A fun i v => g ((A.e i).symm v) * r i v := by
    simp [HolAtlas.part, glue, hr, dens_loc_fn_mul]
  have q2 : A.part (A.fn g * ψ) (-1) = glue A fun i v => g ((A.e i).symm v) * -r i v := by
    simp [HolAtlas.part, glue, hr, dens_loc_fn_mul]
  have f1 : IsFiniteMeasure (glue A r) :=
    ⟨lt_top_iff_ne_top.2 (glueMeas_univ_ne_top_of_compact A.e A.cover A.holo r rc rt)⟩
  have f2 : IsFiniteMeasure (glue A fun i v => -r i v) :=
    ⟨lt_top_iff_ne_top.2 (glueMeas_univ_ne_top_of_compact A.e A.cover A.holo (fun i v => -r i v) nc nt)⟩
  have i1 : Integrable g (glue A r) := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have i2 : Integrable g (glue A fun i v => -r i v) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  rw [glue_mul A rc rt hg] at q1
  rw [glue_mul A (r := fun i v => -r i v) nc nt hg] at q2
  simp only [neg_neg] at q2
  rw [wInt, HolAtlas.integral, q1, q2, p1, p2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part i1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part i2]
  simp only [Measure.real, Measure.add_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have j1 : ∫⁻ y, ENNReal.ofReal (-g y) ∂glue A r ≠ ∞ := i1.neg.lintegral_lt_top.ne
  have j2 : ∫⁻ y, ENNReal.ofReal (-g y) ∂glue A (fun i v => -r i v) ≠ ∞ := i2.neg.lintegral_lt_top.ne
  rw [ENNReal.toReal_add i1.lintegral_lt_top.ne j2, ENNReal.toReal_add i2.lintegral_lt_top.ne j1]
  ring

end GlobalTheory.LineForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilComparisonGeneratorAdditiveFirstVariable
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp.AddFst

theorem prod_pair {S : Scheme.{0}} {A B : Over S} [GrpObj B] [IsCommMonObj B] (f g : A ⟶ B) {T : Over S} (x y : T ⟶ A)
    {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum B ![fst A A ≫ f, snd A A ≫ g] I.down).left) ^
        ((-1 : ℤ) ^ (2 - I.down.card)) =
      h ((x ≫ f) * (y ≫ g)).left * (h (x ≫ f).left)⁻¹ * (h (y ≫ g).left)⁻¹ * h (1 : T ⟶ B).left := by
  have e : ∀ I : Finset (Fin 2), (lift x y).left ≫ (psum B ![fst A A ≫ f, snd A A ≫ g] I).left =
      (psum B ![x ≫ f, y ≫ g] I).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) ![fst A A ≫ f, snd A A ≫ g] I).trans
      (congrArg (fun q => psum B q I) (funext fun i => by fin_cases i <;> simp [preHom])))
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum B ![x ≫ f, y ≫ g] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun I => congrArg (fun q => h q ^ ((-1 : ℤ) ^ (2 - I.down.card))) (e I.down)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum B ![x ≫ f, y ≫ g] ∅ = 1 := rfl
  have p₁ : psum B ![x ≫ f, y ≫ g] {0} = x ≫ f := _root_.mul_one (x ≫ f)
  have p₂ : psum B ![x ≫ f, y ≫ g] {1} = y ≫ g := _root_.mul_one (y ≫ g)
  have p₃ : psum B ![x ≫ f, y ≫ g] {0, 1} = (x ≫ f) * (y ≫ g) := congrArg ((x ≫ f) * ·) (_root_.mul_one (y ≫ g))
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_cmp {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) {T : Over S}
    (x y : T ⟶ P₀.A) {U : Type} [CommGroup U] (h : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → U) :
    ∏ i, h ((lift x y).left ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ i) ^ cmpε i =
      (h (((x ≫ f₂) * (y ≫ g₂)).left ≫ coprod.inr) * (h ((x ≫ f₂).left ≫ coprod.inr))⁻¹ *
          (h ((y ≫ g₂).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ P₂.A).left ≫ coprod.inr)) *
        (h (((x ≫ f₁) * (y ≫ g₁)).left ≫ coprod.inl) * (h ((x ≫ f₁).left ≫ coprod.inl))⁻¹ *
          (h ((y ≫ g₁).left ≫ coprod.inl))⁻¹ * h ((1 : T ⟶ P₁.A).left ≫ coprod.inl))⁻¹ := by
  refine DVR.prod_sum₂ _ ?_ ?_
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (prod_pair f₂ g₂ x y fun q => h (q ≫ coprod.inr))
    rw [Category.assoc]; rfl
  · refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_)
      (DVR.prod_neg _ _ (prod_pair f₁ g₁ x y fun q => h (q ≫ coprod.inl)))
    rw [Category.assoc]; rfl

theorem cmp_add_fst : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x x' y : T ⟶ P₀.A), val u (lift (x * x') y).left z J * cubV c₁ z (rl J) (x ≫ f₁) (x' ≫ f₁) (y ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (x' ≫ f₂) (y ≫ g₂) * (val u (lift x y).left z J * val u (lift x' y).left z J) := by
  intro hG S P₀ P₁ P₂ _ _ f₁ g₁ f₂ g₂ _ _ _ _ r₁ hr₁ c₁ r₂ hr₂ c₂ u hu h₀ T z J hJ x x' y
  have hA := P₀.isAb
  let p₀ := x3 P₀.A 0
  let p₁ := x3 P₀.A 1
  let p₂ := x3 P₀.A 2
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J → ∀ a b : T ⟶ P₀.A,
      val (LB.pullGen (join P₁.L P₂.L) _ _ u (lift a b).left) ρ.left z J = val u (lift (ρ ≫ a) (ρ ≫ b)).left z J :=
    fun ρ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  have v1 : ∀ {y : (𝟙_ (Over S)).left} {J}, Good (join P₁.L P₂.L) y J →
      val u (lift (1 : 𝟙_ (Over S) ⟶ P₀.A) (1 : 𝟙_ (Over S) ⟶ P₀.A)).left y J = 1 := fun {y J} hJ => by
    have e : lift (1 : 𝟙_ (Over S) ⟶ P₀.A) (1 : 𝟙_ (Over S) ⟶ P₀.A) = lift η[P₀.A] η[P₀.A] := by simp [Hom.one_def]
    have := h₀ _ (𝟙 S) y J hJ
    rw [e]
    exact (congrArg (fun q => val u q y J) (Category.id_comp _)).symm.trans this
  let e : 𝟙_ (Over S) ⟶ G3 P₀.A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have sj : Function.Surjective ((snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom).appTop.hom :=
    surj_comp (surj_snd hG hA _) (surj_comp (surj_snd hG hA _) (hG _ _ hA).2)
  have he : e.left ≫ (snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  let ρ : T ⟶ G3 P₀.A := lift x (lift x' y)
  have s₀ : ρ ≫ p₀ = x := by simp [ρ, p₀, x3]
  have s₁ : ρ ≫ p₁ = x' := by simp [ρ, p₁, x3]
  have s₂ : ρ ≫ p₂ = y := by simp [ρ, p₂, x3]
  have o₁ : e ≫ (p₀ * p₁) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])
  have o₂ : ρ ≫ (p₀ * p₁) = x * x' := (MonObj.comp_mul _ _ _).trans (by rw [s₀, s₁])
  have hl := isPart_inl P₁.L P₂.L
  have hr := isPart_inr P₁.L P₂.L
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (LB.pullGen (join P₁.L P₂.L) _ _ u (lift (p₀ * p₁) p₂).left)
        (hl.gen (LB.pullGen P₁.L (thφ P₁.A (x3 P₁.A)) thε c₁.t
          (lift (p₀ ≫ f₁) (lift (p₁ ≫ f₁) (p₂ ≫ g₁))).left))) σ.left z J =
        val u (lift (σ ≫ (p₀ * p₁)) (σ ≫ p₂)).left z J *
          cubV c₁ z (rl J) (σ ≫ p₀ ≫ f₁) (σ ≫ p₁ ≫ f₁) (σ ≫ p₂ ≫ g₁) ∧
      val (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (hr.gen (LB.pullGen P₂.L (thφ P₂.A (x3 P₂.A)) thε c₂.t
          (lift (p₀ ≫ f₂) (lift (p₁ ≫ f₂) (p₂ ≫ g₂))).left))
        (LB.mulGen (join P₁.L P₂.L) _ _ _ _ (LB.pullGen (join P₁.L P₂.L) _ _ u (lift p₀ p₂).left)
          (LB.pullGen (join P₁.L P₂.L) _ _ u (lift p₁ p₂).left))) σ.left z J =
        cubV c₂ z (rr J) (σ ≫ p₀ ≫ f₂) (σ ≫ p₁ ≫ f₂) (σ ≫ p₂ ≫ g₂) *
          (val u (lift (σ ≫ p₀) (σ ≫ p₂)).left z J * val u (lift (σ ≫ p₁) (σ ≫ p₂)).left z J) := fun σ z J hJ =>
    ⟨(val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
        ((hl.val_gen _ _ _ hJ).trans (val_cub c₁ σ (hl.good hJ) _ _ _))),
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((hr.val_gen _ _ _ hJ).trans (val_cub c₂ σ (hr.good hJ) _ _ _))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))⟩
  have key := (ev ρ hJ).1.symm.trans (Eq.trans (gen_unique' (join_isLB P₁.isLB P₂.isLB) (fun V _ k => ?_) _ e.left he sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (hl.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₁.isGen _)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (hr.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₂.isGen _)) (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))) (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ).2)
  · simp only [← Category.assoc] at key
    rwa [o₂, s₀, s₁, s₂] at key
  · refine (DVR.prod_sum₂ (K := thK) (K' := KK ⊕ KK) (U := V) _
        (prod_cub (p₀ ≫ f₂) (p₁ ≫ f₂) (p₂ ≫ g₂) fun q => k (q ≫ coprod.inr))
        (DVR.prod_sum₂ (K := KK) (K' := KK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₂ k)
          (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₁ p₂ k))).trans
        (Eq.trans ?_ (DVR.prod_sum₂ (K := KK) (K' := thK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ (p₀ * p₁) p₂ k)
          (prod_cub (p₀ ≫ f₁) (p₁ ≫ f₁) (p₂ ≫ g₁) fun q => k (q ≫ coprod.inl))).symm)
    rw [MonObj.mul_comp p₀ p₁ f₁, MonObj.mul_comp p₀ p₁ f₂]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · have C₁ := isCub_cubV c₁ (hl.good hI)
    have C₂ := isCub_cubV c₂ (hr.good hI)
    refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
    rw [← Category.assoc e p₀, ← Category.assoc e p₀, o₁, e₀, e₁, e₂, MonObj.one_comp, MonObj.one_comp, v1 hI]
    rw [C₁.face, C₂.face]
    simp

end GlobalTheory.Mum.Two.WeilCmp.AddFst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilComparisonGeneratorAdditiveSecondVariable
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

variable {S : Scheme.{0}} (P₀ P₁ P₂ : PolAV S)

theorem prod_cmp (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) {T : Over S} (a b : T ⟶ P₀.A) {V : Type} [CommGroup V]
    (h : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → V) :
    ∏ k, h ((lift a b).left ≫ cmpφ P₀ P₁ P₂ f₁ g₁ f₂ g₂ k) ^ cmpε k =
      (h (((a ≫ f₂) * (b ≫ g₂)).left ≫ coprod.inr) * (h ((a ≫ f₂).left ≫ coprod.inr))⁻¹ *
        (h ((b ≫ g₂).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ P₂.A).left ≫ coprod.inr)) *
      (h (((a ≫ f₁) * (b ≫ g₁)).left ≫ coprod.inl) * (h ((a ≫ f₁).left ≫ coprod.inl))⁻¹ *
        (h ((b ≫ g₁).left ≫ coprod.inl))⁻¹ * h ((1 : T ⟶ P₁.A).left ≫ coprod.inl))⁻¹ := by
  have c₂ := prod_cube₂ (fst P₀.A P₀.A ≫ f₂) (snd P₀.A P₀.A ≫ g₂) (fun q => h ((lift a b).left ≫ q ≫ coprod.inr))
  have c₁ := prod_neg _ _ (prod_cube₂ (fst P₀.A P₀.A ≫ f₁) (snd P₀.A P₀.A ≫ g₁)
    (fun q => h ((lift a b).left ≫ q ≫ coprod.inl)))
  have e : ∀ {Q : Over S} (q : P₀.A ⊗ P₀.A ⟶ Q) (t : Q.left ⟶ P₁.A.left ⨿ P₂.A.left),
      (lift a b).left ≫ q.left ≫ t = (lift a b ≫ q).left ≫ t := fun q t => by rw [Over.comp_left, Category.assoc]
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) (c₂.trans ?_) (c₁.trans ?_)
  · simp only [e, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.comp_one]
  · simp only [e, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, MonObj.comp_one]

end GlobalTheory.Mum.Two.WeilCmp

namespace GlobalTheory.Mum.Two.WeilCmp

theorem add_snd : GlobalFnsSt → ∀ (S : Scheme.{0}) (P₀ P₁ P₂ : PolAV S) [Nonempty P₁.A.left] [Nonempty P₂.A.left] (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A) [IsMonHom f₁] [IsMonHom g₁] [IsMonHom f₂] [IsMonHom g₂], ∀ (r₁ : LB.Gen (P₁.L.pull (eSec P₁.A))) (hr₁ : r₁.IsGen) (c₁ : CubicalStr P₁.A ⟨P₁.L, r₁, P₁.isLB, hr₁⟩) (r₂ : LB.Gen (P₂.L.pull (eSec P₂.A))) (hr₂ : r₂.IsGen) (c₂ : CubicalStr P₂.A ⟨P₂.L, r₂, P₂.isLB, hr₂⟩) (u : LB.Gen (CmpL P₀ P₁ P₂ f₁ g₁ f₂ g₂)), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good (join P₁.L P₂.L) z J → val u (r ≫ zero2 P₀.A) z J = 1) → ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ P₁.A.left ⨿ P₂.A.left) → (join P₁.L P₂.L).ι), Good (join P₁.L P₂.L) z J → ∀ (x y y' : T ⟶ P₀.A), val u (lift x (y * y')).left z J * cubV c₁ z (rl J) (x ≫ f₁) (y ≫ g₁) (y' ≫ g₁) = cubV c₂ z (rr J) (x ≫ f₂) (y ≫ g₂) (y' ≫ g₂) * (val u (lift x y).left z J * val u (lift x y').left z J) := by
  intro hG S P₀ P₁ P₂ _ _ f₁ g₁ f₂ g₂ _ _ _ _ r₁ hr₁ c₁ r₂ hr₂ c₂ u hu hn T z J hJ x y y'
  let p₀ := x3 P₀.A 0
  let p₁ := x3 P₀.A 1
  let p₂ := x3 P₀.A 2
  have hL := join_isLB P₁.isLB P₂.isLB
  have pl := isPart_inl P₁.L P₂.L
  have pr := isPart_inr P₁.L P₂.L
  have vp : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J → ∀ a b : G3 P₀.A ⟶ P₀.A,
      val (LB.pullGen _ _ _ u (lift a b).left) σ.left z J = val u (lift (σ ≫ a) (σ ≫ b)).left z J :=
    fun σ z J hJ a b => by rw [val_pull hJ, ← Over.comp_left, comp_lift]
  let U₁ := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ u (lift p₀ (p₁ * p₂)).left)
    (pl.gen (LB.pullGen P₁.L _ _ c₁.t (lift (p₀ ≫ f₁) (lift (p₁ ≫ g₁) (p₂ ≫ g₁))).left))
  let U₂ := LB.mulGen _ _ _ _ _ (pr.gen (LB.pullGen P₂.L _ _ c₂.t (lift (p₀ ≫ f₂) (lift (p₁ ≫ g₂) (p₂ ≫ g₂))).left))
    (LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ u (lift p₀ p₁).left) (LB.pullGen _ _ _ u (lift p₀ p₂).left))
  have hU₁ : U₁.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)
    (pl.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₁.isGen _))
  have hU₂ : U₂.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (pr.gen_isGen (DVR.pullGen_isGen _ _ _ _ c₂.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
  have ev₁ : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val U₁ σ.left z J = val u (lift (σ ≫ p₀) (σ ≫ (p₁ * p₂))).left z J *
        cubV c₁ z (rl J) (σ ≫ p₀ ≫ f₁) (σ ≫ p₁ ≫ g₁) (σ ≫ p₂ ≫ g₁) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _)
      ((pl.val_gen _ _ _ hJ).trans (val_cub c₁ σ (pl.good hJ) _ _ _)))
  have ev₂ : ∀ {T' : Over S} (σ : T' ⟶ G3 P₀.A) {z : T'.left} {J}, Good (join P₁.L P₂.L) z J →
      val U₂ σ.left z J = cubV c₂ z (rr J) (σ ≫ p₀ ≫ f₂) (σ ≫ p₁ ≫ g₂) (σ ≫ p₂ ≫ g₂) *
        (val u (lift (σ ≫ p₀) (σ ≫ p₁)).left z J * val u (lift (σ ≫ p₀) (σ ≫ p₂)).left z J) := fun σ z J hJ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((pr.val_gen _ _ _ hJ).trans (val_cub c₂ σ (pr.good hJ) _ _ _))
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))))
  let e : 𝟙_ (Over S) ⟶ G3 P₀.A := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have o₁ : e ≫ (p₁ * p₂) = 1 := (MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])
  have sj : Function.Surjective ((snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom).appTop.hom :=
    surj_comp (surj_snd hG P₀.isAb _) (surj_comp (surj_snd hG P₀.isAb _) (hG _ _ P₀.isAb).2)
  have he : e.left ≫ (snd P₀.A (P₀.A ⊗ P₀.A)).left ≫ (snd P₀.A P₀.A).left ≫ P₀.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' hL (u := U₁) (u' := U₂) (fun V _ k => ?_) _ e.left he sj hU₁ hU₂ (fun w I hI => ?_)
  rotate_left
  · refine (prod_sum₂ (K := thK) (K' := KK ⊕ KK) (U := V) _
      (prod_cub (p₀ ≫ f₂) (p₁ ≫ g₂) (p₂ ≫ g₂) fun q => k (q ≫ coprod.inr))
      (prod_sum₂ (K := KK) (K' := KK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₁ k)
        (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ p₂ k))).trans
      (Eq.trans ?_ (prod_sum₂ (K := KK) (K' := thK) (U := V) _ (prod_cmp P₀ P₁ P₂ f₁ g₁ f₂ g₂ p₀ (p₁ * p₂) k)
        (prod_cub (p₀ ≫ f₁) (p₁ ≫ g₁) (p₂ ≫ g₁) fun q => k (q ≫ coprod.inl))).symm)
    simp only [MonObj.mul_comp, ← _root_.mul_assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [ev₁ e hI, ev₂ e hI]
    simp only [← Category.assoc, e₀, e₁, e₂, o₁, MonObj.one_comp]
    have C₁ := isCub_cubV c₁ (pl.good hI)
    have C₂ := isCub_cubV c₂ (pr.good hI)
    have v1 : val u (lift (1 : 𝟙_ (Over S) ⟶ P₀.A) 1).left w I = 1 := by
      have eL : lift (1 : 𝟙_ (Over S) ⟶ P₀.A) 1 = lift η[P₀.A] η[P₀.A] := by simp [Hom.one_def]
      rw [eL]
      exact (congrArg (fun q => val u q w I) (Category.id_comp _).symm).trans (hn _ (𝟙 _) w I hI)
    rw [v1, C₁.face, C₂.face]
    simp
  have kk := (ev₁ _ hJ).symm.trans ((key _ (lift x (lift y y')).left z J hJ).trans (ev₂ _ hJ))
  have r₀ : lift x (lift y y') ≫ p₀ = x := by simp [p₀, x3]
  have r₁ : lift x (lift y y') ≫ p₁ = y := by simp [p₁, x3]
  have r₂ : lift x (lift y y') ≫ p₂ = y' := by simp [p₂, x3]
  have s₁ : lift x (lift y y') ≫ (p₁ * p₂) = y * y' := (MonObj.comp_mul _ _ _).trans (by rw [r₁, r₂])
  rw [s₁] at kk
  simp only [← Category.assoc, r₀, r₁, r₂] at kk
  exact kk

end GlobalTheory.Mum.Two.WeilCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.XMemNonZeroDivisors
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.Taut

theorem X_mem_nonZeroDivisors (W : Type) [CommRing W] {σ : Type} (k : σ) :
    (MvPolynomial.X k : MvPolynomial σ W) ∈ nonZeroDivisors (MvPolynomial σ W) := by
  refine mem_nonZeroDivisors_iff.2 ⟨fun p hp => ?_, fun p hp => ?_⟩
  · ext m
    have := congrArg (MvPolynomial.coeff (m + Finsupp.single k 1)) hp
    rwa [mul_comm, MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this
  · ext m
    have := congrArg (MvPolynomial.coeff (m + Finsupp.single k 1)) hp
    rwa [MvPolynomial.coeff_mul_X, MvPolynomial.coeff_zero] at this

theorem monomial_chart : ∀ {o : Type} [CommRing o] {ζ : o} (g n : ℕ) (φ : InvFun ℤ), 1 ≤ n → ∀ C : Taut ζ g n φ,
    C.Q.IsMonomialTau C.t (fun k => (n : ℤ) • C.δ k) ∧ Module.finrank ℤ C.Q.X ≤ g ∧ IsCone id φ C.δ ∧
      (∀ z, z ≠ 0 → ∃ k, 0 < C.δ k z z) ∧ (∀ k, C.t k ≠ 0) := by
  intro o _ ζ g n φ _ C
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    obtain ⟨k, hk, hc⟩ := GlobalTheory.T.tautologicalBase_periods_factor_mul_generator C.T (C.ψ.comp MvPolynomial.C) (fun k => C.ψ (MvPolynomial.X k))
      (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.Q C.e C.data a b
    let z : Fin C.N → ℤ := fun j => (n : ℤ) * (C.ε (.inr j) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)
    let w : C.Rˣ := ∏ j, (C.tor j).unit ^ z j
    refine ⟨k * Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹, ?_,
      GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
    rw [Units.val_mul, hk, Fintype.prod_sum_type]
    have hw : ((Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w⁻¹ : (FractionRing C.R)ˣ) : FractionRing C.R) *
        ∏ j : Fin C.N, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inr j))) ^ z j = 1 := by
      rw [← Units.val_one, ← mul_inv_cancel (Units.map (algebraMap C.R (FractionRing C.R) : C.R →* FractionRing C.R) w)]
      simp [w, map_prod, Units.coe_prod, map_zpow]
      refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ?_)
      exact (map_ne_zero_iff _ (IsFractionRing.injective C.R (FractionRing C.R))).2 (C.tor j).ne_zero
    have hl : ∏ i, algebraMap C.R (FractionRing C.R) (C.t i) ^ (((n : ℤ) • C.δ i) a b) =
        ∏ k : Fin C.m, algebraMap C.R (FractionRing C.R) (C.ψ (MvPolynomial.X (.inl k))) ^
          ((n : ℤ) * (C.ε (.inl k) : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ)) (C.e a) (C.e b)) := by
      rfl
    rw [hl, _root_.mul_assoc, mul_comm (∏ j : Fin C.N, _), hw, _root_.mul_one]
  · have h : Module.finrank ℤ C.Q.X = C.T.r := by
      rw [C.e.toIntLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    have := C.genus
    omega
  · exact C.cone.pull_equiv C.e.toIntLinearEquiv
  · intro z hz
    obtain ⟨k, hk⟩ := C.defin (C.e z) (by simpa using hz)
    exact ⟨k, hk⟩
  · intro k hk
    letI := C.ψ.toAlgebra
    haveI : Module.Flat (MvPolynomial (Fin C.m ⊕ Fin C.N) C.W) C.R := C.compl.2.2.1
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := C.R) (X_mem_nonZeroDivisors C.W (Sum.inl k : Fin C.m ⊕ Fin C.N))
    apply one_ne_zero (α := C.R)
    apply hreg
    show C.ψ (MvPolynomial.X (.inl k)) * 1 = C.ψ (MvPolynomial.X (.inl k)) * 0
    rw [show C.ψ (MvPolynomial.X (.inl k)) = 0 from hk]; simp

end GlobalTheory.TChart.Taut
end
end

