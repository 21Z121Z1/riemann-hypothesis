import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFundamentalDomain
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical Topology

namespace GlobalTheory.SW.LatFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
theorem mapL_mul (γ γ' : GL (Fin r) E) (L : Lt E r) : mapL (γ * γ') L = mapL γ (mapL γ' L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL 1 L = L := by
  ext v
  simp [mapL]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  change (1 : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

omit [NumberField E] [IsCMField E] in
theorem lact_mul {Ψ : Finset (E →+* ℂ)} (γ' γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact (γ' * γ) x = lact γ' (lact γ x) := by
  first
  | exact @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame
  | (apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftActionFrameMul.lact_mul_frame ..)

omit [NumberField E] [IsCMField E] in
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact γ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

omit [IsCMField E] in

theorem countable_fg : {L : Lt E r | L.FG}.Countable := by
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  refine (Set.countable_range fun s : Finset (Fin r → E) =>
    Submodule.span (𝓞 E) (s : Set (Fin r → E))).mono ?_
  rintro L ⟨s, hs⟩
  exact ⟨s, hs⟩

omit [IsCMField E] in

theorem exists_den {L : Lt E r} (hL : L.FG) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ L, ∀ a, ∃ c : 𝓞 E, (c : E) = (d : E) * v a := by
  first
  | exact @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator
  | exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator
  | (apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominatorExistence.exists_common_denominator ..)

theorem eq_zero_of_small (X : Data E r) (c : 𝓞 E) (h : ∀ τ : X.Ψ, ‖τ.1 (c : E)‖ < 1) : c = 0 := by
  by_contra hc
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hc
  by_cases hs : σ ∈ X.Ψ
  · exact absurd (h ⟨σ, hs⟩) (not_lt.2 hσ)
  · have h1 : ComplexEmbedding.conjugate σ ∈ X.Ψ := by
      by_contra h2
      exact hs ((X.cmType σ).2 h2)
    have h3 := h ⟨_, h1⟩
    simp only [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj] at h3
    exact absurd h3 (not_lt.2 hσ)

theorem exists_nhds (X : Data E r) {L : Lt E r} (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin r → E)) = ⊤) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ U ∈ 𝓝 x, ∀ γ : GL (Fin r) E, mapL γ L = L → lact γ x ∈ U → γ = 1 := by
  obtain ⟨d, hd0, hd⟩ := exists_den hL
  obtain ⟨s, hs⟩ := hL
  let f : (Fin r → E) → X.Ψ → Fin r → Frame X.Ψ r → ℝ := fun v τ a y =>
    ‖τ.1 (d : E) * ((mat y τ *ᵥ ((mat x τ)⁻¹ *ᵥ fun b => τ.1 (v b))) a - τ.1 (v a))‖
  have hf : ∀ v τ a, Continuous (f v τ a) := fun v τ a => by
    simp only [f, mat, Matrix.mulVec, dotProduct, Matrix.of_apply]
    fun_prop
  have hu : ∀ τ, IsUnit (mat x τ).det := fun τ => (hx τ).1.isUnit
  refine ⟨{y | ∀ v ∈ s, ∀ τ a, f v τ a y < 1}, ?_, fun γ hγ hy => ?_⟩
  · refine (Filter.eventually_all_finset s).2 fun v _ => Filter.eventually_all.2 fun τ =>
      Filter.eventually_all.2 fun a => ?_
    refine (hf v τ a).continuousAt.eventually_lt continuousAt_const ?_
    simp [f, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hu τ)]
  · have h1 : ∀ v ∈ s, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
      have hvL : v ∈ L := hs ▸ Submodule.subset_span hv
      have hγv : (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ L := by
        rw [← hγ]
        exact ⟨v, hvL, by simp⟩
      funext a
      obtain ⟨c, hc⟩ := hd _ (L.sub_mem hγv hvL) a
      have hc0 : c = 0 := eq_zero_of_small X c fun τ => by
        have h2 := hy v hv τ a
        have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
        simp only [f, e1, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          Matrix.mul_nonsing_inv _ (hu τ), Matrix.mul_one] at h2
        rw [hc]
        convert h2 using 2
        simp [Matrix.mulVec, dotProduct]
      rw [hc0] at hc
      have hd1 : (d : E) ≠ 0 := by exact_mod_cast hd0
      have := (mul_eq_zero.1 (hc.symm.trans (by simp))).resolve_left hd1
      exact sub_eq_zero.1 this
    have h2 : ∀ v ∈ L, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v hv => by
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem v hv => exact h1 v hv
      | zero => simp
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul t v _ hv => rw [Matrix.mulVec_smul, hv]
    have h3 : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v := fun v => by
      have hv : v ∈ Submodule.span E (L : Set (Fin r → E)) := hsp ▸ Submodule.mem_top
      induction hv using Submodule.span_induction with
      | mem v hv => exact h2 v hv
      | zero => simp
      | add u v _ _ hu hv => rw [Matrix.mulVec_add, hu, hv]
      | smul t v _ hv => rw [Matrix.mulVec_smul, hv]
    ext i j
    have := congrFun (h3 (Pi.single j 1)) i
    simpa [Matrix.one_apply, Pi.single_apply] using this

theorem exists_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)), (∀ γ ∈ Δ, IsUn X γ) → (∀ L ∈ 𝓛, L.FG ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤) → (∀ γ ∈ Δ, ∀ L ∈ 𝓛, mapL γ L ∈ 𝓛) → 𝓛.Countable ∧ (∀ (γ γ' : GL (Fin r) E) L, mapL (γ * γ') L = mapL γ (mapL γ' L)) ∧ (∀ L : Lt E r, mapL 1 L = L) ∧ ∃ D : Lt E r → Set (Frame X.Ψ r), (∀ L, MeasurableSet (D L) ∧ D L ⊆ X.dom) ∧ ∀ L ∈ 𝓛, ∀ x ∈ X.dom, ∃! γ : Δ, lact γ x ∈ D (mapL γ L) := by
  intro E _ _ _ r X Δ 𝓛 hun hlat hstab
  have hc : 𝓛.Countable := countable_fg.mono fun L hL => (hlat L hL).1
  refine ⟨hc, mapL_mul, mapL_one, ?_⟩
  have : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  have : Countable (GL (Fin r) E) := Units.val_injective.countable
  have : Countable 𝓛 := hc.to_subtype
  letI : TopologicalSpace 𝓛 := ⊥
  have : DiscreteTopology 𝓛 := ⟨rfl⟩
  letI : MeasurableSpace 𝓛 := ⊤
  have : OpensMeasurableSpace 𝓛 := ⟨le_top⟩
  letI act : MulAction Δ (𝓛 × X.dom) :=
    { smul := fun γ p => (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩)
      one_smul := fun p => Prod.ext (Subtype.ext (mapL_one _)) (Subtype.ext (lact_one _))
      mul_smul := fun γ γ' p =>
        Prod.ext (Subtype.ext (mapL_mul _ _ _)) (Subtype.ext (lact_mul _ _ _)) }
  have hsm : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p =
    (⟨mapL γ p.1, hstab _ γ.2 _ p.1.2⟩, ⟨lact γ p.2, (hun _ γ.2).lact_mem p.2.2⟩) := fun _ _ => rfl
  have : MeasurableConstSMul Δ (𝓛 × X.dom) := ⟨fun γ => by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_from_top (f := fun L : 𝓛 => (⟨mapL γ L, hstab _ γ.2 _ L.2⟩ : 𝓛))).comp
        measurable_fst
    · exact (((continuous_lact (γ : GL (Fin r) E)).measurable.comp
        measurable_subtype_coe).comp measurable_snd).subtype_mk⟩
  have hdisc : ∀ p : 𝓛 × X.dom, ∃ U ∈ 𝓝 p, ∀ γ : Δ, γ • p ∈ U → γ = 1 := fun p => by
    obtain ⟨U, hU, h⟩ := exists_nhds X (hlat _ p.1.2).1 (hlat _ p.1.2).2 p.2.2
    refine ⟨{p.1} ×ˢ (Subtype.val ⁻¹' U), prod_mem_nhds ((isOpen_discrete _).mem_nhds rfl)
      (continuous_subtype_val.continuousAt.preimage_mem_nhds hU), fun γ hγ => ?_⟩
    exact Subtype.ext (h γ (congrArg Subtype.val hγ.1) hγ.2)
  have hfree : ∀ (γ : Δ) (p : 𝓛 × X.dom), γ • p = p → γ = 1 := fun γ p h => by
    obtain ⟨U, hU, h'⟩ := hdisc p
    exact h' γ (h.symm ▸ mem_of_mem_nhds hU)
  obtain ⟨D, hD, hcov, hu⟩ := exists_measurableSet_orbitSection_of_discreteOrbits (G := Δ)
    (X := 𝓛 × X.dom)
    (fun g => by
      by_cases hg : g = 1
      · simp [hg]
      · have : {p : 𝓛 × X.dom | g • p = p} = ∅ :=
          Set.eq_empty_of_forall_notMem fun p hp => hg (hfree g p hp)
        simp [this])
    (fun p => by
      obtain ⟨U, hU, h⟩ := hdisc p
      exact ⟨U, hU, fun g hg => by rw [h g hg, one_smul]⟩)
  refine ⟨fun L => {y | ∃ (hL : L ∈ 𝓛) (hy : y ∈ X.dom), ((⟨L, hL⟩, ⟨y, hy⟩) : 𝓛 × X.dom) ∈ D},
    fun L => ⟨?_, fun y hy => hy.2.1⟩, fun L hL x hx => ?_⟩
  · by_cases hL : L ∈ 𝓛
    · have h := (MeasurableEmbedding.subtype_coe
        (FourierCoefficientDomain.isOpen_dom X).measurableSet).measurableSet_image.2
        (measurable_prodMk_left (x := (⟨L, hL⟩ : 𝓛)) hD)
      convert h using 1
      ext y
      exact ⟨fun ⟨_, hy, h⟩ => ⟨⟨y, hy⟩, h, rfl⟩, fun ⟨z, h, e⟩ => e ▸ ⟨hL, z.2, h⟩⟩
    · simp [hL]
  · obtain ⟨g, hg⟩ := hcov (⟨L, hL⟩, ⟨x, hx⟩)
    refine ⟨g, ⟨_, _, hg⟩, fun k hk => ?_⟩
    obtain ⟨_, _, hk⟩ := hk
    have := hu _ hg (k * g⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hk)
    exact mul_inv_eq_one.1 (hfree _ _ this)

end GlobalTheory.SW.LatFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticUnitaryColumns
section
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Classical Kronecker

namespace GlobalTheory.ColumnSymplectic

variable {n g : ℕ}

theorem blk_eq (τ : Matrix (Fin g) (Fin g) ℂ) :
    blk n τ = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ τ := by
  ext p q
  simp only [blk, of_apply, kroneckerMap_apply, one_apply]
  split_ifs <;> simp

theorem blk_mul (A B : Matrix (Fin g) (Fin g) ℂ) : blk n A * blk n B = blk n (A * B) := by
  rw [blk_eq, blk_eq, blk_eq, ← mul_kronecker_mul, one_mul]

theorem blk_one : blk n (1 : Matrix (Fin g) (Fin g) ℂ) = 1 := by
  rw [blk_eq, one_kronecker_one]

theorem blk_mulVec (A : Matrix (Fin g) (Fin g) ℂ) (w : Fin n × Fin g → ℂ) :
    blk n A *ᵥ w = fun p => (A *ᵥ fun i => w (p.1, i)) p.2 := by
  funext p
  simp only [mulVec, dotProduct, blk, of_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single p.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem blk_mem_siegel {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ Siegel (Fin g)) :
    blk n τ ∈ Siegel (Fin n × Fin g) := by
  refine ⟨?_, ?_⟩
  · show (blk n τ)ᵀ = blk n τ
    ext p q
    simp only [transpose_apply, blk, of_apply]
    by_cases e : p.1 = q.1
    · rw [if_pos e.symm, if_pos e]
      exact congrFun (congrFun h.1 p.2) q.2
    · rw [if_neg (Ne.symm e), if_neg e]
  · have e : (blk n τ).map Complex.im = (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ τ.map Complex.im := by
      ext p q
      simp only [map_apply, blk, of_apply, kroneckerMap_apply, one_apply]
      split_ifs <;> simp
    rw [e]
    exact PosDef.one.kronecker h.2

private theorem sum_herm_eq_trace_mul_ccT {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, herm G (y k) (y' k) = (y * G * ccT y').trace := by
  simp only [herm, trace, diag, mul_apply, ccT, transpose_apply, map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem sum_herm_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) (G : Matrix (Fin r) (Fin r) E)
    (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, herm G ((h * y) k) ((h * y') k) = ∑ k, herm G (y k) (y' k) := by
  rw [sum_herm_eq_trace_mul_ccT, sum_herm_eq_trace_mul_ccT, Base.ccT_mul]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc, hu, Matrix.mul_one]

theorem sum_EF_mul {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (y y' : Matrix (Fin n) (Fin r) E) :
    ∑ k, EF X ((h * y) k) ((h * y') k) = ∑ k, EF X (y k) (y' k) := by
  simp only [EF_def, ← map_sum, ← Finset.mul_sum]
  rw [sum_herm_mul hu]

private theorem crd_dotProduct_sub_eq_neg_sum_EF (hs : IsSympl X bas) (Z Z' : Matrix (Fin n) (Fin r) E) :
    (fun p : Fin n × Fin g => crd X bas (Z p.1) (Sum.inl p.2)) ⬝ᵥ
        (fun p : Fin n × Fin g => crd X bas (Z' p.1) (Sum.inr p.2)) -
      (fun p : Fin n × Fin g => crd X bas (Z p.1) (Sum.inr p.2)) ⬝ᵥ
        (fun p : Fin n × Fin g => crd X bas (Z' p.1) (Sum.inl p.2)) =
      -∑ k, EF X (Z k) (Z' k) := by
  simp only [EF_crd hs, dotProduct, Fintype.sum_prod_type, Finset.sum_neg_distrib, neg_neg,
    ← Finset.sum_sub_distrib]

variable (bas) in

noncomputable def famOf (u : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) : Matrix (Fin n) (Fin r) E :=
  Matrix.of fun k => vecQ X bas (Sum.elim (fun i => u.1 (k, i)) fun i => u.2 (k, i))

noncomputable def colMap (hs : IsSympl X bas) (h : Matrix (Fin n) (Fin n) E) :
    ((Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) →ₗ[ℚ] ((Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) where
  toFun u := (fun p => crd X bas ((h * famOf bas u) p.1) (Sum.inl p.2),
    fun p => crd X bas ((h * famOf bas u) p.1) (Sum.inr p.2))
  map_add' u v := by
    have : famOf bas (u + v) = famOf bas u + famOf bas v := by
      refine funext fun k => ?_
      change vecQ X bas _ = vecQ X bas _ + vecQ X bas _
      rw [← vecQ_add]
      congr 1
      funext j; rcases j with j | j <;> rfl
    have e : ∀ k, (h * famOf bas (u + v)) k = (h * famOf bas u) k + (h * famOf bas v) k := fun k => by
      rw [this, Matrix.mul_add]; rfl
    simp only [e, crd_add hs]
    rfl
  map_smul' q u := by
    have : famOf bas (q • u) = q • famOf bas u := by
      refine funext fun k => ?_
      change vecQ X bas _ = q • vecQ X bas _
      rw [← vecQ_smul]
      congr 1
      funext j; rcases j with j | j <;> rfl
    have e : ∀ k, (h * famOf bas (q • u)) k = q • (h * famOf bas u) k := fun k => by
      rw [this, Matrix.mul_smul]; rfl
    simp only [e, crd_smul hs]
    rfl

theorem colMap_form (hs : IsSympl X bas) {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1)
    (u v : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) :
    (colMap hs h u).1 ⬝ᵥ (colMap hs h v).2 - (colMap hs h u).2 ⬝ᵥ (colMap hs h v).1 =
      u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1 := by
  have hcrd : ∀ (w : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) (k : Fin n),
      crd X bas (famOf bas w k) = Sum.elim (fun i => w.1 (k, i)) fun i => w.2 (k, i) := by
    intro w k
    simp only [famOf]
    exact crd_vecQ hs _
  have e1 := crd_dotProduct_sub_eq_neg_sum_EF hs (h * famOf bas u) (h * famOf bas v)
  have e2 := crd_dotProduct_sub_eq_neg_sum_EF hs (famOf bas u) (famOf bas v)
  rw [sum_EF_mul hu, ← e2] at e1
  simp only [hcrd, Sum.elim_inl, Sum.elim_inr] at e1
  exact e1

noncomputable def actM (h : Matrix (Fin n) (Fin n) E) : Matrix (Fin n × Fin g) (Fin n × Fin g) ℂ :=
  blockDiagonal fun i => (rowType X (idx i)).mapMatrix h

theorem actM_mulVec (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) :
    (actM idx h *ᵥ fun p => z p.1 p.2) = fun p => Dict.hAct X idx h z p.1 p.2 := by
  funext p
  simp only [actM, Dict.hAct, mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type, ite_mul,
    zero_mul, RingHom.mapMatrix_apply, map_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem det_actM (h : Matrix (Fin n) (Fin n) E) :
    (actM idx h).det = ∏ i, rowType X (idx i) h.det := by
  rw [actM, det_blockDiagonal]
  exact Finset.prod_congr rfl fun i _ => (RingHom.map_det _ _).symm

theorem per_mul (x : Frame X.Ψ r) (h : Matrix (Fin n) (Fin n) E) (y : Matrix (Fin n) (Fin r) E)
    (k : Fin n) : per X x ((h * y) k) ∘ idx = Dict.hAct X idx h (fun k => per X x (y k) ∘ idx) k := by
  have e : (h * y) k = ∑ k', h k k' • y k' := by
    ext a
    simp [mul_apply, Finset.sum_apply]
  funext i
  rw [e, per_sum]
  simp only [Function.comp_apply, Finset.sum_apply, per_smul, Dict.hAct]

theorem conj_mulVec (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h : Matrix (Fin n) (Fin n) E) (z : Fin n → Fin g → ℂ) :
    ((blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹) *ᵥ
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) =
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  have hH : (hMat X bas idx x)⁻¹ * hMat X bas idx x = 1 :=
    nonsing_inv_mul _ (isUnit_det_hMat (idx := idx) hs hx)
  have e3 : (blk n (hMat X bas idx x)⁻¹ *ᵥ
      fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) = fun p => z p.1 p.2 := by
    rw [blk_mulVec]
    funext p
    simp only [mulVec_mulVec, hH, one_mulVec]
  rw [← mulVec_mulVec, e3, ← mulVec_mulVec, actM_mulVec, blk_mulVec]

theorem exists_symplectic_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∃ s ∈ Matrix.symplecticGroup (Fin n × Fin g) ℚ, ∀ x ∈ X.dom, tauMat X bas idx x ∈ Siegel (Fin g) ∧ spAct s (blk n (tauMat X bas idx x)) = blk n (tauMat X bas idx x) ∧ (spDen s (blk n (tauMat X bas idx x))).det * ∏ i : Fin g, rowType X (idx i) h.det = 1 ∧ ∀ z : Fin n → Fin g → ℂ, (fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ z p.1) p.2) ᵥ* (spDen s (blk n (tauMat X bas idx x)))⁻¹ = fun p : Fin n × Fin g => (hMat X bas idx x *ᵥ Dict.hAct X idx h z p.1) p.2 := by
  intro E _ _ _ r X g bas idx n hs _ h hu
  have hcrd : ∀ (w : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ)) (k : Fin n),
      crd X bas (famOf bas w k) = Sum.elim (fun i => w.1 (k, i)) fun i => w.2 (k, i) := by
    intro w k
    simp only [famOf]
    exact crd_vecQ hs _
  obtain ⟨s, hsS, hact⟩ := GlobalTheory.SymplecticPeriods.exists_symplectic_action (Fin n × Fin g)
    (colMap hs h) (colMap_form hs hu)
  refine ⟨s, hsS, fun x hx => ?_⟩
  have hT : tauMat X bas idx x ∈ Siegel (Fin g) :=
    ⟨tauMat_isSymm (idx := idx) hs hx, tauMat_im_posDef (idx := idx) hs hx⟩
  have hB := blk_mem_siegel (n := n) hT
  have hUnit := isUnit_det_hMat (idx := idx) hs hx
  have key : ∀ u : (Fin n × Fin g → ℚ) × (Fin n × Fin g → ℚ),
      (blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹) *ᵥ
          (qv u.1 + blk n (tauMat X bas idx x) *ᵥ qv u.2) =
        qv (colMap hs h u).1 + blk n (tauMat X bas idx x) *ᵥ qv (colMap hs h u).2 := by
    intro u
    have ea : qv u.1 + blk n (tauMat X bas idx x) *ᵥ qv u.2 =
        fun p : Fin n × Fin g =>
          (hMat X bas idx x *ᵥ (fun k => per X x (famOf bas u k) ∘ idx) p.1) p.2 := by
      funext p
      rw [hMat_mulVec_per_crd idx hs hx, Pi.add_apply, blk_mulVec]
      simp only [Pi.add_apply, hcrd, Sum.elim_inl, Sum.elim_inr]
      rfl
    rw [ea, conj_mulVec idx hs hx h (fun k => per X x (famOf bas u k) ∘ idx)]
    funext p
    rw [← per_mul idx x h (famOf bas u) p.1, hMat_mulVec_per_crd idx hs hx, Pi.add_apply,
      Pi.add_apply, blk_mulVec]
    rfl
  obtain ⟨e1, e2⟩ := hact _ hB _ _ hB.1 key
  have hdetM : (blk n (hMat X bas idx x) * actM idx h * blk n (hMat X bas idx x)⁻¹).det =
      ∏ i, rowType X (idx i) h.det := by
    rw [det_mul, det_mul, mul_right_comm, ← det_mul, blk_mul, mul_nonsing_inv _ hUnit, blk_one,
      det_one, one_mul, det_actM]
  have hdeth : h.det ≠ 0 := by
    have := congrArg Matrix.det hu
    rw [det_mul, det_one] at this
    exact right_ne_zero_of_mul_eq_one this
  have hP : ∏ i, rowType X (idx i) h.det ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (map_ne_zero _).mpr hdeth
  rw [e2, det_transpose, det_nonsing_inv, Ring.inverse_eq_inv'] at hdetM
  have hD : (spDen s (blk n (tauMat X bas idx x))).det ≠ 0 := by
    intro hz
    rw [hz, _root_.inv_zero] at hdetM
    exact hP hdetM.symm
  refine ⟨hT, e1.symm, ?_, fun z => ?_⟩
  · rw [← hdetM, mul_inv_cancel₀ hD]
  · rw [← mulVec_transpose, ← e2]
    exact conj_mulVec idx hs hx h z

end GlobalTheory.ColumnSymplectic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KZeroOnFrConstEntire
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private theorem det_sgnM_eq_prod_sgn {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : (sgnM X).det = ∏ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  simp [sgnM, Matrix.det_diagonal]

theorem normSq_det_of_isONFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {X : Data E r} {x : Frame X.Ψ r} (hx : IsONFr X x) (τ : X.Ψ) :
    normSq (mat x τ).det = ‖(X.Gm.map τ.1).det‖⁻¹ := by

  have hdet := congrArg Matrix.det (hx τ)
  rw [GlobalTheory.SW.Slab.det_gram, det_sgnM_eq_prod_sgn X] at hdet
  have hG : (X.Gm.map τ.1).det = τ.1 X.Gm.det := (RingHom.map_det τ.1 X.Gm).symm
  have hn := congrArg norm hdet
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_prod] at hn
  simp only [GlobalTheory.SW.Slab.norm_sgn, Finset.prod_const_one] at hn
  rw [hG, Complex.normSq_eq_norm_sq]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hn]
  ring

theorem kZero_onFr_const_entire : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∃ κ : ℝ, 0 < κ ∧ ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ kZero X idx x x (0 : Fin n → Fin g → ℂ) 0 = κ) ∧ ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, Differentiable ℂ (fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) => kZero X idx x₁ x₂ p.1 p.2) := by
  intro E _ _ _ r X g q0 hr bas idx n _ _
  refine ⟨⟨∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖⁻¹ ^ (n / 2), ?_, fun x hx => ⟨?_, ?_⟩⟩, ?_⟩
  ·
    refine Finset.prod_pos fun τ _ => pow_pos (inv_pos.mpr (norm_pos_iff.mpr ?_)) _
    exact GlobalTheory.SW.KernSym.det_map_Gm X τ
  ·
    obtain ⟨δ₀, hδ₀, hs⟩ := GlobalTheory.SW.thin_slab E r X
    obtain ⟨-, hsub, hon, -⟩ := hs δ₀ hδ₀ le_rfl
    exact hsub (hon x hx)
  ·

    rw [GlobalTheory.SW.KernSym.kZero_ortho idx hx]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [normSq_det_of_isONFr hx τ]
  ·
    intro x₁ _ x₂ _ p
    exact (GlobalTheory.SW.KernSym.analyticAt_kZero X idx x₁ x₂ p).differentiableAt

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruenceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_unitary_congruence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (conjI 𝔪) → ∀ (A : GL (Fin r) E) (N : ℕ), ∃ ga : GL (Fin r) E, IsUn X ga ∧ ∃ s : 𝓞 E, IsCoprime (Ideal.span {s}) 𝔪 ∧ ∀ i j, ∃ b ∈ 𝔪 ^ N, (s : E) * ((ga : Matrix (Fin r) (Fin r) E) i j - (A : Matrix (Fin r) (Fin r) E) i j) = (b : E) := by
  first | exact @GlobalTheory.UnApprox.weak_approx | exact GlobalTheory.UnApprox.weak_approx | (intros; apply GlobalTheory.UnApprox.weak_approx <;> assumption)
end

