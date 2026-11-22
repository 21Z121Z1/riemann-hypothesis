import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGe
section
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem IsBallFam.subset_of_le_radius {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (h : IsBallFam Λ B) {r r' : ℝ} (hr : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := h.sub_mem r (r' - r) x 0 hx (h.zero_mem _ (by linarith))
  simpa using this

theorem IsBallFam.ncard_sq_le_of_ceil {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (h : IsBallFam Λ B) (hfin : ∀ R, (B R).Finite) {e E : ℝ} (he : 1 ≤ e)
    (hE : (⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2 ≤ E) :
    ((B e).ncard : ℝ) ^ 2 ≤ (B 1).ncard * (B E).ncard := by
  have hn2 : 2 * e ≤ (⌈2 * e⌉₊ : ℝ) := Nat.le_ceil _
  have hnpos : 0 < ⌈2 * e⌉₊ := by
    have : (0:ℝ) < (⌈2 * e⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  have key := GlobalTheory.T.encard_seminormBall_mul_le_convexity G Λ B h _ hnpos (hfin _)
  rw [← (hfin _).cast_ncard_eq, ← (hfin _).cast_ncard_eq, ← (hfin _).cast_ncard_eq,
    ← (hfin _).cast_ncard_eq] at key
  have key' : (B (⌈2 * e⌉₊ : ℝ)).ncard * (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard ≤
      (B 1).ncard * (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard := by
    have := key
    exact_mod_cast this
  have h1 : (B e).ncard ≤ (B (⌈2 * e⌉₊ : ℝ)).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius (by linarith)) (hfin _)
  have h2 : (B e).ncard ≤ (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius (by linarith)) (hfin _)
  have h3 : (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard ≤ (B E).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius hE) (hfin _)
  have : (B e).ncard ^ 2 ≤ (B 1).ncard * (B E).ncard := by
    calc (B e).ncard ^ 2 = (B e).ncard * (B e).ncard := sq _
      _ ≤ (B (⌈2 * e⌉₊ : ℝ)).ncard * (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard := Nat.mul_le_mul h1 h2
      _ ≤ (B 1).ncard * (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard := key'
      _ ≤ _ := Nat.mul_le_mul_left _ h3
  exact_mod_cast this

theorem log_ncard_ball_one_eventually_ge : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G)
    (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) →
    ∀ α β t₀ : ℝ, (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => Real.log ((B m (Real.exp (t * m))).ncard : ℝ) /
      (m : ℝ) ^ d) atTop (𝓝 (α + β * t))) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (α - ε) * (m : ℝ) ^ d ≤ Real.log ((B m 1).ncard : ℝ) := by
  intro G _ Λ B d _ hB hfin α β t₀ hlim ε hε
  obtain ⟨t, ht0, ht⟩ : ∃ t, t₀ ≤ t ∧ 0 ≤ t := ⟨max t₀ 0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨η, hη, hβη⟩ : ∃ η : ℝ, 0 < η ∧ β * η < ε := by
    refine ⟨ε / (2 * (|β| + 1)), by positivity, ?_⟩
    have hpos : 0 < 2 * (|β| + 1) := by positivity
    have hηe : ε / (2 * (|β| + 1)) * (2 * (|β| + 1)) = ε := div_mul_cancel₀ _ hpos.ne'
    have hη : 0 < ε / (2 * (|β| + 1)) := by positivity
    have hb : β * (ε / (2 * (|β| + 1))) ≤ |β| * (ε / (2 * (|β| + 1))) :=
      mul_le_mul_of_nonneg_right (le_abs_self β) hη.le
    nlinarith [mul_nonneg (abs_nonneg β) hη.le]
  have hw := ((hlim t ht0).const_mul 2).sub (hlim (2 * t + η) (by linarith))
  have hlt : α - ε < 2 * (α + β * t) - (α + β * (2 * t + η)) := by
    have : 2 * (α + β * t) - (α + β * (2 * t + η)) = α - β * η := by ring
    rw [this]; linarith
  have ev1 := hw.eventually (lt_mem_nhds hlt)
  have ev2 : ∀ᶠ m : ℕ in atTop, Real.log 12 ≤ η * m :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
  filter_upwards [ev1, ev2, eventually_ge_atTop 1] with m h1 h2 hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hmd : (0:ℝ) < (m:ℝ) ^ d := pow_pos hmpos d
  have he : 1 ≤ Real.exp (t * m) := Real.one_le_exp (mul_nonneg ht hmpos.le)
  have h12 : 12 ≤ Real.exp (η * m) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 12)]; exact Real.exp_le_exp.mpr h2
  have hE : (⌈2 * Real.exp (t * m)⌉₊ : ℝ) ^ 2 + (⌈2 * Real.exp (t * m)⌉₊ : ℝ) / 2 ≤
      Real.exp ((2 * t + η) * m) := by
    have hc : (⌈2 * Real.exp (t * m)⌉₊ : ℝ) ≤ 3 * Real.exp (t * m) := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.exp (t * m) by linarith); linarith
    have hc0 : (0:ℝ) ≤ ⌈2 * Real.exp (t * m)⌉₊ := Nat.cast_nonneg _
    rw [show (2 * t + η) * (m:ℝ) = t * m + t * m + η * m by ring, Real.exp_add, Real.exp_add]
    nlinarith [mul_le_mul hc hc hc0 (by linarith), mul_le_mul_of_nonneg_left h12
      (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp (t * m)) (by linarith : (0:ℝ) ≤ Real.exp (t * m)))]
  have hsq := (hB m).ncard_sq_le_of_ceil (hfin m) he hE
  have hpos : ∀ R, 0 ≤ R → (0:ℝ) < (B m R).ncard := fun R hR => by
    have := (Set.ncard_pos (hfin m R)).mpr ⟨0, (hB m).zero_mem R hR⟩
    exact_mod_cast this
  have hlog := Real.log_le_log (pow_pos (hpos _ (by linarith)) 2) hsq
  rw [Real.log_pow, Real.log_mul (hpos 1 zero_le_one).ne' (hpos _ (Real.exp_pos _).le).ne'] at hlog
  push_cast at hlog
  have hdiv : (2 * Real.log ((B m (Real.exp (t * m))).ncard) - Real.log ((B m (Real.exp ((2 * t + η) * m))).ncard))
      / (m:ℝ) ^ d ≤ Real.log ((B m 1).ncard) / (m:ℝ) ^ d :=
    div_le_div_of_nonneg_right (by linarith) hmd.le
  rw [sub_div, mul_div_assoc] at hdiv
  rw [← le_div_iff₀ hmd]
  linarith

end GlobalTheory.VolBr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxSubsetOfMemNhdsZero
section
open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.GamMul DiscreteGroups.sglob.LConv

namespace GlobalTheory.GamMul.NearOne

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eventually_valuation_sub_lt_one (a : k) : ∀ᶠ x in nhds a, valuation k (x - a) < 1 := by
  have h0 : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨1, one_ne_zero, subset_rfl⟩
  have hc : Filter.Tendsto (fun x : k => x - a) (nhds a) (nhds 0) := by
    have : Continuous (fun x : k => x - a) := by fun_prop
    simpa using this.tendsto a
  exact hc h0

theorem exists_box_subset_of_mem_nhds_zero {p q : ℕ} {S : Set (Matrix (Fin p) (Fin q) k)} (hS : S ∈ nhds 0) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ box p q d ⊆ S := by
  have hk : ∀ s ∈ nhds (0 : k), ∀ᶠ d in nhds (0 : k), {x : k | valuation k x ≤ valuation k d} ⊆ s := by
    intro s hs
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
    have h0 : {x : k | valuation k x < r} ∈ nhds (0 : k) :=
      (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mpr ⟨r, hr, subset_rfl⟩
    filter_upwards [h0] with d hd x hx
    exact hrs (lt_of_le_of_lt hx hd)
  have hS' : {x : Fin p → Fin q → k | Matrix.of x ∈ S} ∈ nhds (0 : Fin p → Fin q → k) := hS
  rw [nhds_pi, Filter.mem_pi'] at hS'
  obtain ⟨I, t, ht, hI⟩ := hS'
  have ht' : ∀ i, ∃ u : Fin q → Set k, (∀ j, u j ∈ nhds (0 : k)) ∧ Set.univ.pi u ⊆ t i := by
    intro i
    have h := ht i
    rw [nhds_pi, Filter.mem_pi'] at h
    obtain ⟨J, u, hu, hJ⟩ := h
    exact ⟨u, hu, fun x hx => hJ fun j _ => hx j trivial⟩
  choose u hu hut using ht'
  have hev : ∀ᶠ d in nhds (0 : k), valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j :=
    (eventually_valuation_sub_lt_one 0).and
      (Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hk _ (hu i j))
  have hne : ∃ d : k, d ≠ 0 ∧ valuation k (d - 0) < 1 ∧
      ∀ i j, {x : k | valuation k x ≤ valuation k d} ⊆ u i j := by
    have hd : (nhdsWithin (0 : k) {0}ᶜ).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
      intro s hs
      obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp hs
      obtain ⟨r', hr', hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
      obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective r
      have hy : y ≠ 0 := by simpa using hr
      refine ⟨r' * y, hrs ?_, mul_ne_zero (by simpa using hr') hy⟩
      show valuation k (r' * y) < valuation k y
      rw [map_mul]
      exact mul_lt_of_lt_one_left (zero_lt_iff.mpr hr) hr1
    exact (eventually_mem_nhdsWithin.and (hev.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ)))).exists
  obtain ⟨d, hd0, hd1, hdu⟩ := hne
  refine ⟨Units.mk0 d hd0, by simpa using hd1.le, fun X hX => hI fun i _ => hut i fun j _ => hdu i j (hX i j)⟩

theorem one_add_small_near_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ d : kˣ, valuation k (d : k) ≤ 1 ∧ ∀ N ∈ box n n d, ∃ A : GL (Fin n) k, A.val = 1 + N ∧ A ∈ U ∧
      valuation k (GeneralLinearGroup.det A : k) = 1 ∧ A⁻¹.val ∈ box n n 1 := by
  have hadd : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => 1 + N) (nhds 0) (nhds 1) := by
    have : Continuous (fun N : Matrix (Fin n) (Fin n) k => 1 + N) := by fun_prop
    simpa using this.tendsto 0
  have hdet : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N).det) (nhds 0) (nhds 1) := by
    have : Continuous (fun M : Matrix (Fin n) (Fin n) k => M.det) := continuous_id.matrix_det
    have h2 := (this.tendsto 1).comp hadd
    rw [det_one] at h2
    exact h2
  have hinv : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => (1 + N)⁻¹) (nhds 0) (nhds 1) := by
    have : ContinuousAt Inv.inv (1 : Matrix (Fin n) (Fin n) k) := by
      apply continuousAt_matrix_inv
      rw [det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h2 := this.tendsto.comp hadd
    rw [inv_one] at h2
    exact h2
  have hv : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, valuation k (1 + N).det = 1 := by
    filter_upwards [hdet (eventually_valuation_sub_lt_one 1)] with N hN
    have hN' : valuation k ((1 + N).det - 1) < 1 := hN
    have := Valuation.map_one_add_of_lt (valuation k) hN'
    simpa using this
  have hb : ∀ᶠ N : Matrix (Fin n) (Fin n) k in nhds 0, ∀ i j, valuation k ((1 + N)⁻¹ i j) ≤ 1 := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have hc : Continuous (fun M : Matrix (Fin n) (Fin n) k => M i j) := continuous_id.matrix_elem i j
    filter_upwards [((hc.tendsto 1).comp hinv) (eventually_valuation_sub_lt_one _)] with N hN
    have hN' : valuation k ((1 + N)⁻¹ i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := hN
    have h1 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have := Valuation.map_add_le (valuation k) hN'.le h1
    simpa using this
  have hval : ∀ N : Matrix (Fin n) (Fin n) k, valuation k (1 + N).det = 1 → (toGL (1 + N)).val = 1 + N := by
    intro N hN
    have hu : IsUnit (1 + N) := by
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro h
      rw [h] at hN
      simp at hN
    unfold toGL
    rw [dif_pos hu]
    rfl
  have hGL : Filter.Tendsto (fun N : Matrix (Fin n) (Fin n) k => toGL (1 + N)) (nhds 0) (nhds 1) := by
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    have h3 := hadd.prodMk_nhds ((MulOpposite.continuous_op.tendsto 1).comp hinv)
    have e : (Units.embedProduct _ (1 : GL (Fin n) k)) = (1, MulOpposite.op 1) := by simp
    rw [e]
    refine Filter.Tendsto.congr' ?_ h3
    filter_upwards [hv] with N hN
    simp only [Function.comp, Units.embedProduct_apply, Matrix.coe_units_inv, hval N hN]
  obtain ⟨d, hd, hS⟩ := exists_box_subset_of_mem_nhds_zero (hv.and (hb.and (hGL hU)))
  refine ⟨d, hd, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS hN
  refine ⟨toGL (1 + N), hval N h1, h3, ?_, fun i j => ?_⟩
  · rw [GeneralLinearGroup.val_det_apply, hval N h1, h1]
  · rw [Matrix.coe_units_inv, hval N h1]
    simpa using h2 i j

end GlobalTheory.GamMul.NearOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactCurveDerivative
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigCurve

theorem exists_unitary_matrix_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E))
    (hZ : star Z = -Z) :
    ∃ f : ℝ → Matrix (Fin a) (Fin a) (Cinf E), (∀ t, f t ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E))) ∧
      f 0 = 1 ∧ HasDerivAt (fun t => toL (f t)) (toL Z) 0 := by
  have hcs : ContinuousStar (Matrix (Fin a) (Fin a) (Cinf E)) := inferInstance
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (Cinf E)) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine ⟨fun t => NormedSpace.exp (t • Z), fun t => ?_, by simp, ?_⟩
  · refine @NormedSpace.exp_mem_unitary_of_mem_skewAdjoint _ _ _ _ _ ⟨hcs.continuous_star⟩ _ ?_
    rw [skewAdjoint.mem_iff, star_smul, hZ, star_trivial, smul_neg]
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
      LinearMap.toContinuousLinearMap
        { toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem exists_kinf_curve_tangent : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z → ∃ c : ℝ → Kinf E a, c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).1) (toL Z) 0 := by
  intro E _ _ a Z hZ
  obtain ⟨f, hu, h0, hd⟩ := exists_unitary_matrix_curve E a Z hZ
  exact ⟨fun t => ⟨f t, hu t⟩, Subtype.ext h0, hd⟩

end GlobalTheory.WigCurve

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqGeneratorFactorialBase
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.MBX
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GlobalVerticalUnit
open GlobalTheory.VerticalUnit

theorem exists_const_mul_eq_gen : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (Y : Scheme.{0}) (φ : Y ⟶ X.left) (p : Y ⟶ Sp K) (M : LB X.left) (c : LB.Gen (M.pull φ)), Smooth X.hom → QuasiCompact X.hom → GeometricallyConnected X.hom → IsPullback φ p X.hom (spMap (algebraMap R K)) → M.IsLB → c.IsGen → ∃ (a : Kˣ) (u : LB.Gen M), u.IsGen ∧ ∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), φ (r z) ∈ M.U i → (gm (r ≫ φ) z (M.U i) (u.s i)).val = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull φ).U fun _ => i) (c.s fun _ => i)).val := by
  intro R K _ _ _ _ _ _ _ X Y φ p M c hsm hqc hgc H hM hc
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ X.hom hsm hgc
  have : IsIntegral X.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian X.hom
  have : IsIntegral Y := DvrModel.isIntegral_of_geometricallyIntegral H
  have := isNormalScheme_of_smooth X.hom
  have := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : AlgebraicGeometry.IsNoetherian X.left := {}
  have hinj := IsFractionRing.injective R K
  have : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) H.flip
    (Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance))
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) H.flip
    (IsPreimmersion.of_isLocalization (nonZeroDivisors R))
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks φ
  have lift : ∀ x : X.left, (X.hom x).asIdeal = ⊥ → ∃ y, φ y = x := fun x hx => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum K)
      (PrimeSpectrum.ext (hx.trans (Ideal.comap_bot_of_injective _ hinj).symm))
    exact ⟨y, hy⟩
  have hφ : φ (genericPoint Y) ⤳ genericPoint X.left := by
    obtain ⟨y, hy⟩ := (Flat.generalizingMap φ).stableUnderGeneralization_range
      (genericPoint_specializes (φ (genericPoint Y))) ⟨_, rfl⟩
    exact hy ▸ (genericPoint_specializes y).map φ.continuous
  have hne : ∀ (V : X.left.Opens) [Nonempty V], Nonempty (φ ⁻¹ᵁ V) := fun V _ =>
    ⟨⟨_, hφ.mem_open V.isOpen (genericPoint_mem_opens V)⟩⟩
  have hne' : ∀ i [Nonempty (M.U i)], Nonempty ((M.pull φ).U fun _ => i) := fun i _ => by
    rw [DvrModel.pull_U]; exact hne _
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩
  have hb := ffMap_bijective φ hφ
  obtain ⟨r, hr⟩ : ∃ r : M.ι → X.left.functionField, ∀ i [Nonempty ((M.pull φ).U fun _ => i)],
      ffMap φ hφ (r i) = Y.germToFunctionField _ (c.s fun _ => i).val := by
    have : ∀ i, ∃ t : X.left.functionField, ∀ [Nonempty ((M.pull φ).U fun _ => i)],
        ffMap φ hφ t = Y.germToFunctionField _ (c.s fun _ => i).val := fun i => by
      by_cases h : Nonempty ((M.pull φ).U fun _ => i)
      · exact (hb.2 (Y.germToFunctionField _ (c.s fun _ => i).val)).imp fun _ h => h
      · exact ⟨0, @fun h' => (h h').elim⟩
    exact ⟨fun i => (this i).choose, fun i => (this i).choose_spec⟩
  let k : K →+* Γ(Y, ⊤) := (p.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let κ : K →+* X.left.functionField := (RingEquiv.ofBijective (ffMap φ hφ).hom hb).symm.toRingHom.comp
    ((Y.germToFunctionField ⊤).hom.comp k)
  have hκ : ∀ a, ffMap φ hφ (κ a) = Y.germToFunctionField ⊤ (constFn p ⊤ a) := fun a =>
    (RingEquiv.ofBijective (ffMap φ hφ).hom hb).apply_symm_apply _
  have hr0 : ∀ i x, x ∈ M.U i → r i ≠ 0 := fun i x hx h => by
    have : Nonempty (M.U i) := ⟨⟨x, hx⟩⟩
    have := hne' i
    have e := hr i
    rw [h, map_zero] at e
    exact ((Units.isUnit _).map _).ne_zero e.symm
  have hg : ∀ i j (x : X.left) (hi : x ∈ M.U i) (hj : x ∈ M.U j),
      haveI : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      r i = X.left.germToFunctionField (M.U i ⊓ M.U j) (M.g i j).val * r j := by
    intro i j x hi hj
    have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
    have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
    have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
    have := hne' i
    have := hne' j
    have := nonempty_inf_of_isIntegral ((M.pull φ).U fun _ => i) ((M.pull φ).U fun _ => j)
    refine hb.1 ?_
    have e := congrArg (Y.germToFunctionField _) (congrArg Units.val (hc (fun _ => i) fun _ => j))
    rw [Units.val_mul, map_mul, DvrModel.coe_pull_g, ← ffMap_germ φ hφ] at e
    rw [map_mul, hr, hr]
    exact (germToFunctionField_res _ _).symm.trans (e.trans (congrArg _ (germToFunctionField_res _ _)))
  have htr : ∀ i j x t, x ∈ M.U i → x ∈ M.U j → UnitAt x (t * r j) → UnitAt x (t * r i) := by
    intro i j x t hi hj h
    rw [hg i j x hi hj, mul_left_comm]
    exact UnitAt.mul ⟨Units.map (X.left.presheaf.germ (M.U i ⊓ M.U j) x ⟨hi, hj⟩).hom (M.g i j),
      X.left.presheaf.germ_stalkSpecializes_apply _ _ _⟩ h
  have hκR : ∀ b : R, κ (algebraMap R K b) = X.left.presheaf.germ ⊤ (genericPoint X.left) trivial (constFn X.hom ⊤ b) := fun b => hb.1 (by
    rw [hκ, ← app_constFn H.w, ← φ.appLE_eq_app]
    exact (ffMap_germ φ hφ ⊤ ⊤ le_top _).symm)
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_const_mul_unitAt_codimOne_of_factorialBase R K X.left X.hom κ hκR M.ι M.U r (LB.mem_of_cover hM) (fun i x hx => hr0 i x hx) htr (fun x hx => by
    obtain ⟨y, rfl⟩ := lift x hx
    obtain ⟨i, hi⟩ := LB.mem_of_cover hM (φ y)
    have : Nonempty (M.U i) := ⟨⟨_, hi⟩⟩
    have := hne' i
    exact ⟨i, hi, unitAt_of_isUnit φ hφ (Units.isUnit _) ((DvrModel.pull_U M φ _).ge hi) (hr i)⟩)
  have hu : ∀ i, ∃ v : Γ(X.left, M.U i)ˣ, ∀ [Nonempty (M.U i)],
      X.left.germToFunctionField (M.U i) v.val = κ a * r i := fun i => by
    by_cases h : Nonempty (M.U i)
    · obtain ⟨v, hv⟩ := exists_unit_eq (M.U i) (κ a * r i)
        (mul_ne_zero ((map_ne_zero κ).2 a.ne_zero) (hr0 i _ h.some.2)) (ha i)
      exact ⟨v, @fun _ => hv⟩
    · exact ⟨1, @fun h' => (h h').elim⟩
  choose u hu using hu
  refine ⟨a, ⟨u⟩, fun i j => ?_, fun i Z rr z hz => ?_⟩
  · by_cases h : Nonempty (M.U i ⊓ M.U j : X.left.Opens)
    · obtain ⟨⟨x, hi, hj⟩⟩ := h
      have : Nonempty (M.U i) := ⟨⟨x, hi⟩⟩
      have : Nonempty (M.U j) := ⟨⟨x, hj⟩⟩
      have : Nonempty (M.U i ⊓ M.U j : X.left.Opens) := ⟨⟨x, hi, hj⟩⟩
      refine Units.ext (X.left.germToFunctionField_injective (M.U i ⊓ M.U j) ?_)
      show X.left.germToFunctionField _ (X.left.presheaf.map (homOfLE _).op (u i).val) =
        X.left.germToFunctionField _ ((M.g i j).val * X.left.presheaf.map (homOfLE _).op (u j).val)
      rw [map_mul, germToFunctionField_res, germToFunctionField_res, hu, hu, hg i j x hi hj]
      ring
    · exact unit_ext fun x hx => (h ⟨⟨x, hx⟩⟩).elim
  · have hm : rr z ∈ (M.pull φ).U fun _ => i := mem_pull.2 hz
    have h₂ : ((M.pull φ).U fun _ => i) ≤ φ ⁻¹ᵁ M.U i := fun y hy => mem_pull.1 hy
    have : Nonempty ((M.pull φ).U fun _ => i) := ⟨⟨_, hm⟩⟩
    have : Nonempty (M.U i) := ⟨⟨_, hz⟩⟩
    have hW : (φ.appLE (M.U i) _ h₂).hom (u i).val = constFn p _ (a : K) * (c.s fun _ => i).val := by
      refine Y.germToFunctionField_injective _ ((ffMap_germ φ hφ _ _ h₂ _).symm.trans ?_)
      rw [hu, map_mul, map_mul, hκ, hr]
      refine congrArg₂ (· * ·) ?_ rfl
      exact (germToFunctionField_res (le_top : ((M.pull φ).U fun _ => i) ≤ ⊤) _).symm.trans
        (congrArg _ (res_appLE_apply p _ _ _))
    show (gm (rr ≫ φ) z (M.U i) (u i)).val = _
    rw [← gs_unit (rr ≫ φ) z _ hz, ← gs_unit rr z _ hm, ← GlobalTheory.OpenPartUnit.gs_appLE rr φ z _ _ h₂ hm, hW,
      gs_mul rr z _ hm]
    refine congrArg (· * _) ?_
    exact GlobalTheory.OpenPartUnit.gs_appLE rr p z ⊤ _ _ hm _

end GlobalTheory.GlobalVerticalUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvalRegularFunctionsAtFieldPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eval_regular_functions_at_fieldPoint : ∀ (F : Type) [Field F] (Y : Var F) (Z : Scheme.{0}) [IsIntegral Z] (k : Type) [Field k] (w : Sp k ⟶ Z), ∃ ev : (algebraMap (Z.presheaf.stalk (w (IsLocalRing.closedPoint k))) Z.functionField).range →+* k, (∀ u, ev u ≠ 0 ↔ UnitAt (w (IsLocalRing.closedPoint k)) (u : Z.functionField)) ∧ ∀ (q : Z ⟶ Y.X) [IsDominant q] (u : Y.Fn), RegAt (q (w (IsLocalRing.closedPoint k))) u → ∃ h, ev ⟨functionFieldMap q u, h⟩ = (ratOf Y).val (w ≫ q) u := by
  first | exact @GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint | exact GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint | (intros; apply GlobalTheory.FlagPush.exists_eval_regular_at_fieldPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicAddRealChartPoint
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem exists_realZero_add_iotaVF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ)
    (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) (ι : (InfinitePlace F → ℂ) →+ AEF F E), IsChartF θ ι →
      ∀ w : WOF F E nS nT, ∃ (u : WOF F E nS nT) (v : IxF F nS nT → ℂ), u.map (infPartF F E) = 0 ∧ w = u + iotaVF ι v := by
  intro F E _ _ _ _ _ nS nT θ ι hι w
  refine ⟨w - iotaVF ι (piWF θ w), piWF θ w, ?_, by abel⟩
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  set a := infPartF F E ((w - iotaVF ι (piWF θ w)) i j) with ha
  have hθ : ∀ w', θ w' a = 0 := by
    intro w'
    rw [ha, Matrix.sub_apply, map_sub, map_sub]
    simp only [iotaVF, piWF, Matrix.of_apply]
    rw [hι.comp]
    exact sub_self _
  have h0 := hι.ext (Formalism.L2.Fam.ThC.pairE a 0) (Formalism.L2.Fam.ThC.snd_pairE a 0) (by
    intro w'
    have : infPartF F E (Formalism.L2.Fam.ThC.pairE a 0) = a := Formalism.L2.Fam.ThC.fst_pairE a 0
    rw [this]; exact hθ w')
  have : infPartF F E (Formalism.L2.Fam.ThC.pairE a 0) = a := Formalism.L2.Fam.ThC.fst_pairE a 0
  rw [← this, h0, map_zero]

end GlobalTheory.RealWeilF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePointsRegularDivAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory

theorem unitAt_fromSpec_fnOf_iff {X : Scheme.{0}} [IsIntegral X] {V : X.Opens} (hA : IsAffineOpen V)
    (hV : genericPoint X ∈ V) (Q : PrimeSpectrum Γ(X, V)) (r : Γ(X, V)) :
    UnitAt (hA.fromSpec Q) (fnOf V hV r) ↔ r ∉ Q.asIdeal := by
  have hz : hA.fromSpec Q ∈ V := by
    have h : hA.fromSpec Q ∈ Set.range hA.fromSpec := ⟨Q, rfl⟩
    rw [hA.range_fromSpec] at h
    exact h
  rw [unitAt_fnOf_iff hz]
  have h := hA.fromSpec_preimage_basicOpen r
  change Q ∈ hA.fromSpec ⁻¹ᵁ X.basicOpen r ↔ _
  rw [h]
  exact PrimeSpectrum.mem_basicOpen _ _

theorem exists_finite_points_regAt_div_of_affine :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (V : X.Opens), IsAffineOpen V → ∀ (hV : genericPoint X ∈ V) (a : Γ(X, V)), fnOf V hV a ≠ 0 → ∃ T : Set X, T.Finite ∧ ∀ x ∈ V, ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ T, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / fnOf V hV a) → RegAt x (g / fnOf V hV a) := by
  intro X _ _ V hA hV a ha
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hA⟩
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  obtain ⟨S, hS, H⟩ := exists_finite_primes_dvd_of_dvd_mul_localization Γ(X, V) a ha0
  refine ⟨(fun Q : PrimeSpectrum Γ(X, V) => hA.fromSpec Q) '' S, hS.image _, ?_⟩
  rintro x hx _ _ ⟨τ, rfl⟩ hτ ⟨g, rfl⟩ ⟨c, hc⟩
  set P : PrimeSpectrum Γ(X, V) := hA.primeIdealOf ⟨x, hx⟩ with hP
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) P.asIdeal := hA.isLocalization_stalk ⟨x, hx⟩
  have hgerm : ∀ r : Γ(X, V), algebraMap (X.presheaf.stalk x) X.functionField
      (algebraMap Γ(X, V) (X.presheaf.stalk x) r) = fnOf V hV r := fun r => algebraMap_germ hx r
  let e : Localization.AtPrime P.asIdeal ≃ₐ[Γ(X, V)] X.presheaf.stalk x :=
    IsLocalization.algEquiv P.asIdeal.primeCompl _ _
  have hd : algebraMap Γ(X, V) (X.presheaf.stalk x) a ∣ g * τ := by
    refine ⟨c, IsFractionRing.injective (X.presheaf.stalk x) X.functionField ?_⟩
    rw [map_mul, map_mul, hgerm, hc, mul_div_cancel₀ _ ha]
  have key := H P (e.symm τ) (e.symm g) ?_ ?_
  · obtain ⟨d, hd⟩ := map_dvd e key
    rw [e.commutes, e.apply_symm_apply] at hd
    exact ⟨d, by rw [hd, map_mul, hgerm, mul_div_cancel_left₀ _ ha]⟩
  · intro Q hQ hQP hm
    have hsp : hA.fromSpec Q ⤳ x := by
      have h := ((PrimeSpectrum.le_iff_specializes Q P).1 hQP).map hA.fromSpec.continuous
      rwa [hP, hA.fromSpec_primeIdealOf] at h
    have hu := hτ _ ⟨Q, hQ, rfl⟩ hsp
    obtain ⟨⟨q, t⟩, hqt⟩ := (IsLocalization.mem_map_algebraMap_iff P.asIdeal.primeCompl _).1 hm
    have h1 := congrArg (fun y => algebraMap (X.presheaf.stalk x) X.functionField (e y)) hqt
    simp only [map_mul, e.commutes, e.apply_symm_apply, hgerm] at h1
    have ht := (unitAt_fromSpec_fnOf_iff hA hV Q t).2 fun h => t.2 (hQP h)
    have h2 := hu.mul ht
    rw [h1] at h2
    exact (unitAt_fromSpec_fnOf_iff hA hV Q q).1 h2 q.2
  · have h := map_dvd e.symm hd
    rwa [e.symm.commutes, map_mul] at h

end GlobalTheory
end

