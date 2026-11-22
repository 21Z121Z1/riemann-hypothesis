import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.L2LocalComponents.Summand

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LinChange
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem linearMap_comp_eq_on_smul_of_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (A B : V →L[ℝ] V)
    (h1 : ∀ x, B (A x) = x) (h2 : ∀ x, A (B x) = x) (f : V → ℂ) :
    ∫ x, f (A x) ∂μ = ((|(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| : ℝ) : ℂ) * ∫ x, f x ∂μ := by
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.equivOfInverse A B h1 h2
  have hd : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hm : MeasurableEmbedding (A : V →ₗ[ℝ] V) := e.toHomeomorph.measurableEmbedding
  have := hm.integral_map (μ := μ) f
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at this
  rw [← Complex.real_smul, this]
  rfl

theorem UpperTheory.V.Af.Smo.linChange :
    UpperTheory.V.Af.Smo.LinChange := by
  intro E _ _ n
  refine ⟨fun s => ((|(LinearMap.det (lmul (toL s.val) : Lie E n →ₗ[ℝ] Lie E n))⁻¹| : ℝ) : ℂ), ?_, fun s f => ?_⟩
  · have : (lmul (toL (1 : GL (Fin n) (Rinf E)).val) : Lie E n →ₗ[ℝ] Lie E n) = LinearMap.id :=
      LinearMap.ext fun x => one_mul (Matrix.of x)
    simp only [this]
    simp
  · haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
    haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    exact linearMap_comp_eq_on_smul_of_eq volume (lmul (toL s.val)) (lmul (toL (s⁻¹).val))
      (fun x => s.inv_mul_cancel_left (Matrix.of x)) (fun x => s.mul_inv_cancel_left (Matrix.of x)) f
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocDual
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one {G : Type} [LinearOrderedCommGroupWithZero G] (ua g ux p : G) (hua : ua ≠ 0)
    (hg : 0 < g) (hgx : g ≤ ux) (hp : p < 1) (hp0 : p ≠ 0) :
    ua * ux⁻¹ < ua * g⁻¹ * p⁻¹ := by
  have h1 : ux⁻¹ ≤ g⁻¹ := inv_anti₀ hg hgx
  have h2 : ua * ux⁻¹ ≤ ua * g⁻¹ := by gcongr
  have h3 : 1 < p⁻¹ := one_lt_inv₀ (zero_lt_iff.mpr hp0) |>.mpr hp
  have h4 : 0 < ua * g⁻¹ := by
    apply zero_lt_iff.mpr
    exact mul_ne_zero hua (inv_ne_zero hg.ne')
  calc ua * ux⁻¹ ≤ ua * g⁻¹ := h2
    _ = ua * g⁻¹ * 1 := (mul_one _).symm
    _ < ua * g⁻¹ * p⁻¹ := mul_lt_mul_of_pos_left h3 h4

private theorem mul_lt_of_lt_mul_inv_of_lt {G : Type} [LinearOrderedCommGroupWithZero G] (q y r g1 : G) (hr : 0 < r)
    (hy : y < r) (hq : q < g1 * r⁻¹) : q * y < g1 := by
  calc q * y ≤ q * r := by gcongr
    _ < g1 * r⁻¹ * r := mul_lt_mul_of_pos_right hq hr
    _ = g1 := by rw [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

theorem UpperTheory.V.Af.Smo.locDual :
    UpperTheory.V.Af.Smo.LocDual := by
  intro E _ _ w ψ hψ V hV
  obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (AddChar.ext _ _ fun x => by simpa using h x)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : HeightOneSpectrum.adicCompletion E w)
  obtain ⟨γ₁, hγ₁⟩ := Valued.mem_nhds_zero.mp hC0
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  have hvπ : Valued.v (π₀ : HeightOneSpectrum.adicCompletion E w) = WithZero.exp (-1 : ℤ) := by
    simp [hπ₀]
  have hπ0 : (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvπ
    exact WithZero.zero_ne_coe hvπ
  have hπ1 : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) < 1 := by
    rw [Valuation.restrict_lt_one_iff, hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπn : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, hvπ]
    exact WithZero.exp_ne_zero
  have hua : Valued.v.restrict a ≠ 0 := by simp [ha0]
  set R := Units.mk0 (Valued.v.restrict a * (γ : _)⁻¹ *
    (Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w))⁻¹)
    (mul_ne_zero (mul_ne_zero hua γ⁻¹.ne_zero) (inv_ne_zero hπn)) with hR
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (γ₁ * R⁻¹)
  refine ⟨Valued.v.restrict.ltAddSubgroup R, ?_, ?_, ?_⟩
  · rw [Valuation.coe_ltAddSubgroup]
    exact Valued.isOpen_ball _ _
  · rw [Valuation.coe_ltAddSubgroup]
    refine IsCompact.of_isClosed_subset
      (hC.image (continuous_const.mul continuous_id :
        Continuous fun z : HeightOneSpectrum.adicCompletion E w =>
          ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n)⁻¹ * z))
      (Valued.isClosed_ball _ _) ?_
    intro y hy
    refine ⟨(π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y, hγ₁ ?_, ?_⟩
    · show Valued.v.restrict ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y) < γ₁
      rw [map_mul, map_pow]
      refine mul_lt_of_lt_mul_inv_of_lt _ _ _ _ (zero_lt_iff.mpr R.ne_zero) hy ?_
      simpa using hn
    · exact inv_mul_cancel_left₀ (pow_ne_zero n hπ0) y
  · intro x hx
    by_contra hxV
    have hxg : (γ : _) ≤ Valued.v.restrict x := by
      by_contra h
      push_neg at h
      exact hxV (hγ h)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hxg
      exact γ.ne_zero (le_antisymm hxg zero_le')
    have hy : a * x⁻¹ ∈ Valued.v.restrict.ltAddSubgroup R := by
      rw [← SetLike.mem_coe, Valuation.coe_ltAddSubgroup]
      show Valued.v.restrict (a * x⁻¹) < R
      rw [map_mul, map_inv₀, hR, Units.val_mk0, Units.val_inv_eq_inv_val]
      exact mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one _ _ _ _ hua (zero_lt_iff.mpr γ.ne_zero) hxg hπ1 hπn
    have h1 := hx _ hy
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    exact ha h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocKir
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_conj_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G) (s : Finset G) : ∃ U₁ : OpenSubgroup G, ∀ u ∈ U₁, ∀ x ∈ s, x⁻¹ * u * x ∈ U := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, by simp⟩
  | insert a s _ ih =>
    obtain ⟨V, hV⟩ := ih
    have hc : Continuous (MulAut.conj a⁻¹).toMonoidHom := by
      change Continuous fun u : G => a⁻¹ * u * a⁻¹⁻¹
      fun_prop
    refine ⟨V ⊓ U.comap (MulAut.conj a⁻¹).toMonoidHom hc, fun u hu x hx => ?_⟩
    obtain ⟨h1, h2⟩ := OpenSubgroup.mem_inf.1 hu
    rcases Finset.mem_insert.1 hx with rfl | hx
    · have h3 : x⁻¹ * u * x⁻¹⁻¹ ∈ U := OpenSubgroup.mem_comap.1 h2
      rwa [inv_inv] at h3
    · exact hV u h1 x hx

private theorem supN_one {R : Type} [CommRing R] {n : ℕ} : supN (1 : Matrix (Fin n) (Fin n) R) = 0 := by
  unfold supN
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne (by rintro rfl; omega)
  · rfl

private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

private theorem isWh_comb {R : Type} [CommRing R] {n : ℕ} {ψ : R → ℂ} {W : GL (Fin n) R → ℂ} (hW : IsWh ψ W)
    (c : GL (Fin n) R →₀ ℂ) : IsWh ψ (comb c W) := by
  intro ν hν g
  unfold comb
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [mul_assoc, hW ν hν]
  ring

theorem UpperTheory.V.Af.Smo.locKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.Smo.LocStep → UpperTheory.V.Af.Smo.LocKir := by
  classical
  intro hcol hrow hstep E _ _ w ψ h0 h1 n m hm U
  induction m with
  | zero =>
    refine ⟨Finsupp.single 1 1, fun p => ψ (supN p.val), ?_, fun W hW _ p hp => ?_⟩
    · simp only [Units.val_one, supN_one, AddChar.map_zero_eq_one]
    · unfold comb
      rw [Finsupp.sum_single_index (by simp), one_mul, hW p hp]
  | succ m ih =>
    obtain ⟨c₀, H₀, hH₀, hc₀⟩ := ih (by omega)
    obtain ⟨U₁, hU₁⟩ := exists_conj_le U c₀.support
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨c₁, h, hh1, hh, hc₁⟩ := hstep E w ψ h0 h1 n m' hm U₁
    obtain ⟨c, -, hc⟩ := exists_comb_comb c₁ c₀
    have hσ : ∃ σ : (Fin n → w.adicCompletion E) → GL (Fin n) (w.adicCompletion E),
        ∀ ξ (s : GL (Fin n) (w.adicCompletion E)), s.val = rowM m' ξ → σ ξ = s := by
      refine ⟨fun ξ => if e : ∃ s : GL (Fin n) (w.adicCompletion E), s.val = rowM m' ξ then e.choose else 1,
        fun ξ s hs => ?_⟩
      have e : ∃ s : GL (Fin n) (w.adicCompletion E), s.val = rowM m' ξ := ⟨s, hs⟩
      simp only [dif_pos e]
      exact Units.ext (e.choose_spec.trans hs.symm)
    obtain ⟨σ, hσ⟩ := hσ
    refine ⟨c, fun p => h (p.val m') * H₀ (p * (σ (p.val m'))⁻¹), ?_, fun W hW hWU p hp => ?_⟩
    · have : σ ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) m') = 1 := hσ _ 1 (rowM_one m').symm
      simp only [Units.val_one, hh1, this, inv_one, mul_one, one_mul, hH₀]
    · have hinv : ∀ g, ∀ u ∈ U₁, comb c₀ W (g * u) = comb c₀ W g := by
        intro g u hu
        unfold comb
        refine Finsupp.sum_congr fun x hx => ?_
        rw [← hWU (g * x) _ (hU₁ u hu x hx)]
        congr 2
        group
      rw [hc, hc₁ (comb c₀ W) hinv p (p.val m') ?_]
      · by_cases hz : h (p.val m') = 0
        · simp only [hz, zero_mul]
        · obtain ⟨s, hsU, hs⟩ := hh _ hz
          simp only [hσ _ s hs]
          rw [← hinv p s⁻¹ (U₁.inv_mem hsU), hc₀ W hW hWU _ (hrow _ n m' p s hp hs), mul_assoc]
      · intro u t ht
        obtain ⟨ν, hν, e1, e2⟩ := hcol _ n m' hm p hp u
        have e : p * t = ν * p := Units.ext (by rw [Units.val_mul, Units.val_mul, ht, e2])
        rw [e, isWh_comb hW c₀ ν hν, e1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocStep
section
noncomputable section

open Matrix Topology

namespace UpperTheory.V.Af.Smo

section Alg

variable {R : Type} [CommRing R] {n : ℕ}

private theorem colM_mul_neg (m : Fin n) (u v : Fin n → R) (huv : u + v = 0) : colM m u * colM m v = 1 := by
  have h0 : (Matrix.of fun (i j : Fin n) => if i ≤ m ∧ j.val = m.val + 1 then u i else 0) *
      (Matrix.of fun (i j : Fin n) => if i ≤ m ∧ j.val = m.val + 1 then v i else 0) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [Matrix.of_apply]
    by_cases h1 : k ≤ m
    · have : ¬ (i ≤ m ∧ k.val = m.val + 1) := fun h => by
        have := Fin.le_def.1 h1
        omega
      rw [if_neg this, zero_mul]
    · have : ¬ (k ≤ m ∧ j.val = m.val + 1) := fun h => h1 h.1
      rw [if_neg this, mul_zero]
  unfold colM
  rw [add_mul, mul_add, mul_add, h0, one_mul, one_mul, mul_one, add_zero, add_assoc, add_eq_left]
  ext i j
  simp only [Matrix.add_apply, Matrix.of_apply, Matrix.zero_apply]
  split_ifs
  · rw [add_comm]; exact congrFun huv i
  · simp

private def colU (m : Fin n) (u : Fin n → R) : GL (Fin n) R :=
  ⟨colM m u, colM m (-u), colM_mul_neg m _ _ (by simp), colM_mul_neg m _ _ (by simp)⟩

private def dlt (m : Fin n) (ξ : Fin n → R) : (Fin n → R) →+ R where
  toFun u := dotLe m ξ u - u m
  map_zero' := by simp [dotLe]
  map_add' u v := by
    have : dotLe m ξ (u + v) = dotLe m ξ u + dotLe m ξ v := by
      unfold dotLe
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · simp [mul_add]
      · simp
    rw [this, Pi.add_apply]; ring

private theorem dlt_apply (m : Fin n) (ξ u : Fin n → R) : dlt m ξ u = dotLe m ξ u - u m := rfl

private theorem dlt_one (m : Fin n) (u : Fin n → R) : dlt m ((1 : Matrix (Fin n) (Fin n) R) m) u = 0 := by
  rw [dlt_apply, sub_eq_zero]
  unfold dotLe
  rw [Finset.sum_eq_single m]
  · simp
  · intro j _ hj
    simp [Matrix.one_apply_ne hj.symm]
  · simp

private theorem dlt_single (m : Fin n) (ξ : Fin n → R) (j : Fin n) (hj : j ≤ m) (y : R) :
    dlt m ξ (Pi.single j y) = (ξ j - (1 : Matrix (Fin n) (Fin n) R) m j) * y := by
  rw [dlt_apply]
  unfold dotLe
  rw [Finset.sum_eq_single j]
  · by_cases h : m = j
    · subst h; simp [sub_mul]
    · simp [hj, Matrix.one_apply_ne h, Pi.single_eq_of_ne h]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

end Alg

section Top

variable {K : Type} [NormedField K] [CompleteSpace K] {n : ℕ}

private theorem img_nhds (U : OpenSubgroup (GL (Fin n) K)) :
    {M : Matrix (Fin n) (Fin n) K | ∃ s ∈ U, s.val = M} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) K) := by
  letI I := Matrix.linftyOpNormedRing (n := Fin n) (α := K)
  have hcs : @CompleteSpace (Matrix (Fin n) (Fin n) K) I.toMetricSpace.toPseudoMetricSpace.toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin n → Fin n → K))
  have h := (@Units.isOpenMap_val (Matrix (Fin n) (Fin n) K) I
    (@instHasSummableGeomSeriesOfCompleteSpace _ I hcs)) _ U.isOpen
  exact h.mem_nhds ⟨1, U.one_mem, rfl⟩

private theorem col_nhds (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∀ᶠ u in 𝓝 (0 : Fin n → K), ∃ s ∈ U, s.val = colM m u := by
  have hc : Continuous fun u : Fin n → K => colM m u := by
    unfold colM
    refine continuous_const.add (continuous_matrix fun i j => ?_)
    simp only [Matrix.of_apply]
    split_ifs
    · exact continuous_apply i
    · exact continuous_const
  have h0 : colM m (0 : Fin n → K) = 1 := by
    ext i j; simp [colM]
  have := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at this
  exact this (img_nhds U)

private theorem row_nhds (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∃ V ∈ 𝓝 (0 : K), ∀ ξ : Fin n → K, (∀ j, j ≤ m → ξ j - (1 : Matrix (Fin n) (Fin n) K) m j ∈ V) →
      ∃ s ∈ U, s.val = rowM m ξ := by
  have hc : Continuous fun u : Fin n → K => rowM m (u + (1 : Matrix (Fin n) (Fin n) K) m) := by
    unfold rowM
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    split_ifs
    · exact (continuous_apply j).add continuous_const
    · exact continuous_const
  have h0 : rowM m ((0 : Fin n → K) + (1 : Matrix (Fin n) (Fin n) K) m) = 1 := by
    ext i j
    simp only [rowM, Matrix.of_apply, zero_add]
    split_ifs with h
    · rw [h.1]
    · rfl
  have h1 := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at h1
  obtain ⟨ε, hε, h2⟩ := Metric.mem_nhds_iff.1 (h1 (img_nhds U))
  refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds _ hε, fun ξ hξ => ?_⟩
  have h3 : (fun j => if j ≤ m then ξ j - (1 : Matrix (Fin n) (Fin n) K) m j else 0) ∈
      Metric.ball (0 : Fin n → K) ε := by
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    split_ifs with h
    · exact hξ j h
    · simpa using hε
  obtain ⟨s, hs, e⟩ := h2 h3
  refine ⟨s, hs, e.trans ?_⟩
  ext i j
  simp only [rowM, Matrix.of_apply, Pi.add_apply]
  by_cases h : i = m ∧ j ≤ m
  · simp [h]
  · rw [if_neg h, if_neg h]

private theorem step_gen (hA : AvgChar) (ψ : AddChar K ℂ) (hψ : ∀ᶠ x in 𝓝 (0 : K), ψ x = 1)
    (hD : ∀ V ∈ 𝓝 (0 : K), ∃ L : AddSubgroup K, IsOpen (L : Set K) ∧ IsCompact (L : Set K) ∧
      ∀ x, (∀ y ∈ L, ψ (x * y) = 1) → x ∈ V) (m : Fin n) (U : OpenSubgroup (GL (Fin n) K)) :
    ∃ (c : GL (Fin n) K →₀ ℂ) (h : (Fin n → K) → ℂ),
      h ((1 : Matrix (Fin n) (Fin n) K) m) = 1 ∧ (∀ ξ, h ξ ≠ 0 → ∃ s ∈ U, s.val = rowM m ξ) ∧
      ∀ W : GL (Fin n) K → ℂ, (∀ g, ∀ u ∈ U, W (g * u) = W g) → ∀ p ξ,
        (∀ u (t : GL (Fin n) K), t.val = colM m u → W (p * t) = ψ (dotLe m ξ u) * W p) →
        comb c W p = h ξ * W p := by
  classical
  obtain ⟨V, hV, hrow⟩ := row_nhds m U
  obtain ⟨L₁, ho, hc, hL₁⟩ := hD V hV
  let L : AddSubgroup (Fin n → K) := AddSubgroup.pi Set.univ fun _ => L₁
  have hLo : IsOpen (L : Set (Fin n → K)) := isOpen_set_pi Set.finite_univ fun _ _ => ho
  have hLc : IsCompact (L : Set (Fin n → K)) := isCompact_univ_pi fun _ => hc
  let N : Set (Fin n → K) := {u | u ∈ L ∧ (∃ s ∈ U, s.val = colM m u) ∧ ψ (u m) = 1}
  have hN : N ∈ 𝓝 (0 : Fin n → K) := by
    refine Filter.inter_mem (hLo.mem_nhds L.zero_mem) (Filter.inter_mem (col_nhds m U) ?_)
    exact (continuous_apply m).continuousAt (x := (0 : Fin n → K)) hψ
  let L₀ := AddSubgroup.closure N
  have hle : L₀ ≤ L := (AddSubgroup.closure_le _).2 fun u hu => hu.1
  have hL₀ : IsOpen (L₀ : Set (Fin n → K)) :=
    L₀.isOpen_of_mem_nhds (Filter.mem_of_superset hN AddSubgroup.subset_closure)
  have hidx : L₀.relIndex L ≠ 0 := by
    haveI : CompactSpace L := isCompact_iff_compactSpace.1 hLc
    have := AddSubgroup.quotient_finite_of_isOpen (L₀.addSubgroupOf L) (hL₀.preimage continuous_subtype_val)
    exact AddSubgroup.index_ne_zero_of_finite
  obtain ⟨T, hT, hTL, hsum⟩ := hA _ L₀ L hle hidx
  have hcard : (T.card : ℂ) ≠ 0 := by exact_mod_cast hT.card_pos.ne'
  refine ⟨∑ t ∈ T, Finsupp.single (colU m t) ((T.card : ℂ)⁻¹ * ψ (-t m)),
    fun ξ => if ∀ u ∈ L, ψ (dlt m ξ u) = 1 then 1 else 0, ?_, fun ξ hξ => ?_, fun W hW p ξ hp => ?_⟩
  · simp [dlt_one]
  · have h1 : ∀ u ∈ L, ψ (dlt m ξ u) = 1 := by
      by_contra h
      exact hξ (if_neg h)
    refine hrow ξ fun j hj => hL₁ _ fun y hy => ?_
    rw [← dlt_single m ξ j hj]
    refine h1 _ fun k _ => ?_
    by_cases h : k = j
    · subst h; simpa using hy
    · rw [Pi.single_eq_of_ne h]; exact L₁.zero_mem
  · have e1 : comb (∑ t ∈ T, Finsupp.single (colU m t) ((T.card : ℂ)⁻¹ * ψ (-t m))) W p =
        (T.card : ℂ)⁻¹ * (∑ t ∈ T, ψ (dlt m ξ t)) * W p := by
      unfold comb
      rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; ring), Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finsupp.sum_single_index (by simp), hp t (colU m t) rfl, dlt_apply, sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    rw [e1]
    by_cases h0 : W p = 0
    · simp [h0]
    congr 1
    dsimp only
    split_ifs with h
    · rw [Finset.sum_congr rfl fun t ht => h t (hTL t ht)]
      simp [hcard]
    · push Not at h
      have h2 : ∀ x ∈ L₀, ψ.compAddMonoidHom (dlt m ξ) x = 1 := by
        intro x hx
        induction hx using AddSubgroup.closure_induction with
        | mem u hu =>
          obtain ⟨-, ⟨s, hs, e⟩, h3⟩ := hu
          have h4 := hp u s e
          rw [hW p s hs] at h4
          have h5 : ψ (dotLe m ξ u) = 1 := mul_right_cancel₀ h0 (by rw [← h4, one_mul])
          rw [AddChar.compAddMonoidHom_apply, dlt_apply, AddChar.map_sub_eq_div, h5, h3, div_one]
        | zero => simp
        | add x y _ _ hx hy => rw [AddChar.map_add_eq_mul, hx, hy, one_mul]
        | neg x _ hx => rw [AddChar.map_neg_eq_inv, hx, inv_one]
      have := hsum _ h2 h
      simp only [AddChar.compAddMonoidHom_apply] at this
      rw [this, mul_zero]

end Top

end UpperTheory.V.Af.Smo

theorem UpperTheory.V.Af.Smo.locStep :
    UpperTheory.V.Af.Smo.AvgChar → UpperTheory.V.Af.Smo.LocDual → UpperTheory.V.Af.Smo.LocStep := by
  intro hA hD E _ _ w ψ hψ h1 n m _ U
  exact UpperTheory.V.Af.Smo.step_gen hA ψ hψ (hD E w ψ h1) m U
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthTr
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

open CuspidalSpectrum RightCosetSpace in
private theorem UpperTheory.V.Af.Smo.coeFn_tr {E : Type} [Field E] [NumberField E] {n : ℕ}
    (μ : Measure (Reduction.normOneGL E n)) [μ.IsHaarMeasure] {φ : cuspForms E n} (hφ : φ ∈ centralCuspForms E n)
    (g : AdelicGLn.AdelicGL E n) :
    (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)) : RightCosetSpace (Reduction.rationalGLOne E n) → ℂ)
      =ᵐ[quotientMeasure (Reduction.rationalGLOne E n) μ] quotTr φ g := by
  rw [toLp_cuspRepT, rightRegularRep_apply, toLp_cuspVecL, quotTr_eq_comp hφ, quotTr_one]
  refine (coeFn_rightTranslate _ μ _ _).trans ?_
  exact (measurePreserving_rightMul μ (toOne g)).quasiMeasurePreserving.ae_eq (coeFn_cuspToL2 μ φ)

private theorem UpperTheory.V.Af.Smo.inner_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {S T : Submodule ℂ H} (h : ∀ x ∈ S, ∀ y ∈ T, inner ℂ x y = 0) {x y : H}
    (hx : x ∈ S.topologicalClosure) (hy : y ∈ T.topologicalClosure) : inner ℂ x y = 0 := by
  have h1 : T ≤ S.topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure]
    exact fun b hb => (Submodule.mem_orthogonal _ _).2 fun a ha => h a ha b hb
  exact (Submodule.mem_orthogonal _ _).1
    (Submodule.topologicalClosure_minimal T h1 (Submodule.isClosed_orthogonal _) hy) x hx

open CuspidalSpectrum RightCosetSpace in
theorem UpperTheory.V.Af.Smo.orthTr :
    UpperTheory.V.Af.Smo.OrthTr := by
  intro E _ _ n μ _ U U' hU hU' sU sU' h φ hφ φ' hφ' g g'
  have i1 := isInvariant_topologicalClosure_map μ hU sU.ρ sU.σ sU.τ
  have i2 := isInvariant_topologicalClosure_map μ hU' sU'.ρ sU'.σ sU'.τ
  have m1 := i1 (toOne g) _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ))
  have m2 := i2 (toOne g') _ (Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (f := cuspVecL μ) hφ'))
  have h0 := UpperTheory.V.Af.Smo.inner_closure (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact h a ha b hb) m1 m2
  have h1 : inner ℂ (toLp μ (cuspRepT μ (toOne g) (cuspVecL μ φ)))
      (toLp μ (cuspRepT μ (toOne g') (cuspVecL μ φ'))) = 0 := h0
  rw [MeasureTheory.L2.inner_def] at h1
  rw [← h1]
  refine integral_congr_ae ?_
  filter_upwards [UpperTheory.V.Af.Smo.coeFn_tr μ (hU hφ) g, UpperTheory.V.Af.Smo.coeFn_tr μ (hU' hφ') g'] with q e1 e2
  rw [e1, e2, RCLike.inner_apply']
end

