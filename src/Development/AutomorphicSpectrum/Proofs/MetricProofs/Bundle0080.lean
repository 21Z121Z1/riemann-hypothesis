import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorOtherSteps
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther

theorem mul_transv_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hc : c = ca
  · subst hc
    simp [Matrix.mul_apply, Matrix.single_apply, mul_comm]
  · simp [Matrix.mul_apply, Matrix.single_apply, hc, Ne.symm hc]

private lemma det_submatrix_mul_transvection_eq {N k : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N)
    (hne : ca ≠ cb) (f g : Fin k → Fin N) (hg : Function.Injective g)
    (hJ : ca ∈ Set.range g ↔ cb ∈ Set.range g) :
    ((h * (1 + Matrix.single cb ca t)).submatrix f g).det = (h.submatrix f g).det := by
  by_cases hca : ca ∈ Set.range g
  · obtain ⟨qa, hqa⟩ := hca
    obtain ⟨qb, hqb⟩ := hJ.mp ⟨qa, hqa⟩
    have hq : qb ≠ qa := by
      rintro rfl
      exact hne (hqa.symm.trans hqb)
    have hiff : ∀ q, g q = ca ↔ q = qa := fun q => by
      rw [← hqa]
      exact hg.eq_iff
    have hM : (h * (1 + Matrix.single cb ca t)).submatrix f g
        = h.submatrix f g * (1 + Matrix.single qb qa t) := by
      ext p q
      simp only [Matrix.submatrix_apply, mul_transv_apply, hqb, hiff]
    have h1 : (1 + Matrix.single qb qa t : Matrix (Fin k) (Fin k) ℂ) = Matrix.transvection qb qa t :=
      rfl
    rw [hM, Matrix.det_mul, h1, Matrix.det_transvection_of_ne qb qa hq t, mul_one]
  · congr 1
    ext p q
    have hq : g q ≠ ca := fun hh => hca ⟨q, hh⟩
    simp only [Matrix.submatrix_apply, mul_transv_apply, hq, if_false, add_zero]

theorem minorIJ_transv {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N) (hne : ca ≠ cb)
    (I J : Finset (Fin N)) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · apply det_submatrix_mul_transvection_eq h t ca cb hne
    · exact (J.orderEmbOfFin _).injective
    · rw [Finset.range_orderEmbOfFin, Finset.mem_coe, Finset.mem_coe]
      exact hJ
  · rfl

theorem minorIJ_other_step : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (i : Fin N), i ≠ a → ∀ I, minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  intro N j a b ca cb hjN hb hab hca hcb h t i hi I
  apply minorIJ_transv h t ca cb
  · intro heq
    have := congrArg Fin.val heq
    omega
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold lastCol at hca
    have hi' : (i : ℕ) ≠ a := fun h' => hi (Fin.ext h')
    have := a.isLt
    have := b.isLt
    have := i.isLt
    have := ca.isLt
    have := cb.isLt
    split_ifs at hca ⊢ <;> omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalar
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane

variable {N : ℕ}

theorem minorIJ_image_of_tri {R : Type} [CommRing R] (M : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N))
    (σ : Fin N → Fin N) (hσ : StrictMonoOn σ S)
    (hT : ∀ x ∈ S, ∀ y ∈ S, y < x → M (σ x) y = 0) :
    minorIJ M (S.image σ) S = ∏ c ∈ S, M (σ c) c := by
  have e : (S.image σ).card = S.card := Finset.card_image_of_injOn hσ.injOn
  unfold minorIJ
  rw [dif_pos e]
  have hf : (fun i => σ (S.orderEmbOfFin rfl i)) = ⇑((S.image σ).orderEmbOfFin e) := by
    apply Finset.orderEmbOfFin_unique e
    · intro i
      exact Finset.mem_image_of_mem σ (Finset.orderEmbOfFin_mem S rfl i)
    · intro i i' hii
      exact hσ (Finset.orderEmbOfFin_mem S rfl i) (Finset.orderEmbOfFin_mem S rfl i')
        ((S.orderEmbOfFin rfl).strictMono hii)
  rw [← hf, Matrix.det_of_upperTriangular]
  · simp only [Matrix.submatrix_apply]
    conv_rhs => rw [← Finset.map_orderEmbOfFin_univ S rfl]
    rw [Finset.prod_map]
    rfl
  · intro i i' hii
    exact hT _ (Finset.orderEmbOfFin_mem S rfl i) _ (Finset.orderEmbOfFin_mem S rfl i')
      ((S.orderEmbOfFin rfl).strictMono hii)

theorem mul_entry (B : Matrix (Fin N) (Fin N) ℂ) (ca cb x y : Fin N) (s : ℂ) :
    (B * (1 + Matrix.single cb ca s)) x y = B x y + if y = ca then s * B x cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hy : y = ca
  · subst hy
    simp [Matrix.mul_single_apply_same, mul_comm]
  · simp [Matrix.mul_single_apply_of_ne, hy]

theorem one_entry (ca cb x y : Fin N) (s : ℂ) :
    (1 + Matrix.single cb ca s : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + if cb = x ∧ ca = y then s else 0 := by
  simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem param_core (S : Finset (Fin N)) (ca cb : Fin N) (hca : ca ∈ S) (hmax : ∀ c ∈ S, c ≤ ca) (hlt : ca < cb)
    (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.BlockTriangular id) (t t' μ : ℂ)
    (H : ∀ J, minorIJ (B * (1 + Matrix.single cb ca t')) J S = μ * minorIJ (1 + Matrix.single cb ca t) J S) :
    μ = (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) ∧
      μ * t = (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
  have hne : ∀ c ∈ S, c ≠ cb := fun c hc => ne_of_lt ((hmax c hc).trans_lt hlt)
  have hcaNe : ca ≠ cb := ne_of_lt hlt
  let σ : Fin N → Fin N := fun c => if c = ca then cb else c
  have hσca : σ ca = cb := if_pos rfl
  have hσne : ∀ c, c ≠ ca → σ c = c := fun c hc => if_neg hc
  have hσ : StrictMonoOn σ S := by
    intro x _ y hy hxy
    have hx' : x ≠ ca := ne_of_lt (hxy.trans_le (hmax y hy))
    rw [hσne x hx']
    by_cases hy' : y = ca
    · rw [hy', hσca]
      exact (hxy.trans_le (hmax y hy)).trans hlt
    · rw [hσne y hy']
      exact hxy
  have hge : ∀ x ∈ S, x ≤ σ x := by
    intro x hx
    by_cases hx' : x = ca
    · rw [hx', hσca]
      exact hlt.le
    · rw [hσne x hx']
  have hyne : ∀ x ∈ S, ∀ y, y < x → y ≠ ca := fun x hx y hy => ne_of_lt (hy.trans_le (hmax x hx))

  have L1 : minorIJ (B * (1 + Matrix.single cb ca t')) S S =
      (∏ c ∈ S.erase ca, B c c) * (B ca ca + t' * B ca cb) := by
    have h0 := minorIJ_image_of_tri (B * (1 + Matrix.single cb ca t')) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [mul_entry, if_neg (hyne x hx y hy), add_zero]
      exact hB hy)
    rw [Finset.image_id] at h0
    rw [h0, ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      rw [id, mul_entry, if_neg (Finset.ne_of_mem_erase hc), add_zero]
    · rw [id, mul_entry, if_pos rfl]
  have R1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
    have h0 := minorIJ_image_of_tri (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) S id strictMonoOn_id (by
      intro x hx y _ hy
      rw [id, one_entry, if_neg (ne_of_gt hy), if_neg (fun h => hne x hx h.1.symm), add_zero])
    rw [Finset.image_id] at h0
    rw [h0]
    refine Finset.prod_eq_one fun c hc => ?_
    rw [id, one_entry, if_pos rfl, if_neg (fun h => hne c hc h.1.symm), add_zero]

  have L2 : minorIJ (B * (1 + Matrix.single cb ca t')) (S.image σ) S =
      (∏ c ∈ S.erase ca, B c c) * (t' * B cb cb) := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [mul_entry, if_neg (hyne x hx y hy), add_zero]
      exact hB (hy.trans_le (hge x hx))), ← Finset.prod_erase_mul S _ hca]
    congr 1
    · refine Finset.prod_congr rfl fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', mul_entry, if_neg hc', add_zero]
    · have h0 : B cb ca = 0 := hB hlt
      rw [hσca, mul_entry, if_pos rfl, h0, zero_add]
  have R2 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (S.image σ) S = t := by
    rw [minorIJ_image_of_tri _ S σ hσ (by
      intro x hx y _ hy
      rw [one_entry, if_neg (ne_of_gt (hy.trans_le (hge x hx))),
        if_neg (fun h => hyne x hx y hy h.2.symm), add_zero]), ← Finset.prod_erase_mul S _ hca]
    have h1 : ∏ c ∈ S.erase ca, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) (σ c) c = 1 := by
      refine Finset.prod_eq_one fun c hc => ?_
      have hc' := Finset.ne_of_mem_erase hc
      rw [hσne c hc', one_entry, if_pos rfl,
        if_neg (fun h => hne c (Finset.mem_of_mem_erase hc) h.1.symm), add_zero]
    rw [h1, one_mul, hσca, one_entry, if_neg (Ne.symm hcaNe), if_pos ⟨rfl, rfl⟩, zero_add]
  have e1 := H S
  have e2 := H (S.image σ)
  rw [L1, R1, mul_one] at e1
  rw [L2, R2] at e2
  exact ⟨e1.symm, e2.symm⟩

theorem param_relation : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h B : Matrix (Fin N) (Fin N) ℂ) (t t' μ : ℂ), h.det ≠ 0 → IsBlockDiag j B → B.BlockTriangular id → (∀ I, minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) = μ * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a)) → μ = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (B ca ca + t' * B ca cb) ∧ μ * t = (∏ c ∈ (stepCols N j a).erase ca, B c c) * (t' * B cb cb) := by
  intro N j a b ca cb hj hb hab hca hcb h B t t' μ hdet _ hBt hyp
  have hinv : h⁻¹ * h = 1 := Matrix.nonsing_inv_mul h (isUnit_iff_ne_zero.2 hdet)
  have hcaS : ca ∈ stepCols N j a := by
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs at hca ⊢ <;> omega
  have hmax : ∀ c ∈ stepCols N j a, c ≤ ca := by
    intro c hc
    unfold lastCol at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rw [Fin.le_def]
    split_ifs at hca hc <;> omega
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine param_core _ ca cb hcaS hmax hlt B hBt t t' μ fun J => ?_
  calc minorIJ (B * (1 + Matrix.single cb ca t')) J (stepCols N j a)
      = minorIJ (h⁻¹ * (h * B * (1 + Matrix.single cb ca t'))) J (stepCols N j a) := by
        rw [Matrix.mul_assoc h, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    _ = ∑ I, minorIJ h⁻¹ J I * minorIJ (h * B * (1 + Matrix.single cb ca t')) I (stepCols N j a) :=
        minorIJ_mul_sum _ _ _ _
    _ = μ * ∑ I, minorIJ h⁻¹ J I * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [hyp I]
        ring
    _ = μ * minorIJ (h⁻¹ * (h * (1 + Matrix.single cb ca t))) J (stepCols N j a) := by
        rw [minorIJ_mul_sum]
    _ = μ * minorIJ (1 + Matrix.single cb ca t) J (stepCols N j a) := by
        rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Plane
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBaseChartAtGoodPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift

section General

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] {n : ℕ}

theorem analytic_eval {G : (Fin n → ℂ) → (Σ k, J k) → ℂ} {T : Set (Fin n → ℂ)}
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (f : MRing J) :
    AnalyticOnNhd ℂ (fun w => eval (G w) (map (Int.castRingHom ℂ) f)) T := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticOnNhd_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, map_X, eval_X]
    exact hp.mul (hG i)

theorem isOpen_forall_ne {A : Type} [Finite A] {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    {f : A → (Fin n → ℂ) → ℂ} (hf : ∀ a, AnalyticOnNhd ℂ (f a) T) :
    IsOpen {w | w ∈ T ∧ ∀ a, f a w ≠ 0} := by
  have e : {w | w ∈ T ∧ ∀ a, f a w ≠ 0} = T ∩ ⋂ a, (T ∩ f a ⁻¹' {0}ᶜ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨h.1, fun a => ⟨h.1, h.2 a⟩⟩, fun h => ⟨h.1, fun a => (h.2 a).2⟩⟩
  rw [e]
  exact hT.inter (isOpen_iInter_of_finite fun a =>
    (hf a).continuousOn.isOpen_inter_preimage hT isOpen_compl_singleton)

theorem form_notMem_iff (z : (Σ k, J k) → ℂ) {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    g ∉ mCoordIdeal z ↔ eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
  rw [Ne, form_mem_mCoordIdeal_iff z hg, aeval_def, algebraMap_int_eq, eval₂_eq_eval_map]

theorem exists_normalised {A : Type} [Finite A] (x : (Σ k, J k) → Ω) (c : ∀ k, J k) (s : A → Ω)
    (G : (Fin n → ℂ) → (Σ k, J k) → ℂ) {T : Set (Fin n → ℂ)} (hT : IsOpen T)
    (hG : ∀ q, AnalyticOnNhd ℂ (fun w => G w q) T) (hmem : ∀ w ∈ T, G w ∈ mcPts (mCoordIdeal x))
    {w₀ : Fin n → ℂ} (hw₀ : w₀ ∈ T) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ mCoordIdeal (G w₀))
    (hreg : ∀ a, RegAt x (mCoordIdeal (G w₀)) (s a)) :
    ∃ (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, J k) → ℂ), V ⊆ T ∧ IsOpen V ∧ w₀ ∈ V ∧
      (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
      (∀ a, AnalyticOnNhd ℂ (fun w => valAt x (s a) (bl w)) V) ∧
      ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal x) ∧ (∀ k, bl w ⟨k, c k⟩ = 1) ∧ SameOrbit (G w) (bl w) ∧
        ∀ a, RegAt x (mCoordIdeal (bl w)) (s a) := by
  choose d g h hg hh hnot heq using hreg
  have hX : ∀ (k : K) (i : J k), IsMultiHomog (X ⟨k, i⟩ : MRing J) (fun k' => if k' = k then 1 else 0) := fun k i =>
    GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single ⟨k, i⟩
  have hx : ∀ a, aeval x (h a) ≠ 0 := fun a e0 => by
    have h1 := (hmem w₀ hw₀).2 _ (mem_mCoordIdeal_of_aeval_eq_zero x (hh a) e0)
    exact (form_notMem_iff _ (hh a)).1 (hnot a) h1
  set bl : (Fin n → ℂ) → (Σ k, J k) → ℂ := fun w p => G w p / G w ⟨p.1, c p.1⟩ with hbl
  set T₁ : Set (Fin n → ℂ) := {w | w ∈ T ∧ ∀ k, G w ⟨k, c k⟩ ≠ 0} with hT₁
  have hT₁o : IsOpen T₁ := isOpen_forall_ne hT fun k => hG ⟨k, c k⟩
  have hT₁T : T₁ ⊆ T := fun w hw => hw.1
  have hblq : ∀ q, AnalyticOnNhd ℂ (fun w => bl w q) T₁ := fun q =>
    ((hG q).mono hT₁T).div ((hG ⟨q.1, c q.1⟩).mono hT₁T) fun w hw => hw.2 q.1
  have hevh : ∀ a, AnalyticOnNhd ℂ (fun w => eval (bl w) (map (Int.castRingHom ℂ) (h a))) T₁ := fun a =>
    analytic_eval hblq (h a)
  have horb : ∀ w ∈ T₁, SameOrbit (G w) (bl w) := fun w hw =>
    ⟨fun k => G w ⟨k, c k⟩, hw.2, funext fun p => by
      have := hw.2 p.1
      simp only [hbl]
      field_simp⟩
  have hw₁ : w₀ ∈ T₁ := ⟨hw₀, fun k e0 => (form_notMem_iff _ (hX k (c k))).1 (hc k) (by simpa using e0)⟩
  refine ⟨{w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0}, bl,
    fun w hw => hw.1.1, isOpen_forall_ne hT₁o hevh, ⟨hw₁, fun a => ?_⟩, fun q => (hblq q).mono fun w hw => hw.1,
    fun a => ?_, fun w hw => ?_⟩
  · rw [← form_notMem_iff _ (hh a), ← GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit (horb w₀ hw₁)]
    exact hnot a
  · have hV : IsOpen {w | w ∈ T₁ ∧ ∀ a, eval (bl w) (map (Int.castRingHom ℂ) (h a)) ≠ 0} :=
      isOpen_forall_ne hT₁o hevh
    refine AnalyticOnNhd.congr hV (((analytic_eval hblq (g a)).mono fun w hw => hw.1).div
      ((hevh a).mono fun w hw => hw.1) fun w hw => hw.2 a) fun w hw => ?_
    have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact (valAt_eq hz ⟨d a, g a, h a, hg a, hh a, hx a, heq a, hw.2 a, rfl⟩).symm
  · have hz : bl w ∈ mcPts (mCoordIdeal x) := mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal x) (orbit_symm (horb w hw.1)) (hmem w hw.1.1)
    exact ⟨hz, fun k => div_self (hw.1.2 k), horb w hw.1,
      fun a => ⟨d a, g a, h a, hg a, hh a, (form_notMem_iff _ (hh a)).2 (hw.2 a), heq a⟩⟩

end General

theorem exists_baseChart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ)
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk) (x₀ : Rb.X)
    (hgood : M.GoodAt F (mCoordIdeal (Rb.lift x₀ x₀))) :
    ∃ (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ),
      x₀ ∈ (Rb.A.chart kb).source ∧ Rb.A.chart kb x₀ ∈ V ∧ IsBaseChart M Rb F kb V bl := by
  obtain ⟨kb, hkb⟩ := Rb.A.cover x₀
  have hT : IsOpen ((Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀) :=
    (Rb.A.chart kb).isOpen_inter_preimage_symm (Rb.isOpen_U x₀)
  have hlw : Rb.lift x₀ ((Rb.A.chart kb).symm (Rb.A.chart kb x₀)) = Rb.lift x₀ x₀ := by
    rw [(Rb.A.chart kb).left_inv hkb]
  have hw₀ : Rb.A.chart kb x₀ ∈ (Rb.A.chart kb).target ∩ (Rb.A.chart kb).symm ⁻¹' Rb.U x₀ :=
    ⟨(Rb.A.chart kb).map_source hkb, by
      show (Rb.A.chart kb).symm (Rb.A.chart kb x₀) ∈ Rb.U x₀
      rw [(Rb.A.chart kb).left_inv hkb]
      exact Rb.mem_U x₀⟩
  let s : (((Σ k, ι k) × Finset (Fin N)) ⊕ ((Σ k, ι k) × Finset (Fin N))) ⊕
      ({p : Ψ × Fin N // M.blk p = none} ⊕ {p : Ψ × Fin N // M.blk p = none}) → M.Ω :=
    Sum.elim (Sum.elim (fun a => F.u a.1 a.2) (fun a => F.u' a.2 a.1))
      (Sum.elim (fun p => F.υ p.1) (fun p => (F.υ p.1)⁻¹))
  obtain ⟨V, bl, hVT, hVo, hV₀, hq, hval, hpt⟩ := exists_normalised M.x F.c s
    (fun w => Rb.lift x₀ ((Rb.A.chart kb).symm w)) hT (fun q => Rb.holo x₀ q kb)
    (fun w hw => Rb.mem x₀ _ hw.2) hw₀
    (by simpa only [hlw] using hgood.1)
    (by
      simp only [hlw]
      rintro ((⟨q, I⟩ | ⟨q, I⟩) | (⟨p, hp⟩ | ⟨p, hp⟩))
      · exact (hgood.2.1 q I).1
      · exact (hgood.2.1 q I).2
      · exact (hgood.2.2 p hp).2.1
      · exact (hgood.2.2 p hp).2.2)
  refine ⟨kb, V, bl, hkb, hV₀, hVo, fun w hw => (hVT hw).1, hq,
    fun q I => hval (Sum.inl (Sum.inl (q, I))), fun w hw => ?_⟩
  obtain ⟨hz, h1, hor, hr⟩ := hpt w hw
  refine ⟨hz, h1, ⟨fun k e0 => ?_, fun q I => ⟨hr (Sum.inl (Sum.inl (q, I))), hr (Sum.inl (Sum.inr (q, I)))⟩,
    fun p hp => ⟨(hgood.2.2 p hp).1, hr (Sum.inr (Sum.inl ⟨p, hp⟩)), hr (Sum.inr (Sum.inr ⟨p, hp⟩))⟩⟩,
    orbit_trans (Rb.compat _ x₀ _ ⟨Rb.mem_U _, (hVT hw).2⟩) hor⟩
  have := (form_mem_mCoordIdeal_iff (bl w) (GroundTheory.Heights₂.Heights.LowerBoundFree.isMultiHomog_X_single
    (⟨k, F.c k⟩ : Σ k, baseIdx ι M.blk k))).1 e0
  rw [aeval_X, h1 k] at this
  exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.WMan.BaseLift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlockDiagFrameChange
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem exists_flags_good : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (z : (Σ k, ι k) → ℂ), z ∈ mcPts (mCoordIdeal y) → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z)) → ∃ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0) ∧ ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk z) p.2 ⟨k, m⟩ (h p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F z hz hF hG
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  have hch : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0])
  obtain ⟨c, hc, hcb, hc1⟩ : ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
      (∀ k : NonPluckerBlocks M.blk, c k.1 * basePart M.blk z ⟨k, F.c k⟩ = 1) ∧
      ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → c k = 1 := by
    refine ⟨fun k => if hk : ∀ p, M.blk p ≠ some k then (basePart M.blk z ⟨⟨k, hk⟩, F.c ⟨k, hk⟩⟩)⁻¹ else 1,
      fun k => ?_, fun k => ?_, fun p k hp => ?_⟩
    · by_cases hk : ∀ p, M.blk p ≠ some k
      · simp only [dif_pos hk]
        exact inv_ne_zero (hch ⟨k, hk⟩)
      · simp only [dif_neg hk]
        exact one_ne_zero
    · simp only [dif_pos k.2]
      exact inv_mul_cancel₀ (hch k)
    · have hk : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
      simp only [dif_neg hk]
  let z₁ : (Σ k, ι k) → ℂ := fun q => c q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal y) c hc hz
  have hb₁ : basePart M.blk z₁ = fun q => (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk z q := rfl
  have hT := StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x (basePart M.blk z)
    (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc k.1)
  have hI : mCoordIdeal (basePart M.blk z₁) = mCoordIdeal (basePart M.blk z) := by
    rw [hb₁]
    exact hT.1
  have hG₁ : M.GoodAt F (mCoordIdeal (basePart M.blk z₁)) := by rw [hI]; exact hG
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, F.c k⟩ = 1 := hcb
  obtain ⟨h, -, hh, hs⟩ := (h3 F hF z₁ (h1 z₁ hz₁) hG₁ hnorm).1 hz₁
  have hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk z₁) = valAt M.x s (basePart M.blk z) := fun s => by
    rw [hb₁]
    exact (hT.2 (h1 z hz)).2 s
  refine ⟨h, hh, fun p k hp => ?_⟩
  obtain ⟨a, ha, hm⟩ := hs p k hp
  refine ⟨a, ha, fun m => ?_⟩
  have e := hm m
  simp only [hval] at e
  have e' : z₁ ⟨k, m⟩ = z ⟨k, m⟩ := by
    show c k * z ⟨k, m⟩ = z ⟨k, m⟩
    rw [hc1 p k hp, one_mul]
  rw [e'] at e
  exact e

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoordinateTieTransfer
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace GlobalTheory.CompanionTheory.Ar.FlagTie

theorem flagCoord_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ X'), CoordTie ℤ ξ' (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → CoordTie ℤ ξ' (flagCoord ((k : K₀) → J₀ k) (seg x₀) φ (cc 𝔐 bW bO)) :=
  @PositivityTheory.Xgp.t_c_fm_exists_flags_tie

end GlobalTheory.CompanionTheory.Ar.FlagTie
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecondStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_second : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w w', CovMap.IsImg Cv z w → CovMap.IsImg Cv z w' → SameOrbit w w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThirdStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_cover_arithmetic_third : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w, CovMap.IsImg Cv z w → SameOrbit (basePart M.blk w) (basePart M'.blk z ∘ Cv.v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over | exact GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeight
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem flagHeight_holds : FlagHeight := PositivityTheory.Xgp.t_top_flh

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlagStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenericFlag_gMat : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω], GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag <;> assumption)
end

