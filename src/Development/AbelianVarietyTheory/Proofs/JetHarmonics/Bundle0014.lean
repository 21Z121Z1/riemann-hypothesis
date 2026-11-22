import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Jets.FactorNonneg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRingEquivApplyEqMulOfTranscendental
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem exists_ringEquiv_apply_eq_mul_of_transcendental {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsAlgClosed L] {x : L} (hx : Transcendental K x) {c : K} (hc : c ≠ 0) :
    ∃ σ : L ≃+* L, (∀ k : K, σ (algebraMap K L k) = algebraMap K L k) ∧
      σ x = algebraMap K L c * x := by
  have h1 : AlgebraicIndepOn K id ({x} : Set L) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let e : MvPolynomial s K ≃ₐ[K] MvPolynomial s K :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => c • MvPolynomial.X i)
      (MvPolynomial.aeval fun i => c⁻¹ • MvPolynomial.X i)
      (by ext i : 1; simp [smul_smul, hc]) (by ext i : 1; simp [smul_smul, hc])
  obtain ⟨σ, hσ⟩ :=
    GlobalTheory.GaloisDescent.exists_ringEquiv_of_isTranscendenceBasis hs hs e.toRingEquiv
  refine ⟨σ, fun k => ?_, ?_⟩
  · simpa [e] using hσ (MvPolynomial.C k)
  · have := hσ (MvPolynomial.X ⟨x, hxs rfl⟩)
    rw [← Algebra.smul_def]
    simpa [e] using this

theorem mem_algebraicClosure_of_norm_le :
    ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (x : ℂ) (B : ℝ),
      (∀ ι' : ℂ ≃+* ℂ_[q], (∀ a : algebraicClosure ℚ ℂ, ι' (a : ℂ) = ι (a : ℂ)) → ‖ι' x‖ ≤ B) →
        x ∈ algebraicClosure ℚ ℂ := by
  intro q hq ι x B h
  by_contra hx
  rw [mem_algebraicClosure_iff] at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isAlgebraic_zero
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hx' : Transcendental (algebraicClosure ℚ ℂ) x := fun ha =>
    hx (ha.restrictScalars ℚ)
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hq0 : q ≠ 0 := hq.out.ne_zero
  have hpos : 0 < ‖ι x‖ := by simpa using hx0
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / ‖ι x‖) hq1
  have hc : ((q : algebraicClosure ℚ ℂ) ^ j)⁻¹ ≠ 0 := by
    simp [hq0]
  obtain ⟨σ, hσ, hσx⟩ := exists_ringEquiv_apply_eq_mul_of_transcendental hx' hc
  have h2 := h (σ.trans ι) fun a => by
    have := hσ a
    simp only [RingEquiv.trans_apply]
    exact congrArg ι this
  have hn : ‖(q : ℂ_[q])‖ = (q : ℝ)⁻¹ := by
    have h3 : (q : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (q : ℚ_[q]) := by simp
    rw [h3, norm_algebraMap', Padic.norm_p]
  rw [RingEquiv.trans_apply, hσx] at h2
  simp only [map_mul, map_inv₀, map_pow, map_natCast, norm_mul, norm_inv, norm_pow, hn,
    inv_pow, inv_inv] at h2
  rw [div_lt_iff₀ hpos] at hj
  linarith

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeisenbergOperatorsOrthogonalFrameCoords
section
open GlobalTheory.MomOne Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.MomOne.Frame

variable {g : ℕ}

theorem hf_sum_left {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm (∑ i, z i • x i) w = ∑ i, z i * hf Hm (x i) w := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem hf_sum_right {ι : Type} [Fintype ι] (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : hf Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * hf Hm w (x i) := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem beta_sum_left {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm (∑ i, z i • x i) w = ∑ i, z i * beta d Hm (x i) w := by
  simp only [beta, hf_sum_left, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem beta_sum_right {ι : Type} [Fintype ι] (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (z : ι → ℂ) (x : ι → Fin g → ℂ)
    (w : Fin g → ℂ) : beta d Hm w (∑ i, z i • x i) = ∑ i, conj (z i) * beta d Hm w (x i) := by
  simp only [beta, hf_sum_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

section
variable {d : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {x : Fin g → Fin g → ℂ} {a : Fin g → ℕ}

theorem beta_coord (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z : Fin g → ℂ) (j : Fin g) :
    beta d Hm (∑ i, z i • x i) (x j) = z j * a j := by
  simp [beta_sum_left, hx]

theorem beta_frame (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * (z i * conj (w i)) := by
  rw [beta_sum_right]
  exact Finset.sum_congr rfl fun i _ => by rw [beta_coord hx]; ring

theorem hf_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (z w : Fin g → ℂ) :
    hf Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 d (z i) (w i) := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt d ≠ 0 := by positivity
    exact_mod_cast this
  have h := beta_frame hx z w
  have e : hf Hm (∑ i, z i • x i) (∑ i, w i • x i) =
      ((2 / Real.sqrt d : ℝ) : ℂ) * beta d Hm (∑ i, z i • x i) (∑ i, w i • x i) := by
    rw [beta]; push_cast; field_simp
  rw [e, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1]; ring

theorem expand (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) (ha : ∀ i, 0 < a i)
    (v : Fin g → ℂ) : v = ∑ i, (beta d Hm v (x i) / (a i : ℂ)) • x i := by
  have ha' : ∀ i, (a i : ℂ) ≠ 0 := fun i => by exact_mod_cast (ha i).ne'
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ x
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have hinj : Function.Injective L := by
    intro z w h
    funext j
    have h1 := beta_coord hx z j
    have h2 := beta_coord hx w j
    rw [← hL] at h1 h2
    rw [h, h2] at h1
    exact (mul_right_cancel₀ (ha' j) h1).symm
  obtain ⟨z, rfl⟩ := (LinearMap.injective_iff_surjective.1 hinj) v
  rw [hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [beta_coord hx, mul_div_cancel_right₀ _ (ha' i)]

theorem opU_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opU Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 d (t i) (f j i) (z i) ^ a i := by
  have e : (∑ i, z i • x i) + ∑ i, t i • x i = ∑ i, (z + t) i • x i := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [opU, e, hG, hf_frame hd hx, hf_frame hd hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [U1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Pi.add_apply,
    Finset.mul_sum, ← Finset.sum_sub_distrib, mul_assoc]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

theorem opW_frame (hd : 0 < d) (hx : ∀ i j, beta d Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    {m : ℕ} (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ)
    (hG : ∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) (t z : Fin g → ℂ) :
    opW d Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 d (t i) (f j i) (z i) ^ a i := by
  have e : (((beta d Hm (∑ i, t i • x i) (∑ i, t i • x i)).re : ℝ) : ℂ) =
      ∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ) := by
    rw [beta_frame hx]
    simp only [Complex.mul_conj]
    have : (∑ i, (a i : ℂ) * ((Complex.normSq (t i) : ℝ) : ℂ)) = ((∑ i, (a i : ℝ) * Complex.normSq (t i) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.ofReal_re]
  rw [opW, opU_frame hd hx c f G hG, e, Finset.mul_sum _ (fun j => c j * _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [W1, mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul, ← Complex.exp_sum, Finset.mul_sum]
  rw [mul_left_comm]
  congr 3
  exact Finset.sum_congr rfl fun i _ => by ring

end

theorem jetV_frame (x : Fin g → Fin g → ℂ) (G : (Fin g → ℂ) → ℂ) (hG : ContDiff ℂ ⊤ G) (k : ℕ)
    (ys : Fin k → Fin g → ℂ) :
    jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys := by
  let L : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap (Fintype.linearCombination ℂ x)
  have hL : ∀ z, L z = ∑ i, z i • x i := fun z => Fintype.linearCombination_apply _ _ _
  have e : (fun z : Fin g → ℂ => G (∑ i, z i • x i)) = G ∘ L := by
    funext z; simp [hL]
  rw [e, L.iteratedFDeriv_comp_right hG 0 le_top, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, jetV]
  simp only [hL]

theorem coord : ∀ (g : ℕ) (S : Setup g) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ), 0 < S.d → (∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0) → (∀ i, 0 < a i) → (∀ v : Fin g → ℂ, v = ∑ i, (beta S.d S.Hm v (x i) / (a i : ℂ)) • x i) ∧ (∀ z w : Fin g → ℂ, hf S.Hm (∑ i, z i • x i) (∑ i, w i • x i) = ∑ i, (a i : ℂ) * h1 S.d (z i) (w i)) ∧ (∀ (m : ℕ) (c : Fin m → ℂ) (f : Fin m → Fin g → ℂ → ℂ) (G : (Fin g → ℂ) → ℂ), (∀ z : Fin g → ℂ, G (∑ i, z i • x i) = ∑ j, c j * ∏ i, f j i (z i) ^ a i) → ∀ t z : Fin g → ℂ, opU S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, U1 S.d (t i) (f j i) (z i) ^ a i ∧ opW S.d S.Hm (∑ i, t i • x i) G (∑ i, z i • x i) = ∑ j, c j * ∏ i, W1 S.d (t i) (f j i) (z i) ^ a i) ∧ ∀ (G : (Fin g → ℂ) → ℂ), ContDiff ℂ ⊤ G → ∀ (k : ℕ) (ys : Fin k → Fin g → ℂ), jetV G (fun l => ∑ i, ys l i • x i) = iteratedFDeriv ℂ k (fun z : Fin g → ℂ => G (∑ i, z i • x i)) 0 ys :=
  fun _ _ x _ hd hx ha =>
    ⟨expand hx ha, hf_frame hd hx,
      fun _ c f G hG t z => ⟨opU_frame hd hx c f G hG t z, opW_frame hd hx c f G hG t z⟩,
      jetV_frame x⟩

end GlobalTheory.MomOne.Frame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqRaising
section
open Finset

noncomputable section

namespace GlobalTheory.WigSh

theorem prod_other_neighbour_raise {n : ℕ} (d : Fin (n + 1) → ℝ) (l : Fin (n + 1))
    (hd : ∀ i, 0 < d i) (hl : d l = 1) :
    (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) * (d 0 * d (Fin.last n))
      = ∏ j : Fin n, d (l.succAbove j) := by
  have hP : ∏ i, d i = ∏ j : Fin n, d (l.succAbove j) := by
    rw [Fin.prod_univ_succAbove d l, hl, one_mul]
  have h1 := Fin.prod_univ_succ d
  have h2 := Fin.prod_univ_castSucc d
  have h3 : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j) = (∏ j : Fin n, d j.succ) * ∏ j : Fin n, d j.castSucc := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold Fin.succAbove
    split_ifs
    · rfl
    · exact mul_comm _ _
  have hpos : 0 < ∏ j : Fin n, d (l.succAbove j) := Finset.prod_pos fun j _ => hd _
  apply mul_right_cancel₀ hpos.ne'
  calc _ = ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      * ∏ j : Fin n, d (l.succAbove j)) * (d 0 * d (Fin.last n)) := by ring
    _ = (d 0 * ∏ j : Fin n, d j.succ) * ((∏ j : Fin n, d j.castSucc) * d (Fin.last n)) := by
      rw [h3]; ring
    _ = _ := by rw [← h1, ← h2, hP]

theorem inv_sq_le_wP (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hL : StrictAnti L) (hM : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l + 1) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hn : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ wP L M l := by
  set e : Fin (n + 1) → ℤ := fun i => max |L i - L l| 1 with he
  set d : Fin (n + 1) → ℝ := fun i => (e i : ℝ) with hd
  have hdpos : ∀ i, 0 < d i := fun i => by
    have : 0 < e i := lt_of_lt_of_le one_pos (le_max_right _ _)
    simp only [hd]; exact_mod_cast this
  have hdl : d l = 1 := by simp [hd, he]
  have key := prod_other_neighbour_raise d l hdpos hdl
  have hd0 : d 0 ≤ D := by
    have a : L l ≤ L 0 := hL.antitone (Fin.zero_le _)
    have a' : (L l : ℝ) ≤ L 0 := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonneg (by linarith)]; exact h0) hD
  have hdn : d (Fin.last n) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hL.antitone (Fin.le_last _)
    have a' : (L (Fin.last n) : ℝ) ≤ L l := by exact_mod_cast a
    simp only [hd, he]
    push_cast
    exact max_le (by rw [abs_of_nonpos (by linarith)]; linarith) hD
  have hden : ∏ j : Fin n, |(L (l.succAbove j) : ℝ) - L l| = ∏ j : Fin n, d (l.succAbove j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    have a : L (l.succAbove j) ≠ L l := fun h => Fin.succAbove_ne l j (hL.injective h)
    have b : 1 ≤ |L (l.succAbove j) - L l| := Int.one_le_abs (sub_ne_zero.2 a)
    simp only [hd, he, max_eq_left b]
    push_cast
    rfl
  have hnum : (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
      ≤ ∏ j : Fin n, |(M j : ℝ) - 1 - L l| := by
    refine Finset.prod_le_prod (fun j _ => (hdpos _).le) fun j _ => ?_
    obtain ⟨h1, h2⟩ := hM j
    have h3 := hne j
    have : e (if j.castSucc < l then j.succ else j.castSucc) ≤ |M j - 1 - L l| := by
      split_ifs with hl
      · have a2 : L l ≤ L j.succ := hL.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
        simp only [he]
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
        omega
      · have a2 : L j.castSucc ≤ L l := hL.antitone (not_lt.1 hl)
        simp only [he]
        rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)]
        omega
    simp only [hd]
    exact_mod_cast this
  rw [← abs_of_nonneg (Model.placeWeight_nonneg hM l)]
  unfold wP
  rw [Model.prod_erase_eq, abs_div, Finset.abs_prod, Finset.abs_prod, hden, ← key]
  have hQ : 0 < ∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc) :=
    Finset.prod_pos fun j _ => hdpos _
  have hm : d 0 * d (Fin.last n) ≤ D ^ 2 := by
    rw [sq]; exact mul_le_mul hd0 hdn (hdpos _).le (by linarith)
  have hmpos : 0 < d 0 * d (Fin.last n) := mul_pos (hdpos _) (hdpos _)
  calc (D ^ 2)⁻¹ ≤ (d 0 * d (Fin.last n))⁻¹ := inv_anti₀ hmpos hm
    _ = (∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc)) /
        ((∏ j : Fin n, d (if j.castSucc < l then j.succ else j.castSucc))
          * (d 0 * d (Fin.last n))) := by
      rw [div_mul_eq_div_div, div_self hQ.ne', one_div]
    _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hQ hmpos).le

end GlobalTheory.WigSh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
section
set_option autoImplicit false

open Cardinal

namespace GlobalTheory.PadicComplexIso

theorem exists_ringEquiv_over (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hsK : #K = #s := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have htL : #L = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hsK.symm.trans (hKL.trans htL))
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e0 : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R] Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e0.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem mk_le_continuum_of_denseRange {X Y : Type} [MetricSpace Y] (f : X → Y)
    (hf : DenseRange f) (hX : #X ≤ 𝔠) : #Y ≤ 𝔠 := by
  have hex : ∀ (y : Y) (n : ℕ), ∃ x, dist (f x) y < 1 / ((n : ℝ) + 1) := by
    intro y n
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 hf y (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨x, by rw [dist_comm]; exact hx⟩
  choose g hg using hex
  have hlim : ∀ y, Filter.Tendsto (fun n => f (g y n)) Filter.atTop (nhds y) := by
    intro y
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hg y n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinj : Function.Injective g := by
    intro y y' h
    have h2 := hlim y'
    rw [← h] at h2
    exact tendsto_nhds_unique (hlim y) h2
  calc #Y ≤ #(ℕ → X) := Cardinal.mk_le_of_injective hinj
    _ = #X ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]
    _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right hX
    _ = 𝔠 := Cardinal.continuum_power_aleph0

theorem mk_padicComplex (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  apply le_antisymm
  · have hQp : #ℚ_[q] ≤ 𝔠 :=
      mk_le_continuum_of_denseRange _ (Padic.denseRange_ratCast q)
        (by rw [Cardinal.mkRat]; exact Cardinal.aleph0_le_continuum)
    have hAl : #(PadicAlgCl q) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
        (max_le hQp Cardinal.aleph0_le_continuum)
    exact mk_le_continuum_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl q)) hAl
  · obtain ⟨g, -, -, hg⟩ :=
      (PerfectSpace.univ_perfect (α := ℂ_[q])).exists_nat_bool_injection Set.univ_nonempty
    calc 𝔠 = #(ℕ → Bool) := by
          rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
      _ ≤ #ℂ_[q] := Cardinal.mk_le_of_injective hg

theorem exists_ringEquiv_extending : ∀ (q : ℕ) [Fact q.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[q]),
    ∃ ι : ℂ ≃+* ℂ_[q], ∀ x : algebraicClosure ℚ ℂ, ι (x : ℂ) = lam x := by
  intro q _ lam
  let _ : Algebra (algebraicClosure ℚ ℂ) ℂ_[q] := lam.toAlgebra
  have _ : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : #(algebraicClosure ℚ ℂ) ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ)).trans
      (by rw [Cardinal.mkRat, max_self])
  have hK : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨e, he⟩ := exists_ringEquiv_over (algebraicClosure ℚ ℂ) ℂ ℂ_[q] hR hK
    (by rw [Cardinal.mk_complex, mk_padicComplex])
  exact ⟨e, fun x => he x⟩

end GlobalTheory.PadicComplexIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_integral_bounded_closure : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type), (∀ S T : MvPowerSeries σ K, Intg S → Intg T → Intg (S + T) ∧ Intg (S - T) ∧ Intg (S * T)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → Bdd (S + T) ∧ Bdd (S - T) ∧ Bdd (S * T)) ∧ (∀ (S : MvPowerSeries σ K) (n : ℕ), (Intg S → Intg (S ^ n)) ∧ (Bdd S → Bdd (S ^ n)) ∧ (Intg S → Bdd S)) ∧ (∀ a : K, Bdd (MvPowerSeries.C a : MvPowerSeries σ K) ∧ (‖a‖ ≤ 1 → Intg (MvPowerSeries.C a : MvPowerSeries σ K)) ∧ (‖a‖ < 1 → Small (MvPowerSeries.C a : MvPowerSeries σ K))) ∧ (∀ i : σ, Small (MvPowerSeries.X i : MvPowerSeries σ K)) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → MvPowerSeries σ K), ((∀ i ∈ t, Intg (f i)) → Intg (∏ i ∈ t, f i) ∧ Intg (∑ i ∈ t, f i)) ∧ ((∀ i ∈ t, Bdd (f i)) → Bdd (∏ i ∈ t, f i) ∧ Bdd (∑ i ∈ t, f i))) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → (Intg S → Intg (MvPowerSeries.subst a S)) ∧ (Bdd S → Bdd (MvPowerSeries.subst a S))) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → (Intg f → Intg (f.subst a)) ∧ (Bdd f → Bdd (f.subst a))) ∧ (∀ (k ι : Type) [CommRing k] (φ : k →+* K) (a : ι → MvPowerSeries σ K) (A : MvPolynomial ι k), (∀ j, Bdd (a j)) → Bdd (MvPolynomial.eval₂ ((MvPowerSeries.C : K →+* MvPowerSeries σ K).comp φ) a A)) ∧ (∀ f : PowerSeries K, (Intg f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1) ∧ (Bdd f ↔ ∃ C : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ C)) := by
  first | exact @GlobalTheory.BddAlg.bdd_alg | exact GlobalTheory.BddAlg.bdd_alg | (intros; apply GlobalTheory.BddAlg.bdd_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormCoeffIntegralPowerSeriesLeProdZerosStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (h : PowerSeries K) (S : Finset K), Intg h → (∀ x ∈ S, ‖x‖ < 1 ∧ ev1 h x = 0) → (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖PowerSeries.coeff k h‖ * r ^ k ≤ ∏ x ∈ S, ‖x‖) ∧ (‖PowerSeries.coeff S.card h‖ = 1 → (∀ k < S.card, ‖PowerSeries.coeff k h‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖PowerSeries.coeff 0 h‖) := by
  first | exact @GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | exact GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | (intros; apply GlobalTheory.ConvSer.norm_coeff_le_prod_zeros <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormLeOfDistinct
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.Triang

variable {q : ℕ} [Fact q.Prime]

theorem bd_one_mul {f g : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (hg : Bd 1 g) : Bd 1 (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

theorem bd_one_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero =>
    intro m
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ]
    exact bd_one_mul ih hf

theorem norm_le_of_distinct {ι : Type*} (s : Finset ι) (e : ι → ℕ) (u : ι → ℂ_[q]⟦X⟧) (c : ι → ℂ_[q]) (B : ℝ)
    (he : Set.InjOn e s) (hu : ∀ j ∈ s, Bd 1 (u j)) (h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1)
    (hB : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j))) : ∀ j ∈ s, ‖c j‖ ≤ B := by
  classical
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hcoeff : ∀ N, coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) =
      ∑ j ∈ s, c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) := by
    intro N
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
  have key : ∀ N, ∀ j ∈ s, e j = N → ‖c j‖ ≤ B := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro j hj hjN
    have hsplit := (hcoeff N).trans (Finset.add_sum_erase s _ hj).symm
    beta_reduce at hsplit
    have hjterm : c j * (if e j ≤ N then coeff (N - e j) (u j) else 0) = c j * constantCoeff (u j) := by
      rw [if_pos hjN.le, hjN, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hrest : ‖∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0)‖ ≤ B := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun i hi => ?_
      obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
      split_ifs with hle
      · have hlt : e i < N := lt_of_le_of_ne hle fun h => hij (he his hj (h.trans hjN.symm))
        rw [norm_mul]
        calc ‖c i‖ * ‖coeff (N - e i) (u i)‖ ≤ B * 1 :=
              mul_le_mul (ih _ hlt i his rfl) (hu i his _) (norm_nonneg _) hB0
          _ = B := mul_one B
      · simpa using hB0
    have hmain : c j * constantCoeff (u j) = coeff N (∑ j ∈ s, C (c j) * (X ^ e j * u j)) -
        ∑ i ∈ s.erase j, c i * (if e i ≤ N then coeff (N - e i) (u i) else 0) := by
      linear_combination -hsplit - hjterm
    have hnorm : ‖c j‖ = ‖c j * constantCoeff (u j)‖ := by rw [norm_mul, h0 j hj, mul_one]
    rw [hnorm, hmain, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hB N) ?_)
    rwa [norm_neg]
  exact fun j hj => key (e j) j hj rfl

theorem coeff_norm_le : ∀ (q : ℕ) [Fact q.Prime] (xs ys : ℂ_[q]⟦X⟧) (k : ℕ) (a b : ℕ → ℂ_[q]) (B : ℝ), Bd 1 xs → Bd 1 ys → ‖constantCoeff xs‖ = 1 → ‖constantCoeff ys‖ = 1 → Bd B (∑ i ∈ Finset.range (k + 1), (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys)) → ∀ i ≤ k, ‖a i‖ ≤ B ∧ ‖b i‖ ≤ B := by
  intro q _ xs ys k a b B hxs hys hx0 hy0 hB
  classical
  let s : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range (k + 1)
  let e : Bool × ℕ → ℕ := fun j => bif j.1 then 2 * (k - j.2) + 3 else 2 * (k - j.2)
  let u : Bool × ℕ → ℂ_[q]⟦X⟧ := fun j => bif j.1 then xs ^ j.2 else xs ^ j.2 * ys
  let c : Bool × ℕ → ℂ_[q] := fun j => bif j.1 then a j.2 else b j.2
  have hmem : ∀ {j : Bool × ℕ}, j ∈ s → j.2 < k + 1 := fun hj =>
    Finset.mem_range.mp (Finset.mem_product.mp hj).2
  have he : Set.InjOn e s := by
    rintro ⟨b₁, i₁⟩ h₁ ⟨b₂, i₂⟩ h₂ heq
    have hi₁ := hmem (Finset.mem_coe.mp h₁)
    have hi₂ := hmem (Finset.mem_coe.mp h₂)
    cases b₁ <;> cases b₂ <;> simp only [e, cond_true, cond_false] at heq hi₁ hi₂ <;>
      first | (exfalso; omega) | (congr 1; omega)
  have hu : ∀ j ∈ s, Bd 1 (u j) := by
    rintro ⟨_ | _, i⟩ _
    · exact bd_one_mul (bd_one_pow hxs i) hys
    · exact bd_one_pow hxs i
  have h0 : ∀ j ∈ s, ‖constantCoeff (u j)‖ = 1 := by
    rintro ⟨_ | _, i⟩ _
    · show ‖constantCoeff (xs ^ i * ys)‖ = 1
      rw [map_mul, map_pow, norm_mul, norm_pow, hx0, hy0, one_pow, one_mul]
    · show ‖constantCoeff (xs ^ i)‖ = 1
      rw [map_pow, norm_pow, hx0, one_pow]
  have hsum : (∑ j ∈ s, C (c j) * (X ^ e j * u j)) = ∑ i ∈ Finset.range (k + 1),
      (C (a i) * X ^ (2 * (k - i) + 3) * xs ^ i + C (b i) * X ^ (2 * (k - i)) * xs ^ i * ys) := by
    simp only [s]
    rw [Finset.sum_product, Fintype.sum_bool, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [e, u, c, cond_true, cond_false]
    ring
  have hB' : Bd B (∑ j ∈ s, C (c j) * (X ^ e j * u j)) := by
    rw [hsum]
    exact hB
  have key := norm_le_of_distinct s e u c B he hu h0 hB'
  intro i hi
  have hi' : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  exact ⟨key (true, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩),
    key (false, i) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hi'⟩)⟩

end GlobalTheory.MomOne.Triang
end
end

