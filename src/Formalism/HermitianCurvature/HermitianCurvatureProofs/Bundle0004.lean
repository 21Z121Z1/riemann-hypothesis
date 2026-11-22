import Formalism.HermitianCurvature.Bundle0001

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Herglotz
section
namespace Formalism.FourierDecayAlt.P.Herglotz

open Real Filter Topology Finset

variable {d : ℕ}

noncomputable def ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))

lemma ee_eq (x : Fin d → ℝ) (σ : Fin d → ℤ) :
    ee x σ = Complex.exp (((2 * π * ∑ j, (σ j : ℝ) * x j : ℝ) : ℂ) * Complex.I) := by
  unfold ee
  congr 1
  push_cast
  ring

lemma norm_ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ‖ee x σ‖ = 1 := by
  rw [ee_eq]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ee_mul_conj (x : Fin d → ℝ) (σ σ' : Fin d → ℤ) :
    ee x σ * starRingEnd ℂ (ee x σ') = ee x (σ - σ') := by
  rw [ee_eq, ee_eq, ee_eq, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Pi.sub_apply, Int.cast_sub, sub_mul,
    Finset.sum_sub_distrib]
  push_cast
  ring

noncomputable def box (d N : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) N)

lemma dsum (F : (Fin d → ℤ) → ℂ) (S : Finset (Fin d → ℤ)) :
    ∑ σ ∈ S, ∑ σ' ∈ S, F (σ - σ') =
      ∑' τ, (((S ×ˢ S).filter (fun p => p.1 - p.2 = τ)).card : ℂ) * F τ := by
  rw [tsum_eq_sum (s := (S ×ˢ S).image (fun p => p.1 - p.2))]
  · rw [← Finset.sum_product' (f := fun σ σ' => F (σ - σ')),
      ← Finset.sum_fiberwise_of_maps_to (g := fun p : (Fin d → ℤ) × (Fin d → ℤ) => p.1 - p.2)
        (t := (S ×ˢ S).image (fun p => p.1 - p.2)) (fun p hp => Finset.mem_image_of_mem _ hp)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.1 hp).2]), Finset.sum_const,
      nsmul_eq_mul]
  · intro τ hτ
    have : (S ×ˢ S).filter (fun p => p.1 - p.2 = τ) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun p hp h => hτ (Finset.mem_image.2 ⟨p, hp, h⟩)
    simp [this]

lemma count_box (N : ℕ) (τ : Fin d → ℤ) :
    (((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card) =
      ∏ j, ((N : ℤ) - |τ j|).toNat := by
  have e1 : ((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card
      = ((box d N).filter (fun s => s + τ ∈ box d N)).card := by
    apply Finset.card_nbij' (fun p => p.2) (fun s => (s + τ, s))
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      refine ⟨h2, ?_⟩
      convert h1 using 1
      rw [← h3]
      abel
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hs ⊢
      exact ⟨⟨hs.2, hs.1⟩, by abel⟩
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
      refine Prod.ext ?_ rfl
      simp only
      rw [← hp.2]
      abel
    · intro s _
      rfl
  have e2 : (box d N).filter (fun s => s + τ ∈ box d N)
      = Fintype.piFinset (fun j => (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)) := by
    ext s
    simp [box, Fintype.mem_piFinset, Finset.mem_filter, forall_and]
  rw [e1, e2, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases le_total 0 (τ j) with ht | ht
  · rw [abs_of_nonneg ht]
    have : (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)
        = Finset.Ico 0 ((N : ℤ) - τ j) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [this, Int.card_Ico, sub_zero]
  · rw [abs_of_nonpos ht]
    have : (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)
        = Finset.Ico (-τ j) N := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [this, Int.card_Ico]

noncomputable def fac (N : ℕ) (t : ℤ) : ℝ := (((N : ℤ) - |t|).toNat : ℝ) / N

noncomputable def wt (N : ℕ) (τ : Fin d → ℤ) : ℝ := ∏ j, fac N (τ j)

lemma fac_nonneg (N : ℕ) (t : ℤ) : 0 ≤ fac N t := by
  unfold fac
  positivity

lemma fac_le_one (N : ℕ) (t : ℤ) : fac N t ≤ 1 := by
  unfold fac
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]
    have : ((N : ℤ) - |t|).toNat ≤ N := by
      have := abs_nonneg t
      omega
    exact_mod_cast this

lemma wt_nonneg (N : ℕ) (τ : Fin d → ℤ) : 0 ≤ wt N τ :=
  Finset.prod_nonneg fun j _ => fac_nonneg N (τ j)

lemma wt_le_one (N : ℕ) (τ : Fin d → ℤ) : wt N τ ≤ 1 :=
  Finset.prod_le_one (fun j _ => fac_nonneg N (τ j)) (fun j _ => fac_le_one N (τ j))

lemma fac_tendsto (t : ℤ) : Tendsto (fun N : ℕ => fac N t) atTop (𝓝 1) := by
  have h : ∀ᶠ N : ℕ in atTop, 1 - (|(t : ℝ)|) / N = fac N t := by
    filter_upwards [eventually_ge_atTop (t.natAbs + 1)] with N hN
    unfold fac
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : ((((N : ℤ) - |t|).toNat : ℕ) : ℤ) = (N : ℤ) - |t| := by
      apply Int.toNat_of_nonneg
      rw [Int.abs_eq_natAbs]
      omega
    have h3 : ((((N : ℤ) - |t|).toNat : ℕ) : ℝ) = (N : ℝ) - |(t : ℝ)| := by
      rw [← Int.cast_natCast, h2]
      push_cast
      ring
    rw [h3]
    field_simp
  refine Tendsto.congr' h ?_
  simpa using (tendsto_const_div_atTop_nhds_zero_nat (|(t : ℝ)|)).const_sub 1

lemma wt_tendsto (τ : Fin d → ℤ) : Tendsto (fun N : ℕ => wt N τ) atTop (𝓝 1) := by
  unfold wt
  simpa using tendsto_finset_prod Finset.univ (fun j _ => fac_tendsto (τ j))

lemma wt_eq (N : ℕ) (hN : N ≠ 0) (τ : Fin d → ℤ) :
    (((N : ℝ) ^ d)⁻¹ * (((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card : ℝ))
      = wt N τ := by
  rw [count_box]
  unfold wt fac
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [inv_mul_eq_div]

end Formalism.FourierDecayAlt.P.Herglotz

namespace Formalism.FourierDecayAlt.P

open Real Filter Topology Finset Formalism.FourierDecayAlt.P.Herglotz

theorem herglotz_Zd : Formalism.FourierDecayAlt.H.HerglotzZd := by
  intro d A hA hpos x
  change 0 ≤ (∑' σ, A σ * ee x σ).re
  have hN : ∀ N : ℕ, N ≠ 0 → 0 ≤ (∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)).re := by
    intro N hN
    have h := hpos (box d N) (fun σ => ee x σ)
    have h2 : ∑ σ ∈ box d N, ∑ σ' ∈ box d N, A (σ - σ') * ee x σ * starRingEnd ℂ (ee x σ')
        = ∑ σ ∈ box d N, ∑ σ' ∈ box d N, (fun τ => A τ * ee x τ) (σ - σ') := by
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
      simp only
      rw [mul_assoc, ee_mul_conj]
    rw [h2, dsum (fun τ => A τ * ee x τ) (box d N)] at h
    have h3 : ∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)
        = ((((N : ℝ) ^ d)⁻¹ : ℝ) : ℂ) * ∑' τ,
            ((((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card : ℂ) * (A τ * ee x τ)) := by
      rw [← tsum_mul_left]
      congr 1
      funext τ
      rw [← wt_eq N hN τ]
      push_cast
      ring
    rw [h3, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) h
  have hlim : Tendsto (fun N : ℕ => ∑' τ, ((wt N τ : ℝ) : ℂ) * (A τ * ee x τ)) atTop
      (𝓝 (∑' τ, A τ * ee x τ)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun τ => ‖A τ‖) hA ?_ ?_
    · intro τ
      have := ((Complex.continuous_ofReal.tendsto 1).comp (wt_tendsto τ)).mul_const (A τ * ee x τ)
      simpa using this
    · refine Eventually.of_forall fun N τ => ?_
      rw [norm_mul, norm_mul, norm_ee, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (wt_nonneg N τ)]
      nlinarith [wt_le_one N τ, norm_nonneg (A τ)]
  exact ge_of_tendsto ((Complex.continuous_re.tendsto _).comp hlim)
    (by filter_upwards [eventually_ne_atTop 0] with N hN' using hN N hN')

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
section
namespace Formalism.FourierDecayAlt.P.Interlace

open Finset Formalism.FourierDecayAlt.I

lemma interlaces_swap {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    Interlaces k u' u ρ := by
  intro i hi
  obtain ⟨a, b, c, d⟩ := h i hi
  exact ⟨b, a, d, c⟩

lemma antitone_on {f : ℕ → ℝ} {k : ℕ} (h : ∀ i, 1 ≤ i → i + 1 ≤ k → f (i + 1) ≤ f i) :
    ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → f j ≤ f i := by
  intro i j hi hij hjk
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact (h n (by omega) hjk).trans (ih (by omega))

lemma u_step {k : ℕ} {u u' ρ : ℕ → ℝ} (h : Interlaces k u u' ρ) :
    ∀ i, 1 ≤ i → i + 1 ≤ k → u (i + 1) ≤ u i := by
  intro i h1 h2
  obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨h1, by omega⟩)
  linarith

lemma sign_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) (e : ℝ)
    (he : -1 ≤ e ∧ e ≤ 1) :
    0 < (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hcard : (filter (fun i => ¬ i < l) (Icc 1 (k - 1))).card = k - l := by
    have : filter (fun i => ¬ i < l) (Icc 1 (k - 1)) = Icc l (k - 1) := by
      ext i; simp only [mem_filter, mem_Icc]; omega
    rw [this, Nat.card_Icc]; omega
  have key : (-1 : ℝ) ^ (k - l) * xpoly k ρ (Y + e) =
      ∏ i ∈ Icc 1 (k - 1), ((if i < l then (1 : ℝ) else -1) * (Y + e + ρ i)) := by
    rw [prod_mul_distrib, prod_ite, prod_const_one, one_mul, prod_const, hcard]
    rfl
  rw [key]
  apply prod_pos
  intro i hi
  have hi' := mem_Icc.1 hi
  obtain ⟨a, b, c, d⟩ := h i hi
  split_ifs with hil
  · have := hu' (i + 1) l (by omega) (by omega) hlk
    rw [one_mul]; linarith
  · have := hu l i hl1 (by omega) (by omega)
    rw [neg_one_mul]; linarith

theorem interlaceSign : InterlaceSign := by
  intro k u u' ρ l Y hl1 hlk h hc e he
  have he' : -1 ≤ e ∧ e ≤ 1 := by
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl <;> norm_num
  rcases hc with hA | hB
  · exact sign_core k u u' ρ l Y hl1 hlk h hA e he'
  · exact sign_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB e he'

lemma q_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  rw [← mul_prod_erase _ _ hl]
  apply mul_neg_of_neg_of_pos
  · apply mul_neg_of_neg_of_pos <;> linarith
  · apply prod_pos
    intro i hi
    have hne := ne_of_mem_erase hi
    have hi' := mem_Icc.1 (mem_of_mem_erase hi)
    rcases lt_or_gt_of_ne hne with hil | hil
    · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi'.1, by omega⟩)
      have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      have h2 := hu' i l hi'.1 (by omega) hlk
      apply mul_pos <;> linarith
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
      have h1 := hu l (j + 1) hl1 (by omega) hi'.2
      have h2 := hu l j hl1 (by omega) (by omega)
      apply mul_pos_of_neg_of_neg <;> linarith

theorem qPositive : QPositive := by
  intro k u u' ρ l Y T T' hl1 hlk h hc hT hT'
  have hTT : 0 < T * T' := mul_pos hT hT'
  have hP : ∏ i ∈ Icc 1 k, ((Y + 1/2 + u i) * (Y + 1/2 + u' i)) < 0 := by
    rcases hc with hA | hB
    · exact q_core k u u' ρ l Y hl1 hlk h hA
    · have := q_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
      rwa [prod_congr rfl (fun i _ => mul_comm (Y + 1/2 + u' i) (Y + 1/2 + u i))] at this
  unfold qpoly
  nlinarith

lemma ratio_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    xpoly k ρ (Y + 1) ^ 2 * (|Y + 1/2 + u l| * |Y + 1/2 + u' l|) ≤
      |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| := by
  have hu := antitone_on (u_step h)
  have hu' := antitone_on (u_step (interlaces_swap h))
  set g : ℕ → ℝ := fun j => |Y + 1/2 + u j| * |Y + 1/2 + u' j| with hg
  have hl : l ∈ Icc 1 k := mem_Icc.2 ⟨hl1, hlk⟩
  have hR : |(∏ i ∈ Icc 1 k, (Y + 1/2 + u i)) * (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))| =
      g l * ∏ i ∈ Icc 1 (k - 1), g (if i < l then i else i + 1) := by
    rw [abs_mul, abs_prod, abs_prod, ← prod_mul_distrib, ← mul_prod_erase _ _ hl]
    congr 1
    symm
    apply prod_nbij' (fun i => if i < l then i else i + 1) (fun j => if j < l then j else j - 1)
    · intro a ha
      simp only [mem_Icc] at ha
      simp only [mem_erase, mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      simp only [mem_Icc]
      split_ifs <;> omega
    · intro a ha
      simp only [mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      simp only [mem_erase, mem_Icc] at ha
      split_ifs <;> omega
    · intro a ha
      rfl
  rw [hR, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold xpoly
  rw [← prod_pow]
  apply prod_le_prod
  · intro i _; positivity
  · intro i hi
    have hi' := mem_Icc.1 hi
    obtain ⟨a, b, c, d⟩ := h i hi
    simp only [hg]
    split_ifs with hil
    · have h1 := hu' (i + 1) l (by omega) (by omega) hlk
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      nlinarith
    · have h1 := hu l i hl1 (by omega) (by omega)
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
      nlinarith

theorem interlaceRatio : InterlaceRatio := by
  intro k u u' ρ l Y hl1 hlk h hc
  rcases hc with hA | hB
  · exact ratio_core k u u' ρ l Y hl1 hlk h hA
  · have := ratio_core k u' u ρ l Y hl1 hlk (interlaces_swap h) hB
    rwa [mul_comm (|Y + 1/2 + u' l|), mul_comm (∏ i ∈ Icc 1 k, (Y + 1/2 + u' i))] at this

end Formalism.FourierDecayAlt.P.Interlace

theorem Formalism.FourierDecayAlt.P.interlacing_sign : Formalism.FourierDecayAlt.I.InterlaceSign := Formalism.FourierDecayAlt.P.Interlace.interlaceSign
theorem Formalism.FourierDecayAlt.P.q_positive_interlacing : Formalism.FourierDecayAlt.I.QPositive := Formalism.FourierDecayAlt.P.Interlace.qPositive
theorem Formalism.FourierDecayAlt.P.interlacing_ratio : Formalism.FourierDecayAlt.I.InterlaceRatio := Formalism.FourierDecayAlt.P.Interlace.interlaceRatio
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MiddleThirdEstimate
section
namespace Formalism.FourierDecayAlt.P.E2

open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory

theorem middleThird_ok : MiddleThird := by
  intro n lam α β Y hI hroot hY1 hY2
  have hL : 0 < β - α := by linarith
  have key : ∀ s, (β-α)/3 ≤ |Y + lam s| := by
    intro s
    have h := hroot s
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h
    rcases h with h | h
    · rw [le_abs]; left; linarith
    · rw [le_abs]; right; linarith
  have key2 : ∀ s, (β-α)/4 ≤ |Y + 1 + lam s| := by
    intro s
    have h := hroot s
    simp only [Set.mem_Ioo, not_and_or, not_lt] at h
    rcases h with h | h
    · rw [le_abs]; left; linarith
    · rw [le_abs]; right; linarith
  constructor
  · rw [← Finset.prod_div_distrib, Finset.abs_prod]
    calc ∏ s, |(Y + 1 + lam s) / (Y + lam s)| ≤ ∏ _s : Fin n, Real.exp (3 / (β - α)) := by
          apply Finset.prod_le_prod (fun s _ => abs_nonneg _)
          intro s _
          have h1 := key s
          have hpos : 0 < |Y + lam s| := by linarith
          have hne : Y + lam s ≠ 0 := abs_pos.mp hpos
          have e0 : (Y + 1 + lam s) / (Y + lam s) = 1 + 1 / (Y + lam s) := by field_simp; ring
          rw [e0]
          calc |1 + 1 / (Y + lam s)| ≤ 1 + 1/|Y + lam s| := by
                 have := abs_add_le (1:ℝ) (1 / (Y + lam s))
                 rw [abs_one, abs_div, abs_one] at this; exact this
            _ ≤ 1 + 3/(β-α) := by
                 have h2 : 1/|Y + lam s| ≤ 1/((β-α)/3) := one_div_le_one_div_of_le (by linarith) h1
                 have e : 1/((β-α)/3) = 3/(β-α) := by field_simp
                 linarith
            _ ≤ Real.exp (3/(β-α)) := by linarith [Real.add_one_le_exp (3/(β-α))]
      _ = Real.exp (3 * n / (β - α)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; congr 1; ring
  · rw [← Finset.prod_div_distrib, Finset.abs_prod]
    calc ∏ s, |(Y + lam s) / (Y + 1 + lam s)| ≤ ∏ _s : Fin n, Real.exp (4 / (β - α)) := by
          apply Finset.prod_le_prod (fun s _ => abs_nonneg _)
          intro s _
          have h1 := key2 s
          have hpos : 0 < |Y + 1 + lam s| := by linarith
          have hne : Y + 1 + lam s ≠ 0 := abs_pos.mp hpos
          have e0 : (Y + lam s) / (Y + 1 + lam s) = 1 + (-1) / (Y + 1 + lam s) := by field_simp; ring
          rw [e0]
          calc |1 + (-1) / (Y + 1 + lam s)| ≤ 1 + 1/|Y + 1 + lam s| := by
                 have := abs_add_le (1:ℝ) ((-1) / (Y + 1 + lam s))
                 rw [abs_one, abs_div, abs_neg, abs_one] at this; exact this
            _ ≤ 1 + 4/(β-α) := by
                 have h2 : 1/|Y + 1 + lam s| ≤ 1/((β-α)/4) := one_div_le_one_div_of_le (by linarith) h1
                 have e : 1/((β-α)/4) = 4/(β-α) := by field_simp
                 linarith
            _ ≤ Real.exp (4/(β-α)) := by linarith [Real.add_one_le_exp (4/(β-α))]
      _ = Real.exp (4 * n / (β - α)) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]; congr 1; ring

theorem bdd_add' {Λ : Type} {f g : Λ → ℂ} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  exact ⟨a + b, fun x => (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩

theorem bdd_smul' {Λ : Type} {f : Λ → ℂ} (c : ℂ) (hf : Bdd f) : Bdd (c • f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨‖c‖ * a, fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (ha x) (norm_nonneg _)⟩

theorem bdd_zero' {Λ : Type} : Bdd (0 : Λ → ℂ) := ⟨0, fun x => by simp⟩

theorem bdd_sum' {Λ ι : Type} (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    Bdd (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using bdd_zero'
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact bdd_add' (hf a) ih

theorem lim_sum' {Λ ι : Type} (LIM : (Λ → ℂ) → ℂ)
    (h1 : ∀ f g, Bdd f → Bdd g → LIM (f + g) = LIM f + LIM g)
    (h2 : ∀ (c : ℂ) f, Bdd f → LIM (c • f) = c * LIM f)
    (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    LIM (∑ i ∈ T, f i) = ∑ i ∈ T, LIM (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := h2 0 0 bdd_zero'
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1 _ _ (hf a) (bdd_sum' s f hf), ih]

theorem mpd : MeanPosDef := by
  intro Λ _ H _ _ LIM h1 h2 h3 h4 u B hu S c
  have hB : ∀ a b : Λ, Bdd (fun x => inner ℂ (u (x + a)) (u (x + b))) := fun a b =>
    ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul (hu _) (hu _) (norm_nonneg _) ((norm_nonneg _).trans (hu (x+a))))⟩
  have hB0 : ∀ b : Λ, Bdd (fun x => inner ℂ (u x) (u (x + b))) := fun b => by simpa using hB 0 b
  have e1 : ∀ σ σ' : Λ, LIM (fun x => inner ℂ (u x) (u (x + (σ - σ'))))
      = LIM (fun x => inner ℂ (u (x + σ')) (u (x + σ))) := by
    intro σ σ'
    rw [← h4 _ σ' (hB0 (σ - σ'))]
    congr 1; funext x; congr 2; abel
  have e2 : (∑ σ ∈ S, ∑ σ' ∈ S,
        LIM (fun x => inner ℂ (u x) (u (x + (σ - σ')))) * c σ * starRingEnd ℂ (c σ'))
      = LIM (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) := by
    rw [lim_sum' LIM h1 h2 S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lim_sum' LIM h1 h2 S _ (fun σ' => bdd_smul' _ (hB σ' σ))]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [h2 _ _ (hB σ' σ), e1]; ring
  rw [e2]
  apply h3
  · exact bdd_sum' S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))
  · intro x
    have key : (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) x
        = inner ℂ (∑ σ ∈ S, c σ • u (x + σ)) (∑ σ ∈ S, c σ • u (x + σ)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [key]
    exact ⟨inner_self_nonneg (𝕜 := ℂ), inner_self_im (𝕜 := ℂ) _⟩

end Formalism.FourierDecayAlt.P.E2

theorem Formalism.FourierDecayAlt.P.middle_third_estimate : Formalism.FourierDecayAlt.E.MiddleThird := Formalism.FourierDecayAlt.P.E2.middleThird_ok
theorem Formalism.FourierDecayAlt.P.mean_matrix_posDef : Formalism.FourierDecayAlt.E.MeanPosDef := Formalism.FourierDecayAlt.P.E2.mpd
end

