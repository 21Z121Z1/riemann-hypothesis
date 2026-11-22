import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatement
section
open MeasureTheory Set
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SlabLemma

noncomputable def wt (c t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * c * t))

lemma wt_add (c s t : ℝ) : wt c (s + t) = wt c s * wt c t := by
  show ENNReal.ofReal (Real.exp (2 * c * (s + t))) =
    ENNReal.ofReal (Real.exp (2 * c * s)) * ENNReal.ofReal (Real.exp (2 * c * t))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

lemma wt_ne_zero (c t : ℝ) : wt c t ≠ 0 := by
  show ENNReal.ofReal (Real.exp (2 * c * t)) ≠ 0
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

lemma measurable_wt (c : ℝ) : Measurable (wt c) := by
  show Measurable fun t => ENNReal.ofReal (Real.exp (2 * c * t))
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.ennreal_ofReal

noncomputable def unitInd : ℝ → ℝ≥0∞ := (Ico (0 : ℝ) 1).indicator 1

lemma measurable_unitInd : Measurable unitInd := by
  show Measurable ((Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞))
  exact measurable_const.indicator measurableSet_Ico

lemma lintegral_unitInd (x : ℝ) : ∫⁻ t, unitInd (x - t) = 1 := by
  show ∫⁻ t, (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (x - t) = 1
  rw [lintegral_sub_left_eq_self (fun y => (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) y) x,
    lintegral_indicator_one measurableSet_Ico, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

noncomputable def line (F : G → ℝ≥0∞) (a : ℝ → G) (c : ℝ) (p : G × G) : ℝ≥0∞ :=
  ∫⁻ t, F (p.1 * p.2 * a t) * wt c t

lemma measurable_line {F : G → ℝ≥0∞} {a : ℝ → G} (c : ℝ) (hF : Measurable F) (ha : Measurable a) :
    Measurable (line F a c) := by
  have hm : Measurable fun q : (G × G) × ℝ => F (q.1.1 * q.1.2 * a q.2) * wt c q.2 :=
    (hF.comp ((measurable_fst.fst.mul measurable_fst.snd).mul (ha.comp measurable_snd))).mul
      ((measurable_wt c).comp measurable_snd)
  exact hm.lintegral_prod_right'

lemma line_shift {F : G → ℝ≥0∞} {a : ℝ → G} {c : ℝ} (hadd : ∀ s t, a (s + t) = a s * a t) (u m : G) (s : ℝ)
    (hF : Measurable F) (ha : Measurable a) :
    line F a c (u, m * a s) = wt c (-s) * line F a c (u, m) := by
  show ∫⁻ t, F (u * (m * a s) * a t) * wt c t = wt c (-s) * ∫⁻ t, F (u * m * a t) * wt c t
  rw [← lintegral_sub_right_eq_self (fun t => F (u * (m * a s) * a t) * wt c t) s,
    ← lintegral_const_mul _ (show Measurable fun t => F (u * m * a t) * wt c t from
      (hF.comp (measurable_const.mul ha)).mul (measurable_wt c))]
  refine lintegral_congr fun t => ?_
  have h1 : u * (m * a s) * a (t - s) = u * m * a t := by
    have h2 : s + (t - s) = t := by ring
    rw [mul_assoc u m, mul_assoc u, mul_assoc m, ← hadd, h2]
  rw [h1, sub_eq_add_neg, wt_add]
  ring

lemma slab_identity (μM : Measure G) [SFinite μM] {S : Set G} {a : ℝ → G} {δ : G → ℝ≥0∞} {τ : G → ℝ} {c : ℝ}
    (hSc : μM Sᶜ = 0) (ha : Measurable a) (hδ : Measurable δ) (hτ : Measurable τ)
    (hinv : ∀ t, μM.map (· * a t) = μM)
    (hδa : ∀ m ∈ S, ∀ t, δ (m * a t) = δ m * wt c t)
    (hτa : ∀ m ∈ S, ∀ t, τ (m * a t) = τ m + t)
    {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume ∂μM = ∫⁻ m, δ m * H m ∂μM := by
  have hSae : ∀ᵐ m ∂μM, m ∈ S := ae_iff.mpr hSc
  have hU : Measurable fun m => unitInd (τ m) := measurable_unitInd.comp hτ
  have e1 : ∀ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume =
      ∫⁻ t, unitInd (τ m) * δ m * (H (m * a t) * wt c t) := fun m =>
    (lintegral_const_mul _ ((hH.comp (measurable_const.mul ha)).mul (measurable_wt c))).symm
  have hmeas : Measurable (Function.uncurry fun (m : G) (t : ℝ) =>
      unitInd (τ m) * δ m * (H (m * a t) * wt c t)) :=
    ((hU.comp measurable_fst).mul (hδ.comp measurable_fst)).mul
      ((hH.comp (measurable_fst.mul (ha.comp measurable_snd))).mul ((measurable_wt c).comp measurable_snd))
  have hmeas2 : Measurable (Function.uncurry fun (t : ℝ) (m : G) => unitInd (τ m - t) * (δ m * H m)) :=
    (measurable_unitInd.comp ((hτ.comp measurable_snd).sub measurable_fst)).mul
      ((hδ.comp measurable_snd).mul (hH.comp measurable_snd))
  have e2 : ∀ t, ∫⁻ m, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂μM =
      ∫⁻ m, unitInd (τ m - t) * (δ m * H m) ∂μM := by
    intro t
    have hg : Measurable fun m => unitInd (τ m - t) * (δ m * H m) :=
      (measurable_unitInd.comp (hτ.sub measurable_const)).mul (hδ.mul hH)
    have hf : Measurable fun m : G => m * a t := measurable_id.mul measurable_const
    conv_rhs => rw [← hinv t]
    rw [lintegral_map hg hf]
    refine lintegral_congr_ae (hSae.mono fun m hm => ?_)
    show unitInd (τ m) * δ m * (H (m * a t) * wt c t) =
      unitInd (τ (m * a t) - t) * (δ (m * a t) * H (m * a t))
    rw [hτa m hm t, hδa m hm t, add_sub_cancel_right]
    ring
  calc ∫⁻ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume ∂μM
      = ∫⁻ m, ∫⁻ t, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂volume ∂μM := lintegral_congr e1
    _ = ∫⁻ t, ∫⁻ m, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂μM ∂volume :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ t, ∫⁻ m, unitInd (τ m - t) * (δ m * H m) ∂μM ∂volume := lintegral_congr e2
    _ = ∫⁻ m, ∫⁻ t, unitInd (τ m - t) * (δ m * H m) ∂volume ∂μM :=
      lintegral_lintegral_swap hmeas2.aemeasurable
    _ = ∫⁻ m, δ m * H m ∂μM := by
      refine lintegral_congr fun m => ?_
      rw [lintegral_mul_const _ (show Measurable fun t => unitInd (τ m - t) from
          measurable_unitInd.comp (measurable_const.sub measurable_id)),
        lintegral_unitInd, one_mul]

end GlobalTheory.CompanionTheory.SlabLemma

open GlobalTheory.CompanionTheory.SlabLemma in

theorem GlobalTheory.CompanionTheory.SlabLemma.slab : CompanionTheory.RgExh.Dec.N.S.Slab := by
  intro G _ _ _ μN μM _ _ S a δ τ c hSm hSc ha hδ hτ hadd hS hinv hδa hτa hδ0 F hF hfin
  have hSae : ∀ᵐ m ∂μM, m ∈ S := ae_iff.mpr hSc
  have hline : Measurable (line F a c) := measurable_line c hF ha
  have hmeasF : Measurable fun q : G × G => δ q.2 * F (q.1 * q.2) :=
    (hδ.comp measurable_snd).mul (hF.comp (measurable_fst.mul measurable_snd))
  have hae1 : ∀ᵐ u ∂μN, ∫⁻ m, δ m * F (u * m) ∂μM < ⊤ :=
    ae_lt_top hmeasF.lintegral_prod_right' hfin.ne
  have key : ∀ᵐ u ∂μN, ∀ᵐ m ∂μM, line F a c (u, m) < ⊤ := by
    refine hae1.mono fun u hu => ?_
    have hid : ∫⁻ m, unitInd (τ m) * δ m * line F a c (u, m) ∂μM = ∫⁻ m, δ m * F (u * m) ∂μM := by
      have h := slab_identity μM hSc ha hδ hτ hinv hδa hτa (H := fun x => F (u * x))
        (hF.comp (measurable_const.mul measurable_id))
      refine Eq.trans (lintegral_congr fun m => ?_) h
      show unitInd (τ m) * δ m * ∫⁻ t, F (u * m * a t) * wt c t =
        unitInd (τ m) * δ m * ∫⁻ t, F (u * (m * a t)) * wt c t
      simp only [mul_assoc]
    have hfin2 : ∫⁻ m, unitInd (τ m) * δ m * line F a c (u, m) ∂μM < ⊤ := hid ▸ hu
    have hmeas3 : Measurable fun m => unitInd (τ m) * δ m * line F a c (u, m) :=
      ((measurable_unitInd.comp hτ).mul hδ).mul (hline.comp (measurable_const.prodMk measurable_id))
    have hae2 := ae_lt_top hmeas3 hfin2.ne
    have hshift : ∀ k : ℤ, ∀ᵐ m ∂μM,
        unitInd (τ (m * a k)) * δ (m * a k) * line F a c (u, m * a k) < ⊤ := by
      intro k
      have hf : AEMeasurable (fun m : G => m * a k) μM := (measurable_id.mul measurable_const).aemeasurable
      rw [← hinv k] at hae2
      exact ae_of_ae_map hf hae2
    have hall : ∀ᵐ m ∂μM, ∀ k : ℤ,
        unitInd (τ (m * a k)) * δ (m * a k) * line F a c (u, m * a k) < ⊤ := ae_all_iff.mpr hshift
    filter_upwards [hall, hSae] with m hm hmS
    have hmk : m * a ((-⌊τ m⌋ : ℤ) : ℝ) ∈ S := hS m hmS _
    have hmem : τ m + ((-⌊τ m⌋ : ℤ) : ℝ) ∈ Ico (0 : ℝ) 1 := by
      constructor <;> push_cast <;> linarith [Int.floor_le (τ m), Int.lt_floor_add_one (τ m)]
    have hU1 : unitInd (τ (m * a ((-⌊τ m⌋ : ℤ) : ℝ))) = 1 := by
      rw [hτa m hmS]
      exact (Set.indicator_of_mem hmem 1).trans rfl
    have h1 := hm (-⌊τ m⌋)
    rw [hU1, one_mul] at h1
    have hL : line F a c (u, m * a ((-⌊τ m⌋ : ℤ) : ℝ)) < ⊤ := by
      rcases ENNReal.mul_lt_top_iff.mp h1 with h | h | h
      · exact h.2
      · exact absurd h (hδ0 _ hmk)
      · rw [h]
        exact ENNReal.zero_lt_top
    rw [line_shift hadd u m _ hF ha] at hL
    rcases ENNReal.mul_lt_top_iff.mp hL with h | h | h
    · exact h.2
    · exact absurd h (wt_ne_zero _ _)
    · rw [h]
      exact ENNReal.zero_lt_top
  have hset : MeasurableSet {p : G × G | line F a c p < ⊤} := measurableSet_lt hline measurable_const
  have hprod : ∀ᵐ p ∂μN.prod μM, line F a c p < ⊤ := (Measure.ae_prod_iff_ae_ae hset).mpr key
  filter_upwards [hprod] with p hp
  exact lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hp
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardBlocksLevelSum
section
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock

theorem card_lev_lt_succ {n : ℕ} (lev : Fin n → ℕ) (k : ℕ) :
    (univ.filter fun a => lev a < k + 1).card =
      (univ.filter fun a => lev a < k).card + (univ.filter fun a => lev a = k).card := by
  have hd : Disjoint (univ.filter fun a => lev a < k) (univ.filter fun a => lev a = k) := by
    refine Finset.disjoint_left.2 fun a ha hb => ?_
    simp only [mem_filter, mem_univ, true_and] at ha hb
    omega
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and, mem_union]
  omega

theorem sum_sz_castLE {n M : ℕ} (lev : Fin n → ℕ) : ∀ (k : ℕ) (hk : k ≤ M),
    ∑ b : Fin k, sz lev M (Fin.castLE hk b) = (univ.filter fun a => lev a < k).card := by
  intro k
  induction k with
  | zero => intro hk; simp
  | succ k ih =>
    intro hk
    rw [Fin.sum_univ_castSucc, card_lev_lt_succ, ← ih (by omega)]
    rfl

theorem lt_card_iff {n : ℕ} {lev : Fin n → ℕ} (hm : Monotone lev) (k : ℕ) (a : Fin n) :
    (a : ℕ) < (univ.filter fun b => lev b < k).card ↔ lev a < k := by
  constructor
  · intro h
    by_contra hn
    have hs : (univ.filter fun b => lev b < k) ⊆ Finset.Iio a := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      exact Finset.mem_Iio.2 (hm.reflect_lt (by omega))
    have := Finset.card_le_card hs
    rw [Fin.card_Iio] at this
    omega
  · intro h
    have hs : Finset.Iic a ⊆ (univ.filter fun b => lev b < k) := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and]
      exact lt_of_le_of_lt (hm (Finset.mem_Iic.1 hb)) h
    have := Finset.card_le_card hs
    rw [Fin.card_Iic] at this
    omega

theorem lev_stdBlocks {n M : ℕ} (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n) (hm : Monotone lev)
    (i : Fin M) (p : Fin (sz lev M i)) : lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ) := by
  have hv := stdBlocks_val (sz lev M) h i p
  rw [sum_sz_castLE lev (i : ℕ) i.2.le] at hv
  have hp : (p : ℕ) < (univ.filter fun a => lev a = (i : ℕ)).card := p.2
  have h1 := lt_card_iff hm (i : ℕ) (stdBlocks (sz lev M) h ⟨i, p⟩)
  have h2 := lt_card_iff hm ((i : ℕ) + 1) (stdBlocks (sz lev M) h ⟨i, p⟩)
  rw [card_lev_lt_succ] at h2
  have h3 := h2.1 (by omega)
  have h4 : ¬ lev (stdBlocks (sz lev M) h ⟨i, p⟩) < (i : ℕ) := fun hl => by
    have := h1.2 hl
    omega
  omega

theorem stdBlocks_clusters : ∀ (n M : ℕ) (lev : Fin n → ℕ) (h : ∑ i, sz lev M i = n), Monotone lev → (∀ a, lev a < M) →
    (∀ (i : Fin M) (p : Fin (sz lev M i)), lev (stdBlocks (sz lev M) h ⟨i, p⟩) = (i : ℕ)) ∧
    ∀ (f : Fin n → ℂ) (i : Fin M), ∑ p : Fin (sz lev M i), f (stdBlocks (sz lev M) h ⟨i, p⟩) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), f a := by
  intro n M lev h hm _
  refine ⟨lev_stdBlocks lev h hm, fun f i => ?_⟩
  refine Finset.sum_bij (fun p _ => stdBlocks (sz lev M) h ⟨i, p⟩) ?_ ?_ ?_ ?_
  · intro p _
    simp only [mem_filter, mem_univ, true_and]
    exact lev_stdBlocks lev h hm i p
  · intro p _ q _ hpq
    have := (stdBlocks (sz lev M) h).injective hpq
    simpa using this
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    obtain ⟨⟨j, q⟩, rfl⟩ := (stdBlocks (sz lev M) h).surjective a
    have hj : j = i := Fin.ext ((lev_stdBlocks lev h hm j q).symm.trans ha)
    subst hj
    exact ⟨q, mem_univ _, rfl⟩
  · intro p _
    rfl

end GlobalTheory.CompanionTheory.RgCOBlock
end

