import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0003
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0082
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BernEqProd
section
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain

namespace GlobalTheory.TopsChoice

open Formalism.FrobeniusOrbits Finset

lemma bern_eq_prod {α : Type} [Fintype α] [DecidableEq α] (δ : ℝ) (T : Finset α) :
    bern δ T = (∏ _a ∈ T, δ) * ∏ _a ∈ univ \ T, (1 - δ) := by
  simp [bern, Finset.card_univ_diff]

lemma fibre_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (δ : ℝ)
    (f : β → α) (hf : Function.Injective f) (S : Finset β) :
    ∑ T : Finset α, (if univ.filter (fun i => f i ∈ T) = S then bern δ T else 0) = bern δ S := by
  classical
  set g : α → ℝ := fun a => if a ∈ (univ \ S).image f then 0 else δ with hg
  set h : α → ℝ := fun a => if a ∈ S.image f then 0 else 1 - δ with hh
  have h1 := Finset.prod_add g h (univ : Finset α)
  rw [powerset_univ] at h1
  have h2 : ∏ a, (g a + h a) = bern δ S := by
    rw [← Finset.prod_subset (subset_univ ((univ : Finset β).image f)), prod_image hf.injOn]
    · rw [bern_eq_prod, ← prod_sdiff (subset_univ S), mul_comm]
      congr 1
      · refine prod_congr rfl fun i hi => ?_
        simp [hg, hh, hf.eq_iff, hi]
      · refine prod_congr rfl fun i hi => ?_
        have hi' : i ∉ S := (mem_sdiff.mp hi).2
        simp [hg, hh, hf.eq_iff, hi']
    · intro a _ ha
      have ha1 : a ∉ (univ \ S).image f := fun h' => ha (image_subset_image (subset_univ _) h')
      have ha2 : a ∉ S.image f := fun h' => ha (image_subset_image (subset_univ _) h')
      simp only [hg, hh, if_neg ha1, if_neg ha2]
      ring
  rw [← h2, h1]
  refine sum_congr rfl fun T _ => ?_
  split_ifs with hT
  · rw [bern_eq_prod]
    congr 1
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ (univ \ S).image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        exact (mem_sdiff.mp hi).2 (hT ▸ mem_filter.mpr ⟨mem_univ _, ha⟩)
      simp only [hg, if_neg this]
    · refine prod_congr rfl fun a ha => ?_
      have : a ∉ S.image f := by
        intro h'
        obtain ⟨i, hi, rfl⟩ := mem_image.mp h'
        rw [← hT] at hi
        exact (mem_sdiff.mp ha).2 (mem_filter.mp hi).2
      simp only [hh, if_neg this]
  · have : ∃ i, ¬ (f i ∈ T ↔ i ∈ S) := by
      by_contra hc
      push Not at hc
      exact hT (by ext i; simp [hc i])
    obtain ⟨i, hi⟩ := this
    by_cases hiS : i ∈ S
    · have hT' : f i ∉ T := fun h' => hi ⟨fun _ => hiS, fun _ => h'⟩
      rw [prod_eq_zero (s := univ \ T) (i := f i) (by simp [hT']), mul_zero]
      simp only [hh, if_pos (mem_image_of_mem f hiS)]
    · have hT' : f i ∈ T := by
        by_contra h'
        exact hi ⟨fun h'' => absurd h'' h', fun h'' => absurd h'' hiS⟩
      rw [prod_eq_zero (s := T) (i := f i) hT', zero_mul]
      simp only [hg, if_pos (mem_image_of_mem f (mem_sdiff.mpr ⟨mem_univ i, hiS⟩))]

lemma marginal {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (δ : ℝ)
    (f : β → α) (hf : Function.Injective f) (A : Finset β → Prop) [DecidablePred A] :
    ∑ T : Finset α, (if A (univ.filter (fun i => f i ∈ T)) then bern δ T else 0) =
      ∑ S : Finset β, if A S then bern δ S else 0 := by
  calc ∑ T : Finset α, (if A (univ.filter (fun i => f i ∈ T)) then bern δ T else 0)
      = ∑ T : Finset α, ∑ S : Finset β,
          (if univ.filter (fun i => f i ∈ T) = S then (if A S then bern δ T else 0) else 0) := by
        refine sum_congr rfl fun T _ => ?_
        rw [Finset.sum_ite_eq]
        simp
    _ = ∑ S : Finset β, if A S then bern δ S else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun S _ => ?_
        by_cases hA : A S
        · simp only [if_pos hA]
          exact fibre_sum δ f hf S
        · simp [hA]

open Classical in
lemma fin_sum_eq (n : ℕ) (δ : ℝ) (i₀ : Fin n) (A : Finset ℕ → Prop) :
    (∑ S : Finset (Fin n), if i₀ ∈ S ∧ A (S.map Fin.valEmbedding) then bern δ S else 0) =
      Formalism.G0.condProbAt n δ i₀ A * δ := by
  unfold Formalism.G0.condProbAt
  rw [sum_mul]
  refine Finset.sum_bij (fun S _ => S.map Fin.valEmbedding) ?_ ?_ ?_ ?_
  · intro S _
    rw [mem_powerset]
    intro x hx
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    simp
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    refine ⟨univ.filter (fun i : Fin n => (i : ℕ) ∈ T), mem_univ _, ?_⟩
    ext x
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro hx
      exact ⟨⟨x, mem_range.mp (mem_powerset.mp hT hx)⟩, hx, rfl⟩
  · intro S _
    have hm : (i₀ : ℕ) ∈ S.map Fin.valEmbedding ↔ i₀ ∈ S :=
      Finset.mem_map' Fin.valEmbedding
    simp only [hm]
    split_ifs with h
    · have hc : 1 ≤ S.card := card_pos.mpr ⟨i₀, h.1⟩
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hc
      simp only [bern, card_map, Fintype.card_fin, hk, Nat.add_sub_cancel]
      ring
    · simp

open Classical in

lemma orbit_sum {α : Type} [Fintype α] [DecidableEq α] [AddCommGroup α] (δ : ℝ) (b h t : α)
    (ht : ∃ i : ℕ, b + i • h = t) (A : Finset ℕ → Prop) :
    ∃ i₀ < addOrderOf h,
      (∑ T : Finset α, if t ∈ T ∧ A ((univ.filter
          (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T)).map Fin.valEmbedding)
        then bern δ T else 0) = Formalism.G0.condProbAt (addOrderOf h) δ i₀ A * δ := by
  obtain ⟨i, hi⟩ := ht
  have hpos : 0 < addOrderOf h := addOrderOf_pos h
  have hlt : i % addOrderOf h < addOrderOf h := Nat.mod_lt _ hpos
  refine ⟨i % addOrderOf h, hlt, ?_⟩
  have hinj : Function.Injective (fun j : Fin (addOrderOf h) => b + (j : ℕ) • h) := by
    intro j k hjk
    have := add_left_cancel hjk
    exact Fin.ext (nsmul_injOn_Iio_addOrderOf j.2 k.2 this)
  rw [← fin_sum_eq (addOrderOf h) δ ⟨_, hlt⟩ A, ← marginal δ _ hinj
    (fun S => (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ S ∧ A (S.map Fin.valEmbedding))]
  refine sum_congr rfl fun T _ => ?_
  have : t ∈ T ↔ (⟨_, hlt⟩ : Fin (addOrderOf h)) ∈ univ.filter
      (fun i : Fin (addOrderOf h) => b + (i : ℕ) • h ∈ T) := by
    simp [mod_addOrderOf_nsmul, hi]
  simp only [this]

end GlobalTheory.TopsChoice

namespace GlobalTheory

open GlobalTheory.TopsChoice

theorem topsChoice : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ Cb x₀ : ℝ, 0 < Cb ∧ ∀ s : Scale, s.eps = eps → x₀ ≤ s.x → ∀ e L₂ : ℕ, s.x ^ Formalism.MainNotions.G.hG s / 2 ≤ ((2 ^ e : ℕ) : ℝ) → ((2 ^ e : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s → (L₂ : ℝ) ≤ 1242 / eps → ∀ bs : ZMod (2 ^ e) → ZMod (2 ^ e) → ZMod (2 ^ e), (∀ h t, ∃ i : ℕ, bs h t + i • h = t) → (∀ h t, bs h (t + h) = bs h t) → ∀ (PP : Finset ℕ) (hp : ℕ → ZMod (2 ^ e)) (ω : ℕ → ℝ), (∀ p, 0 ≤ ω p) → (∀ p ∈ PP, s.x ^ (eps / 4) ≤ (addOrderOf (hp p) : ℝ)) → ∃ TT : Finset (ZMod (2 ^ e)), s.delta1 * ((2 ^ e : ℕ) : ℝ) / 2 ≤ (TT.card : ℝ) ∧ (TT.card : ℝ) ≤ 2 * s.delta1 * ((2 ^ e : ℕ) : ℝ) ∧ ∑ p ∈ PP, ω p * (({t : ZMod (2 ^ e) | t ∈ TT ∧ ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ TT)) L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x}.ncard : ℕ) : ℝ) ≤ 4 * (Cb * s.x ^ (-2 : ℝ)) * s.delta1 * ((2 ^ e : ℕ) : ℝ) * ∑ p ∈ PP, ω p := by
  classical
  intro eps he he'
  obtain ⟨Cb, x₀, hCb, hnum⟩ := GlobalTheory.T.parameter_inequalities_good eps he he'
  refine ⟨Cb, max x₀ 32, hCb, ?_⟩
  intro s hs hx e L₂ hlo hhi hL bs hbs _ PP hp ω hω hPP
  have hx1 : 1 < s.x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hx32 : 32 ≤ s.x := le_trans (le_max_right _ _) hx
  have hδ : 0 < s.delta1 := Real.rpow_pos_of_pos hx0 _
  have hδ1 : s.delta1 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by have := s.eps_pos; linarith)
  haveI : NeZero (2 ^ e) := ⟨by positivity⟩
  have hcard : Fintype.card (ZMod (2 ^ e)) = 2 ^ e := ZMod.card _
  have h16 : 16 ≤ s.delta1 * (Fintype.card (ZMod (2 ^ e)) : ℝ) := by
    rw [hcard]
    have h1 : s.x ≤ s.delta1 * s.x ^ Formalism.MainNotions.G.hG s := by
      unfold Scale.delta1 Formalism.MainNotions.G.hG
      rw [← Real.rpow_add hx0]
      calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1.le (by have := s.eps_pos; linarith)
    have := mul_le_mul_of_nonneg_left hlo hδ.le
    linarith
  have hβ : 0 ≤ Cb * s.x ^ (-2 : ℝ) := by positivity
  obtain ⟨T, hT1, hT2, hT3⟩ := Formalism.FrobeniusOrbits.hostTops (ZMod (2 ^ e)) PP s.delta1 (Cb * s.x ^ (-2 : ℝ))
    (fun p => ω p)
    (fun p t T => ¬ Formalism.MainNotions.G.IsGoodOrbit (addOrderOf (hp p)) (Finset.univ.filter
      (fun i : Fin (addOrderOf (hp p)) => bs (hp p) t + (i : ℕ) • hp p ∈ T)) L₂ (Formalism.MainNotions.G.KG s)
      (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
    hδ hδ1 hβ (fun p => hω p) h16 (by
      intro p t
      have hn : ((addOrderOf (hp p) : ℕ) : ℝ) ≤ 2 * s.x ^ Formalism.MainNotions.G.hG s := by
        refine le_trans ?_ hhi
        exact Nat.cast_le.mpr (addOrderOf_le_card_univ.trans hcard.le)
      obtain ⟨h1, h2⟩ := hnum s hs (le_trans (le_max_left _ _) hx) (addOrderOf (hp p)) L₂
        (hPP p p.2) hn hL
      obtain ⟨i₀, hi₀, hsum⟩ := orbit_sum s.delta1 (bs (hp p) t) (hp p) t (hbs _ _)
        (fun T => ¬ Formalism.G0.GoodOrbitIntervalTileCondition (addOrderOf (hp p)) T L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s)
          (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x)
          (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
          (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x))
      have hu : 1 ≤ Formalism.MainNotions.G.goodU s.delta1 := Nat.ceil_pos.mpr (by positivity)
      have h3 := GlobalTheory.T.choice_of_tops (addOrderOf (hp p)) s.delta1 L₂ (Formalism.MainNotions.G.KG s) (Formalism.MainNotions.G.rG s)
        (Formalism.MainNotions.G.goodU s.delta1) (Formalism.MainNotions.G.orbitSmallMultiplicity (Formalism.MainNotions.G.rG s) (Formalism.MainNotions.G.hG s) s.x)
        (Formalism.MainNotions.G.goodG' (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x)
        (Formalism.MainNotions.G.orbitWindowCount (Formalism.MainNotions.G.rG s) s.delta1 (Formalism.MainNotions.G.hG s) s.x) i₀ hδ.le hδ1
        (Nat.le_add_left 1 _) hu h1 hi₀
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (h3.trans h2) hδ.le)
      rw [← hsum]
      unfold Formalism.MainNotions.G.IsGoodOrbit
      convert rfl)
  rw [hcard] at hT1 hT2 hT3
  refine ⟨T, hT1, hT2, ?_⟩
  rw [← Finset.sum_coe_sort PP, ← Finset.sum_coe_sort PP ω]
  refine le_trans (le_of_eq ?_) hT3
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  rw [← Set.ncard_coe_finset, Finset.coe_filter]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjPConjP
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open nonZeroDivisors
noncomputable section
namespace GlobalTheory.CharVal.Vp
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem conjP_conjP' (P : HeightOneSpectrum (𝓞 E)) : conjPrime₂ (conjPrime₂ P) = P := by
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

omit [StarRing E] in
theorem ne0 (P : HeightOneSpectrum (𝓞 E)) : (P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 P.ne_bot

omit [StarRing E] in
theorem maxV_self (P : HeightOneSpectrum (𝓞 E)) :
    MaxV P ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) (WithZero.exp (-1 : ℤ)) := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using hr)
    simpa using this
  · obtain ⟨r, hr⟩ := P.intValuation_exists_uniformizer
    refine ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, ?_, rfl⟩, ?_⟩
    · have := (P.intValuation_le_pow_iff_mem r 1).1 (by simpa using hr.le)
      simpa using this
    · rw [HeightOneSpectrum.valuation_of_algebraMap, hr]

omit [StarRing E] in
theorem maxV_ne (Q P : HeightOneSpectrum (𝓞 E)) (h : Q ≠ P) :
    MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) 1 := by
  constructor
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
    exact Q.valuation_le_one r
  · have : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
      h (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
    obtain ⟨r, hr, hr'⟩ := SetLike.not_le_iff_exists.1 this
    exact ⟨algebraMap _ _ r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩,
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).2 hr'⟩

omit [StarRing E] in
theorem maxV_inv {Q P : HeightOneSpectrum (𝓞 E)} {γ : WithZero (Multiplicative ℤ)} (h0 : γ ≠ 0)
    (h : MaxV Q ((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ) :
    MaxV Q (((P.asIdeal : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) γ⁻¹ :=
  h.inv h0 (by rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ (ne0 P), FractionalIdeal.coe_one])

theorem mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    x ∈ vpIdeal P ↔ ∀ r ∈ (conjPrime₂ P).asIdeal, ∃ s ∈ P.asIdeal, algebraMap _ E s = x * algebraMap _ E r := by
  unfold vpIdeal
  rw [← div_eq_mul_inv, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (ne0 _)]
  constructor
  · intro h r hr
    exact (FractionalIdeal.mem_coeIdeal _).1 (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩))
  · intro h y hy
    obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact (FractionalIdeal.mem_coeIdeal _).2 (h r hr)

theorem star_mem_vp (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : x ∈ vpIdeal P) : star x ∈ vpIdeal (conjPrime₂ P) := by
  rw [mem_vp] at h ⊢
  intro r hr
  rw [conjP_conjP'] at hr
  obtain ⟨s, hs, e⟩ := h (cO E r) (by rwa [mem_conjP, cO_cO])
  refine ⟨cO E s, by rwa [mem_conjP, cO_cO], ?_⟩
  have e1 : algebraMap _ E (cO E s) = star (algebraMap _ E s) := rfl
  have e2 : algebraMap _ E (cO E r) = star (algebraMap _ E r) := rfl
  rw [e1, e, e2, star_mul, star_star, mul_comm]

theorem detLat_vp (P : HeightOneSpectrum (𝓞 E)) : detLat (vpLat P) = vpIdeal P := by
  unfold detLat
  rw [← Submodule.span_eq (vpIdeal P)]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    have := hA _ (single_mem_stdLat (E := E) (0 : Fin 1) 1)
    rw [Matrix.det_fin_one]
    simpa [vpLat, Matrix.mulVec_single] using this
  · intro hx
    refine ⟨Matrix.of fun _ _ => x, fun v hv => ?_, by simp⟩
    obtain ⟨r, hr⟩ := (mem_stdLat v).1 hv 0
    have : (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 = r • x := by
      simp [Matrix.mulVec, dotProduct, ← hr, Algebra.smul_def, mul_comm]
    show (Matrix.of fun _ _ => x : Matrix (Fin 1) (Fin 1) E).mulVec v 0 ∈ vpIdeal P
    rw [this]
    exact (vpIdeal P).smul_mem r hx

theorem vp_main : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)), P ≠ conjPrime₂ P → (∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ star x ∈ vpIdeal P) ∧ vpIdeal P * J = 1) ∧ MaxV P (vpIdeal P) (WithZero.exp (-1 : ℤ)) ∧ MaxV (conjPrime₂ P) (vpIdeal P) (WithZero.exp (1 : ℤ)) ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q ≠ conjPrime₂ P → MaxV Q (vpIdeal P) 1) ∧ detLat (vpLat P) = vpIdeal P := by
  intro E _ _ _ P hP
  refine ⟨⟨vpIdeal (conjPrime₂ P), fun x => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩, ?_, ?_, fun Q h1 h2 => ?_, detLat_vp P⟩
  · have := star_mem_vp _ _ h
    rwa [conjP_conjP'] at this
  · simpa using star_mem_vp _ _ h
  · unfold vpIdeal
    rw [conjP_conjP', ← FractionalIdeal.coe_mul, mul_assoc, inv_mul_cancel_left₀ (ne0 _), mul_inv_cancel₀ (ne0 _),
      FractionalIdeal.coe_one]
  · have := (maxV_self P).mul (maxV_inv one_ne_zero (maxV_ne P _ hP))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne _ P hP.symm).mul (maxV_inv WithZero.exp_ne_zero (maxV_self (conjPrime₂ P)))
    rw [one_mul, ← WithZero.exp_neg, neg_neg, ← FractionalIdeal.coe_mul] at this
    exact this
  · have := (maxV_ne Q P h1).mul (maxV_inv one_ne_zero (maxV_ne Q _ h2))
    rw [inv_one, mul_one, ← FractionalIdeal.coe_mul] at this
    exact this

end GlobalTheory.CharVal.Vp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetIdNormOneMul
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.RelDetIdeal

open GlobalTheory.CharValCompare GlobalTheory.Survey.StandardDeterminantUnits

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def relDet (L L' : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ L, A.mulVec v ∈ L') ∧ x = A.det}

omit [StarRing E] in
theorem val_pos {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : a ≠ 0) : 0 < P.valuation E a :=
  zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h)

omit [StarRing E] in
theorem gen_mul {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {a b : E} (ha : Gen P I a) (hb : Gen P J b) :
    Gen P (I * J) (a * b) := by
  refine gen_of (mul_ne_zero ha.1 hb.1) ?_ fun x hx => ?_
  · obtain ⟨s, hs, h1⟩ := (ha.2 a).2 le_rfl
    obtain ⟨t, ht, h2⟩ := (hb.2 b).2 le_rfl
    refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    rw [← smul_mul_smul_comm]
    exact Submodule.mul_mem_mul h1 h2
  · refine Submodule.mul_induction_on hx (fun m hm k hk => ?_) (fun x y hx hy => Valuation.map_add_le _ hx hy)
    rw [map_mul, map_mul]
    exact mul_le_mul' ((ha.2 m).1 (ThetaMove.mem_localization_of_mem P hm)) ((hb.2 k).1 (ThetaMove.mem_localization_of_mem P hk))

omit [StarRing E] in
theorem eq_of_gen {I J : Submodule (𝓞 E) E} (a b : HeightOneSpectrum (𝓞 E) → E) (ha : ∀ P, Gen P I (a P)) (hb : ∀ P, Gen P J (b P))
    (h : ∀ P : HeightOneSpectrum (𝓞 E), P.valuation E (a P) = P.valuation E (b P)) : I = J := by
  apply le_antisymm
  · intro x hx
    exact ThetaMove.mem_of_locP fun P => ((hb P).2 x).2 (h P ▸ ((ha P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))
  · intro x hx
    exact ThetaMove.mem_of_locP fun P => ((ha P).2 x).2 ((h P).symm ▸ ((hb P).2 x).1 (ThetaMove.mem_localization_of_mem P hx))

omit [StarRing E] in
theorem gen_one (P : HeightOneSpectrum (𝓞 E)) : Gen P (1 : Submodule (𝓞 E) E) 1 :=
  ⟨one_ne_zero, fun x => by rw [mem_localization_one, intAt_iff, map_one]⟩

theorem gen_bar {P : HeightOneSpectrum (𝓞 E)} {I : Submodule (𝓞 E) E} {a : E} (ha : Gen (conjPrime₂ P) I a) :
    Gen P (barI I) (star a) := by
  have h0 : star a ≠ 0 := star_ne_zero.2 ha.1
  refine gen_of h0 ?_ fun x hx => ?_
  · obtain ⟨s, hs, h1⟩ := (ha.2 a).2 le_rfl
    refine ⟨cO E s, hs, ?_⟩
    show star (cO E s • star a) ∈ I
    rwa [Algebra.smul_def, algebraMap_cO, star_mul', star_star, star_star, ← Algebra.smul_def]
  · have h2 := (ha.2 (star x)).1 (ThetaMove.mem_localization_of_mem _ hx)
    have h3 : IntAt (conjPrime₂ P) (star x / a) := by
      rw [intAt_iff, map_div₀]
      exact div_le_one_of_le₀ h2 zero_le
    have h4 := intAt_iff.1 (intAt_star h3)
    rwa [conjP_conjP, star_div₀, star_star, map_div₀, div_le_one₀ (val_pos h0)] at h4

theorem gen_relDet {P : HeightOneSpectrum (𝓞 E)} {L L' : Submodule (𝓞 E) (Sp E n)} (hL : L.FG) {f f' : Sp E n ≃ₗ[E] Sp E n}
    (hf : IsFr P L f) (hf' : IsFr P L' f') : Gen P (relDet L L') (dt f' / dt f) := by
  classical
  refine gen_of (div_ne_zero (dt_ne _) (dt_ne _)) ?_ ?_
  · let g : Sp E n →ₗ[E] Sp E n := (f' : Sp E n →ₗ[E] Sp E n) ∘ₗ (f.symm : Sp E n →ₗ[E] Sp E n)
    have hg : ∀ v ∈ L, g v ∈ localization₂ P.asIdeal L' := fun v hv =>
      (hf' _).2 ((hf _).1 (by simpa using ThetaMove.mem_localization_of_mem P hv))
    obtain ⟨S, rfl⟩ := hL
    have : ∀ i : S, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • g i ∈ L' := fun i => hg i (Submodule.subset_span i.2)
    choose s hs hs' using this
    have hp : ∏ i, s i ∉ P.asIdeal := fun hm => by
      obtain ⟨y, _, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs y h
    refine ⟨(∏ i, s i) ^ n, P.asIdeal.primeCompl.pow_mem hp n, Submodule.subset_span
      ⟨algebraMap (𝓞 E) E (∏ i, s i) • LinearMap.toMatrix' g, fun v hv => ?_, ?_⟩⟩
    · rw [Matrix.smul_mulVec, LinearMap.toMatrix'_mulVec, algebraMap_smul]
      induction hv using Submodule.span_induction with
      | mem y hy =>
        rw [← Finset.prod_erase_mul _ s (Finset.mem_univ ⟨y, hy⟩), mul_smul]
        exact L'.smul_mem _ (hs' ⟨y, hy⟩)
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, smul_add]; exact add_mem ha hb
      | smul c a _ ha =>
        rw [← algebraMap_smul E c a, map_smul, algebraMap_smul, smul_comm]
        exact L'.smul_mem _ ha
    · have e : LinearMap.det g = dt f' / dt f := by
        rw [eq_div_iff (dt_ne _), LinearMap.det_comp, dt_eq, dt_eq, mul_assoc, LinearEquiv.det_symm_mul_det, mul_one]
      rw [Matrix.det_smul, LinearMap.det_toMatrix', e, Algebra.smul_def, map_pow, Fintype.card_fin]
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, hA, rfl⟩ := hy
      have h1 := val_det_le_one (P := P)
        ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) fun x hx => by
        rw [← hf']
        obtain ⟨s, hs, hx⟩ := (hf x).2 hx
        refine ⟨s, hs, ?_⟩
        have := hA _ hx
        rw [← algebraMap_smul E s (f x), Matrix.mulVec_smul, algebraMap_smul] at this
        simpa using this
      have h2 : A.det = dt f' / dt f *
          LinearMap.det ((f'.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ Matrix.toLin' A ∘ₗ (f : Sp E n →ₗ[E] Sp E n)) := by
        have h3 := LinearEquiv.det_mul_det_symm f'
        have h4 := dt_ne f
        rw [LinearMap.det_comp, LinearMap.det_comp, LinearMap.det_toLin', ← dt_eq f]
        rw [← dt_eq f'] at h3
        field_simp
        linear_combination (-A.det) * h3
      rw [h2, map_mul]
      exact mul_le_of_le_one_right' h1
    | zero => simp
    | add a b _ _ ha hb => exact Valuation.map_add_le _ ha hb
    | smul c a _ ha =>
      rw [Algebra.smul_def, map_mul]
      exact le_trans (mul_le_of_le_one_left' (P.valuation_le_one (K := E) c)) ha

theorem relDet_mul {L L' L'' : Submodule (𝓞 E) (Sp E n)} (hL : Submodule.IsLattice E L) (hL' : Submodule.IsLattice E L')
    (hL'' : Submodule.IsLattice E L'') : relDet L L'' = relDet L L' * relDet L' L'' := by
  choose f hf using fun P => exists_isFr P hL
  choose f' hf' using fun P => exists_isFr P hL'
  choose f'' hf'' using fun P => exists_isFr P hL''
  refine eq_of_gen _ _ (fun P => gen_relDet hL.fg (hf P) (hf'' P))
    (fun P => gen_mul (gen_relDet hL.fg (hf P) (hf' P)) (gen_relDet hL'.fg (hf' P) (hf'' P))) fun P => ?_
  congr 1
  have := dt_ne (f P)
  have := dt_ne (f' P)
  field_simp

theorem normOne_relDet {L L' : Submodule (𝓞 E) (Sp E n)} (hL : IsSdLat L) (hL' : IsSdLat L') : NormOne (relDet L L') := by
  refine ⟨barI (relDet L L'), fun _ => Iff.rfl, ?_⟩
  choose f hf using fun P => exists_isFr P hL.1
  choose f' hf' using fun P => exists_isFr P hL'.1
  have hg := fun P => gen_relDet hL.1.fg (hf P) (hf' P)
  refine eq_of_gen _ _ (fun P => gen_mul (hg P) (gen_bar (hg (conjPrime₂ P)))) gen_one fun P => ?_
  have h1 := val_dual hL (hf (conjPrime₂ P)) (f' := f P) (by rw [conjP_conjP]; exact hf P)
  have h2 := val_dual hL' (hf' (conjPrime₂ P)) (f' := f' P) (by rw [conjP_conjP]; exact hf' P)
  rw [conjP_conjP] at h1 h2
  rw [star_div₀, div_mul_div_comm, map_div₀, mul_comm (dt _), mul_comm (dt _), h1, h2, map_one, div_one]

theorem isSdLat_of {L : Submodule (𝓞 E) (Sp E n)} (h : IsSDLat E n L) : IsSdLat L := by
  refine ⟨⟨h.1, h.2.1⟩, ?_⟩
  ext x
  rw [mem_dual, h.2.2]
  refine forall₂_congr fun y _ => ?_
  rw [Submodule.mem_one]
  rfl

end General

theorem detId_normOne_mul (D : D7) (n : ℕ) (L L' L'' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (hL : StandardLatticesGL3.SD D L) (hL' : StandardLatticesGL3.SD D L') (hL'' : StandardLatticesGL3.SD D L'') :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D L L') ∧ TaylorLogMetric.detId D L L'' = TaylorLogMetric.detId D L L' * TaylorLogMetric.detId D L' L'' := by
  letI := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h1 := isSdLat_of hL
  have h2 := isSdLat_of hL'
  have h3 := isSdLat_of hL''
  refine ⟨?_, relDet_mul h1.1 h2.1 h3.1⟩
  obtain ⟨J, hJ, e⟩ := normOne_relDet h1 h2
  exact ⟨J, fun x => by rw [hJ, hs]; rfl, e⟩

end GlobalTheory.RelDetIdeal
end
end

