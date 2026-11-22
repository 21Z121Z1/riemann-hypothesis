import Formalism.HermitianCurvature.StatementJ

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P

namespace Jx4

theorem rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  have h : (0 : ℝ) < ((|NumberField.discr E| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  unfold S6.rd
  first
    | exact Real.rpow_pos_of_pos h _
    | exact Real.rpow_pos h _

end Jx4

theorem fourier_transform_at_zero : Formalism.FourierDecayAlt.J.TransformAtZero := by
  intro V _ _ _ _ _ φ
  first
    | (simp [Real.fourier_eq]; done)
    | (simp [Real.fourierIntegral_eq']; done)
    | (simp [Real.fourierIntegral_eq]; done)
    | (simp [Real.fourierIntegral, VectorFourier.fourierIntegral]; done)
    | (simp [FourierTransform.fourier, Real.fourierIntegral, VectorFourier.fourierIntegral]; done)
    | (simp [VectorFourier.fourierIntegral]; done)

theorem poisson_level_joint : Formalism.FourierDecayAlt.J.PoissonStepJoint := by
  intro hF hJ E W _ D V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hFr hW
  intro ε hε i hi1 hi2 w Y hY κ hκ t₀ B hB S hS
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW ε hε i hi1 hi2 w Y hY κ hκ
  obtain ⟨hinj, hmem, hd0, hdual⟩ := hFr i hi1 hi2
  have key := hJ hF V ι π hπ (Λ i) E (emb i) (dmap i) (D.La i 1) (D.Lad i) φ Cφ
    (D.Nhat ε i w Y κ) hinj hmem hd0 hdual hc hb hnn hhat t₀ B hB S (fun t ht => (hS t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hS t ht).1

theorem poisson_joint_first_reduction : Formalism.FourierDecayAlt.J.PoissonJointTA := by
  intro hF hJ E _ _ D H _ _ W _ Φ tr i V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hinj hmem hd0 hdual hW
  intro w Hd kap hHd hk t0 T hT B hB
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW w Hd kap hHd hk
  have key := hJ hF V ι π hπ Λ E emb dmap (D.La i 1) (D.Lv i) φ Cφ (tr w Hd kap)
    hinj hmem hd0 hdual hc hb hnn hhat t0 B hB T (fun t ht => (hT t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hT t ht).1

theorem poisson_forms_agree : Formalism.FourierDecayAlt.J.PoissonAgree := by
  intro hA hT E W _ _ _ D H _ _ Φ ε i hε hi1 hi2 hwt hgram hPS
  intro w Hd kap hHd hk t0 T hTT B hB
  have hw : ((D.wt w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hwt w)
  have e : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  have hlev : ∀ h ∈ Hd, TB.level h = i - 1 := fun h hh => (hHd h hh).1
  have hpsd : TB.PSDOn Hd (fun h h' => kap h' h) := hT _ Hd kap ((hA _ Hd kap).1.mpr hk)
  have hT' : ∀ t ∈ T, t ≠ 0 ∧ t - t0 ∈ D.La i 1 := by
    intro t ht
    refine ⟨(hTT t ht).1, ?_⟩
    have h2 := (hTT t ht).2
    change t - t0 ∈ D.La (i - 1 + 1) 1 at h2
    rwa [e] at h2
  have hN : ∀ t, TA.Nst (Φ w) Hd kap 1 t t = D.Nst ε i 1 w Hd (fun h h' => kap h' h) t t := by
    intro t
    unfold TA.Nst TB.Data.Nst
    simp only [hgram]
    rw [Finset.sum_comm, eq_div_iff hw, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [TA.ext, TB.join]
    ring
  refine Eq.trans_le ?_ (hPS ε hε i hi1 hi2 w Hd hlev _ hpsd t0 B hB T hT')
  exact Finset.sum_congr rfl fun t _ => congrArg Complex.re (hN t)

theorem block_poisson_frame : Formalism.FourierDecayAlt.J.BlockPoissonFrame := by
  intro hEmb hTD hTw hPow E _ _ _ g r hg i hi1 hi2
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr hg.ne'
  have hdd : S6.dd E ≠ 0 := by
    unfold S6.dd
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    first
      | exact differentIdeal_ne_bot
      | (intro h; have h2 := NumberField.absNorm_differentIdeal (K := E); rw [h, Ideal.absNorm_bot] at h2; exact NumberField.discr_ne_zero E (Int.natAbs_eq_zero.mp h2.symm))
  have hB0 : ∀ ν : ℤ, S6.idl E g 2 ν ≠ 0 := by
    intro ν
    unfold S6.idl
    refine mul_ne_zero (zpow_ne_zero _ hdd) ?_
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact zpow_ne_zero _ hgE
  have hBA : ∀ ν : ℤ, S6.idl E g 2 ν ≤ S6.idl E g 1 ν := by
    intro ν
    unfold S6.idl
    have hs : FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (2 : ℤ)) ≤
        FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ)) := by
      rw [FractionalIdeal.spanSingleton_le_iff_mem, FractionalIdeal.mem_spanSingleton]
      exact ⟨(g : 𝓞 E), by simp only [Algebra.smul_def, map_natCast, zpow_one, zpow_two]⟩
    first
      | exact FractionalIdeal.mul_le.mpr fun a ha b hb => FractionalIdeal.mul_mem_mul ha (hs hb)
      | exact mul_le_mul_left' hs _
      | (gcongr; exact hs)
  have hc0 : S6.rd E ^ (-(S6.nuBlock r i 1)) ≠ 0 := zpow_ne_zero _ (Jx4.rd_pos E).ne'
  obtain ⟨hinj, -, -, hsm, -⟩ := hEmb E
  refine ⟨?_, ?_, ?_, ?_⟩
  · beta_reduce
    have hfun : ⇑(semb E (S6.rd E ^ (-(S6.nuBlock r i 1)))) =
        fun t => S6.rd E ^ (-(S6.nuBlock r i 1)) • cemb E t := funext (hsm _)
    rw [hfun]
    exact (smul_right_injective (CV E) hc0).comp hinj
  · beta_reduce
    intro t ht
    exact Submodule.mem_map.mpr ⟨t, ht, rfl⟩
  · beta_reduce
    unfold dm
    ext w
    simp
  · beta_reduce
    intro μ hμ
    have hL := hTw E _ _ 1 (hB0 (S6.nuBlock r i 1)) (hBA _) (hPow E g 2 (S6.nuBlock r i 1))
    exact (hTD E _ g _ hg hc0 hL.2 μ).1 hμ

theorem lattice_x_eq_lambda_one : Formalism.FourierDecayAlt.J.XIsLamOne := by
  intro m i C ka N I A g B
  have h : 2 * (i - 1) + 1 - 1 = 2 * i - 2 := by omega
  refine ⟨?_, ?_⟩
  · unfold Sz.xThreshold Sz.lamThreshold
    rw [h]
  · unfold Sz.xHat Sz.lamHat
    rw [h]

theorem frame_product_identities : Formalism.FourierDecayAlt.J.FrameProducts := by
  intro r i s C rd g N I A TT hi hs hrd hg
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hrd0 : rd ≠ 0 := hrd.ne'
  have hg0 : g ≠ 0 := hg.ne'
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have e1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  constructor
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((t + 1 : ℕ) : ℤ) + 1) =
        rd ^ (2 * r + 1) / rd ^ (2 * n + t) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have e2 : 2 * (n + 1 - 1) + (t + 1) - 1 = 2 * n + t := by omega
    unfold Sz.lamThreshold Sz.lamHat
    rw [hz, e1, e2]
    have b1 : C * (2 * Real.pi / g) * N / I = (2 * Real.pi / g) * (C * N / I) := by ring
    have b2 : C * (2 * Real.pi / rd) * N / (g * I) = (2 * Real.pi / (rd * g)) * (C * N / I) := by ring
    rw [b1, b2, mul_pow, mul_pow]
    generalize C * N / I = X
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    ring
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((r : ℤ) + 2 - ((n + 1 : ℕ) : ℤ))) =
        rd ^ r / rd ^ n := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have key : ∀ P a : ℝ, 0 ≤ a → √P * a = √(P * a ^ 2) := fun P a ha => by
      rw [Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq ha]
    rw [hz, key _ _ (mul_nonneg hg.le (div_nonneg (pow_nonneg hrd.le _) (pow_nonneg hrd.le _)))]
    unfold Sz.lamPrimeHat Sz.lamPrimeSq
    congr 1
    have e3 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have e4 : 2 * (n + 1 - 1) = 2 * n := by omega
    have e5 : 2 * (n + 1) - 2 = 2 * n := by omega
    rw [e1, e3, e4, e5]
    have b3 : C * (2 * Real.pi / rd) * N / I = (2 * Real.pi / rd) * (C * N / I) := by ring
    rw [b3, mul_pow]
    generalize C * N / I = X
    generalize (Real.sqrt TT)⁻¹ = Y
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    have hg1 : g * g⁻¹ = 1 := mul_inv_cancel₀ hg0
    have hr1 : rd * rd⁻¹ = 1 := mul_inv_cancel₀ hrd0
    linear_combination
      (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hg1 -
        (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hr1

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RecursionGivesUniformBoundsForm
section
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix

namespace Formalism.FourierDecayAlt.P.Jx6

theorem psd_mul {α : Type} {F : Finset α} {k k' : α → α → ℂ} (hk : TB.PSDOn F k)
    (hk' : TB.PSDOn F k') : TB.PSDOn F (fun x y => k x y * k' x y) := by
  unfold TB.PSDOn at *
  exact hk.hadamard hk'

theorem psd_pull {α β : Type} {G : Finset β} {F : Finset α} (f : G → F) {k : α → α → ℂ}
    {k' : β → β → ℂ} (h : ∀ x y : G, k' x y = k (f x) (f y)) (hk : TB.PSDOn F k) : TB.PSDOn G k' := by
  unfold TB.PSDOn at *
  have e : (Matrix.of fun x y : G => k' x y) = (Matrix.of fun x y : F => k x y).submatrix f f := by
    ext x y; exact h x y
  rw [e]; exact hk.submatrix f

theorem quadM {α : Type} (F : Finset α) (k : α → α → ℂ) (a : α → ℂ) :
    star (fun x : F => a x) ⬝ᵥ (Matrix.of fun x y : F => k x y) *ᵥ (fun x : F => a x) =
      ∑ x ∈ F, ∑ y ∈ F, conj (a x) * k x y * a y := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  rw [← Finset.sum_coe_sort F (fun x => ∑ y ∈ F, conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_coe_sort F (fun y => conj (a x) * k x y * a y)]
  apply Finset.sum_congr rfl; intro y _
  simp only [RCLike.star_def]; ring

theorem sum_nonneg_of_psd {α : Type} {F : Finset α} {k : α → α → ℂ} (hk : TB.PSDOn F k) :
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y).re := by
  unfold TB.PSDOn at hk
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hk
  have h := hk.2 (fun x : F => (fun _ : α => (1 : ℂ)) x)
  rw [quadM F k (fun _ => 1)] at h
  have h2 := (Complex.le_def.1 h).1
  simpa using h2

theorem sum_mul_nonneg {α : Type} {F : Finset α} {k k' : α → α → ℂ} (hk : TB.PSDOn F k)
    (hk' : TB.PSDOn F k') : 0 ≤ (∑ x ∈ F, ∑ y ∈ F, k x y * k' x y).re :=
  sum_nonneg_of_psd (psd_mul hk hk')

theorem maj_mono {E W : Type} [Field E] (D : TB.Data E W) (ρ ρ' : Fin D.f → ℝ) (l : E)
    (h : ∀ v, 0 ≤ ρ v ∧ ρ v ≤ ρ' v) (hav : ∀ v, 0 ≤ D.av v l) : D.maj ρ l ≤ D.maj ρ' l := by
  unfold TB.Data.maj
  apply Finset.prod_le_prod
  · intro v _
    exact le_min zero_le_one (pow_nonneg (div_nonneg (h v).1 (hav v)) _)
  · intro v _
    exact min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg (h v).1 (hav v))
      (div_le_div_of_nonneg_right (h v).2 (hav v)) _)

theorem baseGram_nonneg {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (k : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ := by
  unfold TB.Data.N0
  exact div_nonneg (sum_mul_nonneg hκ (hG ε hε k w Y)) (hW w).le

theorem Nst_nonneg {E W : Type} [Field E] (D : TB.Data E W) (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ}
    (hε : 0 < ε) (i s : ℕ) (w : W) (Y : Finset (TB.Pt E)) {κ : TB.Pt E → TB.Pt E → ℂ}
    (hκ : TB.PSDOn Y κ) (t : E) : 0 ≤ (D.Nst ε i s w Y κ t t).re := by
  classical
  unfold TB.Data.Nst
  rw [Complex.div_ofReal_re]
  refine div_nonneg (sum_mul_nonneg hκ ?_) (hW w).le
  have hm : ∀ x ∈ Y, TB.join x s t ∈ Y.image (fun h => TB.join h s t) :=
    fun x hx => Finset.mem_image_of_mem _ hx
  exact psd_pull (F := Y.image (fun h => TB.join h s t))
    (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) (hG ε hε i w _)

theorem blk_psd {E : Type} [Field E] {Y : Finset (TB.Pt E)} {S : Finset E} {s : ℕ}
    {κ : TB.Pt E → TB.Pt E → ℂ} (hκ : TB.PSDOn (TB.pts Y s S) κ) {t : E} (ht : t ∈ S) :
    TB.PSDOn Y (TB.blk κ s t t) := by
  classical
  have hm : ∀ x ∈ Y, TB.join x s t ∈ TB.pts Y s S := by
    intro x hx
    unfold TB.pts
    exact Finset.mem_image.2 ⟨(x, t), Finset.mem_product.2 ⟨hx, ht⟩, rfl⟩
  exact psd_pull (fun x : Y => ⟨TB.join x.1 s t, hm x.1 x.2⟩) (fun _ _ => rfl) hκ

end Formalism.FourierDecayAlt.P.Jx6

namespace Formalism.FourierDecayAlt.P

open Jx6

theorem estimates_mono : Formalism.FourierDecayAlt.J.EstimatesMono := by
  intro E W _ D szD' szL' vol' C₄ hC4 hav hD hL hV hG hW
  refine ⟨?_, ?_, ?_⟩
  · intro h ε hε i hi1 hi2 w hw hcnt
    obtain ⟨θ, hθ, H⟩ := h ε hε i hi1 hi2 w hw hcnt
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ
    obtain ⟨e0, el⟩ := H Y hY κ hκ
    refine ⟨e0, fun l hl hl0 => ?_⟩
    obtain ⟨A, hA⟩ := el l hl hl0
    refine ⟨A, le_trans hA ?_⟩
    exact mul_le_mul_of_nonneg_right
      (maj_mono D (D.szD i) (szD' i) l (fun v => hD i v) (fun v => hav v l))
      (Finset.sum_nonneg fun w' _ => mul_nonneg ((hθ A).1 w') (baseGram_nonneg D hG hW hε _ w' Y hκ))
  · intro h ε hε i s hs hsi hi hns w hw hcnt
    obtain ⟨θ, hθ, H⟩ := h ε hε i s hs hsi hi hns w hw hcnt
    refine ⟨θ, hθ, ?_⟩
    intro Y S κ hY hκ t ht t' ht' h0 h0' hne
    obtain ⟨π, hπ⟩ := H Y S κ hY hκ t ht t' ht' h0 h0' hne
    refine ⟨π, le_trans hπ ?_⟩
    exact mul_le_mul_of_nonneg_right
      (maj_mono D (D.szL (i - s + 1) s) (szL' (i - s + 1) s) _ (fun v => hL _ _ v)
        (fun v => hav v _))
      (Finset.sum_nonneg fun x _ => mul_nonneg ((hθ π).1 x) (div_nonneg (add_nonneg
        (Nst_nonneg D hG hW hε i s x.1 Y (blk_psd hκ ht) t)
        (Nst_nonneg D hG hW hε i s x.2 Y (blk_psd hκ ht') t')) (by norm_num)))
  · intro h ε hε i s hs hsi hi w hw hcnt hvol
    obtain ⟨θ, hθ, H⟩ := h ε hε i s hs hsi hi w hw hcnt (le_trans (hV _ _).2 hvol)
    refine ⟨θ, hθ, ?_⟩
    intro Y hY κ hκ t₀ S hS
    refine le_trans (H Y hY κ hκ t₀ S hS) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun s' _ => (hV _ s').1) (fun s' _ => (hV _ s').2)) (pow_nonneg hC4 _))
      (Finset.sum_nonneg fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ w' Y hκ))

theorem product_of_energies : Formalism.FourierDecayAlt.J.ProductOfE := by
  intro r e sd h0 h1
  rw [Finset.prod_Icc_succ_top (by omega), h1, Finset.prod_eq_one, one_mul]
  intro i hi; rw [h0 i hi, add_zero]

theorem recursion_gives_explicit_form : Formalism.FourierDecayAlt.J.RecursionGivesBounds := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', h⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hyp hC' hr he P _ B hI hδ hS
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hyp
  unfold S3.MassData.InTheoremA
  apply hS
  intro R
  have := h E W D Θ jn H Vt c a1 a2 a3 hC' hr a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
  rw [Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), mul_one] at this
  rw [hδ, hI]; exact this

theorem recursion_gives_form : Formalism.FourierDecayAlt.J.RecursionGivesForm := by
  intro hA C₁ C₄ h1 h4
  obtain ⟨C, C', h⟩ := hA C₁ C₄ h1 h4
  refine ⟨C, C', ?_⟩
  intro E W _ D Θ jn H _ _ _ Vt c hyp hC' hr he P _ B he1 hI hδ hS
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hyp
  have hprod : ∏ i ∈ Icc 1 (D.r + 1), (1 + D.e i) = B.e1 := by
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ D.r + 1),
      Finset.prod_eq_one (fun i hi => by rw [he i hi, add_zero]), one_mul, he1]
  have key := hS ((1 + B.δ) * B.e1 * B.IntN) (fun R => by
    have := h E W D Θ jn H Vt c a1 a2 a3 hC' hr a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 R
    rw [hprod] at this
    rw [hδ, hI]; exact this)
  calc B.c0 * B.c0' * B.KV ≤ B.n0c * ((1 + B.δ) * B.e1 * B.IntN) := key
    _ = _ := by ring

theorem top_energy : Formalism.FourierDecayAlt.J.TopE := by
  intro sd e h hs
  have h1 : (1 : ℝ) ≤ max sd 1 := le_max_right _ _
  have h2 : sd ≤ max sd 1 := le_max_left _ _
  have h3 : max sd 1 ≤ 2 := max_le hs (by norm_num)
  refine ⟨by linarith, by linarith, by linarith⟩

theorem each_level_counted_once : Formalism.FourierDecayAlt.J.OnceOnly := by
  intro P _ B hpos hk hA
  unfold S3.MassData.InTheoremA S3.MassData.Smod at hA
  obtain ⟨hk1, hk2⟩ := hk
  have hp := hpos.2
  have hvN : 0 < B.volN := by tauto
  have hvH : 0 < B.volH := by tauto
  have hvN' : 0 < B.volN' := by tauto
  have hvH' : 0 < B.volH' := by tauto
  have hd : 0 < B.dimπ := by tauto
  have hd' : 0 < B.dimπ' := by tauto
  have hn : 0 < B.n0c := by tauto
  have hs : 0 ≤ B.supdens := by tauto
  have c0 : 0 ≤ B.c0 * B.c0' := by unfold S3.MassData.c0 S3.MassData.c0'; positivity
  calc B.c0 * B.c0' * B.KV ≤ B.c0 * B.c0' * (B.supdens * B.n0c * B.KtopV) :=
        mul_le_mul_of_nonneg_left hk1 c0
    _ = B.supdens * B.n0c * (B.c0 * B.c0' * B.KtopV) := by ring
    _ ≤ B.supdens * B.n0c * ((1 + B.δ) * B.IntN) := mul_le_mul_of_nonneg_left hA (by positivity)
    _ = _ := by ring

theorem form_gives_theorem_A : Formalism.FourierDecayAlt.J.FormGivesMain := by
  intro hM P _ B hPos he hKV h2A hF hMass hform hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩ := hPos
  have hn : 0 < B.n0c := a33
  have hen : 0 < B.e1 * B.n0c := mul_pos he hn
  have key := hM P { B with supdens := B.e1, KtopV := B.KV / (B.e1 * B.n0c) }
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, he.le, a35⟩ h2A hF
    (by
      constructor
      · show B.KV ≤ B.e1 * B.n0c * (B.KV / (B.e1 * B.n0c))
        rw [mul_div_cancel₀ _ hen.ne']
      · show 0 ≤ B.KV / (B.e1 * B.n0c)
        exact div_nonneg hKV hen.le)
    hMass
    (by show B.e1 ≤ B.e1; exact le_refl _)
    (by
      show B.c0 * B.c0' * (B.KV / (B.e1 * B.n0c)) ≤ (1 + B.δ) * B.IntN
      rw [← mul_div_assoc, div_le_iff₀ hen]
      have e : (1 + B.δ) * B.e1 * (B.n0c * B.IntN) = (1 + B.δ) * B.IntN * (B.e1 * B.n0c) := by ring
      linarith)
    hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  exact key

end Formalism.FourierDecayAlt.P
end

