import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FiniteNarrowIdeleClassesAndUnitsModSquares
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.NarrowCls

theorem exists_finset_mod_sq {G : Type} [CommGroup G] [Group.FG G] :
    ∃ E : Finset G, ∀ g : G, ∃ e ∈ E, ∃ h : G, g = e * h ^ 2 := by
  classical
  let H : Subgroup G := (powMonoidHom 2 : G →* G).range
  have hfin : Finite (G ⧸ H) := by
    apply CommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine (isOfFinOrder_iff_pow_eq_one).2 ⟨2, by norm_num, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨g, rfl⟩
  haveI := Fintype.ofFinite (G ⧸ H)
  refine ⟨Finset.univ.image (fun q : G ⧸ H => q.out), fun g => ?_⟩
  refine ⟨(g : G ⧸ H).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have h1 : ((g : G ⧸ H).out : G ⧸ H) = (g : G ⧸ H) := Quotient.out_eq' _
  rw [QuotientGroup.eq] at h1
  obtain ⟨h, hh⟩ := h1
  refine ⟨h, ?_⟩
  simp only [powMonoidHom_apply] at hh
  rw [hh, mul_inv_cancel_left]

variable {F : Type} [Field F] [NumberField F]

def finIdele : (Af F)ˣ →* Ideles F :=
  Units.map
    { toFun := fun x => (((1 : InfiniteAdeleRing F), x) : AdeleRing (𝓞 F) F)
      map_one' := rfl
      map_mul' := fun x y => Prod.ext (mul_one 1).symm rfl }

def finClass : (Af F)ˣ →* ClassGroup (𝓞 F) := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf F).comp finIdele

theorem eq_of_finClass_eq_one (z : (Af F)ˣ) (hz : finClass z = 1) :
    ∃ (k : Fˣ) (u : (Af F)ˣ), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧
      z = Units.map (algebraMap F (Af F)).toMonoidHom k * u := by
  obtain ⟨k, u', hu', he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff F (finIdele z)).1 hz
  have hsnd := congrArg (ReciprocityTheory.Neutral.Bridge.HCFR.sndU F) he
  rw [map_mul] at hsnd
  have hinv : ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u' * ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u'⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u'⁻¹ * ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u' = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨k, ⟨_, _, hinv, hinv'⟩, ?_, ?_⟩
  · intro w
    exact (ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff F u').1 hu' w
  · ext1
    exact hsnd

variable [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply]
  exact Complex.ofReal_re _

open Classical in

def sgn (k : Fˣ) : InfinitePlace F → Bool := fun v => decide (0 < reAt v (k : F))

theorem tp_of_sgn_eq (k σ : Fˣ) (h : sgn k = sgn σ) : TP ((k * σ⁻¹ : Fˣ) : F) := by
  intro v
  have hv := congrFun h v
  simp only [sgn, decide_eq_decide] at hv
  rw [reAt_eq] at hv ⊢
  set e := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)
  have hk : e (k : F) ≠ 0 := (map_ne_zero e).2 k.ne_zero
  have hs : e (σ : F) ≠ 0 := (map_ne_zero e).2 σ.ne_zero
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  rcases lt_or_gt_of_ne hs with h1 | h1
  · have h2 : e (k : F) < 0 := by
      rcases lt_or_gt_of_ne hk with h3 | h3
      · exact h3
      · exact absurd (hv.1 h3) (not_lt.2 h1.le)
    exact mul_pos_of_neg_of_neg h2 (inv_lt_zero.2 h1)
  · exact mul_pos (hv.2 h1) (inv_pos.2 h1)

theorem narrowClass_unitsSq_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
    (∃ Y : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ y ∈ Y, ∃ (ξ : Fˣ) (u : (Af F)ˣ), TP (ξ : F) ∧
      (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = Units.map (algebraMap F (Af F)).toMonoidHom ξ * y * u) ∧
    ∃ E : Finset (𝓞 F)ˣ, ∀ ε : (𝓞 F)ˣ, ∃ e ∈ E, ∃ η : (𝓞 F)ˣ, ε = e * η ^ 2 := by
  intro F _ _ _
  classical
  refine ⟨?_, ?_⟩
  · let Y0 : Finset (Af F)ˣ := Finset.univ.image
      (fun c : ClassGroup (𝓞 F) => if h : ∃ y, finClass y = c then h.choose else 1)
    let S : Finset Fˣ := Finset.univ.image
      (fun b : InfinitePlace F → Bool => if h : ∃ σ : Fˣ, sgn σ = b then h.choose else 1)
    let ι := Units.map (algebraMap F (Af F)).toMonoidHom
    refine ⟨(S ×ˢ Y0).image (fun p => ι p.1 * p.2), fun z => ?_⟩
    have hc : ∃ y, finClass y = finClass z := ⟨z, rfl⟩
    set y0 := hc.choose with hy0
    have hy0c : finClass y0 = finClass z := hc.choose_spec
    have hy0m : y0 ∈ Y0 := by
      refine Finset.mem_image.2 ⟨finClass z, Finset.mem_univ _, ?_⟩
      rw [dif_pos hc]
    obtain ⟨k, u, hu, hk⟩ := eq_of_finClass_eq_one (z * y0⁻¹) (by rw [map_mul, map_inv, hy0c, mul_inv_cancel])
    have hs : ∃ σ : Fˣ, sgn σ = sgn k := ⟨k, rfl⟩
    set σ := hs.choose with hσ
    have hσs : sgn σ = sgn k := hs.choose_spec
    have hσm : σ ∈ S := by
      refine Finset.mem_image.2 ⟨sgn k, Finset.mem_univ _, ?_⟩
      rw [dif_pos hs]
    refine ⟨ι σ * y0, Finset.mem_image.2 ⟨(σ, y0), Finset.mem_product.2 ⟨hσm, hy0m⟩, rfl⟩,
      k * σ⁻¹, u, tp_of_sgn_eq k σ hσs.symm, hu, ?_⟩
    have hz : z = ι k * u * y0 := by rw [← hk, inv_mul_cancel_right]
    show z = ι (k * σ⁻¹) * (ι σ * y0) * u
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right, mul_right_comm]
    exact hz
  · haveI : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
    exact exists_finset_mod_sq

end GlobalTheory.HilbertThetaSeries.NarrowCls

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∃ Y : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ y ∈ Y, ∃ (ξ : Fˣ) (u : (Af F)ˣ), TP (ξ : F) ∧ (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = Units.map (algebraMap F (Af F)).toMonoidHom ξ * y * u) ∧ ∃ E : Finset (𝓞 F)ˣ, ∀ ε : (𝓞 F)ˣ, ∃ e ∈ E, ∃ η : (𝓞 F)ˣ, ε = e * η ^ 2 := by
  first | exact @GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite | exact GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite | (intros; apply GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.GenByTranslationsInversions
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GeneratorMatrix

theorem matId {F : Type} [Field F] (a b c d δ τ e s : F) (hδ : δ ≠ 0) (hs : s ≠ 0) (he : e ≠ 0)
    (hc : c = s - τ * δ * a) (hdet : a * d - b * c = e) :
    !![a, b; c, d] = !![0, -δ⁻¹; δ, 0] * !![1, τ / δ; 0, 1] * !![0, -(-δ)⁻¹; -δ, 0] * !![1, a / s; 0, 1]
      * !![0, -(s / e)⁻¹; s / e, 0] * !![1, (d + τ * δ * b) * e / s; 0, 1] * !![e, 0; 0, 1] := by
  subst hc
  simp only [Matrix.mul_fin_two]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> field_simp
  all_goals first | ring1 | linear_combination -hdet | linear_combination δ * τ * hdet

variable {F : Type} [Field F] [NumberField F]

theorem exists_place (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk8.exists_place p hp

theorem ne_zero_of_pUnit {p : ℕ} {w : HeightOneSpectrum (𝓞 F)} (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) {x : F}
    (h : PUnit p x) : x ≠ 0 := by
  intro hx; have := h w hw; rw [hx, map_zero] at this; exact zero_ne_one this

theorem val_wm (c : Fˣ) : ((wm c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -(c : F)⁻¹; (c : F), 0] := by
  simp [wm]

theorem val_aff (y : Fˣ) (x : F) : ((aff y x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(y : F), x; 0, 1] := rfl

end GlobalTheory.HilbertThetaSeries.GeneratorMatrix

namespace GlobalTheory.HilbertThetaSeries

open GlobalTheory.HilbertThetaSeries.GeneratorMatrix in

theorem gen_by_translations_inversions : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∀ γ : GL (Fin 2) F, InG p δ γ → ∃ (b₁ b₂ b₃ : F) (c₁ c₂ c₃ ε : Fˣ), PInt p (δ * b₁) ∧ PInt p (δ * b₂) ∧ PInt p (δ * b₃) ∧ PUnit p (c₁ / δ) ∧ PUnit p (c₂ / δ) ∧ PUnit p (c₃ / δ) ∧ TP (ε : F) ∧ γ = wm c₁ * aff 1 b₁ * wm c₂ * aff 1 b₂ * wm c₃ * aff 1 b₃ * aff ε 0 := by
  intro F _ _ _ p hp δ hδ γ hγ
  classical
  obtain ⟨hA, hB, hC, hD, hE, hT⟩ := hγ
  obtain ⟨w₀, hw₀⟩ := exists_place (F := F) p hp
  have hδ0 : δ ≠ 0 := by
    intro h; have := hδ w₀ hw₀; rw [h, map_zero] at this; exact WithZero.exp_ne_zero this.symm
  have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = γ.val.det := (Matrix.det_fin_two _).symm
  have he0 : γ.val.det ≠ 0 := ne_zero_of_pUnit hw₀ hE
  have hI : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set S := (Ideal.finite_factors hI).toFinset with hS
  have hmem : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → w ∈ S := by
    intro w hw
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
    exact hw
  obtain ⟨τ, hτ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun w => w.asIdeal) (fun _ => 1)
    (fun w _ => w.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if w.1.valuation F (γ.val 1 0 / δ) = 1 then 0 else 1)
  set a := γ.val 0 0 with ha
  set b := γ.val 0 1 with hb
  set c := γ.val 1 0 with hc
  set d := γ.val 1 1 with hd
  set e := γ.val.det with he
  set t : F := algebraMap (𝓞 F) F τ with ht
  set s := c + t * δ * a with hs
  have hsd : s / δ = c / δ + t * a := by rw [hs]; field_simp
  have hu : PUnit p (s / δ) := by
    intro w hw
    have hτw := hτ w (hmem w hw)
    simp only [pow_one] at hτw
    rw [hsd]
    by_cases h1 : w.valuation F (c / δ) = 1
    · rw [if_pos h1, sub_zero] at hτw
      have htlt : w.valuation F t < 1 := (w.valuation_lt_one_iff_mem τ).mpr hτw
      have : w.valuation F (t * a) < 1 := by
        rw [map_mul]
        calc w.valuation F t * w.valuation F a ≤ w.valuation F t * 1 := mul_le_mul' le_rfl (hA w hw)
          _ < 1 := by rw [mul_one]; exact htlt
      rw [Valuation.map_add_eq_of_lt_left _ (h1 ▸ this), h1]
    · rw [if_neg h1] at hτw
      have hclt : w.valuation F (c / δ) < 1 := lt_of_le_of_ne (hC w hw) h1
      have hav : w.valuation F a = 1 := by
        by_contra hne
        have halt : w.valuation F a < 1 := lt_of_le_of_ne (hA w hw) hne
        have hE' := hE w hw
        have hx : e = a * d - (δ * b) * (c / δ) := by rw [← hdet]; field_simp
        have h1' : w.valuation F (a * d) < 1 := by
          rw [map_mul]
          calc w.valuation F a * w.valuation F d ≤ w.valuation F a * 1 := mul_le_mul' le_rfl (hD w hw)
            _ < 1 := by rw [mul_one]; exact halt
        have h2' : w.valuation F ((δ * b) * (c / δ)) < 1 := by
          rw [map_mul]
          calc w.valuation F (δ * b) * w.valuation F (c / δ) ≤ 1 * w.valuation F (c / δ) := mul_le_mul' (hB w hw) le_rfl
            _ < 1 := by rw [one_mul]; exact hclt
        have : w.valuation F e < 1 := by
          rw [hx]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1' h2')
        rw [hE'] at this; exact lt_irrefl _ this
      have htm : w.valuation F (t - 1) < 1 := by
        have := (w.valuation_lt_one_iff_mem (K := F) (τ - 1)).mpr hτw
        simpa [ht] using this
      have htv : w.valuation F t = 1 := by
        have : t = 1 + (t - 1) := by ring
        rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact htm), map_one]
      have hta : w.valuation F (t * a) = 1 := by rw [map_mul, htv, hav, mul_one]
      rw [Valuation.map_add_eq_of_lt_right _ (hta ▸ hclt), hta]
  have hs0 : s ≠ 0 := by
    intro h0; exact ne_zero_of_pUnit hw₀ hu (by rw [h0, zero_div])
  refine ⟨t / δ, a / s, (d + t * δ * b) * e / s, Units.mk0 δ hδ0, -Units.mk0 δ hδ0,
    Units.mk0 (s / e) (div_ne_zero hs0 he0), Units.mk0 e he0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; rw [mul_div_cancel₀ _ hδ0]; exact w.valuation_le_one τ
  · intro w hw
    have : δ * (a / s) = a / (s / δ) := by field_simp
    rw [this, map_div₀, hu w hw, div_one]; exact hA w hw
  · intro w hw
    have : δ * ((d + t * δ * b) * e / s) = (d + t * (δ * b)) * e / (s / δ) := by field_simp
    rw [this, map_div₀, hu w hw, div_one, map_mul, hE w hw, mul_one]
    refine Valuation.map_add_le _ (hD w hw) ?_
    rw [map_mul]
    calc w.valuation F t * w.valuation F (δ * b) ≤ 1 * 1 :=
          mul_le_mul' (w.valuation_le_one τ) (hB w hw)
      _ = 1 := one_mul 1
  · intro w hw; rw [Units.val_mk0, div_self hδ0, map_one]
  · intro w hw; rw [Units.val_neg, Units.val_mk0, neg_div, div_self hδ0, Valuation.map_neg, map_one]
  · intro w hw
    have : s / e / δ = s / δ / e := by ring
    rw [Units.val_mk0, this, map_div₀, hu w hw, hE w hw, div_one]
  · rw [Units.val_mk0]; exact hT
  · refine Units.ext ?_
    simp only [Units.val_mul, val_wm, val_aff, Units.val_neg, Units.val_mk0, Units.val_one]
    rw [Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) F)]
    exact matId a b c d δ t e s hδ0 hs0 he0 (by rw [hs]; ring) hdet

end GlobalTheory.HilbertThetaSeries
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.HolKeep

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F]

def U (F : Type) [Field F] [NumberField F] : Set (InfinitePlace F → ℂ) := {z | ∀ v, 0 < (z v).im}

theorem cmp_det (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    ((cmp v h).det : ℝ) = (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  simp [cmp, Matrix.GeneralLinearGroup.map_det]

def mob (h : GL (Fin 2) (InfinitePlace F → ℝ)) (z : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
  fun v => num (cmp v h) (z v) / denom (cmp v h) (z v)

theorem mob_im_pos {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) (v) :
    0 < (mob h z v).im := by
  have hd : 0 < ((cmp v h).det : ℝ) := by
    rw [cmp_det]
    exact hh v
  have hzv : 0 < (z v).im := hz v
  show 0 < (num (cmp v h) (z v) / denom (cmp v h) (z v)).im
  rw [moebius_im]
  exact div_pos (mul_pos hd hzv) (normSq_denom_pos _ hzv.ne')

theorem mob_mapsTo {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) : Set.MapsTo (mob h) (U F) (U F) := by
  intro z hz
  show ∀ v, 0 < (mob h z v).im
  exact fun v => mob_im_pos hh hz v

theorem mob_diff (h : GL (Fin 2) (InfinitePlace F → ℝ)) : DifferentiableOn ℂ (mob h) (U F) := by
  rw [differentiableOn_pi]
  intro v z hz
  have hzv : (z v).im ≠ 0 := (hz v).ne'
  have hp : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => w v) z := differentiable_apply v z
  have hn : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => num (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  have hd : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => denom (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun w => num (cmp v h) (w v) / denom (cmp v h) (w v)) z
  simp only [div_eq_mul_inv]
  exact hn.mul (hd.inv (denom_ne_zero_of_im _ hzv))

theorem act_eq {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) :
    act h (fun v => ofComplex (z v)) = fun v => ofComplex (mob h z v) := by
  funext v
  rw [act.eq_1, ofComplex_apply_of_im_pos (hz v), ofComplex_apply_of_im_pos (mob_im_pos hh hz v)]
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [cmp_det]; exact hh v)]
  rfl

theorem hilbertHolomorphic_unnormalizedSlash_of_pos (k : ℕ) {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {f : Hn F → ℂ} (hf : Hol f) :
    Hol (sl0 k h f) := by
  have hF : DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => f (fun v => ofComplex (z v))) (U F) := hf
  have hcomp := hF.comp (mob_diff h) (mob_mapsTo hh)
  have hden : DifferentiableOn ℂ
      (fun z : InfinitePlace F → ℂ => (∏ v, denom (cmp v h) (z v))⁻¹ ^ k) (U F) := by
    intro z hz
    have hne : (∏ v, denom (cmp v h) (z v)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun v _ => denom_ne_zero_of_im _ (hz v).ne'
    have hpr : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => ∏ v, denom (cmp v h) (w v)) z := by
      simp only [denom]
      fun_prop
    exact ((hpr.inv hne).pow k).differentiableWithinAt
  show DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => sl0 k h f (fun v => ofComplex (z v))) (U F)
  refine (hden.mul hcomp).congr ?_
  intro z hz
  have hc : ∀ v, ((ofComplex (z v) : ℍ) : ℂ) = z v := fun v => by
    rw [ofComplex_apply_of_im_pos (hz v)]
  simp only [sl0.eq_1, act_eq hh hz, hc, Function.comp_apply, Pi.mul_apply]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Hol f → Hol g → Hol (f + g) ∧ Hol (c • f) ∧ Hol (f * g) ∧ Hol (1 : Hn F → ℂ) ∧ Hol (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Hol (sl0 k h f) ∧ Hol (sl k h f) := by
  intro F _ _ k f g c hf hg
  refine ⟨DifferentiableOn.add hf hg, DifferentiableOn.const_smul hf c, DifferentiableOn.mul hf hg,
    differentiableOn_const 1, differentiableOn_const 0, fun h hh => ⟨hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf, ?_⟩⟩
  exact DifferentiableOn.mul (differentiableOn_const _) (hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf)

end GlobalTheory.HilbertThetaSeries.HolKeep
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section
namespace GlobalTheory.HilbertThetaSeries.RatSlash

variable {F : Type} [Field F] [NumberField F]

theorem cmp_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v).toMonoidHom t) * cmp v h := by
  rw [map_mul]
  congr 1
  ext i j
  simp [cmp, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem det_scalar_mul (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det =
      (t : InfinitePlace F → ℝ) ^ 2 * (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det := by
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_mul]

theorem unit_ne (t : (InfinitePlace F → ℝ)ˣ) (v : InfinitePlace F) : (t : InfinitePlace F → ℝ) v ≠ 0 := fun h0 => by
  have := congrFun t.mul_inv v
  simp [h0] at this

theorem denom_scalar_mul (u : ℝˣ) (g : GL (Fin 2) ℝ) (z : ℂ) :
    UpperHalfPlane.denom (Matrix.GeneralLinearGroup.scalar (Fin 2) u * g) z = ((u : ℝ) : ℂ) * UpperHalfPlane.denom g z := by
  simp [UpperHalfPlane.denom, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem sl_scalar_mul {k : ℕ} (hk : Even k) (f : Hn F → ℂ) (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f := by
  obtain ⟨m, rfl⟩ := hk
  funext z
  have hact : act (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) z = act h z := by
    unfold act
    funext v
    rw [cmp_scalar_mul, mul_smul, UpperHalfPlane.glScalar_smul]
  have hdet : ∏ v, |((Matrix.GeneralLinearGroup.scalar (Fin 2) t * h : GL (Fin 2) (InfinitePlace F → ℝ)) :
      Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| =
      (∏ v, (t : InfinitePlace F → ℝ) v) ^ 2 * ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| := by
    rw [det_scalar_mul, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    simp [abs_mul, sq_abs]
  have hden : ∏ v, UpperHalfPlane.denom (cmp v (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h)) (z v) =
      ((∏ v, (t : InfinitePlace F → ℝ) v : ℝ) : ℂ) * ∏ v, UpperHalfPlane.denom (cmp v h) (z v) := by
    simp_rw [cmp_scalar_mul, denom_scalar_mul]
    rw [Finset.prod_mul_distrib]
    push_cast
    simp
  have hP : (∏ v, (t : InfinitePlace F → ℝ) v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => unit_ne t v)
  have hQ : 0 ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
    Finset.prod_nonneg (fun v _ => abs_nonneg _)
  have hexp : (((m + m : ℕ) : ℝ) / 2) = ((m : ℕ) : ℝ) := by
    push_cast
    ring
  unfold sl sl0
  rw [hact, hdet, hden, Real.mul_rpow (by positivity) hQ, hexp, Real.rpow_natCast, ← pow_mul]
  set P := ∏ v, (t : InfinitePlace F → ℝ) v
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  push_cast
  rw [mul_inv, mul_pow, inv_pow (P : ℂ)]
  field_simp
  ring

variable [IsTotallyReal F]

theorem ofReal_rhom (v : InfinitePlace F) (x : F) : ((rhom x v : ℝ) : ℂ) = v.embedding x :=
  InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x

theorem rhom_apply (v : InfinitePlace F) (x : F) : rhom x v = reAt v x := by
  unfold rhom reAt
  show InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x = (v.embedding x).re
  rw [← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x, Complex.ofReal_re]

theorem ofReal_reAt (v : InfinitePlace F) (x : F) : ((reAt v x : ℝ) : ℂ) = v.embedding x := by
  rw [← rhom_apply, ofReal_rhom]

variable (F) in

def embEquiv : InfinitePlace F ≃ (F →+* ℂ) where
  toFun v := v.embedding
  invFun φ := InfinitePlace.mk φ
  left_inv v := InfinitePlace.mk_embedding v
  right_inv φ := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))

theorem prod_reAt (x : F) : ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∏ v : InfinitePlace F, v.embedding x = ∏ φ : F →+* ℂ, φ x :=
    Equiv.prod_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∏ φ : F →+* ℂ, φ x = ∏ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.prod_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast]

theorem sum_reAt (x : F) : ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [ofReal_reAt]
  have h1 : ∑ v : InfinitePlace F, v.embedding x = ∑ φ : F →+* ℂ, φ x :=
    Equiv.sum_comp (embEquiv F) (fun φ => φ x)
  have h2 : ∑ φ : F →+* ℂ, φ x = ∑ σ : F →ₐ[ℚ] ℂ, σ x :=
    Equiv.sum_comp (RingHom.equivRatAlgHom F ℂ) (fun σ : F →ₐ[ℚ] ℂ => σ x)
  rw [h1, h2, ← trace_eq_sum_embeddings ℂ, eq_ratCast]

theorem det_toInf (γ : GL (Fin 2) F) :
    ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det := by
  rw [RingHom.map_det]; rfl

theorem toInf_scalar (η : Fˣ) : toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η) := by
  ext i j v
  simp [toInf, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem rat_slash : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  intro F _ _ _ k f
  refine ⟨rhom_apply, fun γ => ⟨?_, ?_⟩, fun hk t h hh => ⟨?_, sl_scalar_mul hk f t h⟩, toInf_scalar,
    fun x => ⟨prod_reAt x, sum_reAt x⟩⟩
  · unfold Pos TP
    rw [det_toInf]
    simp only [rhom_apply]
  · funext z
    unfold sl
    rw [det_toInf]
    simp only [rhom_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.abs_prod, prod_reAt]
  · unfold Pos at hh ⊢
    intro v
    rw [det_scalar_mul]
    have h1 := unit_ne t v
    have h2 := hh v
    simp only [Pi.mul_apply, Pi.pow_apply]
    positivity

end GlobalTheory.HilbertThetaSeries.RatSlash

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_slash_rational_matrix_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (f : Hn F → ℂ), (∀ v (x : F), rhom x v = reAt v x) ∧ (∀ γ : GL (Fin 2) F, (Pos (toInf γ) ↔ TP γ.val.det) ∧ sl k (toInf γ) f = ((|((Algebra.norm ℚ γ.val.det : ℚ) : ℝ)| ^ ((k : ℝ) / 2) : ℝ) : ℂ) • sl0 k (toInf γ) f) ∧ (Even k → ∀ (t : (InfinitePlace F → ℝ)ˣ) (h : GL (Fin 2) (InfinitePlace F → ℝ)), Pos h → Pos (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) ∧ sl k (Matrix.GeneralLinearGroup.scalar (Fin 2) t * h) f = sl k h f) ∧ (∀ η : Fˣ, toInf (Matrix.GeneralLinearGroup.scalar (Fin 2) η) = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (rhom (F := F)).toMonoidHom η)) ∧ ∀ x : F, ∏ v, reAt v x = ((Algebra.norm ℚ x : ℚ) : ℝ) ∧ ∑ v, reAt v x = ((Algebra.trace ℚ F x : ℚ) : ℝ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | exact GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash | (intros; apply GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash <;> assumption)
end
end

