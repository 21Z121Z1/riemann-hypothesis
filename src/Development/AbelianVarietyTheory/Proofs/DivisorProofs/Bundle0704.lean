import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0675
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeRealMultiplicationSpan
section
open NumberField GlobalTheory.RealMult
open scoped nonZeroDivisors

namespace GlobalTheory.RealMult.SpanDual

theorem exists_im_ne_zero {n : ℕ} (hn : 0 < n) (Λ : Submodule ℤ (Fin n → ℂ))
    (hspan : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤) (h : Fin n → ℝ) (hpos : ∀ j, 0 < h j) :
    ∃ l ∈ Λ, ∃ l' ∈ Λ, (∑ j, (h j : ℂ) * (l j * starRingEnd ℂ (l' j))).im ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun z w ↦ (∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j))).im)
      (fun z z' w ↦ by simp [add_mul, mul_add, Finset.sum_add_distrib])
      (fun r z w ↦ by
        have : (∑ j, (h j : ℂ) * ((r • z) j * starRingEnd ℂ (w j))) =
            (r : ℂ) * ∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [Pi.smul_apply, Complex.real_smul]; ring
        rw [this, Complex.im_ofReal_mul, smul_eq_mul])
      (fun z w w' ↦ by simp [add_mul, mul_add, Finset.sum_add_distrib])
      (fun r z w ↦ by
        have : (∑ j, (h j : ℂ) * (z j * starRingEnd ℂ ((r • w) j))) =
            (r : ℂ) * ∑ j, (h j : ℂ) * (z j * starRingEnd ℂ (w j)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
        rw [this, Complex.im_ofReal_mul, smul_eq_mul])
  have h1 : ∀ l ∈ Λ, B l = 0 := fun l hl ↦
    LinearMap.ext_on hspan (fun w hw ↦ by simpa [B] using hcon l hl w hw)
  have h2 : B = 0 := LinearMap.ext_on hspan (fun z hz ↦ by rw [h1 z hz]; rfl)
  have h3 := congrArg (fun B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ ↦
    B (Pi.single ⟨0, hn⟩ 1) (Pi.single ⟨0, hn⟩ Complex.I)) h2
  simp only [B, LinearMap.mk₂_apply] at h3
  rw [Finset.sum_eq_single ⟨0, hn⟩ (fun b _ hb ↦ by simp [Pi.single_apply, hb]) (by simp)] at h3
  simp at h3
  exact (hpos ⟨0, hn⟩).ne' h3

theorem isIntegral_of_stab {F : Type} [Field F] {n : ℕ} (hn : 0 < n)
    (Λ : Submodule ℤ (Fin n → ℂ)) (e : Fin n → (F →+* ℝ))
    [DiscreteTopology Λ] (hspan : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤) (s : F)
    (hs : ∀ l ∈ Λ, (fun j ↦ (e j s : ℂ) * l j) ∈ Λ) : IsIntegral ℤ s := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let φ : F →+* (Fin n → ℂ) := Pi.ringHom fun j ↦ Complex.ofRealHom.comp (e j)
  letI : Module F (Fin n → ℂ) := Module.compHom _ φ
  have hsmul : ∀ (t : F) (z : Fin n → ℂ), t • z = fun j ↦ (e j t : ℂ) * z j := fun _ _ ↦ rfl
  haveI : IsScalarTower ℤ F (Fin n → ℂ) := ⟨fun k x y ↦ by
    funext j
    simp only [hsmul, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast]
    push_cast; ring⟩
  haveI : Module.IsTorsionFree F (Fin n → ℂ) := ⟨fun r hr z w hzw ↦ by
    have hr0 : r ≠ 0 := hr.ne_zero
    funext j
    have := congrFun hzw j
    simp only [hsmul] at this
    exact mul_left_cancel₀ (by simpa using (e j).injective.ne hr0 |>.trans_eq (map_zero _)) this⟩
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  haveI := ZLattice.module_finite ℝ Λ
  have hfg : Λ.FG := Module.Finite.iff_fg.mp inferInstance
  have hne : Λ ≠ ⊥ := by
    intro h0
    rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
    exact bot_ne_top hspan
  exact isIntegral_of_smul_mem_submodule Λ hne hfg s hs

theorem dualLat_le {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) (c : 𝔠.elt) (hc0 : (c : F) ≠ 0)
    (N : Submodule (𝓞 F) F) (hN0 : N ≠ ⊥) (hN : N ≤ dualLat 𝔠)
    (H : ∀ t : F, (∀ y ∈ N, ∃ m : ℤ, Algebra.trace ℚ F ((c : F) * t * y) = m) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → IsIntegral ℤ ((a : F) * t)) :
    (dualLat 𝔠 : Submodule (𝓞 F) F) ≤ N := by
  set C : FractionalIdeal (𝓞 F)⁰ F := (𝔠 : FractionalIdeal (𝓞 F)⁰ F) with hCdef
  have hC : C ≠ 0 := 𝔠.ne_zero
  have hcC : (c : F) ∈ C := c.2
  let Nf : FractionalIdeal (𝓞 F)⁰ F := ⟨N, FractionalIdeal.isFractional_of_le hN⟩
  have hNf : Nf ≠ 0 := by
    intro h0
    apply hN0
    have := congrArg (fun I : FractionalIdeal (𝓞 F)⁰ F ↦ (I : Submodule (𝓞 F) F)) h0
    simpa [Nf] using this
  set cs := FractionalIdeal.spanSingleton (𝓞 F)⁰ (c : F)
  have hcs : cs ≠ 0 := by simpa [cs, FractionalIdeal.spanSingleton_eq_zero_iff] using hc0
  have key : FractionalIdeal.dual ℤ ℚ (cs * Nf) * (cs * C⁻¹) ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro t ht u hu
    obtain ⟨v, hv, rfl⟩ := (FractionalIdeal.mem_singleton_mul).mp hu
    have hcv : (c : F) * v ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      have := FractionalIdeal.mul_mem_mul hcC hv
      rwa [mul_inv_cancel₀ hC] at this
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).mp hcv
    have hint : IsIntegral ℤ ((a : F) * t) := by
      refine H t (fun y hy ↦ ?_) a (fun d ↦ ?_)
      · have hy' : (c : F) * y ∈ cs * Nf :=
          FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hy
        obtain ⟨m, hm⟩ := (FractionalIdeal.mem_dual (mul_ne_zero hcs hNf)).mp ht _ hy'
        refine ⟨m, ?_⟩
        rw [Algebra.traceForm_apply] at hm
        rw [show (c : F) * t * y = t * ((c : F) * y) by ring, ← hm]; simp
      · have hvd : v * d ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
          have := FractionalIdeal.mul_mem_mul hv d.2
          rwa [inv_mul_cancel₀ hC] at this
        obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).mp hvd
        refine ⟨b, Subtype.ext ?_⟩
        simp only [Submodule.coe_smul, Algebra.smul_def]
        change (a : F) * d = (b : F) * c
        change algebraMap (𝓞 F) F a = _ at ha
        change algebraMap (𝓞 F) F b = _ at hb
        change algebraMap (𝓞 F) F a * d = algebraMap (𝓞 F) F b * c
        rw [ha, hb]; ring
    rw [mul_comm, ← ha]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨_, hint⟩, rfl⟩
  rw [FractionalIdeal.dual_eq_mul_inv, mul_inv] at key
  have key2 : FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ ≤ 1 := by
    convert key using 1
    calc FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹
        = FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ * (cs⁻¹ * cs) := by rw [inv_mul_cancel₀ hcs, mul_one]
      _ = _ := by ring
  have key3 : FractionalIdeal.dual ℤ ℚ 1 * C⁻¹ * Nf⁻¹ * Nf ≤ 1 * Nf :=
    FractionalIdeal.mul_le.mpr fun i hi j hj ↦ FractionalIdeal.mul_mem_mul (key2 hi) hj
  simp only [mul_assoc, inv_mul_cancel₀ hNf, mul_one, one_mul] at key3
  have : dualLat 𝔠 ≤ Nf := by
    unfold dualLat
    rw [FractionalIdeal.dual_eq_mul_inv]
    exact key3
  exact (FractionalIdeal.coe_le_coe.mpr this)

theorem dualLat_le_span_values : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (Λ : Submodule ℤ (Fin (Module.finrank ℚ F) → ℂ)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)) (h : Fin (Module.finrank ℚ F) → ℝ),
    (∀ (a : 𝓞 F) (l : Fin (Module.finrank ℚ F) → ℂ), l ∈ Λ → (fun j ↦ (e j (a : F) : ℂ) * l j) ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin (Module.finrank ℚ F) → ℂ)) = ⊤ → (∀ j, 0 < h j) →
    ∀ P : Λ → Λ → F, (∀ l l' : Λ, P l l' = -P l' l) → (∀ l₁ l₂ l' : Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') →
      (∀ (a : 𝓞 F) (l l' al : Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') →
      (∀ l l' : Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) →
      (∀ l l' : Λ, P l l' ∈ dualLat 𝔠) →
    (∀ x : Fin (Module.finrank ℚ F) → ℂ, (∀ l : Λ, ∃ n : ℤ,
      (∑ j, (h j : ℂ) * (x j * starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im = 2 * n) →
      ∀ a : 𝓞 F, (∀ d : 𝔠.elt, ∃ b : 𝓞 F, a • d = b • c) → (fun j ↦ (e j (a : F) : ℂ) * x j) ∈ Λ) →
    ∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : Λ, t = P l l'} := by
  intro F _ _ _ 𝔠 c hc Λ e h hΛa hdisc hspan hpos P _hanti _hadd hlin htr hdual hker
  have hn : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hc0 : (c : F) ≠ 0 := fun h0 ↦ by
    have := hc (e ⟨0, hn⟩); rw [h0, map_zero] at this; exact lt_irrefl _ this

  have hb : ∀ (s : F) (l₀ l : Λ),
      (∑ j, (h j : ℂ) * (((e j s : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) *
        starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * s * P l₀ l) : ℚ) : ℝ) := by
    intro s l₀ l
    obtain ⟨m, hm0, hmint⟩ :=
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic s)).exists_integral_multiple
    let a : 𝓞 F := ⟨m • s, hmint⟩
    have ha : (a : F) = (m : F) * s := by simp [a, zsmul_eq_mul]
    have hal : (fun j ↦ (e j (a : F) : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) ∈ Λ := hΛa a l₀ l₀.2
    have h1 := htr ⟨_, hal⟩ l
    rw [hlin a l₀ l ⟨_, hal⟩ rfl] at h1
    have e1 : (∑ j, (h j : ℂ) * (((⟨_, hal⟩ : Λ) : Fin (Module.finrank ℚ F) → ℂ) j *
          starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j))) =
        ((m : ℝ) : ℂ) * ∑ j, (h j : ℂ) * (((e j s : ℂ) * (l₀ : Fin (Module.finrank ℚ F) → ℂ) j) *
          starRingEnd ℂ ((l : Fin (Module.finrank ℚ F) → ℂ) j)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [ha, map_mul, map_intCast]; push_cast; ring
    have e2 : Algebra.trace ℚ F ((c : F) * ((a : F) * P l₀ l)) =
        (m : ℚ) * Algebra.trace ℚ F ((c : F) * s * P l₀ l) := by
      rw [ha, show (c : F) * ((m : F) * s * P l₀ l) = (m : ℚ) • ((c : F) * s * P l₀ l) by
        rw [Algebra.smul_def, map_intCast]; ring, map_smul, smul_eq_mul]
    rw [e1, e2, Complex.im_ofReal_mul] at h1
    push_cast at h1
    have hm : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm0
    apply mul_left_cancel₀ hm
    rw [h1]; ring
  set N := Submodule.span (𝓞 F) {t | ∃ l l' : Λ, t = P l l'} with hNdef
  have hN : N ≤ dualLat 𝔠 := Submodule.span_le.mpr (by rintro _ ⟨l, l', rfl⟩; exact hdual l l')
  have hN0 : N ≠ ⊥ := by
    obtain ⟨l, hl, l', hl', hne⟩ := exists_im_ne_zero hn Λ hspan h hpos
    intro hbot
    have hmem : P ⟨l, hl⟩ ⟨l', hl'⟩ ∈ N := Submodule.subset_span ⟨_, _, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    apply hne
    have := htr ⟨l, hl⟩ ⟨l', hl'⟩
    rw [hmem] at this
    simpa using this
  intro t ht
  refine dualLat_le 𝔠 c hc0 N hN0 hN (fun s hs a ha ↦ ?_) ht
  refine isIntegral_of_stab hn Λ e hspan _ (fun l₀ hl₀ ↦ ?_)
  have hx := hker (fun j ↦ (e j s : ℂ) * l₀ j) (fun l ↦ ?_) a ha
  · convert hx using 1
    funext j
    simp only [map_mul]; push_cast; ring
  · obtain ⟨m, hm⟩ := hs (P ⟨l₀, hl₀⟩ l) (Submodule.subset_span ⟨_, _, rfl⟩)
    refine ⟨m, ?_⟩
    rw [hb s ⟨l₀, hl₀⟩ l, hm]
    push_cast; ring

end GlobalTheory.RealMult.SpanDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_coboundary_swap_pullback_commute : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (S : Type) [CommRing S] (r : R →+* S), (∀ f, map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f)) ∧ (∀ c, map r (cob2 μ c) = cob2 (fun i => map r (μ i)) (map r c)) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, map r (Katz.swap c) = Katz.swap (map r c)) ∧ (∀ f : MvPowerSeries (Fin d) R, lin (map r f) = fun i => r (lin f i)) ∧ ∀ φ : Fin d → MvPowerSeries (Fin d) R, (∀ i, constantCoeff (φ i) = 0) → (∀ c, map r (pull2 φ c) = pull2 (fun i => map r (φ i)) (map r c)) ∧ ∀ f : MvPowerSeries (Fin d) R, map r (subst φ f) = subst (fun i => map r (φ i)) (map r f) := by
  first | exact @GlobalTheory.Katz.map_cob_swap_pull | exact GlobalTheory.Katz.map_cob_swap_pull | (intros; apply GlobalTheory.Katz.map_cob_swap_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFormalGroupLawQuasiLogarithms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]

theorem map_inL_fr {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (f : MvPowerSeries (Fin d) R) : MvPowerSeries.map h (inL f) = inL (MvPowerSeries.map h f) := by
  unfold inL
  rw [map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_inR_fr {R S : Type} [CommRing R] [CommRing S] (h : R →+* S) {d : ℕ}
    (f : MvPowerSeries (Fin d) R) : MvPowerSeries.map h (inR f) = inR (MvPowerSeries.map h f) := by
  unfold inR
  rw [map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem map_coboundaryOne_teichmullerLift_law (σ : k →+* k') {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (f : MvPowerSeries (Fin d) (Fr p k)) :
    MvPowerSeries.map (frMap p σ) (cob1 (fun i => lift p (μ i)) f) =
      cob1 (fun i => lift p (MvPowerSeries.map σ (μ i))) (MvPowerSeries.map (frMap p σ) f) := by
  unfold cob1
  rw [map_sub, map_sub, map_inL_fr, map_inR_fr,
    map_subst (hasSubst_of_constantCoeff_zero fun i => constantCoeff_lift p (hμ i))]
  simp only [map_lift]

theorem map_mem_intBy_one (σ : k →+* k') {ι : Type} {g : MvPowerSeries ι (Fr p k)}
    (hg : g ∈ intBy p k ι 1) : MvPowerSeries.map (frMap p σ) g ∈ intBy p k' ι 1 := by
  intro α
  obtain ⟨w, hw⟩ := hg α
  refine ⟨WittVector.map σ w, ?_⟩
  rw [coeff_map, hw, one_mul, one_mul, frMap_algebraMap]

theorem map_mem_quasiInt (σ : k →+* k') {ι : Type} {g : MvPowerSeries ι (Fr p k)}
    (hg : g ∈ quasiInt p k ι) : MvPowerSeries.map (frMap p σ) g ∈ quasiInt p k' ι := by
  intro α i
  obtain ⟨w, hw⟩ := hg α i
  refine ⟨WittVector.map σ w, ?_⟩
  rw [coeff_map, ← map_natCast (frMap p σ), ← map_mul, hw, frMap_algebraMap]

theorem frMap_red (σ : k →+* k') {x : Fr p k} {a : WittVector p k} {b : k}
    (hx : x = algebraMap _ (Fr p k) a) (ha : WittVector.constantCoeff a = b) :
    frMap p σ x = algebraMap _ (Fr p k') (WittVector.map σ a) ∧
      WittVector.constantCoeff (WittVector.map σ a) = σ b := by
  refine ⟨by rw [hx, frMap_algebraMap], ?_⟩
  rw [← ha, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem quasiLog_map :
    ∀ (p : ℕ) [Fact p.Prime] (k k' : Type) [Field k] [CharP k p] [Field k'] [CharP k' p]
      (σ : k →+* k') (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ)
      (hμ' : IsLaw (fun i => MvPowerSeries.map σ (μ i))), ∀ f ∈ quasiLog p hμ,
      MvPowerSeries.map (frMap p σ) f ∈ quasiLog p hμ' ∧
      (f ∈ intBy p k (Fin d) 1 → MvPowerSeries.map (frMap p σ) f ∈ intBy p k' (Fin d) 1) ∧
      (∀ t, Red p (cob1 (fun i => Katz.lift p (μ i)) f) t →
        Red p (cob1 (fun i => Katz.lift p (MvPowerSeries.map σ (μ i)))
          (MvPowerSeries.map (frMap p σ) f)) (MvPowerSeries.map σ t)) ∧
      ∀ w, RedV p (lin f) w → RedV p (lin (MvPowerSeries.map (frMap p σ) f)) (fun i => σ (w i)) := by
  intro p _ k k' _ _ _ _ σ d μ hμ hμ' f hf
  have key := map_coboundaryOne_teichmullerLift_law p σ μ hμ.const f
  refine ⟨⟨map_mem_quasiInt p σ hf.1, ?_⟩, map_mem_intBy_one p σ, ?_, ?_⟩
  · rw [← key]; exact map_mem_intBy_one p σ hf.2
  · intro t ht α
    obtain ⟨w, hw, hw0⟩ := ht α
    obtain ⟨e1, e2⟩ := frMap_red p σ hw hw0
    refine ⟨WittVector.map σ w, ?_, ?_⟩
    · rw [← key, coeff_map, e1]
    · rw [e2, coeff_map]
  · intro w hw i
    obtain ⟨a, ha, ha0⟩ := hw i
    obtain ⟨e1, e2⟩ := frMap_red p σ ha ha0
    refine ⟨WittVector.map σ a, ?_, e2⟩
    change coeff _ (MvPowerSeries.map (frMap p σ) f) = _
    rw [coeff_map]; exact e1

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterateStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R), map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  first | exact @GlobalTheory.LawDer.map_invDer_iterate | exact GlobalTheory.LawDer.map_invDer_iterate | (intros; apply GlobalTheory.LawDer.map_invDer_iterate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNatStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapPowerSeriesFamilyToFractions_formalGroupLawNatMultiple : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  first | exact @GlobalTheory.QLog.up_nmul | exact GlobalTheory.QLog.up_nmul | (intros; apply GlobalTheory.QLog.up_nmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealAffineOpenEqVanishingUniformisationP
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MaxPoints

theorem main : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens), IsAffineOpen U → ∀ m : Ideal Γ(A.left, U), m.IsMaximal →
      ∃ z ∈ pre u.ex U, ∀ b, b ∈ m ↔ val u.ex U b z = 0 := by
  intro A _ g L u hA U hU m hm
  haveI : Smooth A.hom := hA.smooth
  have hft : LocallyOfFiniteType A.hom := inferInstance
  let c : ℂ →+* Γ(A.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ A.hom.appLE ⊤ U (fun _ _ => trivial)).hom
  have hc : c.FiniteType := by
    have h1 : (A.hom.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType A.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  letI : Algebra ℂ Γ(A.left, U) := c.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(A.left, U) := hc
  haveI : IsJacobsonRing Γ(A.left, U) := isJacobsonRing_of_finiteType (A := ℂ)
  letI : Field (Γ(A.left, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(A.left, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(A.left, U) ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (Γ(A.left, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (Γ(A.left, U) ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ _) hb
  let e : Γ(A.left, U) →ₐ[ℂ] ℂ := (i.symm : (Γ(A.left, U) ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)
  have he : ∀ a, e.toRingHom (constFn A.hom U a) = a := fun a => e.commutes a
  obtain ⟨x, ⟨hxU, hx⟩, -⟩ := GlobalTheory.existsUnique_point_of_ringHom A U hU e.toRingHom he
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨z, hxU, fun b => ?_⟩
  change b ∈ m ↔ valAt' (u.ex z).left U b = 0
  rw [hx b]
  change b ∈ m ↔ i.symm (Ideal.Quotient.mk m b) = 0
  rw [← map_zero i.symm, i.symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableNsqExtendAndPsiStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_nsq_and_psi_of_isSecOn : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (Ω : Set Y) (h : ι → Y → ℂ), IsOpen Ω → A.IsSecOn la Ω h → (∀ i y, y ∉ Ω → h i y = 0) → Measurable (A.nsq la h) ∧ ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → Measurable (psi A L s) := by
  first | exact @GlobalTheory.OTY.measurable_nsq_extend_and_psi | exact GlobalTheory.OTY.measurable_nsq_extend_and_psi | (intros; apply GlobalTheory.OTY.measurable_nsq_extend_and_psi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureComplNonvanishingSetEqZeroOfDenseStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_compl_nonvanishingSet_eq_zero_of_dense : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → Dense (nz A τ) → A.mu (nz A τ)ᶜ = 0 := by
  first | exact @GlobalTheory.zeroSet_null_of_dense_nz | exact GlobalTheory.zeroSet_null_of_dense_nz | (intros; apply GlobalTheory.zeroSet_null_of_dense_nz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdentityComponentsOfMulInvStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unitComponent_of_mul_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : G.left), (∀ z ∈ U, G.hom z = G.hom y → z ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))}) → y ∈ {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} → y ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  first | exact @GlobalTheory.mem_identityComponents_of_mul_inv | exact GlobalTheory.mem_identityComponents_of_mul_inv | (intros; apply GlobalTheory.mem_identityComponents_of_mul_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdLiftOfFrameMatrixEquation
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem mu_dvd_of_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (ι κ : Type) [Fintype ι] (R S : Matrix ι ι F.B) (R0 S0 : Matrix ι ι (Ainf p O)) (Y : Matrix ι κ F.B) (F0 : Matrix ι κ (Ainf p O)), (∀ i j, F.τ ∣ R i j - F.a (R0 i j)) → (∀ i j, F.τ ∣ S i j - F.a (S0 i j)) → (∀ i m, F.τ ∣ Y i m - F.a (F0 i m)) → R * Y.map F.σ = S * Y → ∀ i m, Sandwich.mu ε ∣ (R0 * F0.map WittVector.frobenius - S0 * F0) i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F ι κ _ R S R0 S0 Y F0 hR hS hY hRS i m
  apply (F.a_dvd _).1
  set q := Ideal.Quotient.mk (Ideal.span {F.τ})
  have key : ∀ x y : F.B, F.τ ∣ x - y → q x = q y := fun x y h =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
  have hR' : ∀ i j, q (R i j) = q (F.a (R0 i j)) := fun i j => key _ _ (hR i j)
  have hS' : ∀ i j, q (S i j) = q (F.a (S0 i j)) := fun i j => key _ _ (hS i j)
  have hY' : ∀ i m, q (Y i m) = q (F.a (F0 i m)) := fun i m => key _ _ (hY i m)
  have hYσ : ∀ i m, q (F.σ (Y i m)) = q (F.a (WittVector.frobenius (F0 i m))) := fun i m => by
    apply key
    rw [← F.σ_a, ← map_sub]
    exact tau_dvd_sigma F _ (hY i m)
  have h := congrArg (fun M => q (M i m)) hRS
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul] at h
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change q _ = 0
  rw [Matrix.sub_apply, map_sub, map_sub, sub_eq_zero, Matrix.mul_apply, Matrix.mul_apply]
  simp only [map_sum, map_mul, Matrix.map_apply, ← hR', ← hS', ← hYσ, ← hY']
  exact h

end GlobalTheory.WinLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesCoeffsInIdealPowEqFactorialMulStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_coeffsInIdeal_pow_eq_factorial_mul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (τ : Type) (w : MvPowerSeries τ B), (∀ α, coeff α w ∈ J) → ∀ n : ℕ, 0 < n → ∃ y : MvPowerSeries τ B, (∀ α, coeff α y ∈ J) ∧ w ^ n = (n.factorial : MvPowerSeries τ B) * y := by
  first | exact @GlobalTheory.DPSeries.pow_eq_factorial_mul | exact GlobalTheory.DPSeries.pow_eq_factorial_mul | (intros; apply GlobalTheory.DPSeries.pow_eq_factorial_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesSubstCoeffSubMemIdealStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_subst_coeff_sub_mem_ideal : ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ] (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) → (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) → ∀ (m : ℕ) (c : MvPowerSeries σ Q), (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N, coeff w (subst (up Q u) c) - coeff w (subst (up Q ℓ) c) = algebraMap B Q r := by
  first | exact @GlobalTheory.SubstMod.subst_coeff_sub_mem | exact GlobalTheory.SubstMod.subst_coeff_sub_mem | (intros; apply GlobalTheory.SubstMod.subst_coeff_sub_mem <;> assumption)
end

