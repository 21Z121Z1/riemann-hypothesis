import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0060
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisLocallyMonomial
section
noncomputable section

open Filter Topology
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.GaussMono

theorem eventually_iSup_eq_monomial_left (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≤] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push_neg at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  have hσ0 : 0 < ρ / 2 := by positivity
  have hσρ : ρ / 2 < ρ := by linarith
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hσ0 j)) hρ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, OrderDual.toDual n)) ⟨j, Finset.mem_insert_self _ _⟩
  have hpos : ∀ᶠ r in 𝓝[≤] ρ, ρ / 2 < r := (eventually_gt_nhds hσρ).filter_mono nhdsWithin_le_nhds
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≤] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin, hpos] with r hr hr0
      have hr : r ≤ ρ := hr
      have hr0 : 0 ≤ r := hσ0.le.trans hr0.le
      simp only at h h'
      have hin : i ≤ n := OrderDual.toDual_le_toDual.1 h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (div_nonneg hr0 hρ.le) ((div_le_one hρ).2 hr) hin)
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  filter_upwards [(eventually_all_finset _).2 key, hpos, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : r ≤ ρ := hr
  have hr0 : 0 ≤ r := hσ0.le.trans hrσ.le
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * ρ ^ n := by gcongr; exact h1 n
        _ ≤ ρ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hρ.le hρ1.le (not_lt.1 hn)
        _ ≤ c j * (ρ / 2) ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem eventually_monomial {R : Type} [CommRing R] (p : R) {L ρ : ℝ} (hL : 0 < L) (hLρ : L ≤ ρ) (hρ1 : ρ < 1)
    (N : ℝ → R → ℝ)
    (hN : ∀ r, L ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, L ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n)
    (f : Filter ℝ) (hf : f ≤ 𝓝 ρ) (hf0 : pure ρ ≤ f) (hfL : ∀ᶠ r in f, L ≤ r ∧ r < 1)
    (hmono : ∀ c : ℕ → ℝ, (∀ n, 0 ≤ c n) → (∀ n, c n ≤ 1) → (⨆ n, c n * ρ ^ n) ≠ 0 →
      ∃ i, ∀ᶠ r in f, (⨆ n, c n * r ^ n) = c i * r ^ i) :
    ∃ (c : ℝ) (k : ℤ), 0 < c ∧ ∀ᶠ r in f, N r b = c * r ^ k := by
  have hρ : 0 < ρ := hL.trans_le hLρ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, L ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hL.le.trans hr) _) (e1 z)
  have hbb : ∀ r, L ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨-, -, -, e4, e5⟩ := hN r hr hr1
    rw [GlobalTheory.GaussSlope.map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨-, e2, e3, -, -⟩ := hN ρ hLρ hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ hLρ hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ hLρ hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ hLρ hρ1] at ha
  obtain ⟨i, hi⟩ := hmono c h0 h1 ((pow_pos hρ _).trans ha).ne'
  have hiρ : (⨆ n, c n * ρ ^ n) = c i * ρ ^ i := Filter.mem_pure.1 (hf0 hi)
  rw [hiρ] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  refine ⟨c i, (i : ℤ) - k, hci, ?_⟩
  filter_upwards [hi, hf h4, hfL] with r hr1 hr2 hr
  obtain ⟨hr, hr3⟩ := hr
  have hr0 : 0 < r := hL.trans_le hr
  obtain ⟨-, e2, e3, -, -⟩ := hN r hr hr3
  have h6 := hbb r hr hr3
  have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
  rw [hab, GlobalTheory.GaussSlope.add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
  rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
  field_simp

end GlobalTheory.GaussMono

namespace GlobalTheory.PMon.Gauss

theorem gC_monomial_near : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ₀ : ℝ, (l : ℝ)⁻¹ ≤ ρ₀ →
    ρ₀ < 1 → (∃ (c : ℝ) (k : ℤ) (ρ₂ : ℝ), 0 < c ∧ ρ₀ < ρ₂ ∧ ρ₂ < 1 ∧
      ∀ ρ ∈ Set.Icc ρ₀ ρ₂, gC l ρ x = c * ρ ^ k) ∧
    ((l : ℝ)⁻¹ < ρ₀ → ∃ (c : ℝ) (k : ℤ) (ρ₁ : ℝ), 0 < c ∧ (l : ℝ)⁻¹ ≤ ρ₁ ∧ ρ₁ < ρ₀ ∧
      ∀ ρ ∈ Set.Icc ρ₁ ρ₀, gC l ρ x = c * ρ ^ k) := by
  intro l _ x hx ρ₀ hρl hρ1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ0 : 0 < ρ₀ := hL.trans_le hρl
  have hN : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ y, gC l r y ≤ 1) ∧
      (∀ y z, gC l r (y + z) ≤ max (gC l r y) (gC l r z)) ∧ (∀ y, gC l r (-y) = gC l r y) ∧
      (∀ y z, gC l r (y * z) = gC l r y * gC l r z) ∧ gC l r (l : Formalism.Per.Acris l) = r := by
    intro r hr hr1
    obtain ⟨e1, e2, e3, e4, e5⟩ := isGauss_gC_target l r hr hr1
    refine ⟨fun y => (e1 y).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, e5]
    exact GlobalTheory.GaussSlope.gauss_l l (hL.le.trans hr)
  have hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : Formalism.Per.Acris l) (c : ℕ → ℝ),
      (l : Formalism.Per.Acris l) ^ k * x = a + (l : Formalism.Per.Acris l) ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → gC l r a = ⨆ n, c n * r ^ n := by
    intro n
    obtain ⟨s, z, h⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
    obtain ⟨k, a, ha⟩ := GlobalTheory.GaussSlope.exists_pow_mul_eq l s
    refine ⟨k, algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a, z,
      fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (isGauss_gC_target l r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)
  have hb : 0 < gC l ρ₀ x := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ₀ hρl hρ1
  constructor
  · have hfL : ∀ᶠ r in 𝓝[≥] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hρ1).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨hρl.trans hr, hr1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≥] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Ici.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussSlope.eventually_iSup_eq_monomial c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
    have hu : ρ₀ < u := hu
    obtain ⟨ρ₂, h2a, h2b⟩ := exists_between (lt_min hu hρ1)
    exact ⟨c, k, ρ₂, hc, h2a, h2b.trans_le (min_le_right _ _),
      fun r hr => hsub ⟨hr.1, hr.2.trans_lt (h2b.trans_le (min_le_left _ _))⟩⟩
  · intro hlt
    have hfL : ∀ᶠ r in 𝓝[≤] ρ₀, (l : ℝ)⁻¹ ≤ r ∧ r < 1 := by
      filter_upwards [self_mem_nhdsWithin, (eventually_gt_nhds hlt).filter_mono nhdsWithin_le_nhds] with r hr hr1
      exact ⟨(hr1 : (l : ℝ)⁻¹ < r).le, (hr : r ≤ ρ₀).trans_lt hρ1⟩
    obtain ⟨c, k, hc, hev⟩ := GlobalTheory.GaussMono.eventually_monomial (l : Formalism.Per.Acris l) hL hρl hρ1 (gC l) hN x hb
      hd (𝓝[≤] ρ₀) nhdsWithin_le_nhds (pure_le_nhdsWithin (Set.mem_Iic.2 le_rfl)) hfL
      (fun c h0 h1 hG => GlobalTheory.GaussMono.eventually_iSup_eq_monomial_left c h0 h1 hρ0 hρ1 hG)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsLE_iff_exists_Ioc_subset.1 hev
    have hu : u < ρ₀ := hu
    obtain ⟨ρ₁, h1a, h1b⟩ := exists_between (max_lt hu hlt)
    exact ⟨c, k, ρ₁, hc, (le_max_right _ _).trans h1a.le, h1b,
      fun r hr => hsub ⟨(le_max_left _ _).trans_lt (h1a.trans_le hr.1), hr.2⟩⟩

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesPair
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.PairFormula

theorem perp_iff {n : ℕ} [NeZero n] {Λ : Type} [CommRing Λ]
    {M : Type} [AddCommGroup M] [Module Λ M] [Module (ZMod n) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {M' : Type} [AddCommGroup M'] [Module Λ M'] [TopologicalSpace M'] [DiscreteTopology M']
    {D Γ : Type} [Group D] [TopologicalSpace D] [Group Γ]
    (ρ : Representation Λ D M) (ρ' : Representation Λ D M') (P : M →+ M' →+ ZMod n)
    (μ : Γ →* (ZMod n)ˣ) (ρS : Representation (ZMod n) Γ M) (φ : D →* Γ)
    (hρ : ∀ g m, ρ g m = ρS (φ g) m) (hc : ContAction (ρS.comp φ)) (χ : D → ZMod n)
    (hχ : ∀ g, χ g = ((μ (φ g) : (ZMod n)ˣ) : ZMod n))
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y)
    (L : Submodule Λ (H1 ρ)) (LS : Submodule (ZMod n) (H1 (ρS.comp φ)))
    (hL : ∀ (z : Z1 ρ) (z' : Z1 (ρS.comp φ)), (∀ g, z'.1 g = z.1 g) →
      (Submodule.Quotient.mk z ∈ L ↔ Submodule.Quotient.mk z' ∈ LS))
    (y : Z1 ρ') (y' : Z1 ((twDual μ ρS).comp φ)) (hy : ∀ g x, y'.1 g x = P x (y.1 g)) :
    (∀ x ∈ LS, cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') x = 0) ↔
      ∀ x : Z1 ρ, Submodule.Quotient.mk x ∈ L → CupB χ (fun g m => ρ' g m) P x.1 y.1 := by
  let E := GlobalTheory.DualPairFormula.cocycleEquiv ρ (ρS.comp φ) (AddEquiv.refl M) hρ
  have hE : ∀ x g, (E x).1 g = x.1 g := fun _ _ => rfl
  have key : ∀ (x : Z1 ρ) g h, P (x.1 (g * h)) (y.1 (g * h)) = P (x.1 g) (y.1 g) +
      P (x.1 g) (ρ' g (y.1 h)) + P (ρ g (x.1 h)) (y.1 g) + χ g * P (x.1 h) (y.1 h) :=
    fun x g h => by
    rw [x.2.2, y.2.2, ← hP]
    simp only [map_add, AddMonoidHom.add_apply]
    ring
  have cb : ∀ x : Z1 ρ, Continuous fun g => P (x.1 g) (y.1 g) := fun x =>
    (continuous_of_discreteTopology (f := fun p : M × M' => P p.1 p.2)).comp
      (x.2.1.prodMk y.2.1)
  have hcup : ∀ x : Z1 ρ,
      cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        P (x.1 g) (ρ' g (y.1 h)) = χ g * c h - c (g * h) + c g := fun x => by
    have e0 : cupH1H1TwistedDual μ ρS φ hc (Submodule.Quotient.mk y') (Submodule.Quotient.mk (E x)) = 0 ↔
      ∃ c : D → ZMod n, Continuous c ∧ ∀ g h,
        χ g * c h - c (g * h) + c g = P (ρ g (x.1 h)) (y.1 g) := by
      refine (Submodule.Quotient.mk_eq_zero _).trans ((separated_dvr_second_cohomology_mem _ _).trans ?_)
      refine exists_congr fun c => and_congr_right fun _ => ?_
      rw [funext_iff, Prod.forall]
      refine forall_congr' fun g => forall_congr' fun h => ?_
      rw [← hy, hρ, hχ]
      exact Iff.rfl
    rw [e0]
    constructor
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - P (x.1 g) (y.1 g), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h - key x g h
    · rintro ⟨c, hc1, hc2⟩
      refine ⟨fun g => -c g - P (x.1 g) (y.1 g), hc1.neg.sub (cb x), fun g h => ?_⟩
      linear_combination hc2 g h + key x g h
  constructor
  · intro H x hx
    obtain ⟨c, hc1, hc2⟩ := (hcup x).1 (H _ ((hL _ _ (hE _)).1 hx))
    exact ⟨c, (IsLocallyConstant.iff_continuous c).2 hc1, hc2⟩
  · intro H x hx
    induction x using Submodule.Quotient.induction_on with | H x =>
    obtain ⟨x, rfl⟩ := E.surjective x
    obtain ⟨f, hf1, hf2⟩ := H x ((hL _ _ (hE _)).2 hx)
    exact (hcup x).2 ⟨f, hf1.continuous, hf2⟩

open GlobalTheory.DualPairFormula GlobalTheory.SelInf in

theorem greenbergWiles_pair : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1) → ∀ (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ C : Set (H1 ρ'), (∀ y : Z1 ρ', Submodule.Quotient.mk y ∈ C ↔ (∀ v ∉ S, ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧ ∀ v ∈ S, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) → Finite C ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card W ^ InfinitePlace.nrComplexPlaces F = Nat.card C * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ n Λ _ W _ _ _ _ _ W' _ _ _ _ _ ρ ρ' P hn hρ hρ' h1 h2 hP
    S A hS hur L hL C hC
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hk : ∀ (x : W) (y : W'), (l ^ n) • P x y = 0 := fun x y => by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  haveI : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => h1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, hk]
  haveI : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => h2 _ fun x => by
    rw [map_nsmul, hk]
  obtain ⟨ρS, hρS, hd⟩ := exists_descent (zmodRep (l ^ n) ρ) hρ (S : Set _)
    fun v hv B hB σ hσ => by
      ext x
      change ρ σ x = x
      rw [(hur v hv B hB σ hσ).1]
      rfl
  replace hd : ∀ (g : G F Ω) (x : W), ρ g x = ρS (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g) x := hd
  obtain ⟨μ, hμ⟩ := PoitouTate.exists_lift_cycMod (Ω := Ω) (r := n) hS
  have hμ' : ∀ g, ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) =
      ((μ (toGS Ω _ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := fun g => by rw [← hμ]; rfl
  have hfin : Finite (TDual (ZMod (l ^ n)) W) := GlobalTheory.DualSide.finite_TDual
  have hfin' : Finite (TDual (ZMod (l ^ n)) W') := GlobalTheory.DualSide.finite_TDual
  let f : W' →+ TDual (ZMod (l ^ n)) W := AddMonoidHom.mk'
    (fun y => TDual.mk ((P.flip y).toZModLinearMap (l ^ n))) (fun y y' => by ext x; simp)
  have hf : ∀ y x, f y x = P x y := fun _ _ => rfl
  have inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ?_
    rw [← hf, hy]
    rfl
  have c1 : Nat.card (TDual (ZMod (l ^ n)) W) = Nat.card W := GlobalTheory.ZModDual.card_dual_eq _ W
  have c2 : Nat.card (TDual (ZMod (l ^ n)) W') = Nat.card W' := GlobalTheory.ZModDual.card_dual_eq _ W'
  have c3 : Nat.card W ≤ Nat.card W' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective
      (fun x => TDual.mk ((P x).toZModLinearMap (l ^ n))) fun x x' hxx' => ?_
    have : ∀ y, P x y = P x' y := fun y =>
      congrArg (fun φ : TDual (ZMod (l ^ n)) W' => φ y) hxx'
    exact sub_eq_zero.1 (h1 _ fun y => by rw [map_sub, AddMonoidHom.sub_apply, this, sub_self])
  let e : W' ≃+ TDual (ZMod (l ^ n)) W :=
    AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3))
  have he : ∀ y x, e y x = P x y := fun _ _ => rfl
  have hee : ∀ g y, e (ρ' g y) = twDual μ ρS (toGS Ω _ g) (e y) := fun g y => by
    ext x
    rw [twDual_apply, he, he, ← map_inv, ← hd, ← hμ', ← hP, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  have hex := fun v : S => exists_transport_cond (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
    (ρS.comp (locFam S (fun v => A.1 v.1) v)) (AddEquiv.refl W) (fun g x => hd g x) (L v.1)
  choose LS hLS1 hLS2 using hex
  obtain ⟨f1, f2, hmain⟩ := GlobalTheory.GWComplex.greenbergWiles_totallyComplex hPT hLF hGF hEC F Ω l n W S
    ρS hn hS hρS μ hμ (fun v => A.1 v.1) (fun v => A.2 v.1) LS
  obtain ⟨E1⟩ := selAll_equiv_sel F Ω Λ (ZMod (l ^ n)) W W S A ρ ρS (AddEquiv.refl W) hρ hd L LS
    hL hLS2

  have hv' : ∀ (z : Z1 (twDual μ ρS)) (v : S),
      resH1 (twDual μ ρS) (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v)
        (Submodule.Quotient.mk z) ∈ perpCond μ ρS (locFam S fun v => A.1 v.1)
          (fun v => hρS.comp' (continuous_locFam S _ v)) LS v ↔
      ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v.1)).subtype), Submodule.Quotient.mk x ∈ L v.1 →
        CupB (fun g : Dec (F := F) (A.1 v.1) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)))
          (fun g m => ρ' g.1 m) P x.1 (fun g => (infZ e hee z).1 g.1) := fun z v => by
    rw [mem_perpCond]
    exact perp_iff (ρ.comp (Dec (F := F) (A.1 v.1)).subtype) (ρ'.comp (Dec (F := F) (A.1 v.1)).subtype)
      P μ ρS (locFam S (fun v => A.1 v.1) v) (fun g x => hd g x) _
      (fun g => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g => hμ' g.1)
      (fun g => hP g.1) (L v.1) (LS v) (hLS2 v)
      (restrictCocycles1 ρ' (Dec (F := F) (A.1 v.1)).subtype continuous_subtype_val (infZ e hee z))
      (restrictCocycles1 (twDual μ ρS) (locFam S (fun v => A.1 v.1) v) (continuous_locFam S _ v) z)
      (fun g x => by
        change z.1 (toGS Ω _ g.1) x = P x (e.symm (z.1 (toGS Ω _ g.1)))
        rw [← he, e.apply_symm_apply])
  have hmem : ∀ z : Z1 (twDual μ ρS),
      Submodule.Quotient.mk z ∈ Sel (twDual μ ρS) (locFam S fun v => A.1 v.1) (continuous_locFam S _)
        (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) ↔
      Submodule.Quotient.mk (infZ e hee z) ∈ C := fun z => by
    rw [mem_Sel, hC]
    constructor
    · intro h
      refine ⟨fun v hv σ hσ => ?_, fun v hv x hx => (hv' z ⟨v, hv⟩).1 (h ⟨v, hv⟩) x hx⟩
      have : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) σ = 1 :=
        (QuotientGroup.eq_one_iff σ).2 (Ine_le_NS (by simpa using hv) (A.2 v) hσ)
      rw [infZ_apply, this, z_one, map_zero]
    · rintro ⟨-, h⟩ v
      exact (hv' z v).2 (h v.1 v.2)
  have hmem' : ∀ x : H1 (twDual μ ρS),
      x ∈ Sel (twDual μ ρS) (locFam S fun v => A.1 v.1) (continuous_locFam S _)
        (perpCond μ ρS (locFam S fun v => A.1 v.1) (fun v => hρS.comp' (continuous_locFam S _ v)) LS) ↔
      infH e hee x ∈ C := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [infH_mk]
    exact hmem z
  let T := Equiv.ofBijective (fun x : Sel (twDual μ ρS) (locFam S fun v => A.1 v.1)
      (continuous_locFam S _) (perpCond μ ρS (locFam S fun v => A.1 v.1)
        (fun v => hρS.comp' (continuous_locFam S _ v)) LS) =>
      (⟨infH e hee x.1, (hmem' _).1 x.2⟩ : C)) ⟨fun x y h => ?_, fun y => ?_⟩
  · have hs : Function.Surjective (toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) :=
      QuotientGroup.mk'_surjective _
    refine ⟨Finite.of_equiv _ T, ?_⟩
    rw [Nat.card_congr E1, ← Nat.card_congr T, ← card_H0_eq_of_equivariant_equiv ρ' _ _ hs e hee,
      ← card_H0_eq_of_equivariant_equiv ρ ρS _ hs (AddEquiv.refl W) hd, ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort S]
    simp only [← hLS1]
    rw [← hmain]
    congr 2
    refine Finset.prod_congr rfl fun v _ => ?_
    exact (card_H0_eq_of_equivariant_equiv (ρ.comp (Dec (F := F) (A.1 v.1)).subtype)
      (ρS.comp (locFam S (fun v => A.1 v.1) v)) id Function.surjective_id (AddEquiv.refl W)
      (fun g x => hd g x)).symm
  · exact Subtype.ext (infH_injective e hee (congrArg Subtype.val h))
  · obtain ⟨y, hy⟩ := y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z', rfl⟩ := exists_infZ e hee z (vanish_NS e hee A z ((hC z).1 hy).1)
    exact ⟨⟨Submodule.Quotient.mk z', (hmem' _).2 (by rw [infH_mk]; exact hy)⟩,
      Subtype.ext (infH_mk e hee z')⟩

end GlobalTheory.PairFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealSpanPrimeVariableBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_residue_basis_of_isMaximal {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : m.IsMaximal] (h : m.map f ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : A, ∃ a : ι →₀ R, x - a.sum (fun i y => f y * b i) ∈ m.map f) ∧
      ∀ a : ι →₀ R, a.sum (fun i y => f y * b i) ∈ m.map f → ∀ i, a i ∈ m := by
  first
  | exact @_root_.GlobalTheory.ClosedStatement.main
  | exact _root_.GlobalTheory.ClosedStatement.main
  | (apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosedStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosedStatement.main ..)

theorem isMaximal_span_l_sup_span_X (l a : ℕ) [Fact l.Prime] [NeZero a] :
    (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)}).IsMaximal := by
  have hmax : (Ideal.span {(l : Wq l a)}).IsMaximal := by
    rw [← (WittVector.irreducible l (k := Fq l a)).maximalIdeal_eq]
    infer_instance
  have hsurj : Function.Surjective (constantCoeff (R := Wq l a)) := fun w => ⟨C w, by simp⟩
  have heq : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)} =
      (Ideal.span {(l : Wq l a)}).comap (constantCoeff (R := Wq l a)) := by
    apply le_antisymm
    · refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      · rw [map_natCast]
        exact Ideal.mem_span_singleton_self _
      · simp
    · intro x hx
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hx)
      have hX : (X : (Wq l a)⟦X⟧) ∣ x - C w * l := by
        rw [X_dvd_iff, map_sub, map_mul, map_natCast, constantCoeff_C, hw, sub_self]
      have : x = C w * l + (x - C w * l) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mem_span_singleton.2 hX)
  rw [heq]
  exact Ideal.comap_isMaximal_of_surjective _ hsurj

theorem BK.map_span_l_sup_span_X_ne_top {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev ≠ ⊤ := by
  let M : Ideal (Ainf l) := (IsLocalRing.maximalIdeal (OC l)).comap (Per.θ l)
  haveI hM : M.IsPrime := Ideal.comap_isPrime _ _
  let N : Ideal bk.S := M.comap bk.ev
  haveI hN : N.IsPrime := Ideal.comap_isPrime _ _
  have hl : (l : bk.S) ∈ N := by
    change Per.θ l (bk.ev l) ∈ IsLocalRing.maximalIdeal (OC l)
    rw [map_natCast, map_natCast]
    exact (Fact.out : ¬ IsUnit (l : OC l))
  have hE : bk.E ∈ N := by
    change Per.θ l (bk.ev bk.E) ∈ IsLocalRing.maximalIdeal (OC l)
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker.1 this]
    exact Ideal.zero_mem _
  have hX : (X : bk.S) ∈ N := by
    apply hN.mem_of_pow_mem bk.Ep.natDegree
    have h1 := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
    rw [map_add, map_pow, map_sum] at h1
    have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)
        (Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i) ∈ N := by
      refine Ideal.sum_mem _ fun i hi => ?_
      obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
      rw [hw, map_mul, map_mul, map_mul, map_natCast, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hl)
    have h2 := N.sub_mem hE hs
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X] at h1 h2
    have h3 := sub_eq_of_eq_add h1
    rwa [h3] at h2
  intro htop
  apply hM.ne_top
  rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hl) ((Ideal.span_singleton_le_iff_mem _).2 hX)

theorem BK.exists_residue_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ (ι : Type) (b : ι → Ainf l) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : Ainf l, ∃ a : ι →₀ bk.S, x - a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) ∧
      ∀ a : ι →₀ bk.S, a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev →
        ∀ i, a i ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  intro l _ K bk
  haveI := isMaximal_span_l_sup_span_X l bk.a
  exact exists_residue_basis_of_isMaximal bk.ev _ bk.map_span_l_sup_span_X_ne_top

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegerCoboundaryAdditiveModPrimePowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integer_coboundary_additive_mod_prime_pow : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A : Subgroup (L ≃ₐ[K] L)) (x : L) (a : (L ≃ₐ[K] L) → ℤ), p.Prime → 0 < E → OrdIs L p E → (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → ∀ σ ∈ A, ∀ τ ∈ A, (p : ℤ) ^ r ∣ a (σ * τ) - a σ - a τ := by
  first | exact @GlobalTheory.PMon.Ram.coboundary_int_additive_mod | exact GlobalTheory.PMon.Ram.coboundary_int_additive_mod | (intros; apply GlobalTheory.PMon.Ram.coboundary_int_additive_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBdRPlusUnitMatrixRestrictionLatticeMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBdRPlusUnitMatrix_restrictionLatticeMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR), (∀ m, UnitM P (U m)) → UnitM P (U0 P ω hdet U) := by
  first | exact @GlobalTheory.PMon.ResR.unitM_U0_of_unitM | exact GlobalTheory.PMon.ResR.unitM_U0_of_unitM | (intros; apply GlobalTheory.PMon.ResR.unitM_U0_of_unitM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDomainClosedDiscGaugeCompletionOfEquivNormStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_closedDiscGaugeCompletion_of_equiv_norm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), ∀ (N : A → ℝ) (c : ℝ), 0 < c → (∀ x y, N (x * y) = N x * N y) → (∀ x y, N (x + y) ≤ max (N x) (N y)) → N (l : A) = (l : ℝ)⁻¹ → (∀ x, N x ≤ ‖toDisc l u ρ x‖) → (∀ x, c * ‖toDisc l u ρ x‖ ≤ N x) → IsDomain (Disc l u ρ) ∧ ∀ x y : Disc l u ρ, c ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖ := by
  first | exact @GlobalTheory.BSP.DiscDomain.isDomain_disc | exact GlobalTheory.BSP.DiscDomain.isDomain_disc | (intros; apply GlobalTheory.BSP.DiscDomain.isDomain_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlaceStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jump_range_positive_sign_place : StepJumpDirect := by
  first | exact @GlobalTheory.Pass.stepJumpDirect_holds | exact GlobalTheory.Pass.stepJumpDirect_holds | (intros; apply GlobalTheory.Pass.stepJumpDirect_holds <;> assumption)
end

