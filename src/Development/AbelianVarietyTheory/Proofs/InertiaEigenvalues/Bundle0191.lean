import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0181
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleVanishingOnFixingSubgroupDeterminedByGene
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0066
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsIrrDistinctMapSurjectiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrDistinct_map_surjective : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L), Function.Surjective f → ∀ {a : ℕ} (M : Γ →* Matrix (Fin a) (Fin a) k), AbsIrrDistinct (matRep M) → AbsIrrDistinct (matRep (mapM f M)) := by
  first | exact @GlobalTheory.absIrrDistinct_matRep_mapM_of_surjective | exact GlobalTheory.absIrrDistinct_matRep_mapM_of_surjective | (intros; apply GlobalTheory.absIrrDistinct_matRep_mapM_of_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

open Filter Topology

namespace GlobalTheory.GaussSlope

theorem eventually_iSup_eq_monomial (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≥] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push Not at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  obtain ⟨σ, hσ, hσ1⟩ := exists_between hρ1
  have hσ0 : 0 < σ := hρ.trans hσ
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hρ j)) hσ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, n)) ⟨j, Finset.mem_insert_self _ _⟩
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≥] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : ρ ≤ r := hr
      simp only at h h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_div hρ).2 hr) h')
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  have hlt : ∀ᶠ r in 𝓝[≥] ρ, r < σ := (gt_mem_nhds hσ).filter_mono nhdsWithin_le_nhds
  filter_upwards [(eventually_all_finset _).2 key, hlt, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : ρ ≤ r := hr
  have hr0 : 0 ≤ r := hρ.le.trans hr
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * σ ^ n := by gcongr; exact h1 n
        _ ≤ σ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hσ0.le hσ1.le (not_lt.1 hn)
        _ ≤ c j * ρ ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem add_eq_of_lt {R : Type} [CommRing R] (N : R → ℝ) (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hneg : ∀ x, N (-x) = N x) {x y : R} (h : N y < N x) : N (x + y) = N x := by
  refine le_antisymm ((hadd x y).trans (max_le le_rfl h.le)) ?_
  have := hadd (x + y) (-y)
  rw [add_neg_cancel_right, hneg] at this
  rcases le_max_iff.1 this with h' | h'
  · exact h'
  · exact absurd h' (not_le.2 h)

theorem map_pow_mul {R : Type} [CommRing R] (N : R → ℝ) (hmul : ∀ x y, N (x * y) = N x * N y)
    (p x : R) (k : ℕ) : N (p ^ k * x) = N p ^ k * N x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, hmul, ih]; ring

theorem slope_abstract {R : Type} [CommRing R] (p : R) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (N : ℝ → R → ℝ)
    (hN : ∀ r, ρ ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, ρ ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n) :
    ∃ (r₁ c : ℝ) (k : ℤ), ρ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, ρ < r → r < r₁ → N r b = c * r ^ k := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, ρ ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hρ.le.trans hr) _) (e1 z)
  have hbb : ∀ r, ρ ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := hN ρ le_rfl hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ le_rfl hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ le_rfl hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ le_rfl hρ1] at ha
  obtain ⟨i, hi⟩ := eventually_iSup_eq_monomial c h0 h1 hρ hρ1 ((pow_pos hρ _).trans ha).ne'
  rw [hi.self_of_nhdsWithin Set.self_mem_Ici] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  have h5 : ∀ᶠ r in 𝓝[≥] ρ, r < 1 → N r b = c i * r ^ ((i : ℤ) - k) := by
    filter_upwards [hi, h4.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr1 hr2 hr hr3
    have hr : ρ ≤ r := hr
    have hr0 : 0 < r := hρ.trans_le hr
    obtain ⟨e1, e2, e3, e4, e5⟩ := hN r hr hr3
    have h6 := hbb r hr hr3
    have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
    rw [hab, add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
    rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
    field_simp
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h5
  obtain ⟨σ, hσ, hσ1⟩ := exists_between hρ1
  refine ⟨min u σ, c i, (i : ℤ) - k, lt_min hu hσ, (min_le_right _ _).trans_lt hσ1, hci, fun r hr hr' => ?_⟩
  exact hsub ⟨hr.le, hr'.trans_le (min_le_left _ _)⟩ ((hr'.trans_le (min_le_right _ _)).trans hσ1)

variable (l : ℕ) [Fact l.Prime]

theorem untilt_zero : (0 : Per.Fl l).untilt = 0 :=
  Perfection.teichmuller_zero

theorem exists_pow_mul_eq (s : Per.Acris0 l) : ∃ (k : ℕ) (a : Per.Ainf l),
    (l : Per.Acris l) ^ k * algebraMap (Per.Acris0 l) (Per.Acris l) s = algebraMap (Per.Ainf l) (Per.Acris l) a := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (l : Per.Ainf l) (s : Per.AinfP l)
  refine ⟨k, a, ?_⟩
  have h1 : (l : Per.Acris0 l) ^ k * s = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    rw [map_natCast, mul_comm] at h
    simpa using h
  have h2 : algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
    GlobalTheory.RingIface.tower (l := l) a
  rw [h2, ← h1, map_mul, map_pow, map_natCast]

theorem gauss_l {r : ℝ} (hr : 0 ≤ r) :
    (⨆ n : ℕ, ‖((((l : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) = r := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((l : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n
      = if n = 1 then r else 0 := by
    intro n
    rw [WittVector.coeff_p]
    split_ifs with h
    · subst h
      simp
    · rw [untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 1 then r else 0) ≤ r := fun n => by split_ifs <;> simp [hr]
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 1 then r else 0) ⟨_, Set.forall_mem_range.2 hall⟩ 1 (by simp))

end GlobalTheory.GaussSlope

namespace GlobalTheory.MemLoc
open GlobalTheory.GaussSlope

theorem gauss_slope : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, N (l : ℝ)⁻¹ b ≠ 0 → ∃ (r₁ c : ℝ) (k : ℤ), (l : ℝ)⁻¹ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, (l : ℝ)⁻¹ < r → r < r₁ → N r b = c * r ^ k := by
  intro l _ N hN b hb
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine slope_abstract (l : Per.Acris l) hρ hρ1 N (fun r hr hr1 => ?_) b
    (lt_of_le_of_ne ((hN _ le_rfl hρ1).1 b).1 hb.symm) fun n => ?_
  · obtain ⟨e1, e2, e3, e4, e5⟩ := hN r hr hr1
    refine ⟨fun x => (e1 x).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, e5, gauss_l l (hρ.le.trans hr)]
  · obtain ⟨s, z, h⟩ := (acris_basic l).2.2.1 b n
    obtain ⟨k, a, ha⟩ := exists_pow_mul_eq l s
    refine ⟨k, _, z, fun n => ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (hN r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicallyCompleteLatticeReductionAction
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.CocycleLift

variable {O G T M : Type} [CommRing O] [Group G] [TopologicalSpace G] [ContinuousMul G]
  [AddCommGroup T] [Module O T] [AddCommGroup M] [Module O M]

theorem pow_smul_eq_zero (lam : O) (htf : ∀ t : T, lam • t = 0 → t = 0) (n : ℕ) (t : T)
    (h : lam ^ n • t = 0) : t = 0 := by
  induction n generalizing t with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    exact htf _ (ih _ h)

theorem smodeq_iff (lam : O) (n : ℕ) (x y : T) :
    x ≡ y [SMOD ((Ideal.span {lam}) ^ n • ⊤ : Submodule O T)] ↔ ∃ t, x - y = lam ^ n • t := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, hb⟩; exact ⟨b, hb.symm⟩
  · rintro ⟨b, hb⟩; exact ⟨b, trivial, hb.symm⟩

theorem step (lam : O) (π : Representation O G T) (π' : Representation O G M) (q : T →ₗ[O] M)
    (htf : ∀ t : T, lam • t = 0 → t = 0) (hq : Function.Surjective q)
    (hker : ∀ t, q t = 0 ↔ ∃ y, t = lam • y) (heq : ∀ g t, q (π g t) = π' g (q t))
    (hcont : ∀ (a : ℕ) (t : T) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, π g t - π g₀ t = lam ^ a • y)
    (hH : Subsingleton (ReciprocityTheory.Def.H2 π' ⊤)) (a : ℕ) (c : G → T) (hc : IsLocallyConstant c)
    (hd : ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c x = lam ^ (a + 1) • y) :
    ∃ c' : G → T, (IsLocallyConstant c' ∧ ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c' x = lam ^ (a + 1 + 1) • y) ∧
      ∀ g, ∃ y, c' g - c g = lam ^ (a + 1) • y := by
  choose w hw using hd
  have hw' : ∀ g h, π g (c h) - c (g * h) + c g = lam ^ (a + 1) • w (g, h) := fun g h => hw (g, h)
  have hlc : IsLocallyConstant (fun x => q (w x)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨g₀, h₀⟩
    have e1 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c x.1 = c g₀ :=
      (hc.comp_continuous continuous_fst).eventually_eq (g₀, h₀)
    have e2 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c x.2 = c h₀ :=
      (hc.comp_continuous continuous_snd).eventually_eq (g₀, h₀)
    have e3 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀), c (x.1 * x.2) = c (g₀ * h₀) :=
      (hc.comp_continuous continuous_mul).eventually_eq (g₀, h₀)
    have e4 : ∀ᶠ x : G × G in 𝓝 (g₀, h₀),
        ∃ y, π x.1 (c h₀) - π g₀ (c h₀) = lam ^ (a + 1 + 1) • y :=
      (continuous_fst.tendsto (g₀, h₀)).eventually (hcont (a + 1 + 1) (c h₀) g₀)
    filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 ⟨y, h4⟩
    obtain ⟨g, h⟩ := x
    simp only at h1 h2 h3 h4
    rw [← sub_eq_zero, ← map_sub, hker]
    refine ⟨y, ?_⟩
    rw [← sub_eq_zero]
    apply pow_smul_eq_zero lam htf (a + 1)
    rw [smul_sub, smul_sub, ← hw', ← hw', h1, h2, h3, ← mul_smul, ← pow_succ, ← h4]
    abel
  have hcoc : ∀ g h l, π g (w (h, l)) - w (g * h, l) + w (g, h * l) - w (g, h) = 0 := by
    intro g h l
    apply pow_smul_eq_zero lam htf (a + 1)
    rw [smul_sub, smul_add, smul_sub, ← map_smul, ← hw', ← hw', ← hw', ← hw']
    simp only [map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
    abel
  have hZ : (fun x => q (w x)) ∈ ReciprocityTheory.Def.Z2 π' ⊤ := by
    refine ⟨⟨hlc, fun _ => trivial⟩, ?_⟩
    show ReciprocityTheory.Def.d2 π' _ = 0
    funext ⟨g, h, l⟩
    have := congrArg q (hcoc g h l)
    simp only [map_add, map_sub, heq, map_zero] at this
    exact this
  have h0 : (Submodule.Quotient.mk ⟨_, hZ⟩ : ReciprocityTheory.Def.H2 π' ⊤) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨b, ⟨hb, -⟩, hbd⟩ := h0
  have hbd' : ∀ g h, π' g (b h) - b (g * h) + b g = q (w (g, h)) := fun g h => congrFun hbd (g, h)
  choose s hs using hq
  refine ⟨fun g => c g - lam ^ (a + 1) • s (b g), ⟨?_, ?_⟩, fun g => ⟨- s (b g), by simp⟩⟩
  · exact hc.sub (hb.comp (fun m => lam ^ (a + 1) • s m))
  · rintro ⟨g, h⟩
    obtain ⟨y, hy⟩ := (hker (w (g, h) - (π g (s (b h)) - s (b (g * h)) + s (b g)))).1 (by
      simp only [map_add, map_sub, heq, hs, hbd', sub_self])
    refine ⟨y, ?_⟩
    show π g (c h - lam ^ (a + 1) • s (b h)) - (c (g * h) - lam ^ (a + 1) • s (b (g * h)))
      + (c g - lam ^ (a + 1) • s (b g)) = _
    rw [pow_succ lam (a + 1), mul_smul, ← hy, smul_sub, ← hw', map_sub, map_smul, smul_add, smul_sub]
    abel

theorem exists_lift : ∀ (O G T M : Type) [CommRing O] [Group G] [TopologicalSpace G] [ContinuousMul G] [AddCommGroup T] [Module O T] [AddCommGroup M] [Module O M] (lam : O) (π : Representation O G T) (π' : Representation O G M) (q : T →ₗ[O] M), IsAdicComplete (Ideal.span {lam}) T → (∀ t : T, lam • t = 0 → t = 0) → Function.Surjective q → (∀ t, q t = 0 ↔ ∃ y, t = lam • y) → (∀ g t, q (π g t) = π' g (q t)) → (∀ (a : ℕ) (t : T) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, π g t - π g₀ t = lam ^ a • y) → Subsingleton (ReciprocityTheory.Def.H2 π' ⊤) → ∀ z ∈ ReciprocityTheory.Def.Z1 π' ⊤, ∃ c : G → T, (∀ g h, c (g * h) = c g + π g (c h)) ∧ (∀ g, q (c g) = z g) ∧ ∀ (a : ℕ) (g₀ : G), ∀ᶠ g in 𝓝 g₀, ∃ y, c g - c g₀ = lam ^ a • y := by
  intro O G T M _ _ _ _ _ _ _ _ lam π π' q hcomp htf hq hker heq hcont hH z hz
  have hst := step lam π π' q htf hq hker heq hcont hH
  obtain ⟨⟨hz1, -⟩, hz2⟩ := hz
  have hz3 : ∀ g h, π' g (z h) - z (g * h) + z g = 0 := fun g h => congrFun hz2 (g, h)
  choose s hs using hq
  let P : ℕ → (G → T) → Prop := fun a c =>
    IsLocallyConstant c ∧ ∀ x, ∃ y, ReciprocityTheory.Def.d1 π c x = lam ^ (a + 1) • y
  have P0 : P 0 (fun g => s (z g)) := by
    refine ⟨hz1.comp s, ?_⟩
    rintro ⟨g, h⟩
    rw [zero_add, pow_one, ← hker]
    show q (π g (s (z h)) - s (z (g * h)) + s (z g)) = 0
    simp only [map_add, map_sub, heq, hs, hz3]
  have hst' : ∀ a (c : {c // P a c}), ∃ c' : {c // P (a + 1) c},
      ∀ g, ∃ y, c'.1 g - c.1 g = lam ^ (a + 1) • y := by
    intro a c
    obtain ⟨c', h1, h2⟩ := hst a c.1 c.2.1 c.2.2
    exact ⟨⟨c', h1⟩, h2⟩
  choose F hF using hst'
  let u : ∀ a, {c // P a c} := fun a => Nat.rec ⟨_, P0⟩ F a
  have hu : ∀ a g, ∃ y, (u (a + 1)).1 g - (u a).1 g = lam ^ (a + 1) • y := fun a => hF a (u a)
  have hcau : ∀ g m n, m ≤ n → ∃ y, (u n).1 g - (u m).1 g = lam ^ (m + 1) • y := by
    intro g m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ n hmn ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨y', hy'⟩ := hu n g
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      refine ⟨y + lam ^ k • y', ?_⟩
      rw [smul_add, ← mul_smul, ← pow_add, show m + 1 + k = m + k + 1 by ring, ← hy, ← hy']
      abel
  have hlim : ∀ g, ∃ L, ∀ n, ∃ y, (u n).1 g - L = lam ^ n • y := by
    intro g
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hcomp.toIsPrecomplete (f := fun n => (u n).1 g) (by
      intro m n hmn
      apply SModEq.symm
      rw [smodeq_iff]
      obtain ⟨y, hy⟩ := hcau g m n hmn
      exact ⟨lam • y, by rw [hy, pow_succ, mul_smul]⟩)
    exact ⟨L, fun n => (smodeq_iff lam n _ _).1 (hL n)⟩
  choose c hc using hlim
  refine ⟨c, fun g h => ?_, fun g => ?_, fun a g₀ => ?_⟩
  · rw [← sub_eq_zero]
    apply IsHausdorff.haus hcomp.toIsHausdorff
    intro n
    rw [smodeq_iff]
    obtain ⟨y1, h1⟩ := hc g n
    obtain ⟨y2, h2⟩ := hc h n
    obtain ⟨y3, h3⟩ := hc (g * h) n
    obtain ⟨y4, h4⟩ := (u n).2.2 (g, h)
    have h4' : π g ((u n).1 h) - (u n).1 (g * h) + (u n).1 g = lam ^ n • lam • y4 := by
      rw [← mul_smul, ← pow_succ]; exact h4
    refine ⟨y1 + π g y2 - y3 - lam • y4, ?_⟩
    rw [smul_sub, smul_sub, smul_add, ← map_smul, ← h1, ← h2, ← h3, ← h4', map_sub]
    abel
  · obtain ⟨y1, h1⟩ := hc g 1
    obtain ⟨y2, h2⟩ := hcau g 0 1 (by norm_num)
    have h0 : q ((u 0).1 g) = z g := hs _
    rw [← h0, ← sub_eq_zero, ← map_sub, hker]
    refine ⟨y2 - y1, ?_⟩
    rw [zero_add, pow_one] at h2
    rw [pow_one] at h1
    rw [smul_sub, ← h1, ← h2]
    abel
  · filter_upwards [(u a).2.1.eventually_eq g₀] with g hg
    obtain ⟨y1, h1⟩ := hc g a
    obtain ⟨y2, h2⟩ := hc g₀ a
    refine ⟨y2 - y1, ?_⟩
    rw [smul_sub, ← h1, ← h2, hg]
    abel

end GlobalTheory.CocycleLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentFiniteFreeInvertPrimeStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinDescent_finite_free_invertPrime : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D ∧ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Localisation D := by
  first | exact @GlobalTheory.ZFin.finiteFree_and_localisation | exact GlobalTheory.ZFin.finiteFree_and_localisation | (intros; apply GlobalTheory.ZFin.finiteFree_and_localisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingEqIntegralAddEisensteinFiltrationStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilRing_eq_integral_add_eisensteinFiltration : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), j < l → ∀ f ∈ S O K e, ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := by
  first | exact @GlobalTheory.BK.SDec.S_eq_A_add_Fil | exact GlobalTheory.BK.SDec.S_eq_A_add_Fil | (intros; apply GlobalTheory.BK.SDec.S_eq_A_add_Fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingModHighDegreePropertyStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilRing_mod_high_degree_property : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a], GlobalTheory.IndefiniteRowSideFullHecke.ImageStableDegreeBounds.RingModHigh O K l e := by
  first | exact @GlobalTheory.BK.ringModHigh | exact GlobalTheory.BK.ringModHigh | (intros; apply GlobalTheory.BK.ringModHigh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleVanishingOnFixingSubgroupDeterminedByGeneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_vanishing_on_fixingSubgroup_determined_by_generator : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ i : ℤ, (∀ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) Set.univ c → (∀ h ∈ Hinf K, c h = 0) → c g = 0 → ∀ σ ∈ Gj K m, c σ = 0) ∧ ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Ohat K) → ∃ c : GQ l → Fin r → PadicComplex l, CocOn (Gj K m) (twAct act χ i U) {y | ∀ a, y a ∈ Ohat K} c ∧ (∀ h ∈ Hinf K, c h = 0) ∧ c g = w := by
  first | exact @GlobalTheory.Cyc.Procyclic.procyclic | exact GlobalTheory.Cyc.Procyclic.procyclic | (intros; apply GlobalTheory.Cyc.Procyclic.procyclic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealFrobeniusLeMapExpandStatement
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_frobenius_le_map_expand : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧), colon O K (G.map (frob K l)) ≤ (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) := by
  first | exact @GlobalTheory.LiftCoker.colon_map_frob_le | exact GlobalTheory.LiftCoker.colon_map_frob_le | (intros; apply GlobalTheory.LiftCoker.colon_map_frob_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColonIdealMapExpandLeFrobeniusStatement
section
open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colonIdeal_map_expand_le_frobenius : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] (ι κ : Type) [Fintype ι] [Fintype κ] (G : Matrix κ ι K⟦X⟧), (colon O K G).map (PowerSeries.expand l (Fact.out : l.Prime).ne_zero) ≤ colon O K (G.map (frob K l)) := by
  first | exact @GlobalTheory.LiftCoker.colon_map_expand_le | exact GlobalTheory.LiftCoker.colon_map_expand_le | (intros; apply GlobalTheory.LiftCoker.colon_map_expand_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
section
open Matrix

namespace GlobalTheory.UnitDiscAlg

section Basic
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem integ_mul {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x * y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun k _ => by rw [norm_mul]; exact mul_le_one₀ (hx i k) (norm_nonneg _) (hy k j))

theorem integ_add {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x + y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (hy i j))

theorem integ_sub {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x - y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (by rw [norm_neg]; exact hy i j))

theorem integ_one : ∀ i j, ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem integ_zero : ∀ i j, ‖(0 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  simp

theorem integ_pow {x : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (k : ℕ) :
    ∀ i j, ‖(x ^ k) i j‖ ≤ 1 := by
  induction k with
  | zero => simpa using integ_one
  | succ k ih => rw [pow_succ]; exact integ_mul ih hx

theorem integ_smul {x : Matrix (Fin n) (Fin n) E} {a : E} (ha : ‖a‖ ≤ 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ∀ i j, ‖(a • x) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i j)

end Basic

theorem comm_of_bezout {E : Type} [Field E] {n : ℕ} {N a b : Matrix (Fin n) (Fin n) E}
    (h : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (ha : a * N = N * a) (hb : b * N = N * b) : a * b = b * a := by
  obtain ⟨u, v, huv⟩ := h
  have hs : N.charpoly.Separable := ⟨u, v, huv⟩
  obtain ⟨w, hw⟩ := GlobalTheory.RegSS.cyclicField E (Fin n) N hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N w hw).2.2
  have ha' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij ha
  have hb' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij hb
  exact congrArg Subtype.val
    (mul_comm (⟨a, ha'⟩ : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg N) ⟨b, hb'⟩)

end GlobalTheory.UnitDiscAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientTorsionBoundedStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_quotient_torsion_bounded : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  first | exact @GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact | exact GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact | (intros; apply GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterCongrRootOfUnityPowStatement
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCharacter_congr_root_of_unity_pow : ∀ {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (g : Formalism.GaloisCohomology.GK p K) (k : ℕ), ∃ ζ : PadicAlgCl p, ζ ^ (p ^ k) = 1 ∧ ∀ a : ℕ, g ζ = ζ ^ a → (a : ZMod (p ^ k)) = PadicInt.toZModPow k ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK p K) (PadicAlgCl p) g) : ℤ_[p]ˣ) : ℤ_[p]) := by
  first | exact @GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | exact GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr | (intros; apply GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr <;> assumption)
end

