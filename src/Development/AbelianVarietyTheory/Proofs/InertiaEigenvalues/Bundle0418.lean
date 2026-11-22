import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnPrimePowerRootSystems
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isClosed_setOf_gal_apply_eq_padic (l : ℕ) [Fact l.Prime] (a b : Om l) :
    IsClosed {g : GQ l | g a = b} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (MulAction.stabilizer (GQ l) a : Set (GQ l)), ?_,
    (stabilizer_isOpen_of_isIntegral a).preimage (continuous_const.mul continuous_id), ?_⟩
  · intro h hh
    have hs : (g⁻¹ * h) a = a := hh
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hg ⊢
    intro hb
    apply hg
    rw [AlgEquiv.mul_apply] at hs
    have hga := congrArg g hs
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at hga
    rw [← hga, hb]
  · show (g⁻¹ * g) a = a
    rw [inv_mul_cancel, AlgEquiv.one_apply]

theorem galois_transitive_on_root_systems_of_prime : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Prime π → ∀ y z : ℕ → Om l, y 0 = ((π : ↥K.1) : Om l) → z 0 = ((π : ↥K.1) : Om l) → (∀ n, y (n + 1) ^ l = y n) → (∀ n, z (n + 1) ^ l = z n) → ∃ g : ↥(GK K), ∀ n, (g : GQ l) (y n) = z n := by
  intro l _ K π hπ y z hy hz hy' hz'
  have hGK : IsClosed ((GK K : Subgroup (GQ l)) : Set (GQ l)) := by
    unfold GK
    exact InfiniteGalois.fixingSubgroup_isClosed _

  have hpow : ∀ w : ℕ → Om l, (∀ n, w (n + 1) ^ l = w n) → ∀ m k, w (m + k) ^ (l ^ k) = w m := by
    intro w hw m k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_mul', ← add_assoc, hw, ih]

  let T : ℕ → Set (GQ l) := fun n =>
    (GK K : Set (GQ l)) ∩ ⋂ m, ⋂ (_ : m ≤ n), {g : GQ l | g (y m) = z m}
  have hcl : ∀ n, IsClosed (T n) := fun n =>
    hGK.inter (isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_setOf_gal_apply_eq_padic l (y m) (z m))
  have hdec : ∀ n, T (n + 1) ⊆ T n := by
    rintro n g ⟨h1, h2⟩
    refine ⟨h1, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    exact Set.mem_iInter.1 (Set.mem_iInter.1 h2 m) (Nat.le_succ_of_le hm)
  have hne : ∀ n, (T n).Nonempty := by
    intro n
    have hyn : y n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow y hy' 0 n
      rw [zero_add] at h
      rw [h, hy]
    have hzn : z n ^ (l ^ n) = ((π : ↥K.1) : Om l) := by
      have h := hpow z hz' 0 n
      rw [zero_add] at h
      rw [h, hz]
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_apply_eq_of_pow_eq_prime l K π hπ (l ^ n) (y n) (z n) hyn hzn
      (pow_pos (Fact.out : l.Prime).pos n)
    refine ⟨(g : GQ l), g.2, Set.mem_iInter.2 fun m => Set.mem_iInter.2 fun hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    show (g : GQ l) (y m) = z m
    rw [← hpow y hy' m k, ← hpow z hz' m k, map_pow, hg]

  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T hdec hne
    (hcl 0).isCompact hcl
  refine ⟨⟨g, (Set.mem_iInter.1 hg 0).1⟩, fun n => ?_⟩
  exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hg n).2 n) le_rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumUnfoldingOfComplexInvariantIntegrable
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.UnfoldCplx

variable {α ι : Type} [MeasurableSpace α] [Countable ι]

theorem integrable_comp {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {B : α → ℂ} (hB : Measurable B) (hBi : Integrable B (μ.restrict 𝓕))
    (hH : ∀ h ∈ H, ∀ x, B (h x) = B x) (i : ι) :
    Integrable (fun x => B (T i x)) (μ.restrict A) := by
  refine ⟨(hB.comp (hT i)).aestronglyMeasurable, ?_⟩
  have h1 := hU (fun x => ‖B x‖ₑ) hB.enorm (fun h hh x => by simp [hH h hh x])
  have hfin : ∫⁻ x in 𝓕, ‖B x‖ₑ ∂μ < ∞ := hBi.2
  have hle : ENNReal.ofReal (c i) * ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ ≤ ∫⁻ x in 𝓕, ‖B x‖ₑ ∂μ := by
    rw [h1]; exact ENNReal.le_tsum (f := fun i => ENNReal.ofReal (c i) * ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ) i
  have hne : ENNReal.ofReal (c i) ≠ 0 := by simpa using hc i
  show ∫⁻ x in A, ‖B (T i x)‖ₑ ∂μ < ∞
  by_contra hh
  rw [not_lt, top_le_iff] at hh
  rw [hh, ENNReal.mul_top hne] at hle
  exact absurd (lt_of_le_of_lt hle hfin) (lt_irrefl _)

theorem hasSum_nonneg {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {g : α → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g (μ.restrict 𝓕))
    (hH : ∀ h ∈ H, ∀ x, g (h x) = g x) :
    HasSum (fun i => c i * ∫ x in A, g (T i x) ∂μ) (∫ x in 𝓕, g x ∂μ) := by
  have h1 := hU (fun x => ENNReal.ofReal (g x)) hg.ennreal_ofReal (fun h hh x => by simp [hH h hh x])
  have hfin : ∫⁻ x in 𝓕, ENNReal.ofReal (g x) ∂μ ≠ ∞ := (hgi.lintegral_lt_top).ne
  set F : ι → ℝ≥0∞ := fun i => ENNReal.ofReal (c i) * ∫⁻ x in A, ENNReal.ofReal (g (T i x)) ∂μ with hF
  have hsum : ∑' i, F i ≠ ∞ := by rw [← h1]; exact hfin
  have hFi : ∀ i, F i ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hsum
  have key := ENNReal.hasSum_toReal hsum
  rw [← ENNReal.tsum_toReal_eq hFi, ← h1, ← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hg0) hg.aestronglyMeasurable] at key
  convert key using 1
  funext i
  simp only [hF, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hc i).le]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => hg0 _))
    (hg.comp (hT i)).aestronglyMeasurable]

theorem hasSum_real {μ : Measure α} {𝓕 A : Set α} {c : ι → ℝ} (hc : ∀ i, 0 < c i)
    {T : ι → α → α} (hT : ∀ i, Measurable (T i)) {H : Set (α → α)}
    (hU : ∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ)
    {g : α → ℝ} (hg : Measurable g) (hgi : Integrable g (μ.restrict 𝓕))
    (hgA : ∀ i, Integrable (fun x => g (T i x)) (μ.restrict A))
    (hH : ∀ h ∈ H, ∀ x, g (h x) = g x) :
    HasSum (fun i => c i * ∫ x in A, g (T i x) ∂μ) (∫ x in 𝓕, g x ∂μ) := by
  have hp := hasSum_nonneg hc hT hU (g := fun x => max (g x) 0) (hg.max measurable_const)
    (fun x => le_max_right _ _) hgi.pos_part (fun h hh x => by simp only [hH h hh x])
  have hn := hasSum_nonneg hc hT hU (g := fun x => max (-g x) 0) (hg.neg.max measurable_const)
    (fun x => le_max_right _ _) hgi.neg_part (fun h hh x => by simp only [hH h hh x])
  have hsplit : ∀ y : ℝ, max y 0 - max (-y) 0 = y := fun y => by
    rcases le_total y 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
  have e1 : ∫ x in 𝓕, g x ∂μ = (∫ x in 𝓕, max (g x) 0 ∂μ) - ∫ x in 𝓕, max (-g x) 0 ∂μ := by
    rw [← integral_sub hgi.pos_part hgi.neg_part]; simp only [hsplit]
  have hf : (fun i => c i * ∫ x in A, g (T i x) ∂μ) = fun i =>
      c i * (∫ x in A, max (g (T i x)) 0 ∂μ) - c i * ∫ x in A, max (-g (T i x)) 0 ∂μ := by
    funext i
    rw [← mul_sub, ← integral_sub (hgA i).pos_part (hgA i).neg_part]; simp only [hsplit]
  rw [e1, hf]
  exact hp.sub hn

theorem hasSum_complex : ∀ {α ι : Type} [MeasurableSpace α] [Countable ι] (μ : Measure α) (𝓕 A : Set α) (c : ι → ℝ), (∀ i, 0 < c i) →
    ∀ (T : ι → α → α), (∀ i, Measurable (T i)) → ∀ (H : Set (α → α)),
    (∀ f : α → ℝ≥0∞, Measurable f → (∀ h ∈ H, ∀ x, f (h x) = f x) →
      ∫⁻ x in 𝓕, f x ∂μ = ∑' i, ENNReal.ofReal (c i) * ∫⁻ x in A, f (T i x) ∂μ) →
    ∀ B : α → ℂ, Measurable B → Integrable B (μ.restrict 𝓕) → (∀ h ∈ H, ∀ x, B (h x) = B x) →
      (∀ i, Integrable (fun x => B (T i x)) (μ.restrict A)) ∧
        HasSum (fun i => (c i : ℂ) * ∫ x in A, B (T i x) ∂μ) (∫ x in 𝓕, B x ∂μ) := by
  intro α ι _ _ μ 𝓕 A c hc T hT H hU B hB hBi hH
  have hBA := integrable_comp hc hT hU hB hBi hH
  refine ⟨hBA, ?_⟩
  rw [Complex.hasSum_iff]
  constructor
  · have := hasSum_real hc hT hU (g := fun x => (B x).re) (Complex.measurable_re.comp hB) hBi.re
      (fun i => (hBA i).re) (fun h hh x => by simp only [hH h hh x])
    have e2 : ∫ x in 𝓕, (B x).re ∂μ = (∫ x in 𝓕, B x ∂μ).re := integral_re hBi
    have hf : (fun i => c i * ∫ x in A, (B (T i x)).re ∂μ) =
        fun i => ((c i : ℂ) * ∫ x in A, B (T i x) ∂μ).re := by
      funext i
      rw [Complex.re_ofReal_mul]; congr 1; exact integral_re (hBA i)
    rw [e2, hf] at this
    exact this
  · have := hasSum_real hc hT hU (g := fun x => (B x).im) (Complex.measurable_im.comp hB) hBi.im
      (fun i => (hBA i).im) (fun h hh x => by simp only [hH h hh x])
    have e2 : ∫ x in 𝓕, (B x).im ∂μ = (∫ x in 𝓕, B x ∂μ).im := integral_im hBi
    have hf : (fun i => c i * ∫ x in A, (B (T i x)).im ∂μ) =
        fun i => ((c i : ℂ) * ∫ x in A, B (T i x) ∂μ).im := by
      funext i
      rw [Complex.im_ofReal_mul]; congr 1; exact integral_im (hBA i)
    rw [e2, hf] at this
    exact this

end GlobalTheory.UnfoldCplx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Hilbert90MatrixCoboundaryCharPFiniteLevel
section
namespace GlobalTheory.UnramifiedHilbertNinety

open GlobalTheory.UnramifiedCrys

theorem exists_mem_multilinear_ne_zero {R V ι : Type} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (f : MultilinearMap R (fun _ : ι => V) R) (S : Set V)
    (hS : ∀ l : V →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0) (v₀ : ι → V) (h₀ : f v₀ ≠ 0) :
    ∃ v : ι → V, (∀ i, v i ∈ S) ∧ f v ≠ 0 := by
  have key : ∀ T : Finset ι, ∃ v : ι → V, (∀ i ∈ T, v i ∈ S) ∧ f v ≠ 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨v₀, by simp, h₀⟩
    | insert a T ha ih =>
      obtain ⟨v, hv, hf⟩ := ih
      obtain ⟨s, hs, hne⟩ : ∃ s ∈ S, f (Function.update v a s) ≠ 0 := by
        by_contra hc
        push Not at hc
        have h1 := hS (f.toLinearMap v a) hc
        have h2 := LinearMap.congr_fun h1 (v a)
        rw [MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h2
        exact hf h2
      refine ⟨Function.update v a s, fun i hi => ?_, hne⟩
      by_cases hia : i = a
      · subst hia
        rwa [Function.update_self]
      · rw [Function.update_of_ne hia]
        exact hv i ((Finset.mem_insert.1 hi).resolve_left hia)
  obtain ⟨v, hv, hf⟩ := key Finset.univ
  exact ⟨v, fun i => hv i (Finset.mem_univ i), hf⟩

theorem exists_matrix_coboundary (p : ℕ) [hp : Fact p.Prime] (G : Type) [Group G] (R : Type)
    [CommRing R] [IsDomain R] [CharP R p] (ρ : G →* (R ≃+* R)) (m : ℕ) (hm : 0 < m)
    (hfin : Finite (G ⧸ fixer ρ p m)) (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) R)
    (hρ : ∀ g h i j, ρ g (M h i j) = M h i j) (hM : ∀ h i j, M h i j ^ p ^ m = M h i j)
    (hMN : ∀ g ∈ fixer ρ p m, M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) R, IsUnit W.det ∧ (∀ i j, W i j ^ p ^ m = W i j) ∧
      ∀ g, M g * W.map (ρ g) = W := by
  classical
  set N := fixer ρ p m with hN
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  have hsum : ∀ (f : G → R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  let S : Set (Fin r → R) := {v | (∀ i, v i ^ p ^ m = v i) ∧
    ∀ g i, ∑ k, M g i k * ρ g (v k) = v i}
  have hb : ∀ (θ : fixedPow p R m) (j : Fin r),
      (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) ∈ S := by
    intro θ j
    have hθm : (θ : R) ^ p ^ m = θ := θ.2
    refine ⟨fun i => ?_, fun g i => ?_⟩
    · rw [sum_pow_char_pow]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_pow, ← map_pow, hθm, hM]
    · have h2 := hsum (fun g => ρ g θ * M g i j) (fun g n hn => by
        simp only [map_mul, RingAut.mul_apply, hn θ hθm, hMN n hn, mul_one]) g
      simp only [map_sum, Finset.mul_sum]
      rw [← h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [map_mul, RingAut.mul_apply, Matrix.mul_apply, hρ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
  have hS : ∀ l : (Fin r → R) →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0 := by
    intro l hl
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    have h1 := Fintype.linearIndependent_iff.1 hli (fun x => l (fun i => M x.out i j)) (by
      funext θ
      simp only [Finset.sum_apply, Function.comp, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      have h3 : (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) =
          ∑ x : G ⧸ N, ρ x.out θ • (fun i => M x.out i j) := by
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h4 := hl _ (hb θ j)
      rw [h3, map_sum] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl) (QuotientGroup.mk 1)
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (1 : G)
    simp only [hn, one_mul, hMN n n.2] at h1
    have h5 : (fun i => (1 : Matrix (Fin r) (Fin r) R) i j) = Pi.single j 1 := by
      funext i
      rw [Matrix.one_apply, Pi.single_apply]
    rw [h5] at h1
    simpa using h1
  obtain ⟨v, hv, hf⟩ := exists_mem_multilinear_ne_zero
    (Matrix.detRowAlternating (n := Fin r) (R := R)).toMultilinearMap S hS
    (1 : Matrix (Fin r) (Fin r) R) (by
      change (1 : Matrix (Fin r) (Fin r) R).det ≠ 0
      rw [Matrix.det_one]
      exact one_ne_zero)
  have hf' : ((Matrix.of v).transpose).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hf
  have hW : ∀ i j, (Matrix.of v).transpose i j ^ p ^ m = (Matrix.of v).transpose i j :=
    fun i j => (hv j).1 i
  refine ⟨(Matrix.of v).transpose, ?_, hW, fun g => ?_⟩
  · set t := ((Matrix.of v).transpose).det with ht
    have htq : t ^ p ^ m = t := by
      rw [← iterateFrobenius_def, ht, RingHom.map_det]
      congr 1
      ext i j
      exact hW i j
    have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
    have hu : t ^ (p ^ m - 2) * t = 1 := by
      apply mul_right_cancel₀ hf'
      rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
    exact IsUnit.of_mul_eq_one_right _ hu
  · ext i j
    exact (hv j).2 g i

end GlobalTheory.UnramifiedHilbertNinety
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkFrobOfAttached
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.HkFrobProof

theorem eval_charpolyRev_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b
  by_cases h : a = b <;> simp [h] <;> ring

theorem coeff_charpolyRev_map {n : ℕ} {R : Type} [CommRing R] (f : R →+* ℂ) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    f (M.charpolyRev.coeff k) = (M.map f).charpolyRev.coeff k := by
  rw [← Polynomial.coeff_map]
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_smul_inv {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (h : M * A = 1) (β : Multiset ℂ)
    (hβ : (0 : ℂ) ∉ β) (hA : A.charpoly = (β.map fun a => (X : ℂ[X]) - C a).prod) (c : ℂ) :
    (c • M).charpolyRev = (β.map fun a => (1 : ℂ[X]) - C (c * a⁻¹) * X).prod := by
  have ev : ∀ y : ℂ, (y • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = (β.map fun a => y - a).prod := by
    intro y
    have := congrArg (Polynomial.eval y) hA
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at this
    simpa using this
  apply Polynomial.funext
  intro z
  rw [eval_charpolyRev_eq, eval_multiset_prod, Multiset.map_map]
  have h0 := ev 0
  have h1 := ev (z * c)
  have hne : (β.map fun a => (0 : ℂ) - a).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hm
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 hm
    have : a = 0 := by simpa using ha0
    exact hβ (this ▸ ha)
  apply mul_right_cancel₀ hne
  rw [← Multiset.prod_map_mul]
  conv_lhs => rw [← h0, ← Matrix.det_mul]
  have e : (1 - z • c • M) * ((0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) = (z * c) • 1 - A := by
    rw [zero_smul, zero_sub, mul_neg, sub_mul, one_mul, smul_smul, Matrix.smul_mul, h, neg_sub]
  rw [e, h1]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := fun h => hβ (h ▸ ha)
  simp only [Function.comp, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)))

theorem hkFrob_of_tripleAtt : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → HkFrob i s := by
  rintro D bkP i s ⟨ι, π₁, π, -, hA, hR, hS⟩ P hP hsp σ hσ k hk
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)
  have hu : D.naut.unr (D.naut.locG π P) :=
    hR.unr P (fun k h => hP (D.ntw.placesOver_subset_exceptional i k h)) (fun h => hP (D.ntw.primes_subset_exceptional i h))
  have hpl : IsPlaceOver (F := D.host.E) (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  have hfr := hA.frob P hl hu _ _ hpl hσ
  rw [D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at hfr
  have he := (GlobalTheory.TripleGal.eps0_unram_frob D i P hl _ hpl).2 _ hσ
  obtain ⟨h, hh, hrd⟩ := hS P hP hsp k hk
  have hq0 : (normV P : ℕ) ≠ 0 := by
    intro h0
    rw [h0] at he
    exact Units.ne_zero _ (he.trans Nat.cast_zero)
  have hqC : ((normV P : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq0
  have hne := D.naut.frobEig_ne_zero _ hu
  set q : ℂ := ((normV P : ℕ) : ℂ) with hq
  set α := D.naut.frobEig (D.naut.locG π P) with hα
  have hcard : Multiset.card α = D.R.r := by
    have := congrArg natDegree hfr
    rw [Matrix.charpoly_natDegree_eq_dim, natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have heps : rd i ι ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = q⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [hq, ← map_natCast (rd i ι), ← he, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, map_one]
  have hMA : (Tmat i s σ).map (rd i ι) *
      ((Tgl i s σ⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)).map (rd i ι) = 1 := by
    rw [← Tgl_coe, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hne' : (0 : ℂ) ∉ α.map (· * q ^ (((1 - (D.R.t : ℝ)) / 2 : ℝ) : ℂ)) := by
    intro hm
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 hm
    rcases mul_eq_zero.1 ha0 with h0 | h0
    · exact hne (h0 ▸ ha)
    · exact hqC ((Complex.cpow_eq_zero_iff _ _).1 h0).1
  have key := charpolyRev_smul_inv _ _ hMA _ hne' hfr (q⁻¹ ^ D.R.t)
  have hes := GlobalTheory.normalised_esymm_eq_coeff D.R.r ((normV P : ℕ) : ℝ) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq0))
    (α.map fun a => a⁻¹ * q ^ (-((D.R.r : ℂ) + D.R.t) / 2)) (by rw [Multiset.card_map, hcard]) k hk
  rw [Complex.ofReal_natCast, ← hq, ← hrd] at hes
  have hmain : (-1 : D.ntw.O0 i) ^ k * ((normV P : ℕ) : D.ntw.O0 i) ^ (k * (k - 1) / 2) * h =
      (((((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s σ).charpolyRev).coeff k := by
    apply rd_injective i ι
    rw [coeff_charpolyRev_map, Matrix.map_smul' _ _ _ (map_mul _), map_pow (rd i ι) _ D.R.t, heps, key, map_mul,
      map_mul, map_pow, map_pow, map_neg, map_one, map_natCast, ← hq, hes, Multiset.map_map, Multiset.map_map]
    congr 2
    apply Multiset.map_congr rfl
    intro a _
    simp only [Function.comp]
    congr 3
    have e1 : q ^ (((D.R.r : ℂ) - 1) / 2) * q ^ (-((D.R.r : ℂ) + D.R.t) / 2) =
        q⁻¹ ^ D.R.t * (q ^ (((1 - (D.R.t : ℝ)) / 2 : ℝ) : ℂ))⁻¹ := by
      rw [← Complex.cpow_add _ _ hqC, ← Complex.cpow_neg, inv_pow, ← Complex.cpow_natCast, ← Complex.cpow_neg,
        ← Complex.cpow_add _ _ hqC]
      congr 1
      push_cast
      ring
    rw [mul_inv, mul_left_comm, e1]
    ring
  rw [← hmain, hh]
  simp

end GlobalTheory.TripleGal.HkFrobProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeAdaptedBasisGaloisActionBdRPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalAdapted

theorem gal_V : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → (ρ g).map ((aDp l).comp (Per.zA l)) * H.V.map (Per.σDp (g : GQ l)) * Matrix.diagonal (fun j => aDp l w ^ H.p j) = aDp l w ^ H.q • H.V := by
  intro l _ K bk C d ρ H g w hw
  have hinj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := (BdRField.bdR_isField l).2.1
  obtain ⟨u, hu, -⟩ := AdaptedHodge.xi_unit_fil C (bk.ev bk.E) bk.span_ev
  have hΞ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) := hu ▸ u.isUnit
  have hξ : Per.σD (g : GQ l) (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) := by
    rw [ActLaws.σD_alg, ActLaws.σDp_aDp, hw, map_mul, map_mul]
  have hmap : ∀ z : ℤ_[l], C.o (zOm l z) = aDp l (Per.zA l z) := fun z => C.o_sec.z z
  have hinv := H.inv g g.2
  ext i j
  apply hinj
  refine (hΞ.pow (H.p j)).mul_left_cancel ?_
  have hσ : ∀ k, (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w)) ^ H.q *
      Per.σD (g : GQ l) (H.Q k j) = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) * algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w)) ^ H.p j *
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp (g : GQ l) (H.V k j)) := by
    intro k
    have := congrArg (Per.σD (g : GQ l)) (H.Q_eq k j)
    rw [map_mul, map_pow, hξ, ActLaws.σD_alg, map_mul, map_pow, ActLaws.σDp_aDp, hw, map_mul, map_mul, map_pow, map_mul] at this
    rw [this]
  have hI : ∑ k, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (ρ g i k))) * Per.σD (g : GQ l) (H.Q k j) = H.Q i j := by
    have := congrFun (congrFun hinv i) j
    simpa [Matrix.mul_apply, hmap] using this
  rw [Matrix.mul_diagonal, Matrix.smul_apply]
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, RingHom.comp_apply,
    map_mul, map_sum, map_pow]
  have e1 : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.p j *
      (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) ^ H.q * algebraMap (Per.BdRp l) (Per.BdR l) (H.V i j)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l w) ^ H.q *
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E)) ^ H.q * H.Q i j) := by
    rw [H.Q_eq i j, map_mul, map_pow]; ring
  rw [e1, ← hI]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  linear_combination -(algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (ρ g i k)))) * hσ k

end GlobalTheory.BKLim.GalAdapted
end
end

