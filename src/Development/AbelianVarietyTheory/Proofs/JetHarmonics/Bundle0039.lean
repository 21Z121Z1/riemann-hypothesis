import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0003
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0037
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0032
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.StatementD
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenRealToComplex
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem entire_eq_of_eq_on_reals {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (p q : ℂ → E) (hp : Differentiable ℂ p) (hq : Differentiable ℂ q)
    (h : ∀ y : ℝ, p y = q y) : p = q := by
  have hp' : AnalyticOnNhd ℂ p Set.univ := fun z _ => hp.analyticAt z
  have hq' : AnalyticOnNhd ℂ q Set.univ := fun z _ => hq.analyticAt z
  refine AnalyticOnNhd.eq_of_frequently_eq (z₀ := ((0 : ℝ) : ℂ)) hp' hq' ?_
  have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (nhdsWithin 0 {0}ᶜ)
      (nhdsWithin ((0 : ℝ) : ℂ) {((0 : ℝ) : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro h0
      exact hy (Complex.ofReal_injective h0)
  exact ht.frequently (Filter.Frequently.of_forall h)

theorem capelli_eigen_real_to_complex :
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) f → (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (f) g = ((∏ s, (Y + lam s) : ℝ) : ℂ) • (f) g) → ∀ Y : ℂ, ∀ g ∈ B.GV k r, Q.CV k r Y f g = (∏ s, (Y + (lam s : ℂ))) • f g := by
  intro k r Wp Wq _ _ _ _ _ _ lam f hf hR Y g hg
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hs : Q.SmoothLev k r 0 Set.univ f := by
    intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀.1.1
    exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩
  have hg0 : g ∈ Q.Glev k r 0 := ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
  have h0 : Formalism.QuantumDeterminants.inWb k r 0 := by
    unfold Formalism.QuantumDeterminants.inWb
    simp
  obtain ⟨A, hA⟩ := Formalism.FourierDecayAlt.P.leading_term_alt (Wq →L[ℂ] Wp) k r 0 0 0 h0 h0
  have hpoly : (fun Y : ℂ => Q.CV k r Y f g) = fun Y : ℂ => Y ^ Q.mdim k r 0 • f g +
      ∑ j ∈ Finset.range (Q.mdim k r 0), Y ^ j • A 0 0 j f g := by
    funext Y
    exact (hA Set.univ f isOpen_univ hs g ⟨hg0, trivial⟩ Y).1
  have key := entire_eq_of_eq_on_reals (fun Y : ℂ => Q.CV k r Y f g)
    (fun Y : ℂ => (∏ s, (Y + (lam s : ℂ))) • f g) (by rw [hpoly]; fun_prop)
    (by
      refine Differentiable.smul_const ?_ _
      exact Differentiable.fun_finsetProd fun s _ => by fun_prop)
    (fun y => by
      show Q.CV k r (y : ℂ) f g = _
      rw [hR y g hg]; push_cast; rfl)
  exact congrFun key Y

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudNodeProjectionNormLowLevel
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem cloud_node_projector_bound (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (n kk : ℕ) (bv : ℝ)
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : Fin n → H →ₗ[ℂ] H) (lam : Fin n → ℝ)
    (hfd : FiniteDimensional ℂ VV) (hb : 0 < bv)
    (hsum : ∀ x, ∑ i, p i x = x)
    (hp : ∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = (lam i : ℂ) • p i x)
    (hpos : ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ lam a ∧ lam a ≤ bv / 32) ∧
      (kk ≤ a.val + 1 → bv - bv / 32 ≤ lam a ∧ lam a ≤ 2 * bv + bv / 32))
    (hgap : ∀ a c : Fin n, a ≠ c → 1 ≤ |lam a - lam c|)
    (hcard : (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk)
    (hres : ∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → ∀ x ∈ VV, 13 * bv / 32 * ‖x‖ ≤ ‖ζ • x - T x‖)
    (hT : ∀ x ∈ VV, ‖T x‖ ≤ 3 * bv * ‖x‖) :
    ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ ∧
      ∀ s : Fin n, kk ≤ s.val + 1 → ‖p s x‖ ≤ 3 * (6 * bv) ^ (n - kk) * ‖x‖ := by
  have h1 : ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ := by
    intro x hx
    have hnorm : ∀ i, ‖(lam i : ℂ) - (-((bv / 16 : ℝ) : ℂ))‖ = |lam i + bv / 16| := by
      intro i
      rw [sub_neg_eq_add, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    have := GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound H (Fin n) VV T p (fun i => (lam i : ℂ)) (univ.filter (fun a : Fin n => a.val + 1 < kk))
      (-((bv / 16 : ℝ) : ℂ)) (9 * bv / 16) (32 / (13 * bv)) hfd (by positivity) (by positivity)
      (fun x _ => hsum x) hp ?_ ?_ ?_ x hx
    · have e : 9 * bv / 16 * (32 / (13 * bv)) = 18 / 13 := by field_simp; norm_num
      rwa [e] at this
    · intro i hi
      have := (hpos i).1 (mem_filter.1 hi).2
      rw [hnorm, abs_lt]
      constructor <;> linarith [this.1, this.2]
    · intro i hi
      have hi' : kk ≤ i.val + 1 := by
        by_contra h
        exact hi (mem_filter.2 ⟨mem_univ _, not_le.1 h⟩)
      have := (hpos i).2 hi'
      rw [hnorm, lt_abs]
      left
      linarith [this.1, this.2]
    · intro ζ hζ y hy
      rw [sub_neg_eq_add] at hζ
      have h := hres ζ hζ y hy
      have e : ‖y‖ = 32 / (13 * bv) * (13 * bv / 32 * ‖y‖) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
  intro x hx
  refine ⟨h1 x hx, fun s hs => ?_⟩
  have hsN : s ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1) := mem_filter.2 ⟨mem_univ _, hs⟩
  have := GlobalTheory.norm_node_projector_le H (Fin n) VV T p (fun i => (lam i : ℂ))
    (univ.filter (fun a : Fin n => kk ≤ a.val + 1)) s (6 * bv) 3 hsN (by positivity) hp ?_ ?_ ?_ ?_ x hx
  · rw [card_erase_of_mem hsN, hcard] at this
    have e : n + 1 - kk - 1 = n - kk := by omega
    rwa [e] at this
  · intro y hy
    rw [← hsum y, map_sum]
    exact VV.sum_mem fun i _ => by rw [(hp i y hy).2]; exact VV.smul_mem _ (hp i y hy).1
  · intro i hi
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgap s i (ne_of_mem_erase hi).symm
  · intro i hi y hy
    have hi' := (hpos i).2 (mem_filter.1 (mem_of_mem_erase hi)).2
    have h2 : |lam i| ≤ 3 * bv := by
      rw [abs_le]; constructor <;> linarith [hi'.1, hi'.2]
    calc ‖T y - (lam i : ℂ) • y‖ ≤ ‖T y‖ + ‖(lam i : ℂ) • y‖ := norm_sub_le _ _
      _ ≤ 3 * bv * ‖y‖ + 3 * bv * ‖y‖ := by
          refine add_le_add (hT y hy) ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = 6 * bv * ‖y‖ := by ring
  · intro y hy
    have h3 := sum_filter_add_sum_filter_not univ (fun a : Fin n => a.val + 1 < kk) (fun i => p i y)
    rw [hsum y] at h3
    simp only [not_lt] at h3
    have h4 : ∑ i ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1), p i y =
        y - ∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y := by
      rw [eq_sub_iff_add_eq, add_comm]; exact h3
    rw [h4]
    have := h1 y hy
    have h5 := norm_sub_le y (∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y)
    linarith [norm_nonneg y]

theorem cloud_node_projection_norm : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ d, ‖(∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), io s (pr s (Pi.single c w))) d‖ ^ 2 ≤ (18 / 13) ^ 2 * ‖w‖ ^ 2 ∧ ∀ s : Fin n, kk ≤ s.val + 1 → ∑ d, ‖io s (pr s (Pi.single c w)) d‖ ^ 2 ≤ (3 * (6 * bv) ^ (n - kk)) ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hM hF hA hS hj hw c
  obtain ⟨hb, -, hpos⟩ := GlobalTheory.shape_position n kk j ε μ bv hS (by omega)
  obtain ⟨L0, Ladd, Lsmul, -⟩ := GlobalTheory.lev_subspace_mono M n ε E μ hM.1 hM.2.1
  have hcomp := GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hM.2.1 (fun s => (hF s).2.1) hA hw
  have heig := GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hM hF hA
  have hnb : (n : ℝ) ≤ bv := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by have := hS.2.1; omega : 1 ≤ n)
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ h1 (by norm_num)
    have h3 := hS.2.2.2.2.2
    have h4 : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
    linarith
  have hcard := (GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv hS.1 hS.2.1 hnb).1
  let e : PiLp 2 (fun _ : Fin n => M) ≃ₗ[ℂ] (Fin n → M) := WithLp.linearEquiv 2 ℂ (Fin n → M)
  have hn : ∀ x : PiLp 2 (fun _ : Fin n => M), ‖x‖ ^ 2 = ∑ d, ‖e x d‖ ^ 2 := fun x => PiLp.norm_sq_eq_of_L2 _ x
  let T0 : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
    LinearMap.pi fun b => -∑ a, (E b a) ∘ₗ (LinearMap.proj a : (Fin n → M) →ₗ[ℂ] M)
  have hT0 : ∀ x, T0 x = splitCas E x := by
    intro x
    funext b
    simp [T0, splitCas]
  let T : PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := e.symm.toLinearMap ∘ₗ T0 ∘ₗ e.toLinearMap
  have hT : ∀ x, e (T x) = splitCas E (e x) := by
    intro x
    rw [← hT0]
    exact e.apply_symm_apply _
  let p : Fin n → PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := fun s =>
    e.symm.toLinearMap ∘ₗ io s ∘ₗ pr s ∘ₗ e.toLinearMap
  have hp : ∀ s x, e (p s x) = io s (pr s (e x)) := fun s x => e.apply_symm_apply _
  let x₀ : PiLp 2 (fun _ : Fin n => M) := e.symm (Pi.single c w)
  have hx₀ : e x₀ = Pi.single c w := e.apply_symm_apply _
  have hx₀n : ‖x₀‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [hn, hx₀, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [hd]
    · simp
  let VV : Submodule ℂ (PiLp 2 (fun _ : Fin n => M)) := Submodule.span ℂ (Set.range fun s => p s x₀)
  have hfd : FiniteDimensional ℂ VV := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hsum : ∀ x, ∑ i, p i x = x := by
    intro x
    apply e.injective
    rw [map_sum]
    simp only [hp]
    exact hA.sum_io_pr _
  have hx₀V : x₀ ∈ VV := by
    rw [← hsum x₀]
    exact VV.sum_mem fun i _ => Submodule.subset_span ⟨i, rfl⟩
  have hpV : ∀ i, ∀ x ∈ VV, p i x ∈ VV := by
    intro i x hx
    have : VV ≤ VV.comap (p i) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, rfl⟩
      show p i (p s x₀) ∈ VV
      by_cases h : i = s
      · subst h
        have : p i (p i x₀) = p i x₀ := by
          apply e.injective
          rw [hp, hp, hA.pr_io]
        rw [this]
        exact Submodule.subset_span ⟨i, rfl⟩
      · have : p i (p s x₀) = 0 := by
          apply e.injective
          rw [hp, hp, hA.pr_io_ne i s h, map_zero, map_zero]
        rw [this]
        exact VV.zero_mem
    exact this hx
  have hlev : ∀ x ∈ VV, ∀ d, Lev ε E μ (j + 2) (e x d) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      intro d
      rw [hp, hx₀]
      exact hcomp s c d
    | zero => intro d; rw [map_zero]; exact L0 _
    | add x y _ _ hx hy => intro d; rw [map_add]; exact Ladd _ _ _ (hx d) (hy d)
    | smul a x _ hx => intro d; rw [map_smul]; exact Lsmul _ _ _ (hx d)
  have hres := fun x (hx : x ∈ VV) =>
    GlobalTheory.T.splitCasimir_resolvent_circle_bounds M n ε E μ kk (j + 2) bv (e x) hM hS (by omega) (hlev x hx)
  have key := cloud_node_projector_bound (PiLp 2 (fun _ : Fin n => M)) n kk bv VV T p
    (fun s => -μ s + (1 - (n : ℝ)) / 2) hfd hb hsum ?_ hpos ?_ hcard ?_ ?_ x₀ hx₀V
  · refine ⟨?_, fun s hs => ?_⟩
    · have h := pow_le_pow_left₀ (norm_nonneg _) key.1 2
      rw [mul_pow, hx₀n, hn, map_sum] at h
      simp only [hp, hx₀] at h
      exact h
    · have h := pow_le_pow_left₀ (norm_nonneg _) (key.2 s hs) 2
      rw [mul_pow, hx₀n, hn, hp, hx₀] at h
      exact h
  · intro i x hx
    refine ⟨hpV i x hx, ?_⟩
    apply e.injective
    rw [hT, map_smul, hp, heig]
  · intro a b hab
    rw [le_abs]
    rcases lt_or_gt_of_ne hab with h | h
    · right
      have := hS.2.2.1 a b h
      linarith
    · left
      have := hS.2.2.1 b a h
      linarith
  · intro ζ hζ x hx
    have h := (hres x hx).1 ζ hζ
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, map_sub, map_smul, hT]
    exact h
  · intro x hx
    have h := (hres x hx).2
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, hT]
    exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupHeightOneTorsionTowerStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroup_heightOne_torsion_tower : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧ ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  first | exact @GlobalTheory.ConvSer.exists_torsion_tower | exact GlobalTheory.ConvSer.exists_torsion_tower | (intros; apply GlobalTheory.ConvSer.exists_torsion_tower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupTorsionTowerExactOrderStatement
section
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_torsionTower_exact_order : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → (∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n)) ∧ (∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n)) ∧ ∀ n i j, ev1 (nMul F i) (t n) = ev1 (nMul F j) (t n) ↔ i ≡ j [MOD p ^ n] := by
  first | exact @GlobalTheory.ConvSer.tower_exact_order | exact GlobalTheory.ConvSer.tower_exact_order | (intros; apply GlobalTheory.ConvSer.tower_exact_order <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelCoverDatumSimilitudeAdjointTransport
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DatumCoverAdjoint

open GlobalTheory.DatumInverseCharacter

theorem span_image_sup_eq_top {R M J : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (φ : M →ₗ[R] M) (hφ : ∀ a, ∃ b, φ b - a ∈ (K • ⊤ : Submodule R M)) (x : J → M) (s : Set J)
    (h : Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤) :
    Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  obtain ⟨b, hb⟩ := hφ a
  have h1 : φ b ∈ Submodule.map φ (Submodule.span R (x '' s) ⊔ (K • ⊤ : Submodule R M)) :=
    Submodule.mem_map_of_mem (by rw [h]; exact Submodule.mem_top)
  rw [Submodule.map_sup, Submodule.map_span, Set.image_image, Submodule.map_smul''] at h1
  have h2 : φ b ∈ Submodule.span R ((fun i => φ (x i)) '' s) ⊔ (K • ⊤ : Submodule R M) :=
    SetLike.le_def.1 (sup_le_sup le_rfl (Submodule.smul_mono le_rfl le_top)) h1
  have := sub_mem h2 (Submodule.mem_sup_right hb)
  rwa [sub_sub_cancel] at this

theorem datum_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.l₂.M = l.M * d.pd → d.l₂.Mb = l.Mb * d.I → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ g : Sim Dw, (∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) → ∃ σq : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂, (∀ a, σq (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f d.l₂.M a)) ∧ ∀ (rk : Bool) (x0 : Fin n → Dw.La), AdmX (l := l) rk x0 → ∃ x0' : Fin n → Dw.La, AdmX (l := l) rk x0' ∧ ∀ q : Fin n → LevQ Dw d.l₂, d.w x0 (fun b => σq.symm (q b)) = d.w x0' q := by
  intro E _ _ _ H Dw l Xo c n d hM hb ph ψ x₀ hpin g hg
  obtain ⟨-, -, -, -, -, hφ⟩ := hpin
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hb
  have hspan : ∀ (l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H),
      ((l'.M : ℕ) : 𝓞 E) ∈ l'.Mb * l'.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := fun l' => by
    rw [l'.prod]; exact Ideal.mem_span_singleton_self _
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hbM : d.l₂.Mb ≤ l.Mb := hb ▸ (Ideal.mul_le_inf.trans inf_le_left)
  have hmb : ((d.l₂.M : ℕ) : 𝓞 E) ∈ d.l₂.Mb := (Ideal.mul_le_inf.trans inf_le_left) (hspan d.l₂)
  have hmJ : ((d.l₂.M : ℕ) : 𝓞 E) ∈ Mfr l :=
    Ideal.map_mono hbM ((Ideal.mul_le_inf.trans inf_le_right) (hspan d.l₂))
  obtain ⟨g', hg'⟩ := g.inv d.l₂.M hM₂
  set f := g.f d.l₂.M with hf
  obtain ⟨σ, hσ⟩ := exists_quot_equiv Dw hmb f g' hg'
  obtain ⟨fa, hfa⟩ := exists_adjoint Dw f
  obtain ⟨ga, hga⟩ := exists_adjoint Dw g'
  have hsurj : ∀ a, ∃ b, ga b - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    ⟨fa a, mem_of_modN Dw hmJ (modN_of_dvd Dw hM₂ fun v => by
      rw [map_sub, LinearMap.sub_apply, hga, hfa, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).2)⟩
  refine ⟨σ.toEquiv, hσ, fun rk x0 hx => ⟨fun b => ga (x0 b),
    span_image_sup_eq_top (Mfr l) ga hsurj x0 _ hx, fun q => ?_⟩⟩
  have hq : ∀ b, f (levRep (σ.toEquiv.symm (q b))) - levRep (q b) ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro b
    rw [← Submodule.Quotient.eq, ← hσ, levRep_spec, levRep_spec]
    exact σ.apply_symm_apply _
  have hz : zetaM c ^ pairL (l := l) x0 (fun b => levRep (σ.toEquiv.symm (q b))) =
      zetaM c ^ pairL (l := l) (fun b => ga (x0 b)) (fun b => levRep (q b)) := by
    refine zpow_congr hM₁ (root_pow c dvd_rfl) ?_
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [hga, g'.map_smul, ← map_sub, ← smul_sub]
    refine dvd_right Dw l.prod (cSep_mem l) _ ?_
    set a := levRep (σ.toEquiv.symm (q b))
    have h1 : g' (f a - levRep (q b)) ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
      have := Submodule.mem_map_of_mem (f := g') (hq b)
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono hbM le_top this
    have h2 : g' (f a) - a ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
      mem_of_modN Dw (hbM hmb) (hg' a).1
    have := sub_mem h1 h2
    convert this using 1
    rw [map_sub]
    abel
  have hroot := root_pow d.c₂ (N := d.pd) (hM ▸ Dvd.intro_left _ rfl)
  have hδ : d.eF (d.φδ (fun b => σ.toEquiv.symm (q b))) = d.eF (d.φδ q) := by
    rw [hφ, hφ]
    refine finsum_congr fun x => ?_
    congr 1
    refine zpow_congr hpd hroot ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [← map_sub, ← smul_sub]
    refine dvd_right Dw hIJ (cHalf_mem d.I) _ ?_
    have := sub_mem (Submodule.smul_mono hbI le_rfl (hq b)) (hg (levRep (σ.toEquiv.symm (q b))))
    convert this using 1
    abel
  unfold DeltaDat.w
  rw [hz, map_mul, map_mul, hδ]

end GlobalTheory.DatumCoverAdjoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OperatorEabPreservesSmoothClassCC
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.EabClass

theorem rdV_class {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {X : B.Mat k r}
    (hX : B.inLie k r X) {f : B.Mat k r → E} (hf : B.CkOn ⊤ (B.GV k r) f ∧ ∀ m : ℕ, B.InCC A m f) :
    B.CkOn ⊤ (B.GV k r) (RdV X f) ∧ ∀ m : ℕ, B.InCC A m (RdV X f) := by
  refine ⟨Formalism.FourierDecayAlt.P.B5.ckOn_RdV hX (by simpa using hf.1), fun m => ?_⟩
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.InCC_Rw (v := [X]) (by simpa using hX) (hf.2 _)

theorem eh_class : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (A : ℝ) (a b : Fin (2 * r + k + 1)) (f : B.Mat k r → (Wq →L[ℂ] Wp)), (B.CkOn ⊤ (B.GV k r) (f) ∧ ∀ m : ℕ, B.InCC (A) m (f)) → (B.CkOn ⊤ (B.GV k r) (Q.EH k r a b f) ∧ ∀ m : ℕ, B.InCC (A) m (Q.EH k r a b f)) := by
  intro k r Wp Wq _ _ _ _ _ _ A a b f hf
  have h1 := rdV_class (X := hpart1 (Hpk k r) (Matrix.single a b 1)) (Formalism.FourierDecayAlt.P.Qx2.hpart1_lie _) hf
  have h2 := rdV_class (X := hpart2 (Hpk k r) (Matrix.single a b 1)) (Formalism.FourierDecayAlt.P.Qx2.hpart2_lie _) hf
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h1.1 (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul Complex.I h2.1), fun m => ?_⟩
  obtain ⟨c₁, hc₁⟩ := h1.2 m
  obtain ⟨c₂, hc₂⟩ := h2.2 m
  exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul Complex.I hc₂)⟩

end GlobalTheory.EabClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryConjEntryAndInvEntryLinearStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_conj_entry_and_inv_entry_linear : ∀ (k r : ℕ) (i j : Fin (2 * r + k + 1)), (∃ co : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ, ∀ g ∈ B.GV k r, star (g i j) = ∑ a, ∑ b, co a b * g⁻¹ a b) ∧ ∃ q : B.Mat k r → ℂ, U.IsPolyDeg 1 q ∧ ∀ g ∈ B.GV k r, g⁻¹ i j = q g := by
  first | exact @GlobalTheory.unitary_conj_entry_and_inv_entry | exact GlobalTheory.unitary_conj_entry_and_inv_entry | (intros; apply GlobalTheory.unitary_conj_entry_and_inv_entry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryMeasureDatumProductMeasureEqOfSameVectors
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q MeasureTheory

namespace GlobalTheory

theorem haarOn_UW_eq_of_mass_one {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (μ ν : Measure (Mt k r))
    (hμ : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) μ) (hν : Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r z) ν)
    (h1 : μ Set.univ = 1) (h2 : ν Set.univ = 1) : ν = μ := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r _ μ ν (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hμ hν.conc hν.left hν.finite_compact
  have h3 := congrArg (fun m : Measure (Mt k r) => m Set.univ) hc
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h1, h2, mul_one] at h3
  have h4 : c = 1 := by exact_mod_cast h3.symm
  rw [hc, h4, one_smul]

theorem unitaryMeasureDatum_productMeasure_eq_of_same_vectors : ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (k r : ℕ) (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (D' : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq'), D'.z = D.z → D'.z' = D.z' → D.μW Set.univ = 1 → D.μW' Set.univ = 1 → D'.μW Set.univ = 1 → D'.μW' Set.univ = 1 → D'.μN = D.μN → D'.μSS = D.μSS := by
  intro Wp _ _ _ Wq _ _ _ Wq' _ _ _ k r D D' hz hz' h1 h2 h3 h4 hN
  have e1 : D'.μW = D.μW := haarOn_UW_eq_of_mass_one D.z _ _ D.haarW (hz ▸ D'.haarW) h1 h3
  have e2 : D'.μW' = D.μW' := haarOn_UW_eq_of_mass_one D.z' _ _ D.haarW' (hz' ▸ D'.haarW') h2 h4
  unfold Formalism.FourierDecayAlt.B.RealPlaceData.μSS
  rw [e1, e2, hN]

end GlobalTheory
end

