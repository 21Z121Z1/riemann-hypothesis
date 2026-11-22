import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetPieceProductAnalytic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

noncomputable section

namespace SheetPieceProductAnalytic

def tailL (d : ℕ) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ

theorem tailL_apply {d : ℕ} (p : Fin (d + 1) → ℂ) (i : Fin d) : tailL d p i = p i.succ := rfl

theorem tailL_cons {d : ℕ} (a : ℂ) (y : Fin d → ℂ) : tailL d (Fin.cons a y) = y := by
  ext i
  simp [tailL_apply]

theorem cons_tailL {d : ℕ} (p : Fin (d + 1) → ℂ) : (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ) = p := by
  ext i
  cases i using Fin.cases <;> simp [tailL_apply]

def prodFn {σ : Type} [Fintype σ] (X B U : Set (σ → ℂ)) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (ℓ : (σ → ℂ) →L[ℂ] ℂ) (p : Fin (d + 1) → ℂ) : ℂ :=
  ∏ᶠ x ∈ {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}, (p 0 - ℓ x)

theorem exists_ne_zero_of_open {d : ℕ} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ}
    (hδ : AnalyticOnNhd ℂ δ D) (hD : IsPreconnected D) (hne : ∃ y ∈ D, δ y ≠ 0)
    (V : Set (Fin (d + 1) → ℂ)) (hV : IsOpen V) (hVW : V ⊆ tailL d ⁻¹' D) (hVne : V.Nonempty) :
    ∃ p ∈ V, δ (tailL d p) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨p, hp⟩ := hVne
  have hc : Continuous fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ) := by
    refine continuous_pi fun i => ?_
    cases i using Fin.cases
    · simpa using continuous_const
    · simpa using continuous_apply _
  have hev : δ =ᶠ[𝓝 (tailL d p)] 0 := by
    have hmem : (fun y : Fin d → ℂ => (Fin.cons (p 0) y : Fin (d + 1) → ℂ)) ⁻¹' V ∈ 𝓝 (tailL d p) := by
      refine hc.continuousAt.preimage_mem_nhds ?_
      show V ∈ 𝓝 (Fin.cons (p 0) (tailL d p) : Fin (d + 1) → ℂ)
      rw [cons_tailL]
      exact hV.mem_nhds hp
    filter_upwards [hmem] with y hy
    have := h _ hy
    rwa [tailL_cons] at this
  obtain ⟨y, hy, hy0⟩ := hne
  exact hy0 (hδ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hD (hVW hp) hev hy)

theorem differentiableAt_prodFn (hsec : UnbranchedFibreSections.Statement)
    {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    {U V : Set (σ → ℂ)} (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V)
    (hdisj : {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅)
    {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) (hδp₀ : δ (tailL d p₀) ≠ 0) :
    DifferentiableAt ℂ (prodFn X B U A ℓ) p₀ := by
  classical
  obtain ⟨r, g, hr, -, hrδ, hg, hfib⟩ := hsec σ X w B d A D δ N hP _ hp₀ hδp₀
  set y₀ := tailL d p₀ with hy₀def
  have hy₀ : y₀ ∈ ball y₀ r := mem_ball_self hr
  have hconst : ∀ i, ∀ y ∈ ball y₀ r, (g i y ∈ U ↔ g i y₀ ∈ U) := by
    intro i
    have hgc : ContinuousOn (g i) (ball y₀ r) := (hg i).continuousOn
    have hS : ∀ y ∈ ball y₀ r, g i y ∈ X ∩ B ∧ δ (A (g i y)) ≠ 0 := by
      intro y hy
      have hx : g i y ∈ {x | x ∈ X ∩ B ∧ A x = y} := by
        rw [(hfib y hy).2]
        exact ⟨i, rfl⟩
      exact ⟨hx.1, by rw [hx.2]; exact hrδ y hy⟩
    have hopU := hgc.isOpen_inter_preimage isOpen_ball hU
    have hopV := hgc.isOpen_inter_preimage isOpen_ball hV
    have hdj : Disjoint (ball y₀ r ∩ g i ⁻¹' U) (ball y₀ r ∩ g i ⁻¹' V) := by
      rw [Set.disjoint_left]
      rintro y ⟨hy, hyU⟩ ⟨-, hyV⟩
      have : g i y ∈ {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) := ⟨hS y hy, hyU, hyV⟩
      rw [hdisj] at this
      exact this
    have hcv : ball y₀ r ⊆ (ball y₀ r ∩ g i ⁻¹' U) ∪ (ball y₀ r ∩ g i ⁻¹' V) := by
      intro y hy
      rcases hcov (hS y hy) with h | h
      · exact Or.inl ⟨hy, h⟩
      · exact Or.inr ⟨hy, h⟩
    have hc : IsPreconnected (ball y₀ r) := (convex_ball y₀ r).isPreconnected
    intro y hy
    constructor
    · intro hyU
      by_contra hy0U
      have hy0V : y₀ ∈ ball y₀ r ∩ g i ⁻¹' V := (hcv hy₀).resolve_left fun h => hy0U h.2
      have hsub := hc.subset_right_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy0V⟩
      exact Set.disjoint_left.1 hdj ⟨hy, hyU⟩ (hsub hy)
    · intro hy0U
      exact (hc.subset_left_of_subset_union hopU hopV hdj hcv ⟨y₀, hy₀, hy₀, hy0U⟩ hy).2
  set I : Finset (Fin N) := Finset.univ.filter fun i => g i y₀ ∈ U with hIdef
  have hrep : ∀ p : Fin (d + 1) → ℂ, tailL d p ∈ ball y₀ r →
      prodFn X B U A ℓ p = ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    intro p hp
    have hset : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} =
        (fun i => g i (tailL d p)) '' (I : Set (Fin N)) := by
      ext x
      constructor
      · rintro ⟨hxB, hxU, hxA⟩
        have hx : x ∈ Set.range (fun i => g i (tailL d p)) := by
          rw [← (hfib _ hp).2]
          exact ⟨hxB, hxA⟩
        obtain ⟨i, rfl⟩ := hx
        exact ⟨i, by simpa [hIdef] using (hconst i _ hp).1 hxU, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        have hx : g i (tailL d p) ∈ {x | x ∈ X ∩ B ∧ A x = tailL d p} := by
          rw [(hfib _ hp).2]
          exact ⟨i, rfl⟩
        exact ⟨hx.1, (hconst i _ hp).2 (by simpa [hIdef] using hi), hx.2⟩
    unfold prodFn
    rw [hset, finprod_mem_image ((hfib _ hp).1.injOn), finprod_mem_coe_finset]
  have hev : prodFn X B U A ℓ =ᶠ[𝓝 p₀] fun p => ∏ i ∈ I, (p 0 - ℓ (g i (tailL d p))) := by
    have hmem : tailL d ⁻¹' ball y₀ r ∈ 𝓝 p₀ :=
      (tailL d).continuous.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hy₀)
    filter_upwards [hmem] with p hp using hrep p hp
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hfac : ∀ i, DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0 - ℓ (g i (tailL d p))) p₀ := by
    intro i
    have h1 : DifferentiableAt ℂ (fun p : Fin (d + 1) → ℂ => p 0) p₀ := differentiableAt_apply 0 p₀
    have h2 : DifferentiableAt ℂ (fun p => ℓ (g i (tailL d p))) p₀ :=
      ℓ.differentiableAt.comp _ (((hg i) _ hy₀).differentiableAt.comp _ (tailL d).differentiableAt)
    exact h1.sub h2
  refine Finset.induction_on I ?_ ?_
  · simp
  · intro j s hj ih
    simp only [Finset.prod_insert hj]
    exact (hfac j).mul ih

theorem isBounded_prodFn {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {w : σ → ℂ} {B : Set (σ → ℂ)} {d : ℕ}
    {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {D : Set (Fin d → ℂ)} {δ : (Fin d → ℂ) → ℂ} {N : ℕ}
    (U : Set (σ → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (hP : IsLocalParametrisation X w B A D δ N) {p₀ : Fin (d + 1) → ℂ} (hp₀ : tailL d p₀ ∈ D) :
    ∃ Nb ∈ 𝓝 p₀, Bornology.IsBounded
      (prodFn X B U A ℓ '' (Nb ∩ tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0})) := by
  obtain ⟨-, -, hD, -, -, hprop, -, -, -, hcard, -, -⟩ := hP
  obtain ⟨ρ, hρ, hρD⟩ := Metric.isOpen_iff.1 hD _ hp₀
  set y₀ := tailL d p₀ with hy₀def
  have hK : IsCompact {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
    hprop _ ((closedBall_subset_ball (half_lt_self hρ)).trans hρD) (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hK.image ℓ.continuous).isBounded
  set C : ℝ := max 1 (‖p₀ 0‖ + 1 + M) with hCdef
  refine ⟨tailL d ⁻¹' ball y₀ (ρ / 2) ∩ {p | ‖p 0‖ < ‖p₀ 0‖ + 1}, ?_, ?_⟩
  · refine Filter.inter_mem ((tailL d).continuous.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_self (half_pos hρ)))) ?_
    exact (isOpen_lt (continuous_norm.comp (continuous_apply 0)) continuous_const).mem_nhds (by simp)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C ^ N, ?_⟩
  rintro _ ⟨p, ⟨⟨⟨hpb, hpn⟩, hpD⟩, hpδ⟩, rfl⟩
  have hpn' : ‖p 0‖ < ‖p₀ 0‖ + 1 := hpn
  have hsub : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p} ⊆ {x | x ∈ X ∩ B ∧ A x = tailL d p} :=
    fun x hx => ⟨hx.1, hx.2.2⟩
  have hfin : {x | x ∈ X ∩ B ∧ A x = tailL d p}.encard = N := hcard _ hpD hpδ
  have hsfin : {x | x ∈ X ∩ B ∧ x ∈ U ∧ A x = tailL d p}.Finite :=
    (Set.finite_of_encard_eq_coe hfin).subset hsub
  have hcardle : hsfin.toFinset.card ≤ N := by
    have h1 := Set.encard_le_encard hsub
    rw [hfin, ← hsfin.coe_toFinset, Set.encard_coe_eq_coe_finsetCard] at h1
    exact_mod_cast h1
  have hbd : ∀ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ ≤ C := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have hxK : x ∈ {x | x ∈ X ∩ B ∧ A x ∈ closedBall y₀ (ρ / 2)} :=
      ⟨hx.1, by rw [hx.2.2]; exact ball_subset_closedBall hpb⟩
    have hMx := hM _ ⟨x, hxK, rfl⟩
    calc ‖p 0 - ℓ x‖ ≤ ‖p 0‖ + ‖ℓ x‖ := norm_sub_le _ _
      _ ≤ ‖p₀ 0‖ + 1 + M := by linarith
      _ ≤ C := le_max_right _ _
  unfold prodFn
  rw [finprod_mem_eq_finite_toFinset_prod _ hsfin]
  calc ‖∏ x ∈ hsfin.toFinset, (p 0 - ℓ x)‖ ≤ ∏ x ∈ hsfin.toFinset, ‖p 0 - ℓ x‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ _x ∈ hsfin.toFinset, C := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hbd
    _ = C ^ hsfin.toFinset.card := Finset.prod_const C
    _ ≤ C ^ N := pow_le_pow_right₀ (le_max_left _ _) hcardle

end SheetPieceProductAnalytic

open SheetPieceProductAnalytic in

theorem SheetPieceProductAnalytic.proof (hsec : UnbranchedFibreSections.Statement) :
    SheetPieceProductAnalytic.Statement := by
  intro σ _ X w B d A D δ N U V ℓ hP hU hV hcov hdisj
  have hP' := hP
  obtain ⟨-, -, hD, hDc, -, -, -, hδ, hne, -, -, -⟩ := hP'
  have hW : IsOpen (tailL d ⁻¹' D) := hD.preimage (tailL d).continuous
  have hgd : DifferentiableOn ℂ (fun p => δ (tailL d p)) (tailL d ⁻¹' D) := fun p hp =>
    ((hδ _ hp).differentiableAt.comp p (tailL d).differentiableAt).differentiableWithinAt
  obtain ⟨F, hF, hFG⟩ := RiemannExtensionAnalytic.proof (d + 1) (tailL d ⁻¹' D) (fun p => δ (tailL d p))
    (prodFn X B U A ℓ) hW hgd (fun V' hV' hsub hne' => exists_ne_zero_of_open hδ hDc hne V' hV' hsub hne')
    (fun p hp => (differentiableAt_prodFn hsec ℓ hP hU hV hcov hdisj hp.1 hp.2).differentiableWithinAt)
    (fun p hp => isBounded_prodFn U ℓ hP hp)
  have hFa : AnalyticOnNhd ℂ F (tailL d ⁻¹' D) := RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hW hF
  have hcons : ∀ z, tailL d (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) = A z := fun z => tailL_cons _ _
  refine ⟨fun z => F (Fin.cons (ℓ z) (A z)), fun z hz => ?_, fun z hz hδz => ?_⟩
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈ tailL d ⁻¹' D := by
      rw [Set.mem_preimage, hcons]
      exact hz
    have hlin : AnalyticAt ℂ (fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) z := by
      rw [analyticAt_pi_iff]
      intro i
      cases i using Fin.cases
      · simpa using ℓ.analyticAt z
      · rename_i j
        simp only [Fin.cons_succ]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) j).comp A).analyticAt z
    exact AnalyticAt.comp (g := F) (f := fun z => (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ)) (hFa _ hm) hlin
  · have hm : (Fin.cons (ℓ z) (A z) : Fin (d + 1) → ℂ) ∈
        tailL d ⁻¹' D ∩ {p | δ (tailL d p) ≠ 0} := by
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage, hcons]
        exact hz
      · show δ (tailL d _) ≠ 0
        rw [hcons]
        exact hδz
    show F _ = _
    rw [hFG hm]
    simp only [prodFn, hcons, Fin.cons_zero]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSmallSetTubeVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

theorem zeroSet_subset_biUnion_minimalPrimes {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSet I ⊆ ⋃ P ∈ I.minimalPrimes, zeroSet P := by
  intro x hx
  have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hle
  exact Set.mem_biUnion hP fun q hq => (RingHom.mem_ker).1 (hPle hq)

theorem withBot_enat_le_pred {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x) (h : x < (d : WithBot ℕ∞)) :
    0 < d ∧ x ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => simp at h
    | coe m =>
      have hm : m < d := by exact_mod_cast h
      refine ⟨by omega, ?_⟩
      rw [← WithBot.coe_natCast]
      exact WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : m ≤ d - 1))

theorem minimalPrime_tube_bound (h : PrimeTubeVolume.Statement) {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)}
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ)) (hK : IsCompact K)
    {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P ∈ I.minimalPrimes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (Metric.thickening r (zeroSet P ∩ K)) ≤
        ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) := by
  have hprime : P.IsPrime := hP.1.1
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2) (Ideal.Quotient.factor_surjective hP.1.2)
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨hd, hk⟩ := withBot_enat_le_pred hnn (hle.trans_lt hdim)
  obtain ⟨C, hC, hCr⟩ := h n (d - 1) P K hprime hk hK
  refine ⟨C, hC, fun r hr => ?_⟩
  have he : ((2 * n : ℤ) - 2 * ((d - 1 : ℕ) : ℤ)) = (2 * n + 2 : ℤ) - 2 * d := by omega
  simpa [he] using hCr r hr

theorem SmallSetTubeVolume.proof (h : PrimeTubeVolume.Statement) : SmallSetTubeVolume.Statement := by
  intro n d I K hdim hK
  set e : ℤ := (2 * n + 2 : ℤ) - 2 * d
  have key : ∀ F : Finset (Ideal (MvPolynomial (Fin n) ℂ)), (↑F : Set _) ⊆ I.minimalPrimes →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (⋃ P ∈ F, zeroSet P ∩ K)) ≤ ENNReal.ofReal (C * r ^ e) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, le_rfl, fun r _ => by simp⟩
    | insert a F ha ih =>
      intro hsub
      obtain ⟨C₁, hC₁, h₁⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      obtain ⟨C₂, hC₂, h₂⟩ := minimalPrime_tube_bound h hdim hK (hsub (Finset.mem_insert_self a F))
      refine ⟨C₂ + C₁, add_nonneg hC₂ hC₁, fun r hr => ?_⟩
      have hre : 0 ≤ r ^ e := zpow_nonneg hr.1.le e
      rw [Finset.set_biUnion_insert, Metric.thickening_union, add_mul,
        ENNReal.ofReal_add (mul_nonneg hC₂ hre) (mul_nonneg hC₁ hre)]
      exact (measure_union_le _ _).trans (add_le_add (h₂ r hr) (h₁ r hr))
  obtain ⟨F, hF⟩ := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).exists_finset_coe
  obtain ⟨C, hC, hCr⟩ := key F hF.le
  refine ⟨C, hC, fun r hr => le_trans (measure_mono (Metric.thickening_subset_of_subset r ?_)) (hCr r hr)⟩
  intro x ⟨hxI, hxK⟩
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.1 (zeroSet_subset_biUnion_minimalPrimes I hxI)
  rw [← hF] at hP
  exact Set.mem_iUnion₂.2 ⟨P, hP, hxP, hxK⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PStokesOnVariety
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem StokesOnVariety.proof (hD : ComplexSets.DiscriminantCover.Statement)
    (hS : StokesOffDiscriminant.Statement) (hL : CutOffLimit.Statement) :
    StokesOnVariety.Statement := by
  have key : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
      (φ : Fin d → (Fin n → ℂ) → ℝ), J.IsPrime →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) →
      SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport f → varInt J (d + 1) f (vecCons g φ) = varInt J (d + 1) g (vecCons f φ) := by
    intro n d J f g φ hJ hdim hf hg hφ hc
    unfold varInt
    split_ifs with hA
    · have hAf := hA.choose_spec
      generalize hA.choose = A at hAf ⊢
      obtain ⟨P, hP0, hPcov⟩ := hD n (d + 1) J A hJ hdim hAf

      have hsheet : ∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s := by
        intro x hx hPx
        obtain ⟨-, -, hloc⟩ := hPcov (A *ᵥ x) hPx
        obtain ⟨U, V, s, hU, hyU, hV, hxV, hs, hsy, hAs, hZV⟩ := hloc x ⟨hx, rfl⟩
        refine ⟨s, U, hU, hyU, hs, hsy, fun w hw => ⟨hAs w hw, ?_⟩, V, hV.mem_nhds hxV, ?_⟩
        · have hw' : s w ∈ zeroSet J ∩ V := hZV ▸ Set.mem_image_of_mem s hw
          exact hw'.1
        · rintro x' hx' -
          rw [hZV] at hx'
          obtain ⟨w, hw, rfl⟩ := hx'
          rw [hAs w hw]
      obtain ⟨χ, hχs, hχU, hlim⟩ := hL n d J A P hJ hdim hAf hP0
      obtain ⟨h1, h2⟩ := hlim f g φ hf hg hφ hc
      refine tendsto_nhds_unique h1 (Tendsto.congr (fun k => ?_) h2)
      obtain ⟨U, hU, hDU, hχ0⟩ := hχU k
      obtain ⟨V, hV, hZV, hfV⟩ := hf
      have hcχ : HasCompactSupport (fun x => χ k x * f x) := hc.mul_left (f := χ k)
      refine (hS n d J A P hJ hdim hAf hP0 hsheet (fun x => χ k x * f x) g φ
        ⟨V, hV, hZV, (hχs k).contDiffOn.mul hfV⟩ hg hφ hcχ ⟨U, hU, hDU, fun x hx => ?_⟩).symm
      rw [hχ0 x hx, zero_mul]
    · rfl
  intro n d J f g φ hJ hdim hf hg hφ hc
  rcases hc with hc | hc
  · exact key n d J f g φ hJ hdim hf hg hφ hc
  · exact (key n d J g f φ hJ hdim hg hf hφ hc).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVanishNearPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem VanishNearPoint.proof (hOpen : FiniteMapOpen.Statement) : VanishNearPoint.Statement := by
  classical
  intro n J f x hJ hx hf
  by_contra hfJ
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ.ne_top
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ (MvPolynomial (Fin n) ℂ ⧸ J)
  choose p hp using fun i => Ideal.Quotient.mk_surjective (g (X i))
  have hg : g = (Ideal.Quotient.mkₐ ℂ J).comp (aeval p) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hp]
  subst hg
  let _ := ((Ideal.Quotient.mkₐ ℂ J).comp (aeval p)).toRingHom.toAlgebra
  have hint : IsIntegral (MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk J f) :=
    RingHom.IsIntegral.of_finite hfin _
  have hf0 : Ideal.Quotient.mk J f ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.comap_ne_bot_of_integral_mem hf0 (Ideal.mem_span_singleton_self _) hint)
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hh
  obtain ⟨a, ha⟩ := hh
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hJmem : aeval p h - q * f ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, sub_eq_zero]
    exact ha.symm

  have hval : ∀ z ∈ zeroLocus J, eval (fun i => eval z (p i)) h = eval z q * eval z f := by
    intro z hz
    have h1 := hz _ hJmem
    rw [map_sub, map_mul, sub_eq_zero] at h1
    rw [← h1]
    have h2 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℂ) (aeval z : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (f := p)) h
    rw [AlgHom.comp_apply] at h2
    exact h2.symm
  have hV := hOpen n d J p hJ hinj hfin x hx _ hf
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  apply hh0
  refine MvPolynomial.funext_set (fun i => Metric.ball (eval x (p i)) ε)
    (fun i => infinite_of_mem_nhds _ (Metric.ball_mem_nhds _ hε)) fun w hw => ?_
  rw [← ball_pi _ hε] at hw
  obtain ⟨z, ⟨hz, hzU⟩, rfl⟩ := hball hw
  rw [hval z hz, hzU hz, mul_zero, map_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyMassLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open scoped ENNReal

noncomputable section

theorem VarietyMassLower.proof (hG : VarietyTangentGraphDense.Statement)
    (hL : TangentGraphLowerDensity.Statement) (hM : VarietyLelongMono.Statement) :
    VarietyMassLower.Statement := by
  intro n d J hJ hd R
  set τ := μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) with hτdef
  have hτ : 0 < τ := TangentGraphLowerDensity.unitBall_pos d
  set m : ℝ≥0∞ := min τ 1 with hmdef
  have hm0 : 0 < m := lt_min hτ one_pos
  have hmtop : m ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hmτ : m ≤ τ := min_le_left _ _
  have hmr : 0 < m.toReal := ENNReal.toReal_pos hm0.ne' hmtop
  refine ⟨(1 / 2) * (1 / 2) ^ (2 * d) * m.toReal, by positivity, fun z hz _ ρ hρ => ?_⟩
  obtain ⟨hρ0, -⟩ := hρ
  obtain ⟨b, I₀, Ω, V, g, w₀, hcard, hΩ, hV, hw₀, hg, hproj, hZV, htan, hdist⟩ :=
    hG n d J hJ hd z hz (ρ / 2) (by linarith)
  have hz₀ : g w₀ ∈ zeroSetEuc J := by
    have h : g w₀ ∈ g '' Ω := ⟨w₀, hw₀, rfl⟩
    rw [← hZV] at h
    exact h.1
  obtain ⟨r₀, hr₀, hlow⟩ := hL n d b I₀ (zeroSetEuc J) Ω V g w₀ hcard hΩ hV hw₀ hg hproj hZV htan
    (1 / 2) ⟨by norm_num, by norm_num⟩
  set t := min (r₀ / 2) (ρ / 2) with htdef
  have ht0 : 0 < t := lt_min (by linarith) (by linarith)
  have htr : t < r₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hts : t ≤ ρ / 2 := min_le_right _ _
  have h1 := hlow t ⟨ht0, htr⟩
  have h2 := hM n d J hJ hd (g w₀) hz₀ t (ρ / 2) ht0 hts
  have hsub : zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2) ⊆ zeroSetEuc J ∩ Metric.ball z ρ :=
    Set.inter_subset_inter_right _ (Metric.ball_subset_ball' (by linarith))
  have h3 := measure_mono (μ := μH[((2 * d : ℕ) : ℝ)]) hsub
  have key : ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ) ≤
      ENNReal.ofReal (t ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := by
    calc ENNReal.ofReal (t ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ)
        = ENNReal.ofReal ((ρ / 2) ^ (2 * d)) * (ENNReal.ofReal ((1 / 2) * t ^ (2 * d)) * τ) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          ring
      _ ≤ ENNReal.ofReal ((ρ / 2) ^ (2 * d)) *
            μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) t) := by gcongr
      _ ≤ _ := h2
  have key' := (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (pow_pos ht0 _)).ne'
    ENNReal.ofReal_ne_top).1 key
  have hc : (1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d) =
      ((1 / 2) * (ρ / 2) ^ (2 * d)) * m.toReal := by
    rw [div_pow, div_pow, one_pow]
    ring
  calc ENNReal.ofReal ((1 / 2) * (1 / 2) ^ (2 * d) * m.toReal * ρ ^ (2 * d))
      = ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * m := by
        rw [hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmtop]
    _ ≤ ENNReal.ofReal ((1 / 2) * (ρ / 2) ^ (2 * d)) * τ := by gcongr
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball (g w₀) (ρ / 2)) := key'
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) := h3

end

end GroundTheory.Heights₂.Heights
end

