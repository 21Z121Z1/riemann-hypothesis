import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0055
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0031
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChamberPairThreeFour
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0074
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0075
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.TwKerLeComapOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaFirstHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0076

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaCompactDisjointRefinement
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.CroftonPartition

theorem isSigmaCompact_of_isOpen_compact {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] {U : Set X} (hU : IsOpen U) : IsSigmaCompact U := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance

theorem isSigmaCompact_inter_isClosed {X : Type} [TopologicalSpace X] {s C : Set X}
    (hs : IsSigmaCompact s) (hC : IsClosed C) : IsSigmaCompact (s ∩ C) := by
  obtain ⟨K, hK, hKs⟩ := hs
  refine ⟨fun n => K n ∩ C, fun n => (hK n).inter_right hC, ?_⟩
  rw [← hKs, Set.iUnion_inter]

theorem exists_sigmaCompact_partition : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) →
    (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X),
      Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧
      ∀ t, IsSigmaCompact (A t) := by
  intro X _ _ _ _ ι S hS hcov
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover S hS hcov.ge
  let e := t.equivFin
  let l : Fin t.card → ι := fun j => (e.symm j : ι)
  let A : Fin t.card → Set X := fun j => S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i)
  refine ⟨t.card, l, A, ?_, ?_, ?_, ?_⟩
  · intro j j' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Set.disjoint_left.2 fun x hx hx' => hx'.2 (Set.mem_iUnion₂.2 ⟨j, h, hx.1⟩)
    · exact Set.disjoint_left.2 fun x hx hx' => hx.2 (Set.mem_iUnion₂.2 ⟨j', h, hx'.1⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hl : l (e ⟨i, hit⟩) = i := by simp [l]
    obtain ⟨j, hj, hmin⟩ := wellFounded_lt.has_min {j : Fin t.card | x ∈ S (l j)}
      ⟨e ⟨i, hit⟩, by simpa [hl] using hxi⟩
    refine Set.mem_iUnion.2 ⟨j, hj, fun hx => ?_⟩
    obtain ⟨i', hi', hxi'⟩ := Set.mem_iUnion₂.1 hx
    exact hmin i' hxi' hi'
  · intro j
    exact Set.sdiff_subset
  · intro j
    show IsSigmaCompact (S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i))
    rw [Set.sdiff_eq]
    exact isSigmaCompact_inter_isClosed (isSigmaCompact_of_isOpen_compact (hS _))
      (isClosed_compl_iff.2 (isOpen_iUnion fun i => isOpen_iUnion fun _ => hS _))

end GlobalTheory.CompanionTheory.CroftonPartition
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardEtaleLocalSection
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.EtaleSection

theorem exists_sub_mem_of_prod_mem {S B : Type} [CommRing S] [CommRing B] [Algebra S B]
    (Q : Ideal B) (hQ : Q.IsPrime) (x : B) (s : Multiset S)
    (h : (s.map fun b => x - algebraMap S B b).prod ∈ Q) :
    ∃ b ∈ s, x - algebraMap S B b ∈ Q := by
  induction s using Multiset.induction_on with
  | empty =>
    exact absurd ((Ideal.eq_top_iff_one Q).2 (by simpa using h)) hQ.ne_top
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons] at h
    rcases hQ.mem_or_mem h with h | h
    · exact ⟨a, Multiset.mem_cons_self a s, h⟩
    · obtain ⟨b, hb, hbQ⟩ := ih h
      exact ⟨b, Multiset.mem_cons_of_mem hb, hbQ⟩

theorem exists_section_standardEtale : ∀ {S : Type} [CommRing S] , Aic S → Loc S →
    ∀ (B : Type) [CommRing B] [Algebra S B] [Algebra.IsStandardEtale S B] (Q : Ideal B), Q.IsPrime →
    (Q.comap (algebraMap S B)).IsMaximal →
    ∃ e : S, IsIdempotentElem e ∧ e ∉ Q.comap (algebraMap S B) ∧
      Nonempty (B →ₐ[S] Localization.Away e) := by
  intro S _ hA hL B _ _ _ Q hQ hm
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := S) (S := B)
  obtain ⟨s, hs⟩ := GlobalTheory.T.absolutely_closed_polynomial_splits hA P.f P.monic_f

  have hprod : (s.map fun b => P.x - algebraMap S B b).prod ∈ Q := by
    have h0 : Polynomial.aeval P.x P.f = 0 := P.hasMap.1
    rw [hs, map_multiset_prod, Multiset.map_map] at h0
    have : (s.map fun b => P.x - algebraMap S B b).prod = 0 := by
      rw [← h0]
      congr 1
      apply Multiset.map_congr rfl
      intro b _
      simp
    rw [this]
    exact Q.zero_mem
  obtain ⟨b, hbs, hbQ⟩ := exists_sub_mem_of_prod_mem Q hQ P.x s hprod
  have hroot : Polynomial.eval b P.f = 0 := by
    have hd : (Polynomial.X - Polynomial.C b) ∣ P.f := by
      rw [hs]
      exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hbs)
    exact Polynomial.dvd_iff_isRoot.1 hd

  set c : S := Polynomial.eval b P.g with hc
  have hcm : c ∉ Q.comap (algebraMap S B) := by
    intro hcQ
    have hcQ' : algebraMap S B c ∈ Q := hcQ
    have hd : P.x - algebraMap S B b ∣
        Polynomial.aeval P.x P.g - algebraMap S B c := by
      have := Polynomial.sub_dvd_eval_sub P.x (algebraMap S B b) (P.g.map (algebraMap S B))
      rwa [Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval] at this
    have hgQ : Polynomial.aeval P.x P.g ∈ Q := by
      have h1 := Ideal.mem_of_dvd Q hd hbQ
      simpa using Q.add_mem h1 hcQ'
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hgQ P.hasMap.2)

  obtain ⟨a, μ, hμ, haμ⟩ := hm.exists_inv hcm
  obtain ⟨e, he, hec, he1⟩ := hL (a * c)
  have h1ac : 1 - a * c = μ := by rw [← haμ]; ring
  have he1m : 1 - e ∈ Q.comap (algebraMap S B) := by
    rw [h1ac] at he1
    exact (Ideal.span_singleton_le_iff_mem _).2 hμ he1
  have hem : e ∉ Q.comap (algebraMap S B) := by
    intro hem
    have : (1 : S) ∈ Q.comap (algebraMap S B) := by
      simpa using Ideal.add_mem _ hem he1m
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine ⟨e, he, hem, ?_⟩

  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hec
  have heu : IsUnit (algebraMap S (Localization.Away e) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hcu : IsUnit (algebraMap S (Localization.Away e) c) := by
    have : algebraMap S (Localization.Away e) e =
        algebraMap S (Localization.Away e) (r * a) * algebraMap S (Localization.Away e) c := by
      rw [← map_mul, ← hr]; ring_nf
    rw [this] at heu
    exact isUnit_of_mul_isUnit_right heu
  have hmap : P.P.HasMap (algebraMap S (Localization.Away e) b) := by
    refine ⟨?_, ?_⟩
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, hroot, map_zero]
    · rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hcu
  exact ⟨(P.P.lift _ hmap).comp P.equivRing.toAlgHom⟩

end GlobalTheory.CompanionTheory.EtaleSection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripEntireOfFac
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

section Slice

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma Fac_const (c : X) (Ω : Set (ℝ × ℝ)) : Fac (fun _ => c) Ω :=
  ⟨fun _ _ => differentiableOn_const c, continuousOn_const, fun _ _ _ => ⟨‖c‖, fun _ _ => le_rfl⟩⟩

lemma Fac_exp (Ω : Set (ℝ × ℝ)) : Fac (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2)) Ω := by
  refine ⟨lineHol_exp _, by fun_prop, fun C _ hCc => ?_⟩
  have hc : Continuous fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2 := by fun_prop
  obtain ⟨M, hM⟩ := (hCc.image hc).bddAbove
  refine ⟨Real.exp M, fun l hl => ?_⟩
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 (le_trans ?_ (hM ⟨_, hl, rfl⟩))
  simp only [pow_two, Complex.add_re, Complex.mul_re]
  nlinarith [mul_self_nonneg l.1.im, mul_self_nonneg l.2.im]

lemma line_zero (τ : ℂ) : (0 : ℂ × ℂ) + τ • ((0 : ℂ), (1 : ℂ)) = (0, τ) := by
  ext <;> simp

lemma slice_mem_tube {C : Set ℝ} {y : ℂ} (h : y.re ∈ C) :
    ((0 : ℂ), y) ∈ tube (({0} : Set ℝ) ×ˢ C) := by
  simpa [tube] using h

lemma leftGood_of_fac {f : ℂ → X} {A : ℂ × ℂ → X} {a : ℝ} (hA : Fac A {x | x.2 < a})
    (h : ∀ y, f y = A (0, y)) : LeftGood f a := by
  refine ⟨?_, fun b c hc => ?_⟩
  · have h₁ := hA.hol 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube {x : ℝ × ℝ | x.2 < a}} = {z | z.re < a} := by
      ext z; simp [tube]
    rw [hs] at h₁
    have e : f = fun τ => A (0, τ) := funext h
    rw [e]
    exact h₁
  · obtain ⟨M, hM⟩ := hA.bdd (({0} : Set ℝ) ×ˢ Set.Icc b c)
      (by rintro x ⟨-, hx⟩; exact lt_of_le_of_lt hx.2 hc)
      (isCompact_singleton.prod isCompact_Icc)
    exact ⟨M, fun z h₁ h₂ => by rw [h]; exact hM _ (slice_mem_tube ⟨h₁, h₂⟩)⟩

lemma stripEntire_of_fac {f : ℂ → X} {A : ℂ × ℂ → X} (hA : Fac A Set.univ)
    (h : ∀ y, f y = A (0, y)) : StripEntire f := by
  refine ⟨?_, fun b c => ?_⟩
  · have h₁ := hA.hol 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube (Set.univ : Set (ℝ × ℝ))} = Set.univ := by
      ext z; simp [tube]
    rw [hs] at h₁
    have e : f = fun τ => A (0, τ) := funext h
    rw [e]
    exact differentiableOn_univ.1 h₁
  · obtain ⟨M, hM⟩ := hA.bdd (({0} : Set ℝ) ×ˢ Set.Icc b c) (Set.subset_univ _)
      (isCompact_singleton.prod isCompact_Icc)
    exact ⟨M, fun z h₁ h₂ => by rw [h]; exact hM _ (slice_mem_tube ⟨h₁, h₂⟩)⟩

lemma slice_good {T : Type} [TopologicalSpace T] {Φ : ℂ × ℂ → T → X} (hΦ : TubeGood Φ Set.univ) :
    (∀ g, Differentiable ℂ fun y : ℂ => Φ (0, y) g) ∧
    (Continuous fun y : ℂ × T => Φ (0, y.1) y.2) ∧
    ∀ (b a : ℝ) (g : T), ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g' ∈ U,
      ‖Φ (0, z) g'‖ ≤ M := by
  refine ⟨fun g => ?_, ?_, fun b a g => ?_⟩
  · have h₁ := hΦ.hol g 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube (Set.univ : Set (ℝ × ℝ))} = Set.univ := by
      ext z; simp [tube]
    rw [hs] at h₁
    exact differentiableOn_univ.1 h₁
  · have hc : Continuous fun y : ℂ × T => (((0 : ℂ), y.1), y.2) := by fun_prop
    have := hΦ.cont.comp hc.continuousOn (s := Set.univ) (fun y _ => by simp [tube])
    exact continuousOn_univ.1 this
  · obtain ⟨U, hU, M, hM⟩ := hΦ.bdd (({0} : Set ℝ) ×ˢ Set.Icc b a) (Set.subset_univ _)
      (isCompact_singleton.prod isCompact_Icc) g
    exact ⟨U, hU, M, fun z h₁ h₂ g' hg' => hM _ (slice_mem_tube ⟨h₁, h₂⟩) g' hg'⟩

end Slice

lemma exists_ne_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h₁ : ∃ z, f z ≠ 0) (h₂ : ∃ z, g z ≠ 0) : ∃ z, f z * g z ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z₀, hz₀⟩ := h₁
  obtain ⟨z₁, hz₁⟩ := h₂
  have hev : ∀ᶠ z in 𝓝 z₀, f z ≠ 0 := hf.continuous.continuousAt.eventually_ne hz₀
  have hg0 : g =ᶠ[𝓝 z₀] 0 :=
    hev.mono fun z hz => (mul_eq_zero.1 (hcon z)).resolve_left hz
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  exact hz₁ (hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₀) hg0 (Set.mem_univ z₁))

lemma exists_ne_aff {f : ℂ → ℂ} (h : ∃ z, f z ≠ 0) (α β γ : ℝ) (hβ : β ≠ 0) :
    ∃ y : ℂ, f (aff α β γ (0, y)) ≠ 0 := by
  obtain ⟨z, hz⟩ := h
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  refine ⟨(z - γ) / β, ?_⟩
  have e : aff α β γ (0, (z - γ) / (β : ℂ)) = z := by
    simp only [aff]
    field_simp
    ring
  rwa [e]

lemma ex_bounds (u R : ℝ) :
    ∃ m M : ℝ, m ≤ u ∧ m ≤ -2 * R ∧ (m = u ∨ m = -2 * R) ∧ u ≤ M ∧ R ≤ M ∧ (M = u ∨ M = R) :=
  ⟨min u (-2 * R), max u R, min_le_left _ _, min_le_right _ _, min_choice _ _, le_max_left _ _,
    le_max_right _ _, max_choice _ _⟩

section Conds

variable {G : Type} [Group G]

lemma conv_congr {Γ P : Subgroup G} {f f' : G → ℝ} (h : Conv Γ P f') (e : ∀ g, f g = f' g) :
    Conv Γ P f := by
  have : f = f' := funext e
  rwa [this]

variable {Γ A B : Subgroup G} {a b h : G → ℝ} {N R Rw : ℝ}

lemma cond_first (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneI (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ A (fun g => p * a g + t * h g) ∧
        Conv Γ B fun g => (h g + N * b g) - q * b g + t * h g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · exact conv_congr (hA (M + 1) t (by linarith) (by linarith [ht'.1])) fun g => rfl
  · refine conv_congr (hB (N - (m - 1)) (1 + t - N + (m - 1)) (by linarith [hN'.1]) ?_)
      fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1, hN'.2]

lemma cond_c (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneC (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ B (fun g => p * (-b g) + t * (h g + b g)) ∧
        Conv Γ B fun g => (-b g) - q * (-b g) + t * (h g + b g) := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hB (t - (M + 1)) (M + 1) ?_ (by linarith)) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · refine conv_congr (hB (t - 1 + (m - 1)) (1 - (m - 1)) ?_ (by linarith)) fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1]

lemma cond_a (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneA (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ B (fun g => p * b g + t * h g) ∧
        Conv Γ A fun g => (N * a g - h g) - q * a g + t * h g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hB (M + 1) (t - (M + 1)) (by linarith) ?_) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · exact conv_congr (hA (N - (m - 1)) (t - 1) (by linarith [hN'.1]) (by linarith [ht'.1]))
      fun g => by ring

lemma cond_b (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g) :
    ∀ x ∈ coneC (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ A (fun g => p * (h g - a g) + t * a g) ∧
        Conv Γ A fun g => ((N - 1) * (h g - a g)) - q * (h g - a g) + t * a g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hA (t - (M + 1)) (M + 1) ?_ (by linarith)) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · refine conv_congr (hA (t - N + 1 + (m - 1)) (N - 1 - (m - 1)) ?_ (by linarith [hN'.1]))
      fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1, hN'.2]

end Conds

section Series

variable {G : Type} [Group G]

lemma tsum_cos_inf {X : Type} [AddCommMonoid X] [TopologicalSpace X] (Γ S : Subgroup G)
    (f : G → X) : ∑' r : Cos (Γ ⊓ S) Γ, f (rep r) = ∑' q : Cos S Γ, f (rep q) := by
  have e : (Γ ⊓ S).subgroupOf Γ = S.subgroupOf Γ := Subgroup.inf_subgroupOf_left S Γ
  have key : ∀ U V : Subgroup Γ, U = V →
      ∑' r : Quotient (QuotientGroup.rightRel U), f (Quotient.out r).1 =
        ∑' q : Quotient (QuotientGroup.rightRel V), f (Quotient.out q).1 := by
    rintro U _ rfl
    rfl
  exact key _ _ e

variable {L W : Type} [NormedAddCommGroup L] [NormedSpace ℂ L] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]

lemma outer_apply {Γ Δ : Subgroup G} (ξ : G → ℝ) (H : ℂ → G → L →L[ℂ] W) (l : ℂ × ℂ) (g : G)
    (hs : Summable fun r : Cos Δ Γ => ‖Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)‖)
    (w : L) : outer Γ Δ ξ H l g w =
      ∑' r : Cos Δ Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w :=
  (ContinuousLinearMap.apply ℂ W w).map_tsum hs.of_norm

end Series

section Eis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]

lemma eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (s : ℂ)
    (w : W) : eis Γ K P c ρ Λ g (s • w) = s • eis Γ K P c ρ Λ g w := by
  simp only [eis, map_smul]
  rw [← tsum_const_smul'' s]
  congr 1
  ext q
  rw [smul_comm]

end Eis

end GlobalTheory.CompanionTheory.RgEisGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLawStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_of_section_law : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.Twist := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTwist.twist | exact GlobalTheory.CompanionTheory.RgEisTwist.twist | (intros; apply GlobalTheory.CompanionTheory.RgEisTwist.twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetExactSmoothStatement
section
open GlobalTheory.PRep GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_exact_smooth : ∀ {G V₁ V₂ V₃ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (ρ₃ : Representation ℂ G V₃), IsSmooth ρ₁ → IsSmooth ρ₂ → IsSmooth ρ₃ → ∀ (N : Subgroup G) (θ : N →* ℂˣ), IsOpen (θ.ker : Set N) → (∀ s : Finset G, (↑s : Set G) ⊆ N → ∃ L : Subgroup G, L ≤ N ∧ (↑s : Set G) ⊆ L ∧ IsCompact (L : Set G)) → ∀ (f : V₁ →ₗ[ℂ] V₂) (g : V₂ →ₗ[ℂ] V₃) (hf : ∀ x v, f (ρ₁ x v) = ρ₂ x (f v)) (hg : ∀ x v, g (ρ₂ x v) = ρ₃ x (g v)), LinearMap.range f = LinearMap.ker g → LinearMap.range (twMap ρ₁ ρ₂ N θ f hf) = LinearMap.ker (twMap ρ₂ ρ₃ N θ g hg) := by
  first | exact @GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker | exact GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker | (intros; apply GlobalTheory.CompanionTheory.PRep.TwExact.twMap_range_eq_ker <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatementStatement
section
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_boundedness_statement : GlobalTheory.CompanionTheory.Jp.JpUnif := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Unif.jpUnif | exact GlobalTheory.CompanionTheory.Jp.Unif.jpUnif | (intros; apply GlobalTheory.CompanionTheory.Jp.Unif.jpUnif <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHaarRightInvariant
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob

namespace GlobalTheory.CompanionTheory.HaarUnimod

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

theorem modularCharacterFun_eq_one (hG : IsUnimod G) (g : G) : modularCharacterFun g = 1 :=
  hG g

theorem isMulRightInvariant_of_isUnimod :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
      [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G →
      ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro G _ _ _ _ _ _ _ hG μ _
  refine ⟨fun g => ?_⟩
  rw [isMulLeftInvariant_eq_smul (map (· * g) μ) μ,
    ← modularCharacterFun_eq_haarScalarFactor, modularCharacterFun_eq_one hG g, one_smul]

end GlobalTheory.CompanionTheory.HaarUnimod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthPropertyStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_hecke_fourth_property : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.T0 → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.MeasureTransportOpenSet := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.transport_open_trace | exact GlobalTheory.CompanionTheory.TfLoc.transport_open_trace | (intros; apply GlobalTheory.CompanionTheory.TfLoc.transport_open_trace <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaFirstHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_fundamental_lemma_first_holds : PositivityTheory.Rg.Tf.Loc.D0a → PositivityTheory.Rg.Tf.Loc.T0 → PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.L3 → PositivityTheory.Rg.Tf.Loc.L4 → PositivityTheory.Rg.Tf.Loc.H2 → PositivityTheory.Rg.Tf.Loc.H3 → PositivityTheory.Rg.Tf.Loc.H4 → PositivityTheory.Rg.Tf.Loc.Z1 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first | exact GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first | (intros; apply GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_first <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaSecondHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_fundamental_lemma_second_holds : PositivityTheory.Rg.Tf.Loc.L2 → PositivityTheory.Rg.Tf.Loc.N4 → PositivityTheory.Rg.Tf.Loc.Z2 := by
  first | exact @GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second | exact GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second | (intros; apply GlobalTheory.CompanionTheory.UnitFL.unit_fundamental_lemma_second <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_dual_family_holds : PositivityTheory.Rg.Tf.Loc.IntegralBasisUnramified → PositivityTheory.Rg.Tf.Loc.TraceOneIntegralElement := by
  first | exact @GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family | exact GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family | (intros; apply GlobalTheory.CompanionTheory.UnramDual.unramified_trace_one_dual_family <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasisStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_integral_basis : PositivityTheory.Rg.Tf.Loc.D0a := by
  first | exact @GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | exact GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | (intros; apply GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a <;> assumption)
end

