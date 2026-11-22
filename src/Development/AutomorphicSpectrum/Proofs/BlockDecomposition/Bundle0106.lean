import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0090
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0097
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitDivisibleOfVanishingLevel
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.Tower

theorem rho_lim {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W} (L : LSeq l S S') (x : S.lim)
    (b c : ℕ) (h : b ≤ c) : L.ρ c b (x.1 c) = x.1 b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact L.ρ_self b _
  | succ d ih =>
    have h' := L.ρ_succ (b + d) b (Nat.le_add_right _ _) (x.1 (b + d + 1))
    rw [x.2 (b + d), ih (Nat.le_add_right _ _)] at h'
    exact h'

theorem lim_eq_pow_smul : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    (∀ n, IsArtinian W (S.M n)) → ∀ n (x : S.lim), x.1 n = 0 → ∃ y : S.lim, x = ((l : W) ^ n) • y := by
  intro W _ l S S' L hA n x hx
  have hex : ∀ a, ∃ y, L.ν a (n + a) y = x.1 (n + a) := fun a =>
    L.ex₁ a n (n + a) (Nat.add_comm _ _) _ (by rw [rho_lim L x n (n + a) (Nat.le_add_right _ _), hx])
  choose y hy using hex
  have hN : ∀ a w, w ∈ LinearMap.ker (L.ν (a + 1) (n + (a + 1))) →
      S.r a w ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a w hw
    have hw' : L.ν (a + 1) (n + a + 1) w = 0 := hw
    rw [LinearMap.mem_ker, ← L.ν_r a (n + a) (Nat.le_add_left _ _), hw', map_zero]
  have hc : ∀ a, S.r a (y (a + 1)) - y a ∈ LinearMap.ker (L.ν a (n + a)) := by
    intro a
    have h1 : L.ν (a + 1) (n + a + 1) (y (a + 1)) = x.1 (n + a + 1) := hy (a + 1)
    rw [LinearMap.mem_ker, map_sub, ← L.ν_r a (n + a) (Nat.le_add_left _ _), h1, x.2 (n + a), hy a,
      sub_self]
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA (fun a => LinearMap.ker (L.ν a (n + a))) y hN hc
  have key : ∀ a, ((l : W) ^ n) • z.1 (n + a) = x.1 (n + a) := by
    intro a
    have h1 := L.ν_ρ a (n + a) (Nat.le_add_left _ _) (z.1 (n + a))
    have h2 : L.ν a (n + a) (z.1 a) = x.1 (n + a) := by
      have h3 : L.ν a (n + a) (z.1 a - y a) = 0 := hz a
      rw [map_sub, hy a, sub_eq_zero] at h3
      exact h3
    rw [rho_lim L z a (n + a) (Nat.le_add_left _ _), h2, Nat.add_sub_cancel] at h1
    exact h1.symm
  refine ⟨z, Subtype.ext (funext fun c => ?_)⟩
  calc x.1 c = L.ρ (n + c) c (x.1 (n + c)) := (rho_lim L x c (n + c) (Nat.le_add_left _ _)).symm
    _ = L.ρ (n + c) c (((l : W) ^ n) • z.1 (n + c)) := by rw [key]
    _ = ((l : W) ^ n) • L.ρ (n + c) c (z.1 (n + c)) := map_smul _ _ _
    _ = ((l : W) ^ n) • z.1 c := by rw [rho_lim L z c (n + c) (Nat.le_add_left _ _)]

end GlobalTheory.CompanionTheory.Tower
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorSandwichApprox
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

variable {F : Type} [Field F] [NumberField F]

def ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Set (Fv F v) :=
  {y | Valued.v y ≤ WithZero.exp (-(n : ℤ))}

theorem isClopen_ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : IsClopen (ballV v n) := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-(n : ℤ)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : ballV v n = {y : Fv F v | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [ballV, Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isClopen_closedBall _ (by simp [hc0])

theorem ballV_subset (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ballV v n ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
  intro y hy
  have h1 : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 : Valued.v y ≤ 1 := le_trans (show Valued.v y ≤ _ from hy) h1
  exact h2

theorem antitone_ballV (v : HeightOneSpectrum (𝓞 F)) : Antitone (ballV (F := F) v) := by
  intro m n hmn y hy
  show Valued.v y ≤ _
  refine le_trans (show Valued.v y ≤ _ from hy) ?_
  rw [WithZero.exp_le_exp]
  omega

theorem iInter_ballV (v : HeightOneSpectrum (𝓞 F)) : ⋂ n, ballV (F := F) v n = {0} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hy
    have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h1 := h (-(Valued.v y).log + 1).toNat
    have h2 : Valued.v y ≤ WithZero.exp (-(((-(Valued.v y).log + 1).toNat : ℕ) : ℤ)) := h1
    conv_lhs at h2 => rw [← WithZero.exp_log hv0]
    rw [WithZero.exp_le_exp] at h2
    have := Int.self_le_toNat (-(Valued.v y).log + 1)
    omega
  · rintro rfl n
    simp [ballV]

theorem nhdsNE_Fv (v : HeightOneSpectrum (𝓞 F)) : (𝓝[≠] (0 : Fv F v)).NeBot := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

theorem tendsto_real_ballV {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    Tendsto (fun n => lam.real (ballV v n)) atTop (𝓝 0) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  have hfin : ∀ n, lam (ballV v n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono (ballV_subset v n))
  have h := tendsto_measure_iInter_atTop (μ := lam) (s := ballV v)
    (fun n => (isClopen_ballV v n).isOpen.measurableSet.nullMeasurableSet) (antitone_ballV v) ⟨0, hfin 0⟩
  rw [iInter_ballV, measure_singleton] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Measure.real, Function.comp_def] using h2

theorem exists_sandwich : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  intro F _ _ v lam C g hstd hg0 hg η hη
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  obtain ⟨hcont, hout, hint, -, hone⟩ := hg
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + |C| := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hgK : ∀ s, s ≠ 0 → g s ≤ K := by
    intro s hs
    by_cases hO : s ∈ v.adicCompletionIntegers F
    · have h1 := hint s hO hs
      have h2 : C / (Ideal.absNorm v.asIdeal : ℝ) ≤ |C| :=
        (div_le_self (abs_nonneg C) hq |>.trans' (div_le_div_of_nonneg_right (le_abs_self C) (by linarith)))
      have h3 := (abs_le.1 h1).2
      rw [hKdef]; linarith
    · rw [hout s hO]; exact hK0.le
  have hgi : Integrable g lam := by
    by_contra h
    rw [integral_undef h] at hone
    norm_num at hone
  have hnz : ∀ᵐ s ∂lam, s ≠ 0 := by
    have : ({0}ᶜ : Set (Fv F v)) ∈ ae lam := compl_mem_ae_iff.2 (measure_singleton 0)
    exact this
  have hlim : Tendsto (fun n => K * lam.real (ballV v n)) atTop (𝓝 0) := by
    simpa using (tendsto_real_ballV hstd).const_mul K
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  obtain ⟨B, hB⟩ : ∃ B, B = ballV v n := ⟨_, rfl⟩
  rw [← hB] at hn
  have hBc : IsClopen B := hB ▸ isClopen_ballV v n
  have hBO : B ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := hB ▸ ballV_subset v n
  have h0B : (0 : Fv F v) ∈ B := by rw [hB]; simp [ballV]
  have hBm : MeasurableSet B := hBc.isOpen.measurableSet
  have hBfin : lam B ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono hBO)
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Formalism.L2.S.S7.AdeleLC.isCompact_integers v
  have hψm : Continuous (Bᶜ.indicator g) := by
    refine continuous_indicator ?_ ?_
    · intro a ha
      rw [hBc.compl.frontier_eq] at ha
      exact absurd ha (Set.notMem_empty a)
    · rw [hBc.compl.isClosed.closure_eq]
      refine hcont.mono ?_
      intro s hs h0
      exact hs (by rw [Set.mem_singleton_iff.1 h0]; exact h0B)
  have hψb : Continuous (B.indicator fun _ => K) :=
    by
    refine continuous_indicator ?_ continuous_const.continuousOn
    intro a ha
    rw [hBc.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty a)
  have hIm : ∫ s, Bᶜ.indicator g s ∂lam = ∫ s in Bᶜ, g s ∂lam := integral_indicator hBm.compl
  have hsplit : ∫ s in B, g s ∂lam + ∫ s in Bᶜ, g s ∂lam = 1 := by
    rw [integral_add_compl hBm hgi, hone]
  have hpos : 0 ≤ ∫ s in B, g s ∂lam := setIntegral_nonneg hBm fun s _ => hg0 s
  have hconst : ∫ s in B, K ∂lam = K * lam.real B := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hup : ∫ s in B, g s ∂lam ≤ K * lam.real B := by
    rw [← hconst]
    refine integral_mono_ae hgi.integrableOn (integrableOn_const hBfin) ?_
    exact ae_restrict_of_ae (hnz.mono fun s hs => hgK s hs)
  have hi1 : Integrable (Bᶜ.indicator g) lam := hgi.indicator hBm.compl
  have hi2 : Integrable (B.indicator fun _ => K) lam :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  have hIp : ∫ s, (Bᶜ.indicator g s + B.indicator (fun _ => K) s) ∂lam =
      ∫ s in Bᶜ, g s ∂lam + K * lam.real B := by
    rw [integral_add hi1 hi2, hIm, integral_indicator hBm, hconst]
  refine ⟨Bᶜ.indicator g, fun s => Bᶜ.indicator g s + B.indicator (fun _ => K) s, hψm, ?_,
    hψm.add hψb, ?_, fun s => Set.indicator_nonneg (fun s _ => hg0 s) s, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    simp [Set.indicator, hout s hs]
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    have hsB : s ∉ B := fun h => hs (hBO h)
    simp [hsB, hout s hs]
  · intro s hs
    by_cases hsB : s ∈ B
    · simp only [Set.indicator, Set.mem_compl_iff, hsB, not_true_eq_false, if_false, if_true, zero_add]
      exact ⟨hg0 s, hgK s hs⟩
    · simp [Set.indicator, hsB]
  · rw [hIm]; linarith
  · rw [hIp]; linarith

end GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MackeyInnerProduct
section
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.MackeyFn

variable {Γ : Type} [Group Γ] [Fintype Γ]

open Classical in

def mS (A B : Subgroup Γ) (a b : Γ → ℂ) (x : Γ) : ℂ :=
  ∑ h, if h ∈ (A ⊓ cj x B : Subgroup Γ) then a h⁻¹ * b (x * h * x⁻¹) else 0

def dc (A B : Subgroup Γ) (g : Γ) : Set Γ := {x | ∃ β ∈ B, ∃ α ∈ A, x = β * g * α}

theorem conj_mem_iff (H : Subgroup Γ) {u h : Γ} (hu : u ∈ H) : u * h * u⁻¹ ∈ H ↔ h ∈ H := by
  constructor
  · intro hh
    have : u⁻¹ * (u * h * u⁻¹) * u⁻¹⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hu) hh) (H.inv_mem (H.inv_mem hu))
    simpa [mul_assoc] using this
  · intro hh
    exact H.mul_mem (H.mul_mem hu hh) (H.inv_mem hu)

theorem ip_inter (A B : Subgroup Γ) (a b : Γ → ℂ) (y : Γ) :
    ip ((A ⊓ cj y B : Subgroup Γ) : Set Γ) a (fun h => b (y * h * y⁻¹)) =
      (Nat.card (A ⊓ cj y B : Subgroup Γ) : ℂ)⁻¹ * mS A B a b y := by
  classical
  have hc : (((A ⊓ cj y B : Subgroup Γ) : Set Γ)).ncard = Nat.card (A ⊓ cj y B : Subgroup Γ) :=
    (Nat.card_coe_set_eq _).symm
  unfold ip mS
  rw [hc]
  rfl

theorem ip_ind (A B : Subgroup Γ) (a b : Γ → ℂ) :
    ip (A : Set Γ) a (indF B b) =
      ((Nat.card A : ℂ)⁻¹ * (Nat.card B : ℂ)⁻¹) * ∑ x, mS A B a b x := by
  classical
  have hc : ((A : Set Γ)).ncard = Nat.card A := (Nat.card_coe_set_eq _).symm
  unfold ip indF mS
  rw [hc, Finset.sum_comm, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  by_cases hh : h ∈ A
  · have hh' : h ∈ (A : Set Γ) := hh
    rw [if_pos hh', mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x * h * x⁻¹ ∈ B
    · have hm : h ∈ (A ⊓ cj x B : Subgroup Γ) := ⟨hh, hx⟩
      rw [if_pos hx, if_pos hm]
    · have hm : h ∉ (A ⊓ cj x B : Subgroup Γ) := fun q => hx q.2
      rw [if_neg hx, if_neg hm, mul_zero]
  · have hh' : h ∉ (A : Set Γ) := hh
    rw [if_neg hh']
    have : ∀ x, h ∉ (A ⊓ cj x B : Subgroup Γ) := fun x q => hh q.1
    simp [this]

theorem mS_inv {A B : Subgroup Γ} {a b : Γ → ℂ} (hA : IsClassOn A a) (hB : IsClassOn B b)
    {β α : Γ} (x : Γ) (hβ : β ∈ B) (hα : α ∈ A) :
    mS A B a b (β * x * α) = mS A B a b x := by
  classical
  unfold mS
  refine Fintype.sum_equiv (MulAut.conj α).toEquiv _ _ fun h => ?_
  have he : (MulAut.conj α).toEquiv h = α * h * α⁻¹ := rfl
  rw [he]
  have hk : (β * x * α) * h * (β * x * α)⁻¹ = β * (x * (α * h * α⁻¹) * x⁻¹) * β⁻¹ := by group
  have hmem : h ∈ (A ⊓ cj (β * x * α) B : Subgroup Γ) ↔
      α * h * α⁻¹ ∈ (A ⊓ cj x B : Subgroup Γ) := by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_cj, mem_cj, hk, conj_mem_iff B hβ,
      conj_mem_iff A hα]
  by_cases hm : α * h * α⁻¹ ∈ (A ⊓ cj x B : Subgroup Γ)
  · have hx2 : x * (α * h * α⁻¹) * x⁻¹ ∈ B := hm.2
    rw [if_pos hm, if_pos (hmem.2 hm), hk, hB β hβ _ hx2]
    have hinv : (α * h * α⁻¹)⁻¹ = α * h⁻¹ * α⁻¹ := by group
    have hhA : h ∈ A := (conj_mem_iff A hα).1 hm.1
    rw [hinv, hA α hα _ (A.inv_mem hhA)]
  · rw [if_neg hm, if_neg (fun q => hm (hmem.1 q))]

theorem card_dc (A B : Subgroup Γ) (g : Γ) :
    Nat.card (dc A B g) * Nat.card (A ⊓ cj g B : Subgroup Γ) = Nat.card A * Nat.card B := by
  classical
  let φ : B × A → dc A B g := fun p => ⟨p.1 * g * p.2, p.1, p.1.2, p.2, p.2.2, rfl⟩
  have fib : ∀ x : dc A B g, Nat.card {p // φ p = x} = Nat.card (A ⊓ cj g B : Subgroup Γ) := by
    rintro ⟨x, β₀, hβ₀, α₀, hα₀, rfl⟩
    symm
    have hB' : ∀ c : (A ⊓ cj g B : Subgroup Γ), β₀ * (g * (c : Γ)⁻¹ * g⁻¹) ∈ B := fun c => by
      have h2 : g * (c : Γ) * g⁻¹ ∈ B := c.2.2
      have : g * (c : Γ)⁻¹ * g⁻¹ = (g * (c : Γ) * g⁻¹)⁻¹ := by group
      rw [this]
      exact B.mul_mem hβ₀ (B.inv_mem h2)
    have hA' : ∀ c : (A ⊓ cj g B : Subgroup Γ), (c : Γ) * α₀ ∈ A := fun c => A.mul_mem c.2.1 hα₀
    let f : (A ⊓ cj g B : Subgroup Γ) → {p // φ p = ⟨β₀ * g * α₀, β₀, hβ₀, α₀, hα₀, rfl⟩} := fun c =>
      ⟨(⟨_, hB' c⟩, ⟨_, hA' c⟩), by
        apply Subtype.ext
        show β₀ * (g * (c : Γ)⁻¹ * g⁻¹) * g * ((c : Γ) * α₀) = β₀ * g * α₀
        group⟩
    refine Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
    · intro c c' hcc
      have h3 : (c : Γ) * α₀ = (c' : Γ) * α₀ := by
        have := congrArg (fun p => ((p.1.2 : A) : Γ)) hcc
        exact this
      exact Subtype.ext (mul_right_cancel h3)
    · rintro ⟨⟨⟨β, hβ⟩, ⟨α, hα⟩⟩, hp⟩
      have he : β * g * α = β₀ * g * α₀ := congrArg Subtype.val hp
      have hcA : α * α₀⁻¹ ∈ A := A.mul_mem hα (A.inv_mem hα₀)
      have hβe : β = β₀ * (g * (α * α₀⁻¹)⁻¹ * g⁻¹) := by
        have : β = (β * g * α) * α⁻¹ * g⁻¹ := by group
        rw [this, he]
        group
      have hcB : g * (α * α₀⁻¹) * g⁻¹ ∈ B := by
        have : g * (α * α₀⁻¹) * g⁻¹ = (β₀⁻¹ * β)⁻¹ := by
          rw [hβe]
          group
        rw [this]
        exact B.inv_mem (B.mul_mem (B.inv_mem hβ₀) hβ)
      refine ⟨⟨α * α₀⁻¹, hcA, hcB⟩, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · exact Subtype.ext hβe.symm
      · apply Subtype.ext
        show α * α₀⁻¹ * α₀ = α
        group
  have e : (B × A) ≃ Σ x : dc A B g, {p // φ p = x} := (Equiv.sigmaFiberEquiv φ).symm
  have h4 : Nat.card (B × A) = Nat.card (dc A B g) * Nat.card (A ⊓ cj g B : Subgroup Γ) := by
    rw [Nat.card_congr e, Nat.card_sigma]
    simp only [fib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  rw [← h4, Nat.card_prod, mul_comm]

theorem sum_dc {A B : Subgroup Γ} {a b : Γ → ℂ} (hA : IsClassOn A a) (hB : IsClassOn B b)
    (g : Γ) [DecidablePred (· ∈ dc A B g)] :
    (∑ x, if x ∈ dc A B g then mS A B a b x else 0) = (Nat.card (dc A B g) : ℂ) * mS A B a b g := by
  classical
  have h1 : ∀ x, (if x ∈ dc A B g then mS A B a b x else 0) =
      if x ∈ dc A B g then mS A B a b g else 0 := by
    intro x
    by_cases hx : x ∈ dc A B g
    · obtain ⟨β, hβ, α, hα, rfl⟩ := hx
      rw [if_pos ⟨β, hβ, α, hα, rfl⟩, if_pos ⟨β, hβ, α, hα, rfl⟩, mS_inv hA hB g hβ hα]
    · rw [if_neg hx, if_neg hx]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

theorem mackeyIp : ReciprocityTheory.Ty.Fin.St.MackeyIp := by
  classical
  intro Γ _ _ A B a b hA hB R _ g h1 h2
  have cardC : ∀ y, (Nat.card (A ⊓ cj y B : Subgroup Γ) : ℂ) ≠ 0 := fun y =>
    Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have cardA : (Nat.card A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have cardB : (Nat.card B : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hvan : ∀ x, (∀ r, x ∉ dc A B (g r)) → mS A B a b x = 0 := by
    intro x hx
    rcases h2 x with ⟨r, β, hβ, α, hα, e⟩ | ⟨y, ⟨β, hβ, α, hα, rfl⟩, hy⟩
    · exact absurd ⟨β, hβ, α, hα, e⟩ (hx r)
    · rw [mS_inv hA hB y hβ hα]
      rw [ip_inter] at hy
      exact (mul_eq_zero.1 hy).resolve_left (inv_ne_zero (cardC y))
  have hdisj : ∀ x r r', x ∈ dc A B (g r) → x ∈ dc A B (g r') → r = r' := by
    rintro x r r' ⟨β, hβ, α, hα, rfl⟩ ⟨β', hβ', α', hα', e⟩
    refine h1 r r' ⟨β'⁻¹ * β, B.mul_mem (B.inv_mem hβ') hβ, α * α'⁻¹, A.mul_mem hα (A.inv_mem hα'), ?_⟩
    have : g r' = β'⁻¹ * (β' * g r' * α') * α'⁻¹ := by group
    rw [this, ← e]
    group
  have hsum : ∀ x, mS A B a b x = ∑ r, if x ∈ dc A B (g r) then mS A B a b x else 0 := by
    intro x
    by_cases hx : ∃ r, x ∈ dc A B (g r)
    · obtain ⟨r, hr⟩ := hx
      rw [Fintype.sum_eq_single r, if_pos hr]
      intro r' hne
      exact if_neg fun q => hne (hdisj x r r' hr q).symm
    · push_neg at hx
      rw [hvan x hx]
      simp
  rw [ip_ind, Finset.sum_congr rfl fun x _ => hsum x, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sum_dc hA hB, ip_inter]
  have hc : (Nat.card (dc A B (g r)) : ℂ) * (Nat.card (A ⊓ cj (g r) B : Subgroup Γ) : ℂ) =
      (Nat.card A : ℂ) * (Nat.card B : ℂ) := by
    exact_mod_cast card_dc A B (g r)
  have := cardC (g r)
  field_simp
  linear_combination (mS A B a b (g r)) * hc

end GlobalTheory.CompanionTheory.MackeyFn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHCompEqSmul
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CrystallineSemistableComparison CrystallineSemistableComparison.Tw CrystallineSemistableComparison.Ls

namespace GlobalTheory.CompanionTheory.LsRho

variable {W : Type} [CommRing W]

theorem mapH_eq_self {K : Cx.{1} W} (φ : Cx.Hom K K (RingHom.id W)) (n : ℕ)
    (h : ∀ x, φ.f n x = x) (u : K.H n) : φ.mapH n u = u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem mapH_of_comp {K L P : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L P (RingHom.id W))
    (χ : Cx.Hom K P (RingHom.id W)) (n : ℕ) (h : ∀ x, χ.f n x = ψ.f n (φ.f n x)) (u : K.H n) :
    χ.mapH n u = ψ.mapH n (φ.mapH n u) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem mapH_comp_eq_smul {K L : Cx.{1} W} (φ : Cx.Hom K L (RingHom.id W)) (ψ : Cx.Hom L K (RingHom.id W))
    (s : W) (n : ℕ) (h : ∀ x, ψ.f n (φ.f n x) = s • x) (u : K.H n) :
    ψ.mapH n (φ.mapH n u) = s • u := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  exact congrArg Submodule.Quotient.mk (Subtype.ext (h z.1))

theorem kill (l : ℕ) (K : Cx.{1} W) (j n : ℕ) (x : (qsys l K j).M n) : ((l : W) ^ n) • x = 0 := by
  change ((l : W) ^ n) • (x : (quo l K n).H j) = 0
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : ((l : W) ^ n) • z = 0 := by
    refine Subtype.ext ?_
    change ((l : W) ^ n) • z.1 = 0
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ z.1
    rw [← hw]
    change Submodule.Quotient.mk (((l : W) ^ n) • w) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  rw [← Submodule.Quotient.mk_smul, hz]
  rfl

end GlobalTheory.CompanionTheory.LsRho

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumCongrInvarianceStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_gauss_sum_congr_invariance : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ), (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (h D g g' : Matrix (Fin n) (Fin n) R) (S E p p' : Matrix (Fin m) (Fin m) R), g * g' = 1 → g' * g = 1 → p * p' = 1 → p' * p = 1 → cT σ g * h * g = D → cT σ p * S * p = E → (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) = ∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegCov.gauss_cov | exact GlobalTheory.CompanionTheory.SiegCov.gauss_cov | (intros; apply GlobalTheory.CompanionTheory.SiegCov.gauss_cov <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumDiagonalFactorStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_gauss_sum_diagonal_factor : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R), (∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k (Matrix.diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (Matrix.diagonal E) * y)))) = ∏ i : Fin n, ∏ l : Fin m, ∑ w : R ⧸ lev ϖ k, χ (Ideal.Quotient.mk (lev ϖ k) (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  first | exact @GlobalTheory.CompanionTheory.GaussProd.gauss_prod | exact GlobalTheory.CompanionTheory.GaussProd.gauss_prod | (intros; apply GlobalTheory.CompanionTheory.GaussProd.gauss_prod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityReductionDiagonalProdStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_reduction_diagonal_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod | exact GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.NuDiag.nuAt_eq_prod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMulStatement
section
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counting_bound_alt : CountBd := by
  first | exact @GlobalTheory.CompanionTheory.MassCount.countBd | exact GlobalTheory.CompanionTheory.MassCount.countBd | (intros; apply GlobalTheory.CompanionTheory.MassCount.countBd <;> assumption)
end

