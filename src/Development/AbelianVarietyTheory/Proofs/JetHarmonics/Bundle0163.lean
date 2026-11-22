import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0149
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0037
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0162
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0208
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0156
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0154
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0089
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
import Formalism.HermitianCurvature.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveGridLiftGridOfLayoutNormaliserBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0229
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0105
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroEnergyLeOfEigenSum
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem levelZero_energy_le_of_eigen_sum :
    GlobalTheory.HCXi.BesselXiIntegrable → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (s : ℂ) (nn : ℝ → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (s = 1 ∨ s = -1) → B.AB k r ≤ A → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) → (∀ y : ℝ, ∏ t, (|y + lam t| + (d : ℝ)) ≤ nn y) → ∀ w : List (Bool × ℝ), (C7.principalHermitianLattice D s w F).re ≤ (w.map fun l => nn l.2).prod * (B.beta D F F).re := by
  intro hXi k r Wp Wq _ _ _ _ _ _ D lam d A s nn F hs hA hex hnn w
  obtain ⟨N₀, Fi, ν, hν, hcl, hev, hF⟩ := hex
  obtain ⟨σ, hσs, hσ⟩ : ∃ σ : ℝ, s = (σ : ℂ) ∧ |σ| = 1 := by
    rcases hs with h | h
    · exact ⟨1, by simp [h], by simp⟩
    · exact ⟨-1, by simp [h], by simp⟩
  have h5 : ∀ i, B.InCC A 5 (Fi i) := fun i => (hcl i).2 5
  set e : Fin N₀ → ℝ → ℝ := fun i Y => ∏ t, (Y + lam t + (ν i t : ℝ)) with he
  set c : Fin N₀ → Bool × ℝ → ℝ := fun i a => σ * e i a.2 with hc
  have hF1 : ∀ g ∈ B.GV k r, F g = ∑ i ∈ Finset.univ, (1 : ℂ) • Fi i g := by
    intro g hg; simpa using hF g hg
  have hfold := GlobalTheory.foldr_capelli_sum_eigen k r Wp Wq N₀ Fi (fun i Y => ((e i Y : ℝ) : ℂ)) s F (fun i => (hcl i).1)
    (fun i Y g hg => hev i Y g hg) hF w
  have e1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ _ (fun _ => 1) Fi _ F hA h5 hfold hF1
  have e2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) Finset.univ Finset.univ (fun _ => 1) (fun _ => 1) Fi F F hA h5
    hF1 hF1
  have hcast : ∀ i, (w.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((w.map (c i)).prod : ℝ) : ℂ) := by
    intro i
    have : ∀ v : List (Bool × ℝ),
        (v.map fun a => s * ((e i a.2 : ℝ) : ℂ)).prod = (((v.map (c i)).prod : ℝ) : ℂ) := by
      intro v
      induction v with
      | nil => simp
      | cons a v ih =>
        rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, hσs]
        simp only [hc, Complex.ofReal_mul]
    exact this w
  have key := gram_blockDiagonal_energy_bound (Fin N₀) (Bool × ℝ) (fun i j => B.beta D (Fi i) (Fi j)) c w
    (fun l => nn l.2) ?_ ?_ ?_
  · unfold C7.principalHermitianLattice
    rw [e1, e2]
    simp only [star_one, mul_one, one_mul, hcast]
    exact key
  · intro S
    have e3 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) S S (fun _ => 1) (fun _ => 1) Fi
      (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g) hA h5
      (fun _ _ => rfl) (fun _ _ => rfl)
    have e4 := GlobalTheory.BetaPos.beta_self_re_nonneg k r Wp Wq D (fun g => ∑ i ∈ S, (1 : ℂ) • Fi i g)
    rw [e3] at e4
    simpa only [star_one, mul_one, one_mul] using e4
  · intro i j a _ hne
    have hne' : e i a.2 ≠ e j a.2 := fun h => hne (by simp only [hc, h])
    have hsym := GlobalTheory.beta_capelli_symm_of_bessel hXi k r Wp Wq D a.2 A (Fi i) (Fi j) hA (hcl i) (hcl j)
    have h1 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => ((e i a.2 : ℝ) : ℂ)) (fun _ => 1) Fi (Q.CV k r (a.2 : ℂ) (Fi i)) (Fi j) hA h5
      (fun g hg => by rw [Finset.sum_singleton]; exact hev i a.2 g hg) (fun g _ => by simp)
    have h2 := GlobalTheory.beta_finset_sum_smul_of_bessel hXi k r Wp Wq D A (Fin N₀) {i} {j}
      (fun _ => 1) (fun _ => ((e j a.2 : ℝ) : ℂ)) Fi (Fi i) (Q.CV k r (a.2 : ℂ) (Fi j)) hA h5
      (fun g _ => by simp) (fun g hg => by rw [Finset.sum_singleton]; exact hev j a.2 g hg)
    simp only [Finset.sum_singleton, star_one, mul_one, one_mul,
      Complex.star_def, Complex.conj_ofReal] at h1 h2
    rw [h1, h2] at hsym
    have hcc : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne')
    have h0 : ((e i a.2 : ℂ) - (e j a.2 : ℂ)) * B.beta D (Fi i) (Fi j) = 0 := by
      rw [sub_mul, hsym, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left hcc
  · intro i a _
    refine le_trans ?_ (hnn a.2)
    simp only [hc, he, abs_mul, hσ, one_mul, Finset.abs_prod]
    refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun t _ => (abs_add_le _ _).trans ?_)
    have : |(ν i t : ℝ)| ≤ (d : ℝ) := by exact_mod_cast hν i t
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelZeroPairingCompactApproximantsCauchyBound
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelZeroApprox

theorem ccle_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ} {m : ℕ}
    {F F' : B.Mat k r → E} {c c' : ℝ} (h : B.CCle A m F c) (h' : B.CCle A m F' c') :
    B.CCle A m (F - F') (c + c') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rw [e] at h1
  simpa using h1

theorem ckOn_sub {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {U : Set (B.Mat k r)}
    {F F' : B.Mat k r → E} (h : B.CkOn m U F) (h' : B.CkOn m U F') : B.CkOn m U (F - F') := by
  have h1 := Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add h (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul (-1 : ℂ) h')
  have e : (fun g => F g + (fun g => (-1 : ℂ) • F' g) g) = F - F' := by
    funext g; simp [sub_eq_add_neg]
  rwa [e] at h1

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem ckOn_bump_smul {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H : B.Mat k r → E} (h : B.CkOn ⊤ (B.GV k r) H) (n : ℕ) :
    B.CkOn ⊤ (B.GV k r) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H g) := by
  have hcs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) := by
    have e : (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) = fun g => 1 - Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
      funext g
      rw [Formalism.FourierDecayAlt.P.JCx2.pdPsi, sub_sub_cancel]
      rfl
    rw [e]
    exact contDiff_const.sub (Formalism.FourierDecayAlt.P.JCx2.pd_psi_cd _)
  exact Formalism.FourierDecayAlt.P.JCx2.pd_smooth_smul hcs h
end

theorem threshold (k r N l : ℕ) (hl : l ≤ N) :
    B.AB k r + 1 + 2 * ((r : ℝ) + 1) * ((5 + l * (2 * r + k + 1) : ℕ) : ℝ) ≤
      20 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) := by
  unfold B.AB
  push_cast
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hlN : (l : ℝ) ≤ N := by exact_mod_cast hl
  set ρ : ℝ := (r : ℝ) + 1 with hρ
  set ν : ℝ := 2 * (r : ℝ) + k + 1 with hν
  have hρ1 : 1 ≤ ρ := by linarith
  have hν1 : 1 ≤ ν := by linarith
  have hkr : (k : ℝ) + r ≤ ν := by linarith
  have h4 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have h2 : ν ≤ ν ^ 2 := le_self_pow₀ hν1 (by norm_num)
  have h3 : ν ≤ ν ^ 3 := le_self_pow₀ hν1 (by norm_num)
  have hS : (l : ℝ) * ν + ν ≤ N * ν ^ 2 + ν ^ 3 :=
    add_le_add (mul_le_mul hlN h2 (by linarith) (by linarith)) h3
  have hlν : 0 ≤ (l : ℝ) * ν := by positivity
  have h5 : 20 * ρ * ((l : ℝ) * ν + ν) ≤ 20 * ρ ^ 4 * (N * ν ^ 2 + ν ^ 3) :=
    mul_le_mul (by linarith) hS (by linarith) (by positivity)
  refine le_trans ?_ h5
  have a1 : ((k : ℝ) + r) * ρ ≤ ν * ρ := mul_le_mul_of_nonneg_right hkr (by linarith)
  have a2 : ρ ≤ ν * ρ := le_mul_of_one_le_left (by linarith) hν1
  have a3 : 0 ≤ ρ * ((l : ℝ) * ν) := by positivity
  nlinarith

theorem beta_approx : ∃ Cc : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (χ : ℝ → ℝ) (f : B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ) (N : ℕ), C6.IsCut0 χ → B.CkOn ⊤ (B.GV k r) f → (∀ m : ℕ, B.InCC A m f) → Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A → w.length ≤ N → ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → 0 < ε₂ → Tendsto (fun n : ℕ => B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₂ g))) atTop (𝓝 (B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((D.cutF Bs χ f ε₁)) w) (D.cutF Bs χ f ε₂))) ∧ ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g)) w) ((fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g) - (fun g : B.Mat k r => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((m : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • D.cutF Bs χ f ε₁ g))‖ ≤ K / ((n : ℝ) + 1) := by
  refine ⟨20, ?_⟩
  intro k r Wp Wq _ _ _ _ _ _ Bs s w χ f A N hχ hf hfA hA hw ε₁ ε₂ h₁ h₂
  have hth := (threshold k r N w.length hw).trans hA
  obtain ⟨K₁, hK₁, hH₁, hX₁⟩ := GlobalTheory.T.cutoff_compact_approximants_converge_decay_class k r Wp Wq Bs χ f A ε₁ (B.AB k r) _ hχ h₁ hf hfA hth
  obtain ⟨K₂, hK₂, hH₂, hX₂⟩ := GlobalTheory.T.cutoff_compact_approximants_converge_decay_class k r Wp Wq Bs χ f A ε₂ (B.AB k r) _ hχ h₂ hf hfA hth
  obtain ⟨C, hC, hbd⟩ := GlobalTheory.T.capelliProduct_levelZeroPairing_norm_le k r Wp Wq Bs s w (B.AB k r) le_rfl
  have hsq := GlobalTheory.T.capelliProduct_levelZeroPairing_sesquilinear k r Wp Wq Bs s w (B.AB k r) le_rfl 1
  have hc₁ := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hχ hf ε₁
  have hx₁ := ckOn_bump_smul hc₁
  have lo : ∀ {F : B.Mat k r → (Wq →L[ℂ] Wp)} {c : ℝ},
      B.CCle (B.AB k r) (5 + w.length * (2 * r + k + 1)) F c → B.CCle (B.AB k r) 5 F c :=
    fun h => Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (Nat.le_add_right _ _) h
  generalize D.cutF Bs χ f ε₁ = H₁ at *
  generalize D.cutF Bs χ f ε₂ = H₂ at *
  set X₁ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₁ g with hX₁def
  set X₂ : ℕ → B.Mat k r → (Wq →L[ℂ] Wp) := fun n g => ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ) • H₂ g with hX₂def
  set b : (B.Mat k r → (Wq →L[ℂ] Wp)) → (B.Mat k r → (Wq →L[ℂ] Wp)) → ℂ := fun X Z =>
    B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) X w) Z with hb
  change ∀ n, B.CCle _ _ (X₁ n) K₁ ∧ B.CCle _ _ (X₁ n - H₁) _ at hX₁
  change ∀ n, B.CCle _ _ (X₂ n) K₂ ∧ B.CCle _ _ (X₂ n - H₂) _ at hX₂
  change ∀ n, B.CkOn _ _ (X₁ n) at hx₁
  change ∀ X Z c c', _ → _ → _ → ‖b X Z‖ ≤ _ at hbd
  change ∀ X X' Z Z', _ → _ → _ → _ → _ → _ → b (X + (1 : ℂ) • X') Z = b X Z + 1 * b X' Z ∧
    b X (Z + (1 : ℂ) • Z') = b X Z + (starRingEnd ℂ) 1 * b X Z' at hsq
  change Tendsto (fun n => b (X₁ n) (X₂ n)) atTop (𝓝 (b H₁ H₂)) ∧
    ∃ K : ℝ, ∀ n m : ℕ, n ≤ m → ‖b (X₁ n - X₁ m) (X₁ n - X₁ m)‖ ≤ K / ((n : ℝ) + 1)
  clear_value X₁ X₂ b
  constructor
  · have key : ∀ n : ℕ, ‖b (X₁ n) (X₂ n) - b H₁ H₂‖ ≤ 2 * C * K₁ * K₂ * (1 / ((n : ℝ) + 1)) := by
      intro n
      have hd := ckOn_sub (hx₁ n) hc₁
      have e1 := (hsq H₁ (X₁ n - H₁) (X₂ n) (X₂ n) hc₁ hd ⟨_, hH₁⟩ ⟨_, (hX₁ n).2⟩ ⟨_, lo (hX₂ n).1⟩
        ⟨_, lo (hX₂ n).1⟩).1
      have e2 := (hsq H₁ H₁ H₂ (X₂ n - H₂) hc₁ hc₁ ⟨_, hH₁⟩ ⟨_, hH₁⟩ ⟨_, lo hH₂⟩ ⟨_, lo (hX₂ n).2⟩).2
      simp only [one_smul, add_sub_cancel, one_mul, map_one] at e1 e2
      have b1 := hbd _ _ _ _ hd (hX₁ n).2 (lo (hX₂ n).1)
      have b2 := hbd _ _ _ _ hc₁ hH₁ (lo (hX₂ n).2)
      have e : b (X₁ n) (X₂ n) - b H₁ H₂ = b (X₁ n - H₁) (X₂ n) + b H₁ (X₂ n - H₂) := by
        rw [e1, e2]; ring
      rw [e]
      refine (norm_add_le _ _).trans ((add_le_add b1 b2).trans (le_of_eq ?_))
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) key ?_
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * C * K₁ * K₂)
  · refine ⟨4 * C * K₁ * K₁, fun n m hnm => ?_⟩
    have hd := ckOn_sub (hx₁ n) (hx₁ m)
    have c1 := ccle_sub (hX₁ n).2 (hX₁ m).2
    rw [sub_sub_sub_cancel_right] at c1
    have hle : K₁ / ((m : ℝ) + 1) ≤ K₁ / ((n : ℝ) + 1) := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hnm
      exact div_le_div_of_nonneg_left hK₁ (by positivity) (by linarith)
    have c2 := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c c1 (add_le_add_right hle (K₁ / ((n : ℝ) + 1)))
    have c3 := ccle_sub (hX₁ n).1 (hX₁ m).1
    refine (hbd _ _ _ _ hd c2 (lo c3)).trans (le_of_eq ?_)
    ring

end GlobalTheory.LevelZeroApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedOfMemBoundedFactorsMonoid
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.BoundedFactors

theorem star_prod_ofFn {A : Type} [Ring A] [StarRing A] {r : ℕ} (f g : Fin r → A)
    (h : ∀ l, star (f l) = g l) (hc : ∀ l m, Commute (g l) (g m)) :
    star (List.ofFn f).prod = (List.ofFn g).prod := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun l => h _) (fun l m => hc _ _)]
    refine (Commute.list_prod_left _ _ ?_).eq
    intro x hx
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hc _ _

theorem star_phase {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
    (hc : ∀ l, star (L.c l) = L.cb l) (hi : ∀ l, star (L.ci l) = L.cbi l) :
    star (L.Drb * L.Dri) = L.Dr * L.Drbi := by
  have h1 : star L.Drb = L.Dr :=
    star_prod_ofFn _ _ (fun l => by rw [← hc l, star_star])
      (fun l m => L.fns_comm _ (by simp) _ (by simp))
  have h2 : star L.Dri = L.Drbi :=
    star_prod_ofFn _ _ hi (fun l m => L.fns_comm _ (by simp) _ (by simp))
  rw [star_mul, h1, h2]
  refine (Commute.list_prod_left _ _ ?_).eq
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hy
  exact L.fns_comm _ (by simp) _ (by simp)

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem hsInner_self_norm (A : Wq →L[ℂ] Wp) : ‖B.hsInner A A‖ = ‖B.hsVec A‖ ^ 2 := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K]
  simp

theorem hsInner_norm_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsVec A‖ * ‖B.hsVec C‖ := by
  unfold B.hsInner
  rw [mul_comm]
  exact norm_inner_le_norm _ _

theorem ptB_of_star_mul_self (b : RA P Bs) (ha : PtAdj P Bs b) (hb : PtB P Bs (star b * b)) : PtB P Bs b := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun Φ x hx => ?_⟩
  have h1 := ha Φ (b.1 Φ) x hx
  have h2 : nv ((star b).1 (b.1 Φ)) x ≤ C * nv Φ x := h Φ x hx
  have h3 : nv (b.1 Φ) x ^ 2 ≤ nv Φ x * nv ((star b).1 (b.1 Φ)) x := by
    unfold nv
    rw [← hsInner_self_norm, h1]
    exact hsInner_norm_le _ _
  have h0 : 0 ≤ nv Φ x := norm_nonneg _
  have h4 : nv (b.1 Φ) x ^ 2 ≤ (Real.sqrt C * nv Φ x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) h0) two_ne_zero).1 h4

theorem ptB_star (b : RA P Bs) (ha : PtAdj P Bs b) (hb : PtB P Bs b) : PtB P Bs (star b) := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨C, hC, fun Ψ x hx => ?_⟩
  have h1 := ha ((star b).1 Ψ) Ψ x hx
  have h2 := h ((star b).1 Ψ) x hx
  have h3 : nv ((star b).1 Ψ) x ^ 2 ≤ nv (b.1 ((star b).1 Ψ)) x * nv Ψ x := by
    unfold nv
    rw [← hsInner_self_norm, ← h1]
    exact hsInner_norm_le _ _
  have h0 : 0 ≤ nv Ψ x := norm_nonneg _
  have h0' : 0 ≤ nv ((star b).1 Ψ) x := norm_nonneg _
  rcases h0'.eq_or_lt with he | hp
  · rw [← he]; exact mul_nonneg hC h0
  · have h4 : nv ((star b).1 Ψ) x * nv ((star b).1 Ψ) x ≤ nv ((star b).1 Ψ) x * (C * nv Ψ x) := by
      nlinarith [mul_le_mul_of_nonneg_right h2 h0]
    exact le_of_mul_le_mul_left h4 hp

end

theorem ptB_of_mem_bmon : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ b ∈ bmon d, PtB P Bs b := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN
  obtain ⟨⟨-, -, hRel, -, hc, hi, -⟩, -⟩ := GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN
  have hκ := GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN
  obtain ⟨⟨h1, hmul⟩, hζi, hζbi, hD1, hD2, hD3, hD4, -⟩ := GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN
  have hS := GlobalTheory.T.radialRaisingOperators_pointwiseAdjointPair Wp Wq P Bs X μ L st l0 d hD hN
  have hSb : ∀ l ∈ Finset.Icc 1 (P.k - 1), PtB P Bs (d.SS l) := fun l hl =>
    ptB_of_star_mul_self _ (hS l hl) (by rw [hRel.2.2.2.2.2 l hl]; exact (hκ _).2)
  have hSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), PtB P Bs (star (d.SS l)) := fun l hl =>
    ptB_star _ (hS l hl) (hSb l hl)
  intro b hb
  induction hb using Submonoid.closure_induction with
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul _ _ hx hy
  | mem x hx =>
    rcases hx with ((hx | ⟨f, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩
    · rcases hx with rfl | rfl | rfl | rfl
      exacts [hζi, hζbi, hD1, hD2]
    · exact (hκ f).2
    · exact hmul _ _ hD3 (hSb l (by simpa using hl))
    · show PtB P Bs (star (d.L.Drb * d.L.Dri * d.SS l))
      rw [star_mul, star_phase d.L hc hi]
      exact hmul _ _ (hSs l (by simpa using hl)) hD4

end GlobalTheory.HatNF.BoundedFactors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TopVectorCutoffEqAndVanishStatement
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topVector_cutoff_eq_and_vanish : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (χ : ℝ → ℝ) (δ ε : ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CutWord P p.l0 w → C6.IsCut0 χ → (∀ x, x < δ → χ x = 0) → 0 < ε → B.CkOn ⊤ (B.GV P.k P.r) F → (ε < TBB.Gp p (TBB.bigPt P.r c) → tv p (D.cutF p.T.base χ F ε) w c = tv p F w c) ∧ (TBB.Gp p (TBB.bigPt P.r c) < δ * ε → tv p (D.cutF p.T.base χ F ε) w c = 0) ∧ (TBB.Gp p (TBB.bigPt P.r c) ≤ 0 → tv p F w c = 0) := by
  first | exact @GlobalTheory.TopVec.tv_cutF | exact GlobalTheory.TopVec.tv_cutF | (intros; apply GlobalTheory.TopVec.tv_cutF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveGridLiftGridOfLayoutNormaliserBoundStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ), (∀ y, 0 < nn y) → ((∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧ N * (2 * P.r + 1) ≤ Y.card ∧ ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1)) → (∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (M.qC P (y : ℂ)).re) → 0 ≤ Λ → Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2 → TBBx5.WaveGrid p nn Y Λ K N ∧ TBBx5.LiftGrid p nn Y Λ K N := by
  first | exact @GlobalTheory.GridsFromLayout.main | exact GlobalTheory.GridsFromLayout.main | (intros; apply GlobalTheory.GridsFromLayout.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WithRightAction
section
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace GlobalTheory.WithRightAction

noncomputable def withRight {k r : ℕ} {Wp Wq Wq' : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq']
    (Bs : B.RealPlaceData k r Wp Wq) (π'' : B.Mat k r → (Wq' →L[ℂ] Wq')) (u' : ℕ → ℝ)
    (h : Q.IsType k r Bs.z' π'' u') : B.RealPlaceData k r Wp Wq' :=
  { z := Bs.z, z' := Bs.z', π := Bs.π, π' := π'', μG := Bs.μG, μW := Bs.μW, μN := Bs.μN, μW' := Bs.μW',
    μsec := Bs.μsec, χ := Bs.χ, k_pos := Bs.k_pos, z_mem := Bs.z_mem, z'_mem := Bs.z'_mem, T_pos := Bs.T_pos,
    T'_pos := Bs.T'_pos, π_rep := Bs.π_rep, π'_rep := h.2.1, π_unitary := Bs.π_unitary, π'_unitary := h.2.2.2.1,
    π_cont := Bs.π_cont, π'_cont := h.2.2.1, haarG := Bs.haarG, haarW := Bs.haarW, haarN := Bs.haarN,
    haarW' := Bs.haarW', sec := Bs.sec, χ_smooth := Bs.χ_smooth, χ_supp := Bs.χ_supp, χ_int := Bs.χ_int }

theorem exists_place_other_right_type : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Wq' : Type) [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq'] (p : KB.Pl P Wp Wq) (u u' : ℕ → ℝ) (π'' : B.Mat P.k P.r → (Wq' →L[ℂ] Wq')) (l0 : ℕ), Q.IsPlace (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) p.T.base.z p.T.base.z' p.T.base.π π'' → 1 ≤ l0 → l0 ≤ P.k → ∃ q : KB.Pl (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) Wp Wq', q.l0 = l0 ∧ q.T.base.z = p.T.base.z ∧ q.T.base.z' = p.T.base.z' ∧ q.T.base.π = p.T.base.π ∧ q.T.base.π' = π'' ∧ q.ν' = p.ν' ∧ q.m₀ = p.m₀ ∧ KB.InDDplus2 (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) q.l0 q.T.base Cb q.Θ := by
  obtain ⟨Cb, hCb, hTL⟩ := Formalism.FourierDecayAlt.P.top_lift_exists
  refine ⟨Cb, hCb, ?_⟩
  intro P Wp _ _ _ Wq _ _ _ Wq' _ _ _ p u u' π'' l0 hPl hl1 hl2
  obtain ⟨T, h1, h2, h3, h4, hN⟩ := Formalism.FourierDecayAlt.P.exists_normalized_tower P.k P.r Wp Wq'
    (withRight p.T.base π'' u' hPl.2.2.2.2.2.2)
  change T.base.z = p.T.base.z at h1
  change T.base.z' = p.T.base.z' at h2
  change T.base.π = p.T.base.π at h3
  change T.base.π' = π'' at h4
  have hPT : Q.IsPlace (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base.z T.base.z' T.base.π T.base.π' := by
    rw [h1, h2, h3, h4]; exact hPl
  have hF : D.IsBaseFrame T.base p.ν' p.m₀ := by
    have := p.hF
    unfold D.IsBaseFrame at this ⊢
    rw [h1, h2]; exact this
  obtain ⟨-, μ, -, -, ⟨-, hμ, -⟩, -⟩ := p.hΘ
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPT
  obtain ⟨L, st, g1, g2, g3, g4, g5, g6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPT X l0
  have hD : P5.IsData (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base.z T.base.z' T.base.π T.base.π' X μ L st l0 :=
    ⟨hPT, hμ, g1, g2, g3, g4, g5, g6⟩
  obtain ⟨f1, f2, f3⟩ := Formalism.FourierDecayAlt.P.HaarMassHermitianCurvature.frameVec_facts T.base p.ν' p.m₀ hF
  obtain ⟨Θ, hI, hC⟩ := hTL Wp Wq' (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par) T.base X μ L st l0 hl1 hl2 hD
  obtain ⟨TP⟩ := Formalism.FourierDecayAlt.P.type_projectors_exist Wp Wq' (⟨P.k, P.r, P.T, P.T', u, u'⟩ : M.Par)
    T.base.z T.base.z' T.base.π T.base.π' (p.m₀.mulVec p.ν') hPT f1 f2 f3
  exact ⟨⟨l0, T, p.ν', p.m₀, Θ, TP, ⟨hl1, hl2, p.hl.2.2⟩, hN, hF, hPT, ⟨X, μ, L, st, hD, hI⟩⟩,
    rfl, h1, h2, h3, h4, rfl, rfl, hC⟩

end GlobalTheory.WithRightAction
end

