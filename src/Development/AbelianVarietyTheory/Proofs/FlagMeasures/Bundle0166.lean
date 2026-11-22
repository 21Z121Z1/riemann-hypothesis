import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SymmetricKMapEqZeroOfVminusSlices
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n j : ℕ}

def sliceIns (α' : Fin j → Fin n × Fin n) (m : Arr V n 1) : Arr V n (j + 1) :=
  WithLp.toLp 2 (fun α : Fin (j + 1) → Fin n × Fin n =>
    if Fin.tail α = α' then m (fun _ => α 0) else 0)

theorem slice_sliceIns (α' β' : Fin j → Fin n × Fin n) (m : Arr V n 1) :
    sliceLin V n β' (sliceIns α' m) = if β' = α' then m else 0 := by
  apply indexArray_ext
  intro β
  rw [firstPositionSlice_apply]
  have hβ : (fun _ : Fin 1 => β 0) = β := by
    funext i
    rw [Fin.fin_one_eq_zero i]
  simp only [sliceIns, PiLp.toLp_apply, Fin.tail_cons, Fin.cons_zero]
  split_ifs with h
  · rw [hβ]
  · rfl

theorem sliceIns_mem {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {α' : Fin j → Fin n × Fin n} (hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2) {m : Arr V n 1}
    (hm : m ∈ arrV0 ε E u 1) : sliceIns α' m ∈ arrV0 ε E u (j + 1) := by
  rw [mem_admissibleArrays]
  intro α
  by_cases ht : Fin.tail α = α'
  · have hv : (sliceIns α' m) α = m (fun _ => α 0) := by simp [sliceIns, ht]
    rw [hv]
    by_cases h0 : ε (α 0).1 ≠ ε (α 0).2
    · have hall : ∀ i, ε (α i).1 ≠ ε (α i).2 := by
        intro i
        cases i using Fin.cases with
        | zero => exact h0
        | succ k =>
          have hk := hα k
          rw [← ht] at hk
          simpa [Fin.tail] using hk
      rw [if_pos hall]
      exact admissibleArrays_apply_mem hm _
    · rw [admissibleArrays_apply_eq_zero hm _ (fun h => h0 (h 0))]
      split_ifs <;> exact Submodule.zero_mem _
  · have hv : (sliceIns α' m) α = 0 := by simp [sliceIns, ht]
    rw [hv]
    split_ifs <;> exact Submodule.zero_mem _

theorem slice_mem_highest_jets {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n (j + 1)} (hF : F ∈ arrV0 ε E u (j + 1)) (α' : Fin j → Fin n × Fin n) :
    sliceLin V n α' F ∈ arrV0 ε E u 1 := by
  rw [mem_admissibleArrays]
  intro β
  rw [firstPositionSlice_apply]
  split_ifs with h
  · exact admissibleArrays_apply_mem hF _
  · rw [admissibleArrays_apply_eq_zero hF _ (fun h' => h (fun i => by rw [Fin.fin_one_eq_zero i]; simpa using h' 0))]
    exact Submodule.zero_mem _

theorem slice_eq_zero_of_compact {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n (j + 1)} (hF : F ∈ arrV0 ε E u (j + 1)) (α' : Fin j → Fin n × Fin n)
    (hα : ¬ ∀ i, ε (α' i).1 ≠ ε (α' i).2) : sliceLin V n α' F = 0 := by
  apply indexArray_ext
  intro β
  rw [firstPositionSlice_apply, admissibleArrays_apply_eq_zero hF _ (fun h => hα (fun i => by simpa using h i.succ))]
  rfl

theorem permute_mem_highest_jets {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    {F : Arr V n j} (hF : F ∈ arrV0 ε E u j) (s : Equiv.Perm (Fin j)) :
    permArr V n s F ∈ arrV0 ε E u j := by
  rw [mem_admissibleArrays]
  intro α
  rw [permutePositions_apply]
  split_ifs with h
  · exact admissibleArrays_apply_mem hF _
  · rw [admissibleArrays_apply_eq_zero hF _ (fun h' => h (fun i => by simpa using h' (s.symm i)))]
    exact Submodule.zero_mem _

private theorem finiteDimensional_arrV0_of_finiteDimensional_kSpan (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V) (h : FiniteDimensional ℂ (kSpan ε E u)) :
    FiniteDimensional ℂ (arrV0 ε E u j) := by
  let ψ : arrV0 ε E u j →ₗ[ℂ] ((Fin j → Fin n × Fin n) → kSpan ε E u) :=
    LinearMap.pi fun α => LinearMap.codRestrict (kSpan ε E u)
      ((LinearMap.proj α ∘ₗ arrOf V n j) ∘ₗ (arrV0 ε E u j).subtype)
      (fun F => by simpa [arrOf] using admissibleArrays_apply_mem F.2 α)
  refine Module.Finite.of_injective ψ ?_
  intro F G hFG
  apply Subtype.ext
  apply indexArray_ext
  intro α
  have h1 := congrArg Subtype.val (congrFun hFG α)
  simpa [ψ, arrOf] using h1

private theorem permArr_inv_permArr (s : Equiv.Perm (Fin j)) (F : Arr V n j) : permArr V n s⁻¹ (permArr V n s F) = F := by
  apply indexArray_ext
  intro α
  rw [permutePositions_apply, permutePositions_apply]
  simp

end

theorem jet_map_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V) (j : ℕ), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ T : Arr V n (j + 1) →ₗ[ℂ] V, (∀ F ∈ arrV0 ε E u (j + 1), T F ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ F ∈ arrV0 ε E u (j + 1), T (arrE E (j + 1) c d F) = E c d (T F)) → (∀ F ∈ arrV0 ε E u (j + 1), ∀ s : Equiv.Perm (Fin (j + 1)), T (permArr V n s F) = T F) → (∀ F ∈ arrV0 ε E u (j + 1), (∀ α', sliceLin V n α' F ∈ Vminus ε E (LamOf ε lam) u) → T F = 0) → ∀ F ∈ arrV0 ε E u (j + 1), T F = 0 := by
  intro V _ _ n ε E lam g u j hgl hun hhi hfd hgap hg T hT hE hS hM
  have hsplit := typesSplit V n ε E (LamOf ε lam) u hgl hun hhi hfd
  have hstab := admissibleArrays_invariant ε E u (j + 1)
  let K : Submodule ℂ (Arr V n (j + 1)) := arrV0 ε E u (j + 1) ⊓ LinearMap.ker T
  have memK : ∀ G, G ∈ arrV0 ε E u (j + 1) → T G = 0 → G ∈ K := fun G h1 h2 => ⟨h1, h2⟩

  have key : ∀ f ∈ arrV0 ε E u (j + 1), (∀ k ∈ K, ⟪k, f⟫_ℂ = 0) → f = 0 := by
    intro f hf horth

    have hsym : f ∈ symSub V n (j + 1) := by
      rw [mem_symmetricArrays]
      intro s
      have hGW : permArr V n s f - f ∈ arrV0 ε E u (j + 1) := sub_mem (permute_mem_highest_jets hf s) hf
      have hGT : T (permArr V n s f - f) = 0 := by rw [map_sub, hS f hf s, sub_self]
      have hGK : permArr V n s f - f ∈ K := memK _ hGW hGT
      have hG'K : permArr V n s⁻¹ (permArr V n s f - f) ∈ K :=
        memK _ (permute_mem_highest_jets hGW s⁻¹) (by rw [hS _ hGW s⁻¹, hGT])
      have h1 : ⟪permArr V n s f - f, permArr V n s f⟫_ℂ = 0 := by
        rw [← inner_permutePositions s⁻¹, permArr_inv_permArr]
        exact horth _ hG'K
      have h2 : ⟪permArr V n s f - f, f⟫_ℂ = 0 := horth _ hGK
      have h3 : ⟪permArr V n s f - f, permArr V n s f - f⟫_ℂ = 0 := by
        rw [inner_sub_right, h1, h2, sub_self]
      exact sub_eq_zero.mp (inner_self_eq_zero.mp h3)

    have hplus : ∀ α' : Fin j → Fin n × Fin n, sliceLin V n α' f ∈ Vplus ε E (LamOf ε lam) u := by
      intro α'
      by_cases hα : ∀ i, ε (α' i).1 ≠ ε (α' i).2
      · have hmem : sliceLin V n α' f ∈ Vplus ε E (LamOf ε lam) u ⊔ Vminus ε E (LamOf ε lam) u := by
          rw [hsplit.2]
          exact slice_mem_highest_jets hf α'
        obtain ⟨p, hp, m, hm, hpm⟩ := Submodule.mem_sup.mp hmem
        have hm0 : m ∈ arrV0 ε E u 1 := by
          rw [← hsplit.2]
          exact Submodule.mem_sup_right hm
        have hGW : sliceIns α' m ∈ arrV0 ε E u (j + 1) := sliceIns_mem hα hm0
        have hGT : T (sliceIns α' m) = 0 := by
          apply hM _ hGW
          intro β'
          rw [slice_sliceIns]
          split_ifs
          · exact hm
          · exact Submodule.zero_mem _
        have hin : ⟪sliceIns α' m, f⟫_ℂ = 0 := horth _ (memK _ hGW hGT)
        have hsum : ∑ β' : Fin j → Fin n × Fin n,
            ⟪sliceLin V n β' (sliceIns α' m), sliceLin V n β' f⟫_ℂ = ⟪m, sliceLin V n α' f⟫_ℂ := by
          rw [Finset.sum_eq_single α']
          · rw [slice_sliceIns, if_pos rfl]
          · intro b _ hb
            rw [slice_sliceIns, if_neg hb, inner_zero_left]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [inner_eq_sum_firstPositionSlice, hsum, ← hpm, inner_add_right] at hin
        have hmp : ⟪m, p⟫_ℂ = 0 := by
          rw [← inner_conj_symm, hsplit.1 p hp m hm, map_zero]
        rw [hmp, zero_add] at hin
        have hm' : m = 0 := inner_self_eq_zero.mp hin
        rw [← hpm, hm', add_zero]
        exact hp
      · rw [slice_eq_zero_of_compact hf α' hα]
        exact Submodule.zero_mem _
    have hN : f ∈ Formalism.REAL.Nset ε E (LamOf ε lam) u j := by
      unfold Formalism.REAL.Nset
      exact ⟨⟨hf, hsym⟩, (Submodule.mem_iInf _).mpr fun α' => Submodule.mem_comap.mpr (hplus α')⟩

    have hCasW : CasK ε (arrE E (j + 1)) f ∈ arrV0 ε E u (j + 1) := by
      rw [compactCasimir_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with hab
      · exact hstab a b hab _ (hstab b a hab.symm _ hf)
      · exact Submodule.zero_mem _
    have hCasT : T (CasK ε (arrE E (j + 1)) f) = CasK ε E (T f) := by
      rw [compactCasimir_apply, compactCasimir_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hab
      · rw [hE a b hab _ (hstab b a hab.symm _ hf), hE b a hab.symm _ hf]
      · exact map_zero T
    have hKf : CasK ε E (T f) = ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • T f :=
      kCasSpan V n ε E (LamOf ε lam) u (glRel_kRel ε E hgl) hhi (T f) (hT f hf)
    have hkK : CasK ε (arrE E (j + 1)) f - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • f ∈ K :=
      memK _ (sub_mem hCasW (Submodule.smul_mem _ _ hf))
        (by rw [map_sub, map_smul, hCasT, hKf, sub_self])
    have hfk : ⟪f, CasK ε (arrE E (j + 1)) f - ((ckv ε (LamOf ε lam) : ℝ) : ℂ) • f⟫_ℂ = 0 := by
      rw [← inner_conj_symm, horth _ hkK, map_zero]
    have hre : (⟪f, CasK ε (arrE E (j + 1)) f⟫_ℂ).re = ckv ε (LamOf ε lam) * ‖f‖ ^ 2 := by
      rw [inner_sub_right, sub_eq_zero] at hfk
      rw [hfk, inner_smul_right, Complex.re_ofReal_mul, re_inner_self_indexArray]

    have hpos := nPos V n ε E lam g u j hgl hun hhi hfd hgap f hN
    rw [hre] at hpos
    have hcoef : 0 < 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) := by
      have h1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < g - 2 * (n : ℝ) := by linarith
      positivity
    have h4 : 2 * ((j : ℝ) + 1) * (g - 2 * (n : ℝ)) * ‖f‖ ^ 2 ≤ 0 := by nlinarith
    have h5 : ‖f‖ ^ 2 = 0 := le_antisymm (by nlinarith) (by positivity)
    simpa using h5

  haveI : FiniteDimensional ℂ (arrV0 ε E u (j + 1)) := finiteDimensional_arrV0_of_finiteDimensional_kSpan ε E u hfd
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le inf_le_left
  intro F hF
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.exists_add_mem_mem_orthogonal (K := K) F
  have hzW : z ∈ arrV0 ε E u (j + 1) := by
    have hz' : z = F - y := by rw [hyz]; abel
    rw [hz']
    exact sub_mem hF hy.1
  have hz0 : z = 0 := key z hzW (fun k hk => (Submodule.mem_orthogonal K z).mp hz k hk)
  rw [hyz, hz0, add_zero]
  exact hy.2

end GlobalTheory.Jet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoMulPiPowLeFourPow
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem two_mul_pi_pow_le_four_pow (k : ℕ) (hk : 3 ≤ k) : 2 * Real.pi ^ k ≤ (4 : ℝ) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h0 := Real.pi_pos.le
  have h1 : Real.pi ^ 3 ≤ (3.15 : ℝ) ^ 3 := pow_le_pow_left₀ h0 Real.pi_lt_d2.le 3
  have h2 : Real.pi ^ m ≤ (4 : ℝ) ^ m := pow_le_pow_left₀ h0 Real.pi_le_four m
  have h3 : 2 * Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 := by norm_num at h1 ⊢; linarith
  rw [pow_add, pow_add, ← mul_assoc]
  exact mul_le_mul h3 h2 (by positivity) (by positivity)

theorem box_volume_arith : ∀ (r j n₁ n₂ n₃ : ℕ) (M : ℝ), 1 ≤ j → j ≤ r → 2 * n₁ ≤ r * (r - 1) → 2 * n₂ ≤ r * (r - 1) → n₃ ≤ r → 1 ≤ M → (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2)) ≤ (4 * r : ℝ) ^ (4 * r ^ 2) * M ^ (8 * r ^ 2) := by
  intro r j n₁ n₂ n₃ M hj hjr h1 h2 h3 hM
  have hr : 1 ≤ r := hj.trans hjr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpi := Real.pi_pos.le
  have hpi4 := Real.pi_le_four
  have hM0 : 0 ≤ M := by linarith
  have hA : (1 : ℝ) ≤ 4 * r := by linarith
  have hrr : r * (r - 1) + r = r ^ 2 := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    simp only [Nat.add_sub_cancel_left]; ring
  have hjj : j ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hjr 2
  have hr2 : r ≤ r ^ 2 := by nlinarith
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have e : (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2))
      = (Real.pi ^ n₁ * (Real.pi * (2 * r) ^ 2) ^ n₂ * (4 * r) ^ n₃ * (2 * Real.pi ^ (2 * j + j ^ 2))) *
        M ^ (2 * n₁ + 4 * n₂ + 2 * n₃ + 4 * j + 2 * j ^ 2) := by
    have a1 : Real.pi * (2 * r * M ^ 2) ^ 2 = (Real.pi * (2 * r) ^ 2) * M ^ 4 := by ring
    have a2 : 2 * (2 * r * M ^ 2) = (4 * (r : ℝ)) * M ^ 2 := by ring
    rw [a1, a2, mul_pow Real.pi, mul_pow _ (M ^ 4), mul_pow _ (M ^ 2), mul_pow Real.pi (M ^ 2)]
    generalize Real.pi * (2 * (r : ℝ)) ^ 2 = B
    generalize 4 * (r : ℝ) = C
    ring
  rw [e]
  have b1 : Real.pi ^ n₁ ≤ (4 * r : ℝ) ^ n₁ := pow_le_pow_left₀ hpi (by linarith) _
  have b2 : (Real.pi * (2 * r) ^ 2) ^ n₂ ≤ (4 * r : ℝ) ^ (2 * n₂) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (0 : ℝ) ≤ (2 * r) ^ 2 := by positivity
    nlinarith
  have b4 : 2 * Real.pi ^ (2 * j + j ^ 2) ≤ (4 * r : ℝ) ^ (2 * j + j ^ 2) :=
    (two_mul_pi_pow_le_four_pow _ (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith) _)
  refine mul_le_mul ?_ (pow_le_pow_right₀ hM (by omega)) (by positivity) (by positivity)
  calc _ ≤ (4 * r : ℝ) ^ n₁ * (4 * r : ℝ) ^ (2 * n₂) * (4 * r) ^ n₃ * (4 * r : ℝ) ^ (2 * j + j ^ 2) := by
        gcongr
    _ = (4 * r : ℝ) ^ (n₁ + 2 * n₂ + n₃ + (2 * j + j ^ 2)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hA (by omega)

end GlobalTheory.Amp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UEmbMulPEl
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Swap

open GlobalTheory.Amp.Rad GlobalTheory.Amp.UEmb

variable {k r : ℕ}

theorem mI_eq (j : Fin (k + 1)) : mI k r j = wI k r j := rfl

def rowAct (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin (k + 1) → ℂ) : Fin r → Fin (k + 1) → ℂ :=
  fun a j => ∑ c, star (u a c) * B c j

theorem herm_rowAct (u : Matrix (Fin r) (Fin r) ℂ) (B : Fin r → Fin (k + 1) → ℂ) :
    (Matrix.of fun a b => herm (Hb k) (rowAct u B b) (rowAct u B a)) =
      u * (Matrix.of fun a b => herm (Hb k) (B b) (B a)) * uᴴ := by
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, herm_Hb, rowAct, star_sum, star_mul', star_star,
    Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => by ring

theorem uEmb_mul_pEl (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (B : Fin r → Fin (k + 1) → ℂ)
    (S : Matrix (Fin r) (Fin r) ℂ) :
    uEmb k r u * pEl k r B S = pEl k r (rowAct u B) (u * S * uᴴ) * uEmb k r u := by
  have h1 : ∀ a b, ∑ c, u⁻¹ a c * u c b = if a = b then 1 else 0 := fun a b => by
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul u hu, Matrix.one_apply]
  have h2 : uᴴ * (u⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul u hu, Matrix.conjTranspose_one]
  ext x y
  rw [Matrix.mul_apply, Matrix.mul_apply, sum3, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp only [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss, ← mI_eq,
      u_ee, u_em, u_es, u_me, u_mm, u_ms, u_se, u_sm, u_ss] <;> simp only [mI_eq] <;>
    simp [pEl_ee, pEl_ew, pEl_es, pEl_we, pEl_ww, pEl_ws, pEl_se, pEl_sw, pEl_ss]
  · simp [rowAct, Finset.sum_mul, mul_assoc]
  · rename_i a b
    set G : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => herm (Hb k) (B b) (B a) with hG
    have h3 : ∀ a c, herm (Hb k) (rowAct u B c) (rowAct u B a) = (u * G * uᴴ) a c := fun a c =>
      congrFun (congrFun (herm_rowAct u B) a) c
    have h4 : u * (S - (1 / 2 : ℂ) • G) = (u * S * uᴴ - (1 / 2 : ℂ) • (u * G * uᴴ)) * (u⁻¹)ᴴ := by
      rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc _ uᴴ, Matrix.mul_assoc _ uᴴ, h2, Matrix.mul_one,
        Matrix.mul_one, Matrix.mul_sub, Matrix.mul_smul]
    have h5 := congrFun (congrFun h4 a) b
    rw [Matrix.mul_apply, Matrix.mul_apply] at h5
    simp only [h3]
    convert h5 using 2 with c _ c _
    · simp [hG, div_eq_inv_mul]
    · simp [div_eq_inv_mul]
  · rename_i i b
    simp only [rowAct, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ d, ∑ c, star (u c d) * B d i * (starRingEnd ℂ) (u⁻¹ b c) = star (∑ c, u⁻¹ b c * u c d) * B d i := by
      intro d
      rw [star_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by simp; ring
    simp only [this, h1]
    simp [apply_ite (starRingEnd ℂ)]

theorem det_eq_one {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (ι : V →ₗ[ℝ] W) (hι : Function.Injective ι) (L : Module.End ℝ V) (T : Module.End ℝ W)
    (h : ∀ v, ι (L v) = T (ι v)) (hT : IsNilpotent (T - 1)) : LinearMap.det L = 1 := by
  have hL : IsNilpotent (L - 1) := by
    obtain ⟨n, hn⟩ := hT
    have : ∀ (m : ℕ) (v : V), ι (((L - 1) ^ m) v) = ((T - 1) ^ m) (ι v) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => intro v; simp [pow_succ, ih, h]
    refine ⟨n, LinearMap.ext fun v => hι ?_⟩
    rw [this, hn]; simp
  have hc := hL.neg.charpoly_eq_X_pow_finrank
  have he := LinearMap.eval_charpoly (-(L - 1)) 1
  rw [hc] at he
  simpa using he.symm

theorem nil_mul {R : Type*} [Ring R] {a b : R} (h : Commute a b) (ha : IsNilpotent (a - 1)) (hb : IsNilpotent (b - 1)) :
    IsNilpotent (a * b - 1) := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by noncomm_ring
  have c1 : Commute (a - 1) b := h.sub_left (Commute.one_left b)
  rw [e]
  refine Commute.isNilpotent_add ?_ (c1.isNilpotent_mul_right ha) hb
  exact Commute.mul_left (c1.sub_right (Commute.one_right _)) ((Commute.refl b).sub_right (Commute.one_right _))

theorem nil_upper (x : UT r → ℂ) : IsNilpotent (upper x - 1) := by
  have hc : (upper x - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular]
    · simp [upper]
    · intro a b h
      have h : b < a := h
      simp [upper, h.not_gt, h.ne']
  have := Matrix.aeval_self_charpoly (upper x - 1)
  rw [hc] at this
  exact ⟨r, by simpa using this⟩

def rowLin (k : ℕ) (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (Fin r → Fin (k + 1) → ℂ) where
  toFun := rowAct u
  map_add' B B' := by ext a j; simp [rowAct, mul_add, Finset.sum_add_distrib]
  map_smul' c B := by
    ext a j; simp only [rowAct, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm]

def skewLin (r : ℕ) : ((UT r → ℂ) × (Fin r → ℝ)) →ₗ[ℝ] Matrix (Fin r) (Fin r) ℂ where
  toFun p := skewM p.1 p.2
  map_add' p q := by
    ext a b; simp only [skewM, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp <;> ring
  map_smul' c p := by
    ext a b; simp only [skewM, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp <;> ring

def coordLin (r : ℕ) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℝ] ((UT r → ℂ) × (Fin r → ℝ)) where
  toFun S := (fun q => S q.1.1 q.1.2, fun a => (S a a).im)
  map_add' S T := by ext <;> simp
  map_smul' c S := by ext <;> simp

theorem coord_skew (p : (UT r → ℂ) × (Fin r → ℝ)) : coordLin r (skewLin r p) = p := by
  ext q
  · simp [coordLin, skewLin, skewM, q.2]
  · simp [coordLin, skewLin, skewM]

theorem skew_coord (S : Matrix (Fin r) (Fin r) ℂ) (hS : Sᴴ = -S) : skewLin r (coordLin r S) = S := by
  obtain ⟨p, hp, -⟩ := skewM_unique S hS
  have : S = skewLin r p := hp
  rw [this, coord_skew]

def conjLin (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ (Matrix (Fin r) (Fin r) ℂ) :=
  LinearMap.mulLeft ℝ u * LinearMap.mulRight ℝ uᴴ

def skewAct (u : Matrix (Fin r) (Fin r) ℂ) : Module.End ℝ ((UT r → ℂ) × (Fin r → ℝ)) :=
  coordLin r ∘ₗ conjLin u ∘ₗ skewLin r

theorem skew_skewAct (u : Matrix (Fin r) (Fin r) ℂ) (p : (UT r → ℂ) × (Fin r → ℝ)) :
    skewLin r (skewAct u p) = u * skewLin r p * uᴴ := by
  have h : (skewLin r p)ᴴ = -skewLin r p := skewM_skew p.1 p.2
  have e : skewAct u p = coordLin r (u * skewLin r p * uᴴ) := by
    simp [skewAct, conjLin, Matrix.mul_assoc]
  rw [e, skew_coord]
  simp [Matrix.conjTranspose_mul, h, Matrix.mul_assoc]

theorem mp_of_det {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure] (L : E →ₗ[ℝ] E) (h : LinearMap.det L = 1) :
    MeasurePreserving L μ μ :=
  ⟨L.continuous_of_finiteDimensional.measurable, by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ (by rw [h]; exact one_ne_zero), h]; simp⟩

def parAct (u : Matrix (Fin r) (Fin r) ℂ) (q : PPar k r) : PPar k r := (rowLin k u q.1, skewAct u q.2)

theorem uEmb_mul_pOf (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (q : PPar k r) :
    uEmb k r u * pOf k r q = pOf k r (parAct u q) * uEmb k r u := by
  have h := skew_skewAct u q.2
  unfold pOf
  rw [uEmb_mul_pEl u hu]
  congr 2
  exact h.symm

theorem cont_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold upper
  split_ifs <;> fun_prop

theorem cont_uEmb (k r : ℕ) : Continuous fun x : UT r → ℂ => uEmb k r (upper x) := by
  have hi : Continuous fun x : UT r → ℂ => (upper x)⁻¹ := by
    have : (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate := by
      funext x; rw [Matrix.inv_def, det_upper]; simp
    rw [this]; exact (cont_upper r).matrix_adjugate
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold uEmb
  split_ifs
  · exact (cont_upper r).matrix_elem _ _
  · exact (hi.matrix_elem _ _).star
  all_goals exact continuous_const

theorem cont_pOf (k r : ℕ) : Continuous (pOf k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold pOf pEl skewM herm Matrix.mulVec dotProduct
  simp only [Pi.star_apply]
  split_ifs <;> fun_prop

theorem cont_parAct (k r : ℕ) : Continuous fun q : (UT r → ℂ) × PPar k r => parAct (upper q.1) q.2 := by
  have hu : Continuous fun q : (UT r → ℂ) × PPar k r => upper q.1 := (cont_upper r).comp continuous_fst
  refine Continuous.prodMk ?_ ?_
  · refine continuous_pi fun a => continuous_pi fun j => ?_
    change Continuous fun q : (UT r → ℂ) × PPar k r => ∑ c, star (upper q.1 a c) * q.2.1 c j
    exact continuous_finset_sum _ fun c _ => (hu.matrix_elem a c).star.mul (by fun_prop)
  · have hs : Continuous fun q : (UT r → ℂ) × PPar k r => skewLin r q.2.2 :=
      (skewLin r).continuous_of_finiteDimensional.comp (by fun_prop)
    exact (coordLin r).continuous_of_finiteDimensional.comp (hu.matrix_mul (hs.matrix_mul hu.matrix_conjTranspose))

end GlobalTheory.Amp.Swap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAutomorphicCountingUnbundledStatement
section
open MeasureTheory NumberField Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAutomorphicCounting_unbundled : GlobalTheory.IndefiniteRowSideFullHecke.LatticeCountingTheorem.CountingTheorem → ∀ A : ℝ, ∃ (n₀ : ℕ) (C₀ : ℝ), 0 ≤ C₀ ∧ ∀ n₁ ≥ n₀, ∀ C ≥ C₀, ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)] [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ), (n₁ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧ Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ ∀ P : Ideal (𝓞 I.E), P.IsMaximal → ((g₀ : 𝓞 I.E) ∈ P) → Ideal.absNorm P = g₀ ∧ (g₀ : 𝓞 I.E) ∉ P ^ 2) → ((∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧ I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧ I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re) → (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h → Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) → Real.log (Real.log b) ≤ 1 / 16 * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) → |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e| ≤ Real.exp (-(1 / 16) * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)) μf fund e := by
  first | exact @GlobalTheory.CountBridge.count_unbundled | exact GlobalTheory.CountBridge.count_unbundled | (intros; apply GlobalTheory.CountBridge.count_unbundled <;> assumption)
end

