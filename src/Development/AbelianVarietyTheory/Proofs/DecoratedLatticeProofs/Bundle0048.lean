import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterLowerHeckeRepsEqRelIndexPow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentBlockDiagCosetsDistinct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormWeierstrassPSubEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterLowerHeckeRepsEqRelIndexPowStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_filter_lowerHecke_reps_eq_relIndex_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (m g y : GL D k), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → (∃ κ'' ∈ KO k D, y = m * g * κ'') → ∀ N : Finset (Matrix D A k), ((∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ) → (N.filter fun ν => ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ m.1 * ν = ν₁ + y.1 * ν₂).card = ((preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D)) ^ Fintype.card A ∧ 0 < (preLat m.1 ⊓ preLat (g⁻¹).1).relIndex (preLat m.1 ⊓ mLat k D) := by
  first | exact @GlobalTheory.LowerHeckeCount.card_filter_eq | exact GlobalTheory.LowerHeckeCount.card_filter_eq | (intros; apply GlobalTheory.LowerHeckeCount.card_filter_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardFilterParahoricCosetsEqSchurCountStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_filter_parahoric_cosets_eq_schur_count : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D') (R : Finset (GL (A ⊕ D') k)) d, IsReps (mtor ϖ (indic s)) R d → ∀ RK, IsRepsK (torusElt k D' ϖ (indic s)) RK → ∀ x : Matrix (A ⊕ D') (A ⊕ D) k, InSupp x → (R.filter fun j => InSupp (((j * mtor ϖ (indic s))⁻¹).1 * x)).card = (RK.filter fun g => ∀ i l, ((g⁻¹).1 * schur x) i l ∈ 𝒪[k]).card := by
  first | exact @GlobalTheory.ParHeckeTarget.card_filter_eq | exact GlobalTheory.ParHeckeTarget.card_filter_eq | (intros; apply GlobalTheory.ParHeckeTarget.card_filter_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPattern
section
namespace GlobalTheory.SymResCount

open Formalism.L2.DIV

theorem mem_unipSym_iff {K : Type} [CommRing K] {r : ℕ} (ρ κ : ℕ) (g : GL (Fin r) K) :
    g ∈ unipSym K r ρ κ ↔ ∀ a b : Fin r, ¬ (a.val < b.val ∧ ¬ (ρ ≤ a.val ∧ a.val < ρ + κ ∧ b.val = ρ + κ)) →
      (g : Matrix (Fin r) (Fin r) K) a b = (1 : Matrix (Fin r) (Fin r) K) a b := by
  constructor
  · rintro ⟨⟨hl, hd⟩, hc⟩ a b hab
    by_cases e : a = b
    · subst e; rw [hd a, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne e]
      have hne : a.val ≠ b.val := fun h => e (Fin.ext h)
      by_cases h1 : b.val < a.val
      · exact hl (show b.val < a.val from h1)
      · exact hc a b (by omega) (by omega) (by omega)
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j h0 h1 h2 => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (by omega), Matrix.one_apply_eq]
    · rw [h i j (by omega), Matrix.one_apply_ne (fun e => by rw [e] at h1; omega)]

def permFn (ρ κ i : ℕ) : ℕ := if i < κ then ρ + i else if i < κ + ρ then i - κ else i

def permInv (ρ κ a : ℕ) : ℕ := if a < ρ then κ + a else if a < ρ + κ then a - ρ else a

def perm (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : Fin r ≃ Fin r where
  toFun i := ⟨permFn ρ κ i.val, by unfold permFn; split_ifs <;> omega⟩
  invFun a := ⟨permInv ρ κ a.val, by unfold permInv; split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega
  right_inv a := by
    apply Fin.ext; simp only; unfold permFn permInv; split_ifs <;> omega

theorem perm_val {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (i : Fin r) : (perm r ρ κ hr i).val = permFn ρ κ i.val := rfl

theorem freePos_iff (ρ κ i j : ℕ) :
    GlobalTheory.SymRes.FreePos ρ κ i j ↔ (permFn ρ κ i < permFn ρ κ j ∧
      ¬ (ρ ≤ permFn ρ κ i ∧ permFn ρ κ i < ρ + κ ∧ permFn ρ κ j = ρ + κ)) := by
  unfold GlobalTheory.SymRes.FreePos permFn; split_ifs <;> omega

def reidx {K : Type} [CommRing K] (r ρ κ : ℕ) (hr : κ + ρ ≤ r) : GL (Fin r) K ≃* GL (Fin r) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K (perm r ρ κ hr)).toMulEquiv

theorem reidx_apply {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) (i j : Fin r) :
    ((reidx r ρ κ hr g : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) (perm r ρ κ hr i) (perm r ρ κ hr j) =
      (g : Matrix (Fin r) (Fin r) K) i j := by
  simp [reidx, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

theorem reidx_mem_iff {K : Type} [CommRing K] {r ρ κ : ℕ} (hr : κ + ρ ≤ r) (g : GL (Fin r) K) :
    reidx r ρ κ hr g ∈ unipSym K r ρ κ ↔ GlobalTheory.SymRes.IsPat ρ κ g := by
  rw [mem_unipSym_iff]
  constructor
  · intro h i j hf
    have := h (perm r ρ κ hr i) (perm r ρ κ hr j) (by rw [perm_val, perm_val, ← freePos_iff]; exact hf)
    rw [reidx_apply] at this
    rw [this]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]
  · intro h a b hab
    obtain ⟨i, rfl⟩ := (perm r ρ κ hr).surjective a
    obtain ⟨j, rfl⟩ := (perm r ρ κ hr).surjective b
    rw [reidx_apply, h i j (by rw [freePos_iff, ← perm_val hr, ← perm_val hr]; exact hab)]
    by_cases e : i = j
    · subst e; simp
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e ((perm r ρ κ hr).injective e'))]

end GlobalTheory.SymResCount

namespace GlobalTheory.SymResCount
open Formalism.L2.DIV

theorem conj_pat_onto : ∀ (K : Type) [CommRing K] [Finite K] (r ρ κ : ℕ), r = κ + (2 * ρ + 1) →
    ∀ m : GL (Fin r) K, (∀ g : GL (Fin r) K, GlobalTheory.SymRes.IsPat ρ κ g → m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ) →
    ∀ g : GL (Fin r) K, m * g * m⁻¹ ∈ Formalism.L2.DIV.unipSym K r ρ κ → GlobalTheory.SymRes.IsPat ρ κ g := by
  intro K _ _ r ρ κ hr m hm g hg
  have hr' : κ + ρ ≤ r := by omega
  haveI : Finite (GL (Fin r) K) := Finite.of_injective (fun u : GL (Fin r) K => (u : Matrix (Fin r) (Fin r) K)) Units.val_injective
  set S : Set (GL (Fin r) K) := {g | GlobalTheory.SymRes.IsPat ρ κ g} with hS
  set U : Set (GL (Fin r) K) := (unipSym K r ρ κ : Set (GL (Fin r) K)) with hU
  have hSU : (reidx (K := K) r ρ κ hr') '' S = U := by
    ext h
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (reidx_mem_iff hr' x).2 hx
    · intro hh
      refine ⟨(reidx r ρ κ hr').symm h, (reidx_mem_iff hr' _).1 (by rw [MulEquiv.apply_symm_apply]; exact hh), by simp⟩
  have hinj : Function.Injective (fun x : GL (Fin r) K => m * x * m⁻¹) := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hc : (fun x : GL (Fin r) K => m * x * m⁻¹) '' S = U := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨x, hx, rfl⟩; exact hm x hx
    · rw [Set.ncard_image_of_injective S hinj, ← hSU, Set.ncard_image_of_injective S (reidx r ρ κ hr').injective]
    · exact Set.toFinite U
  have hg' : m * g * m⁻¹ ∈ U := hg
  rw [← hc] at hg'
  obtain ⟨x, hx, he⟩ := hg'
  have : x = g := hinj he
  rw [← this]; exact hx

end GlobalTheory.SymResCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetRepsMaximalIdealMatrixModMulStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_reps_maximalIdealMatrix_mod_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (g : GL D k), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∃ N : Finset (Matrix D A k), (∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ := by
  first | exact @GlobalTheory.LowerHecke.exists_finset_reps_maxLat_mod_mul | exact GlobalTheory.LowerHecke.exists_finset_reps_maxLat_mod_mul | (intros; apply GlobalTheory.LowerHecke.exists_finset_reps_maxLat_mod_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHomotheticPeriodPairLattice
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory

theorem homotheticLattice : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair,
    (∀ z, z ∈ L'.lattice ↔ c * z ∈ L.lattice) ∧ L'.g₂ = c ^ 4 * L.g₂ ∧ L'.g₃ = c ^ 6 * L.g₃ ∧
    (∀ z, L'.weierstrassP z = c ^ 2 * L.weierstrassP (c * z) ∧
      L'.derivWeierstrassP z = c ^ 3 * L.derivWeierstrassP (c * z)) ∧
    ∀ d, HasCMBy d L → HasCMBy d L' := by
  intro L c hc
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  obtain ⟨hmem, -, -, hwp, -, -, -, -, -, hg2, hg3⟩ := Formalism.L2.Th1.F.homogeneity L c⁻¹ hc'
  refine ⟨Formalism.L2.Th1.F.scalePair L c⁻¹ hc', ?_, ?_, ?_, ?_, ?_⟩
  · intro z; rw [hmem, inv_inv]
  · rw [hg2, inv_pow, inv_inv]
  · rw [hg3, inv_pow, inv_inv]
  · intro z
    constructor
    · have := hwp (c * z)
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul, inv_pow, inv_inv] at this
      exact this
    · unfold PeriodPair.derivWeierstrassP
      rw [Formalism.L2.Th1.F.Homog.tsum_scale L c⁻¹ hc' (fun l => 2 / (z - l) ^ 3), mul_neg,
        ← tsum_mul_left]
      congr 1
      refine tsum_congr fun l => ?_
      have : z - c⁻¹ * (l : ℂ) = c⁻¹ * (c * z - l) := by field_simp
      rw [this, mul_pow, inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
      ring
  · intro d hd
    exact Formalism.L2.Th1.F.hasCMByScale d L c⁻¹ hc' hd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLowerUnipotentBlockDiagCosetRepStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerUnipotent_blockDiag_coset_rep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  first | exact @GlobalTheory.LowerHecke.exists_lowU_diag_coset | exact GlobalTheory.LowerHecke.exists_lowU_diag_coset | (intros; apply GlobalTheory.LowerHecke.exists_lowU_diag_coset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerLeHilbertSchmidtNormSqSubId
section
open Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem finrank_ker_le_hsNormSq_sub_id {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (K : V →L[ℂ] V) (N : Submodule ℂ V) (hN : ∀ x ∈ N, K x = 0) :
    (Module.finrank ℂ N : ℝ) ≤ hsNormSq (K - ContinuousLinearMap.id ℂ V) := by
  let b := stdOrthonormalBasis ℂ N
  let v : Fin (Module.finrank ℂ N) → V := fun i => (b i : V)
  have hv : Orthonormal ℂ v := b.orthonormal.comp_linearIsometry N.subtypeₗᵢ
  have h := GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt (K - ContinuousLinearMap.id ℂ V) v hv
  have hterm : ∀ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = 1 := by
    intro i
    have hK : K (v i) = 0 := hN _ (b i).2
    have hn : ‖v i‖ = 1 := hv.1 i
    simp [hK, hn]
  have hsum : ∑ i, ‖(K - ContinuousLinearMap.id ℂ V) (v i)‖ ^ 2 = (Module.finrank ℂ N : ℝ) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  rw [hsum] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogAdditiveModPrimeStatement
section
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hondaFrobeniusTwistLog_additive_mod_prime : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (i : ℕ), 0 < i → ∀ m, ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (frobOp σ l i f) (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.twistLog_additive_mod | exact GlobalTheory.Honda.twistLog_additive_mod | (intros; apply GlobalTheory.Honda.twistLog_additive_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogEigenModPrimeStatement
section
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hondaFrobeniusTwistLog_eigen_mod_prime : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → ∀ (i : ℕ), 0 < i → CoefLe ‖(l : K)‖ ((frobOp σ l i f).subst (Formalism.L2.Th1.C.mulBy f e w) - C ((σ ^ i) w) * frobOp σ l i f) := by
  first | exact @GlobalTheory.Honda.frobLog_eigen | exact GlobalTheory.Honda.frobLog_eigen | (intros; apply GlobalTheory.Honda.frobLog_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralHondaLogarithmPairShortWeierstrassStatement
section
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralHondaLogarithmPair_shortWeierstrass : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K), ‖(2 : K)‖ = 1 → ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3)) (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  first | exact @GlobalTheory.Honda.intLog_shortW | exact GlobalTheory.Honda.intLog_shortW | (intros; apply GlobalTheory.Honda.intLog_shortW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerUnipotentBlockDiagCosetsDistinctStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_blockDiag_cosets_distinct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ g ∈ R, ∀ g' ∈ R, ∀ ν ν' : Matrix D A k, (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (lowU ν' * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g') * mtor ϖ (indic s)) ∈ parahoric k A D → g = g' ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν' - ν = g.1 * μ := by
  first | exact @GlobalTheory.CosetDistinct.coset_uniq | exact GlobalTheory.CosetDistinct.coset_uniq | (intros; apply GlobalTheory.CosetDistinct.coset_uniq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormWeierstrassPSubEqOneOfGood
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM

namespace GlobalTheory.Honda

theorem norm_weierstrassP_sub_eq_one_of_good :
    ∀ (L : PeriodPair) (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ (ι : ℂ ≃+* ℂ_[l]), ‖ι L.g₂‖ ≤ 1 → ‖ι L.g₃‖ ≤ 1 →
      ‖ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2‖ = 1 → ∀ u v : ℂ, u ∉ L.lattice → v ∉ L.lattice → u + v ∉ L.lattice →
      u - v ∉ L.lattice → ‖ι (L.weierstrassP u)‖ ≤ 1 → ‖ι (L.weierstrassP v)‖ ≤ 1 →
      ‖ι (L.weierstrassP (u + v))‖ ≤ 1 → ‖ι (L.weierstrassP (u - v))‖ ≤ 1 →
      ‖ι (L.weierstrassP u) - ι (L.weierstrassP v)‖ = 1 := by
  intro L l _ hl ι hg2 hg3 hD u v hu hv huv hmuv hpu hpv hpuv hpmuv
  have hgood : GlobalTheory.Klein.Good ι L 0 := by
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hg2
    · simpa using hg3
    · rw [map_sub, map_pow, map_mul, map_pow, map_ofNat]; exact hD
  have hred : ∀ z, z ∉ L.lattice → ‖ι (L.weierstrassP z)‖ ≤ 1 → GlobalTheory.Klein.Red ι L 0 z :=
    fun z hz hp => ⟨hz, by simpa using hp⟩
  have h := GlobalTheory.Klein.norm_weierstrassP_sub_eq_one l ι L 0 hgood u v (hred u hu hpu) (hred v hv hpv)
    (hred _ huv hpuv) (hred _ hmuv hpmuv)
  simpa [map_sub] using h

end GlobalTheory.Honda
end

