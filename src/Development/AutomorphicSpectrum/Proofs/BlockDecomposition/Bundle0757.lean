import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0752
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0750
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle0001
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerDiagonalOfUpperTriangularBlock
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.MuC.LeftCell

variable {D : D7} {p : ℕ}

theorem upper_triangular_block_mul_lower_rows (a b d : Mx D p p) (N : Mx D (p + p) (p + p)) (k : Fin p → Fin (p + p)) :
    (blk4 a b 0 d * N).submatrix (fun i : Fin p => finSumFinEquiv (Sum.inr i)) k =
      d * N.submatrix (fun i : Fin p => finSumFinEquiv (Sum.inr i)) k := by
  ext i j
  rw [Matrix.submatrix_apply, Matrix.mul_apply, ← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
  simp only [blk4, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem lowerDiagonal_of_upper_triangular_block {a b d : Mx D p p} {q : G D p} (h : mat q = blk4 a b 0 d) : lowD q = d := by
  ext i j
  simp only [lowD, h, blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem low_mul {q : G D p} (hq : q ∈ P D p) (g : G D p) :
    lowC (q * g) = lowD q * lowC g ∧ lowD (q * g) = lowD q * lowD g := by
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  have hd := lowerDiagonal_of_upper_triangular_block hm
  rw [hd]
  constructor
  · change (mat (q * g)).submatrix _ _ = _
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]
    exact upper_triangular_block_mul_lower_rows _ _ _ _ _
  · change (mat (q * g)).submatrix _ _ = _
    rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, hm]
    exact upper_triangular_block_mul_lower_rows _ _ _ _ _

theorem lowD_one : lowD (1 : G D p) = 1 := by
  ext i j
  simp [lowD, GlobalTheory.StdUnn.LeftInvSect.mat_one, Matrix.one_apply]

theorem lowD_inv_mul {q : G D p} (hq : q ∈ P D p) : lowD q⁻¹ * lowD q = 1 := by
  have h := (low_mul ((P D p).inv_mem hq) q).2
  rw [inv_mul_cancel, lowD_one] at h
  exact h.symm

theorem isB_mul {e : AE D} {q g : G D p} (hq : q ∈ P D p) {x : hermS D p e} (h : IsB e g x) :
    IsB e (q * g) x := by
  obtain ⟨⟨y, hy⟩, hx⟩ := h
  obtain ⟨hC, hD⟩ := low_mul hq g
  refine ⟨⟨mm y (lowD q⁻¹), ?_⟩, ?_⟩
  · change (y * lowD q⁻¹) * lowC (q * g) = _
    change y * lowC g = _ at hy
    rw [hC, Matrix.mul_assoc, ← Matrix.mul_assoc (lowD q⁻¹), lowD_inv_mul hq, Matrix.one_mul, hy]
  · change lowC (q * g) * x.1.1 = _
    change lowC g * x.1.1 = _ at hx
    rw [hC, hD, Matrix.mul_assoc, hx, Matrix.mul_smul]

theorem isB_left : ∀ {D : D7} {p : ℕ} {e : AE D} {q g : G D p} (hq : q ∈ P D p) (x : hermS D p e),
    IsB e (q * g) x ↔ IsB e g x := by
  intro D p e q g hq x
  refine ⟨fun h => ?_, isB_mul hq⟩
  have h' := isB_mul ((P D p).inv_mem hq) h
  rwa [inv_mul_cancel_left] at h'

end GlobalTheory.CompanionTheory.MuC.LeftCell
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaximumPrincipleLatticeFunctions
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair GlobalTheory.CompanionTheory.BZCore
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.BZCore.MaxPrin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {d : ℕ}

theorem exists_pow_val_lt {ϖ : k} (hϖ : ValuativeRel.valuation k ϖ < 1) (γ : ValuativeRel.ValueGroupWithZero k)
    (hγ : γ ≠ 0) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ValuativeRel.valuation k ϖ ^ n < γ := by
  have : MulArchimedean (ValuativeRel.ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
  exact ⟨n, fun m hm => lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn⟩

theorem latZ_add (z : GL (Fin d) k) (a b : ℤ) : latZ z (a + b) = (latZ z b).act (z ^ a) := by
  rw [latZ, latZ, COSub.act_act, _root_.zpow_add]

theorem smul_mem_latZ (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0) (a b : ℤ)
    (w : Fin d → k) : ϖ ^ a • w ∈ (latZ z (a + b)).sub ↔ w ∈ (latZ z b).sub := by
  rw [latZ_add, ← zpow_mulVec z ϖ hz hϖ0 a w]
  exact COSub.mulVec_mem_act _

theorem scale_step (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) (x : Fin d → k) : F (latZ z (r + 1)) (ϖ • x) = F (latZ z r) x := by
  have h := hS (latZ z r) x
  have e : (latZ z r).act z = latZ z (r + 1) := by
    rw [add_comm, latZ_add, zpow_one]
  rw [e, hz, Matrix.smul_mulVec, one_mulVec] at h
  exact h

theorem scale (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0)
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) : ∀ x : Fin d → k, F (latZ z r) (ϖ ^ r • x) = F (latZ z 0) x := by
  induction r using Int.induction_on with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [zpow_add₀ hϖ0, zpow_one, mul_comm, mul_smul, scale_step z ϖ hz F hS, ih]
  | pred n ih =>
    intro x
    have h := scale_step z ϖ hz F hS (-(n : ℤ) - 1) (ϖ ^ (-(n : ℤ) - 1) • x)
    rw [sub_add_cancel, smul_smul, ← zpow_one_add₀ hϖ0, add_sub_cancel, ih] at h
    exact h.symm

theorem scale_inv (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k)) (hϖ0 : ϖ ≠ 0)
    (F : COSub k d → (Fin d → k) → ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r : ℤ) (y : Fin d → k) : F (latZ z r) y = F (latZ z 0) (ϖ ^ (-r) • y) := by
  rw [← scale z ϖ hz hϖ0 F hS r, smul_smul, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, one_smul]

theorem shell_unif (z : GL (Fin d) k) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hN : ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r →
      F (latZ z (r : ℤ)) y = c) :
    ∃ r₁ : ℕ, ∀ y : Fin d → k, y ∈ (latZ z 0).sub → y ∉ (latZ z 1).sub → ∀ r : ℕ, r₁ ≤ r →
      F (latZ z (r : ℤ)) y = c := by
  have hK : IsCompact (((latZ z 0).sub : Set (Fin d → k)) \ ((latZ z 1).sub : Set (Fin d → k))) :=
    (latZ z 0).isCompact.diff (latZ z 1).isOpen
  have h := hK.induction_on
    (p := fun A => ∃ s : ℕ, ∀ y ∈ A, ∀ r : ℕ, s ≤ r → F (latZ z (r : ℤ)) y = c)
    ⟨0, by simp⟩
    (fun A B hAB ⟨s, hs⟩ => ⟨s, fun y hy => hs y (hAB hy)⟩)
    (fun A B ⟨s, hs⟩ ⟨t, ht⟩ => ⟨max s t, fun y hy r hr => hy.elim
      (fun h => hs y h r (le_trans (le_max_left _ _) hr))
      (fun h => ht y h r (le_trans (le_max_right _ _) hr))⟩)
    (by
      intro x hx
      have hx0 : x ≠ 0 := fun h => hx.2 (h ▸ (latZ z 1).sub.zero_mem)
      obtain ⟨s, hs⟩ := hN x hx0
      exact ⟨{y | y - x ∈ (latZ z (s : ℤ)).sub},
        mem_nhdsWithin_of_mem_nhds ((isClopen_coset _ x).isOpen.mem_nhds
          (by simp [(latZ z (s : ℤ)).sub.zero_mem])), s, fun y hy r hr => hs y hy r hr⟩)
  obtain ⟨s, hs⟩ := h
  exact ⟨s, fun y h0 h1 r hr => hs y ⟨h0, h1⟩ r hr⟩

theorem exists_shell (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (w : Fin d → k) (hw : w ≠ 0) :
    ∃ m : ℤ, w ∈ (latZ z m).sub ∧ w ∉ (latZ z (m + 1)).sub := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have hvi : ValuativeRel.valuation k (w i) ≠ 0 := by simpa using hi
  have hv : 0 < ValuativeRel.valuation k ϖ := zero_lt_iff.2 (by simpa using hϖ0)
  have hbdd : ∃ b : ℤ, ∀ m : ℤ, w ∈ (latZ z m).sub → m ≤ b := by
    obtain ⟨N, hN⟩ := exists_pow_val_lt hϖ _ hvi
    refine ⟨N, fun m hm => ?_⟩
    by_contra hlt
    have hm0 : 0 ≤ m := by omega
    lift m to ℕ using hm0
    have h1 := (mem_latZ z ϖ hz hϖ0 _ w).1 hm i
    rw [zpow_natCast] at h1
    exact absurd h1 (not_le.2 (hN m (by omega)))
  have hinh : ∃ m : ℤ, w ∈ (latZ z m).sub := by
    have hall : ∀ᶠ n : ℕ in Filter.atTop, ∀ j, ValuativeRel.valuation k (w j) ≤
        (ValuativeRel.valuation k ϖ ^ n)⁻¹ := by
      refine Filter.eventually_all.2 fun j => ?_
      by_cases hj : ValuativeRel.valuation k (w j) = 0
      · exact Filter.Eventually.of_forall fun n => by rw [hj]; exact zero_le'
      · obtain ⟨N, hN⟩ := exists_pow_val_lt hϖ _ (inv_ne_zero hj)
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        exact (le_inv_comm₀ (zero_lt_iff.2 hj) (pow_pos hv n)).2 (hN n hn).le
    obtain ⟨n, hn⟩ := hall.exists
    refine ⟨-(n : ℤ), (mem_latZ z ϖ hz hϖ0 _ w).2 fun j => ?_⟩
    rw [_root_.zpow_neg, zpow_natCast]
    exact hn j
  obtain ⟨m, hm, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
  exact ⟨m, hm, fun h => absurd (hmax _ h) (by omega)⟩

theorem far (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r₁ : ℕ)
    (hr₁ : ∀ y : Fin d → k, y ∈ (latZ z 0).sub → y ∉ (latZ z 1).sub → ∀ r : ℕ, r₁ ≤ r →
      F (latZ z (r : ℤ)) y = c)
    (w : Fin d → k) (hw : w ∉ (latZ z (-(r₁ : ℤ))).sub) : F (latZ z 0) w = c := by
  have hw0 : w ≠ 0 := fun h => hw (h ▸ (latZ z (-(r₁ : ℤ))).sub.zero_mem)
  obtain ⟨m, hm, hm1⟩ := exists_shell z ϖ hz hϖ hϖ0 w hw0
  have hlt : m < -(r₁ : ℤ) := by
    by_contra hge
    exact hw (latZ_anti z ϖ hz hϖ hϖ0 _ _ (not_lt.1 hge) hm)
  have h0 : ϖ ^ (-m) • w ∈ (latZ z 0).sub := by
    have := (smul_mem_latZ z ϖ hz hϖ0 (-m) m w).2 hm
    rwa [neg_add_cancel] at this
  have h1 : ϖ ^ (-m) • w ∉ (latZ z 1).sub := by
    intro h
    have e : (1 : ℤ) = -m + (m + 1) := by ring
    rw [e] at h
    exact hm1 ((smul_mem_latZ z ϖ hz hϖ0 (-m) (m + 1) w).1 h)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = -m := ⟨(-m).toNat, by omega⟩
  have h2 := hr₁ _ h0 h1 t (by omega)
  rw [ht, scale z ϖ hz hϖ0 F hS] at h2
  exact h2

theorem exists_vector_standard_lattice_not_sub {hd : 0 < d} (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) :
    ∃ e : Fin d → k, e ∈ (latZ z 0).sub ∧ e ∉ (latZ z 1).sub := by
  classical
  refine ⟨Pi.single ⟨0, hd⟩ 1, (mem_latZ z ϖ hz hϖ0 _ _).2 fun j => ?_, fun h => ?_⟩
  · rw [zpow_zero, Pi.single_apply]
    split_ifs <;> simp
  · have h1 := (mem_latZ z ϖ hz hϖ0 _ _).1 h ⟨0, hd⟩
    rw [zpow_one, Pi.single_eq_same, map_one] at h1
    exact absurd h1 (not_le.2 hϖ)

theorem eq_const_standard_lattice_refining (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hR : Refines F) (hP : ∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (r₁ : ℕ)
    (hfar : ∀ w : Fin d → k, w ∉ (latZ z (-(r₁ : ℤ))).sub → F (latZ z 0) w = c) (x : Fin d → k) :
    F (latZ z 0) x = c := by
  classical
  have hcont : Continuous (F (latZ z 0)) := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
    filter_upwards [(isClopen_coset (latZ z 0) x).isOpen.mem_nhds
      (by simp [(latZ z 0).sub.zero_mem])] with y hy
    have h := hP (latZ z 0) x (y - x) hy
    rwa [add_sub_cancel] at h
  obtain ⟨xs, -, hmax⟩ := (latZ z (-(r₁ : ℤ))).isCompact.exists_isMaxOn
    ⟨0, (latZ z (-(r₁ : ℤ))).sub.zero_mem⟩
    (f := fun x => ‖F (latZ z 0) x - c‖) (hcont.sub continuous_const).norm.continuousOn
  set M : ℝ := ‖F (latZ z 0) xs - c‖ with hM
  have hall : ∀ x, ‖F (latZ z 0) x - c‖ ≤ M := by
    intro x
    by_cases hx : x ∈ (latZ z (-(r₁ : ℤ))).sub
    · exact hmax hx
    · rw [hfar x hx, sub_self, norm_zero]
      exact norm_nonneg _
  have hle : (latZ z ((r₁ + 1 : ℕ) : ℤ)).sub ≤ (latZ z 0).sub :=
    latZ_anti z ϖ hz hϖ hϖ0 _ _ (by positivity)
  have hle1 : (latZ z ((r₁ + 1 : ℕ) : ℤ)).sub ≤ (latZ z 1).sub :=
    latZ_anti z ϖ hz hϖ hϖ0 _ _ (by push_cast; omega)
  obtain ⟨S, hSr⟩ := exists_reps _ _ hle
  have hsum := hR _ _ S hle hSr xs
  obtain ⟨e, he0, he1⟩ := exists_vector_standard_lattice_not_sub (hd := hd) z ϖ hz hϖ hϖ0
  have hex : ∃ s ∈ S, xs + s ∉ (latZ z 1).sub := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨s0, ⟨hs0, h0⟩, -⟩ := hSr.2 0 (latZ z 0).sub.zero_mem
    obtain ⟨s1, ⟨hs1, h1⟩, -⟩ := hSr.2 e he0
    apply he1
    have e' : e = (e - s1) + (xs + s1) - (xs + s0) - (0 - s0) := by abel
    rw [e']
    exact (latZ z 1).sub.sub_mem ((latZ z 1).sub.sub_mem ((latZ z 1).sub.add_mem (hle1 h1) (hcon s1 hs1))
      (hcon s0 hs0)) (hle1 h0)
  obtain ⟨ss, hss, hss1⟩ := hex
  let t : (Fin d → k) → ℂ := fun s => F (latZ z 0) (ϖ ^ (-((r₁ + 1 : ℕ) : ℤ)) • (xs + s)) - c
  have hts : t ss = 0 := by
    have hn : ϖ ^ (-((r₁ + 1 : ℕ) : ℤ)) • (xs + ss) ∉ (latZ z (-(r₁ : ℤ))).sub := by
      intro h
      have e' : -(r₁ : ℤ) = -((r₁ + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [e'] at h
      exact hss1 ((smul_mem_latZ z ϖ hz hϖ0 _ 1 _).1 h)
    simp only [t]
    rw [hfar _ hn, sub_self]
  have hid : (S.card : ℂ) * (F (latZ z 0) xs - c) = ∑ s ∈ S, t s := by
    simp only [t, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [mul_sub, hsum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => scale_inv z ϖ hz hϖ0 F hS _ _
  have h1 : (S.card : ℝ) * M ≤ ∑ s ∈ S, ‖t s‖ := by
    have := norm_sum_le S t
    rw [← hid, norm_mul, Complex.norm_natCast] at this
    exact this
  have h2 : M ≤ ∑ s ∈ S, (M - ‖t s‖) := by
    have := Finset.single_le_sum (f := fun s => M - ‖t s‖) (fun s _ => sub_nonneg.2 (hall _)) hss
    simpa [hts] using this
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h2
  have hM0 : M ≤ 0 := by linarith
  have := (hall x).trans hM0
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem eq_const (hd : 0 < d) (z : GL (Fin d) k) (ϖ : k)
    (hz : (z : Matrix (Fin d) (Fin d) k) = ϖ • (1 : Matrix (Fin d) (Fin d) k))
    (hϖ : ValuativeRel.valuation k ϖ < 1) (hϖ0 : ϖ ≠ 0) (F : COSub k d → (Fin d → k) → ℂ) (c : ℂ)
    (hR : Refines F) (hP : ∀ (L : COSub k d) (x l : Fin d → k), l ∈ L.sub → F L (x + l) = F L x)
    (hS : ∀ (L : COSub k d) (x : Fin d → k), F (L.act z) ((z : Matrix (Fin d) (Fin d) k).mulVec x) = F L x)
    (hN : ∀ x : Fin d → k, x ≠ 0 → ∃ s : ℕ, ∀ y : Fin d → k, y - x ∈ (latZ z (s : ℤ)).sub → ∀ r : ℕ, s ≤ r →
      F (latZ z (r : ℤ)) y = c) (r : ℕ) (x : Fin d → k) : F (latZ z (r : ℤ)) x = c := by
  obtain ⟨r₁, hr₁⟩ := shell_unif z F c hN
  rw [scale_inv z ϖ hz hϖ0 F hS]
  exact eq_const_standard_lattice_refining hd z ϖ hz hϖ hϖ0 F c hR hP hS r₁ (far z ϖ hz hϖ hϖ0 F c hS r₁ hr₁) _

end GlobalTheory.CompanionTheory.BZCore.MaxPrin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d : Mx D n n) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases h1 : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases h2 : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> rfl

def bT (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) : hermA D n :=
  ⟨bl hn z.1 x (adj x) y.1, by
    show adj (bl hn z.1 x (adj x) y.1 : Mx D n n) = _
    rw [adj_bl, adj_adj]
    have hz : adj z.1 = z.1 := z.2
    have hy : adj y.1 = y.1 := y.2
    rw [hz, hy]⟩

def dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) : HermE D n :=
  ⟨bl hn b₀.1 0 0 β'.1, by
    have h1 := b₀.2
    have h2 := β'.2
    refine Matrix.ext fun i j => ?_
    simp only [bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
    rcases h1' : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
      rcases h2' : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, map_zero]
    · exact congrFun (congrFun h1 i') j'
    · exact congrFun (congrFun h2 i') j'⟩

def cg (a : GL (Fin n) D.host.E) (β : HermE D n) : HermE D n :=
  ⟨(a.1.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * β.1 * a.1, by
    have h : ∀ M : Matrix (Fin n) (Fin n) D.host.E, (M.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = Mᴴ := fun _ => rfl
    have hb : β.1ᴴ = β.1 := β.2
    rw [h, h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hb, Matrix.mul_assoc]⟩

def IsPer (Φ : hermA D n → ℂ) : Prop := ∀ γ ∈ ratHerm D n, ∀ x, Φ (γ + x) = Φ x

def chn (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) : ℂ :=
  ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))

def pm (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ) (y : hermA D p) : ℂ :=
  ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

section Transport
variable {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [T2Space B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem mean_transport (Γ : AddSubgroup A) (Δ : AddSubgroup B) [Countable Γ] [Countable Δ] (T : A ≃ₜ+ B)
    (hT : ∀ a, T a ∈ Δ ↔ a ∈ Γ) (μ : Measure A) (ν : Measure B) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) (hs1 : μ s = 1) (ht1 : ν t = 1)
    (f : B → ℂ) (hf : ∀ γ ∈ Δ, ∀ x, f (γ + x) = f x) :
    ∫ a in s, f (T a) ∂μ = ∫ b in t, f b ∂ν := by
  have hm : Measurable T := T.continuous.measurable
  have hAC : (μ.map T).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ T
  have hAC2 : (ν.map T.symm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν T.symm
  have hsm : Measure.QuasiMeasurePreserving (T.symm.toAddEquiv.toEquiv) ν μ :=
    ⟨T.symm.continuous.measurable, Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩
  let eΓ : Δ ≃ Γ :=
    { toFun := fun d => ⟨T.symm d.1, (hT _).1 (by simpa using d.2)⟩
      invFun := fun c => ⟨T c.1, (hT _).2 c.2⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun c => Subtype.ext (by simp) }
  have hFD : IsAddFundamentalDomain Δ (T.toAddEquiv.toEquiv '' s) ν :=
    hs.image_of_equiv T.toAddEquiv.toEquiv hsm eΓ (fun g x => by
      show T (T.symm g.1 + x) = g.1 + T x
      simp)
  have h1 : ν (T.toAddEquiv.toEquiv '' s) = 1 := by rw [hFD.measure_eq ht, ht1]
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h2 : μ.map T (T.toAddEquiv.toEquiv '' s) = 1 := by
    rw [hemb.map_apply, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective, hs1]
  have h3 : μ.map T = ν := by
    have h4 := Measure.isAddLeftInvariant_eq_smul (μ.map T) ν
    rw [h4] at h2
    have hc : Measure.addHaarScalarFactor (μ.map T) ν = 1 := by
      rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at h2
      exact_mod_cast h2
    rw [h4, hc, one_smul]
  have h5 : ∫ a in s, f (T a) ∂μ = ∫ b in T.toAddEquiv.toEquiv '' s, f b ∂ν := by
    rw [← h3, hemb.setIntegral_map, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective]
  rw [h5]
  exact hFD.setIntegral_eq ht (fun g x => hf g.1 g.2 x)
end Transport
end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulNBlockInr
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mul_nBlock_inl {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inl j)) = A i (finSumFinEquiv (Sum.inl j)) := by
  simp [Matrix.mul_apply, blk4, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_nBlock_inr {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inr j)) =
      ∑ k, A i (finSumFinEquiv (Sum.inl k)) * y k j + A i (finSumFinEquiv (Sum.inr j)) := by
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂]
  simp [Matrix.one_apply]

theorem lowC_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowC (g * nb y) = lowC g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, Matrix.submatrix_apply, hm]
  exact mul_nBlock_inl _ _ _ _

theorem lowD_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowD (g * nb y) = lowC g * y.1 + lowD g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, lowD, Matrix.submatrix_apply, hm, Matrix.add_apply, Matrix.mul_apply]
  exact mul_nBlock_inr _ _ _ _

theorem isB_mul_nb {D : D7} {p : ℕ} {e : AE D} {nb : hermA D p → G D p} (hnb : IsNMap nb) {g : G D p}
    (y x : hermS D p e) : IsB e (g * nb y.1) (x + y) ↔ IsB e g x := by
  have hy : e • y.1.1 = y.1.1 := y.2
  have hc : e • (lowC g * y.1.1) = lowC g * y.1.1 := by rw [← Matrix.mul_smul, hy]
  have hs : (x + y).1.1 = x.1.1 + y.1.1 := rfl
  unfold IsB InCell
  rw [lowC_mul_nb hnb, lowD_mul_nb hnb, hs]
  refine and_congr_right fun _ => ?_
  simp only [mm]
  rw [mul_add, smul_add, hc, add_comm (lowC g * y.1.1) (e • lowD g), add_left_inj]

end GlobalTheory.CompanionTheory.MuC

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateOfWhittakerStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_of_whittaker : PositivityTheory.PfSWUS.NDOfWhit := by
  first | exact @GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | exact GlobalTheory.CompanionTheory.SWGlue.ndOfWhit | (intros; apply GlobalTheory.CompanionTheory.SWGlue.ndOfWhit <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentityStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polar_part_identity : MapsExist → HtExist → HeckeEta → RightId → PoleReal → FJEis → PcBound → RSec → EisHol → ThTotal → CfFJ → PcFc → SphBound → Polar := by
  first | exact @GlobalTheory.CompanionTheory.RswPolar.polar | exact GlobalTheory.CompanionTheory.RswPolar.polar | (intros; apply GlobalTheory.CompanionTheory.RswPolar.polar <;> assumption)
end

