import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0208
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0103
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0219
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0220
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolume
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemCongruenceLevelIffOrthEmbedding
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

namespace GlobalTheory.StabUnfold

private theorem exists_intertwiner_decomp_of_kernel_intertwines {R : Type} [CommRing R] {n m : ℕ} (x u : Fin n → R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h5 : vecMulVec x u + A * A' = 1) (z : Fin n → R) :
    z = (u ⬝ᵥ z) • x + A *ᵥ (A' *ᵥ z) := by
  have h : (vecMulVec x u + A * A') *ᵥ z = z := by rw [h5, Matrix.one_mulVec]
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec] at h
  conv_lhs => rw [← h]
  congr 1
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem coords_smul_add_mulVec {R : Type} [CommRing R] {n m : ℕ} (x u : Fin n → R)
    (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (h1 : A' * A = 1) (h2 : A' *ᵥ x = 0) (h3 : u ᵥ* A = 0) (h4 : u ⬝ᵥ x = 1) (a : R) (w : Fin m → R) :
    u ⬝ᵥ (a • x + A *ᵥ w) = a ∧ A' *ᵥ (a • x + A *ᵥ w) = w := by
  constructor
  · rw [dotProduct_add, dotProduct_smul, h4, Matrix.dotProduct_mulVec, h3, zero_dotProduct, smul_eq_mul,
      mul_one, add_zero]
  · rw [Matrix.mulVec_add, Matrix.mulVec_smul, h2, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, smul_zero,
      zero_add]

theorem conj_stab_and_cong_of_split {R : Type} [CommRing R] (S : Subring R) {n m : ℕ}
    (L : Submodule S (Fin n → R)) (L' : Submodule S (Fin m → R))
    (X Xi G : Matrix (Fin n) (Fin n) R) (g : Matrix (Fin m) (Fin m) R)
    (x u : Fin n → R) (A : Matrix (Fin n) (Fin m) R) (A' : Matrix (Fin m) (Fin n) R)
    (hX : X * Xi = 1) (hXi : Xi * X = 1)
    (h1 : A' * A = 1) (h2 : A' *ᵥ x = 0) (h3 : u ᵥ* A = 0) (h4 : u ⬝ᵥ x = 1)
    (h5 : vecMulVec x u + A * A' = 1)
    (hL : ∀ z, Xi *ᵥ z ∈ L ↔ ∃ a ∈ S, ∃ w ∈ L', z = a • x + A *ᵥ w)
    (hGx : G *ᵥ x = x) (hGA : G * A = A * g) :
    ((∀ w, w ∈ L' ↔ g *ᵥ w ∈ L') ↔ ∀ y, y ∈ L ↔ (Xi * G * X) *ᵥ y ∈ L) ∧
      ∀ c : R, (∀ w ∈ L', ∃ w' ∈ L', (g - 1) *ᵥ w = c • w') ↔
        ∀ y ∈ L, ∃ z ∈ L, (Xi * G * X - 1) *ᵥ y = c • z := by
  have hu0 : ∀ w, u ⬝ᵥ (A *ᵥ w) = 0 := fun w => by
    rw [Matrix.dotProduct_mulVec, h3, zero_dotProduct]
  have hA0 : ∀ w, A' *ᵥ (A *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hM : ∀ z, Xi *ᵥ z ∈ L ↔ u ⬝ᵥ z ∈ S ∧ A' *ᵥ z ∈ L' := by
    intro z
    rw [hL]
    constructor
    · rintro ⟨a, ha, w, hw, rfl⟩
      obtain ⟨e1, e2⟩ := coords_smul_add_mulVec x u A A' h1 h2 h3 h4 a w
      rw [e1, e2]
      exact ⟨ha, hw⟩
    · rintro ⟨ha, hw⟩
      exact ⟨_, ha, _, hw, exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 z⟩
  have hG : ∀ z, G *ᵥ z = (u ⬝ᵥ z) • x + A *ᵥ (g *ᵥ (A' *ᵥ z)) := by
    intro z
    conv_lhs => rw [exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 z]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hGx, Matrix.mulVec_mulVec, hGA, ← Matrix.mulVec_mulVec]
  have hXiX : ∀ y, Xi *ᵥ (X *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hXi, Matrix.one_mulVec]
  have hXXi : ∀ y, X *ᵥ (Xi *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, hX, Matrix.one_mulVec]
  have hconj : ∀ y, (Xi * G * X) *ᵥ y = Xi *ᵥ (G *ᵥ (X *ᵥ y)) := fun y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hGm : ∀ p, (G - 1) *ᵥ p = A *ᵥ ((g - 1) *ᵥ (A' *ᵥ p)) := by
    intro p
    have hp := exists_intertwiner_decomp_of_kernel_intertwines x u A A' h5 p
    calc (G - 1) *ᵥ p = G *ᵥ p - p := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      _ = ((u ⬝ᵥ p) • x + A *ᵥ (g *ᵥ (A' *ᵥ p))) - ((u ⬝ᵥ p) • x + A *ᵥ (A' *ᵥ p)) := by
          rw [← hp, hG]
      _ = A *ᵥ ((g - 1) *ᵥ (A' *ᵥ p)) := by
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
          abel
  have hsub : ∀ y, (Xi * G * X - 1) *ᵥ y = Xi *ᵥ (A *ᵥ ((g - 1) *ᵥ (A' *ᵥ (X *ᵥ y)))) := by
    intro y
    rw [← hGm]
    simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, hconj, Matrix.one_mulVec, hXiX]
  refine ⟨⟨fun hg y => ?_, fun h w => ?_⟩, fun c => ⟨fun hc y hy => ?_, fun h w hw => ?_⟩⟩
  · rw [hconj y]
    conv_lhs => rw [← hXiX y]
    rw [hM, hM, hG, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).1, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).2]
    exact Iff.and Iff.rfl (hg _)
  · have hw := h (Xi *ᵥ (A *ᵥ w))
    rw [hconj, hXXi, hM, hM, hG, (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).1,
      (coords_smul_add_mulVec x u A A' h1 h2 h3 h4 _ _).2, hu0, hA0] at hw
    simpa [S.zero_mem] using hw
  · rw [← hXiX y, hM] at hy
    obtain ⟨w', hw', hgw⟩ := hc _ hy.2
    refine ⟨Xi *ᵥ (A *ᵥ w'), ?_, ?_⟩
    · rw [hM, hu0, hA0]
      exact ⟨S.zero_mem, hw'⟩
    · rw [hsub, hgw, Matrix.mulVec_smul, Matrix.mulVec_smul]
  · have hy : Xi *ᵥ (A *ᵥ w) ∈ L := by
      rw [hM, hu0, hA0]
      exact ⟨S.zero_mem, hw⟩
    obtain ⟨z, hz, hcz⟩ := h _ hy
    rw [hsub, hXXi, hA0] at hcz
    have e := congrArg (fun v => A' *ᵥ (X *ᵥ v)) hcz
    simp only [hXXi, hA0, Matrix.mulVec_smul] at e
    refine ⟨A' *ᵥ (X *ᵥ z), ?_, e⟩
    have hz' : Xi *ᵥ (X *ᵥ z) ∈ L := by rw [hXiX]; exact hz
    exact ((hM _).1 hz').2

theorem mem_level_iff_of_isFinEmb (I : AutInst) (D : Sib I) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin D.n) I.E) (xf : I.Gf) (hp : IsPerp D s x A xf)
    (jf : D.inst.Gf →* I.Gf) (hj : IsFinEmb D x A jf) :
    (∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset) ∧
      ∀ (N : ℕ) (g : D.inst.Gf), g ∈ D.inst.Kg N ↔ xf⁻¹ * jf g * xf ∈ I.Kg N := by
  obtain ⟨hn, hβ, hxJA, hAJA, hp5, hp6⟩ := hp
  have hJ : I.Jᴴ = I.J := by
    have h := I.J_herm
    unfold Formalism.UG.IsHerm at h
    conv_rhs => rw [← h]
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, starRingEnd_apply]
  have hβ' : star x ⬝ᵥ (I.J *ᵥ x) ≠ 0 := by
    rw [hβ]
    cases s <;> simp [sgn]
  obtain ⟨u, A', e1, e2, e3, e4, e5, -⟩ :=
    exists_dual_of_anisotropic_orthogonal I.E I.n D.n I.J D.J x A hn hJ D.J_det hβ' hxJA hAJA
  have h1 : afMat I A' * afMat I A = 1 := by
    simp only [afMat]
    rw [← Matrix.map_mul, e1, Matrix.map_one _ (Formalism.UG.inclE (F := I.F) (Af I.F)).map_zero (Formalism.UG.inclE (F := I.F) (Af I.F)).map_one]
  have h2 : afMat I A' *ᵥ afVec I x = 0 := by
    funext i
    have := RingHom.map_mulVec (Formalism.UG.inclE (F := I.F) (Af I.F)) A' x i
    rw [e2, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h3 : afVec I u ᵥ* afMat I A = 0 := by
    funext i
    have := RingHom.map_vecMul (Formalism.UG.inclE (F := I.F) (Af I.F)) A u i
    rw [e3, Pi.zero_apply, map_zero] at this
    exact this.symm
  have h4 : afVec I u ⬝ᵥ afVec I x = 1 := by
    have := RingHom.map_dotProduct (Formalism.UG.inclE (F := I.F) (Af I.F)) u x
    rw [e4, map_one] at this
    exact this.symm
  have h5 : vecMulVec (afVec I x) (afVec I u) + afMat I A * afMat I A' = 1 := by
    have hv : vecMulVec (afVec I x) (afVec I u) = (vecMulVec x u).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
      ext i j
      simp [afVec, vecMulVec]
    rw [hv]
    simp only [afMat]
    rw [← Matrix.map_mul, ← Matrix.map_add _ (map_add (Formalism.UG.inclE (F := I.F) (Af I.F))), e5, Matrix.map_one _ (Formalism.UG.inclE (F := I.F) (Af I.F)).map_zero (Formalism.UG.inclE (F := I.F) (Af I.F)).map_one]
  have hX : I.fmat xf * I.fmat xf⁻¹ = 1 := by simp [AutInst.fmat]
  have hXi : I.fmat xf⁻¹ * I.fmat xf = 1 := by simp [AutInst.fmat]
  have hprod : ∀ g, I.fmat (xf⁻¹ * jf g * xf) = I.fmat xf⁻¹ * I.fmat (jf g) * I.fmat xf := by
    intro g
    simp [AutInst.fmat]
  have key := fun g => conj_stab_and_cong_of_split (IntAf I.F I.E) I.Lf D.inst.Lf (I.fmat xf) (I.fmat xf⁻¹)
    (I.fmat (jf g)) (D.inst.fmat g) (afVec I x) (afVec I u) (afMat I A) (afMat I A') hX hXi h1 h2 h3 h4 h5
    (adelicLattice_split I D s x A xf ⟨hn, hβ, hxJA, hAJA, hp5, hp6⟩) (hj g).1 (hj g).2
  have hK : ∀ g, g ∈ D.inst.Kset ↔ xf⁻¹ * jf g * xf ∈ I.Kset := by
    intro g
    show (∀ w, w ∈ D.inst.Lf ↔ D.inst.fmat g *ᵥ w ∈ D.inst.Lf) ↔
      ∀ y, y ∈ I.Lf ↔ I.fmat (xf⁻¹ * jf g * xf) *ᵥ y ∈ I.Lf
    rw [hprod]
    exact (key g).1
  refine ⟨hK, fun N g => ?_⟩
  show (g ∈ D.inst.Kset ∧ ∀ y ∈ D.inst.Lf, ∃ z ∈ D.inst.Lf,
      (D.inst.fmat g - 1) *ᵥ y = (N : I.E ⊗[I.F] Af I.F) • z) ↔
    (xf⁻¹ * jf g * xf ∈ I.Kset ∧ ∀ y ∈ I.Lf, ∃ z ∈ I.Lf,
      (I.fmat (xf⁻¹ * jf g * xf) - 1) *ᵥ y = (N : I.E ⊗[I.F] Af I.F) • z)
  rw [hprod]
  exact Iff.and (hK g) ((key g).2 _)

end GlobalTheory.StabUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NegLogProdLValEtaLeAndPos
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas.LProd

private lemma eventually_abs_le_half_add_of_doubling_bounds (m : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    1 / (x + 1) ^ (3 + m) + 4 / 2 ^ (3 + m) / ((x + 1) * (x + 1 + 1)) ≤
      4 / 2 ^ (3 + m) / (x * (x + 1)) := by
  have hx0 : 0 < x := by linarith
  have hp : (2 : ℝ) ^ m ≤ (x + 1) ^ m := pow_le_pow_left₀ (by norm_num) (by linarith) m
  have hp0 : (0 : ℝ) < 2 ^ m := by positivity

  have hdiff : 4 / 2 ^ (3 + m) / (x * (x + 1)) - 4 / 2 ^ (3 + m) / ((x + 1) * (x + 1 + 1)) =
      1 / (2 ^ m * (x * (x + 1) * (x + 2))) := by
    rw [pow_add]
    field_simp
    ring

  have hcube : x * (x + 1) * (x + 2) ≤ (x + 1) ^ 3 := by nlinarith
  have hle : 2 ^ m * (x * (x + 1) * (x + 2)) ≤ (x + 1) ^ (3 + m) := by
    calc 2 ^ m * (x * (x + 1) * (x + 2)) ≤ (x + 1) ^ m * (x + 1) ^ 3 :=
          mul_le_mul hp hcube (by positivity) (by positivity)
      _ = (x + 1) ^ (3 + m) := by ring
  have hterm : 1 / (x + 1) ^ (3 + m) ≤ 1 / (2 ^ m * (x * (x + 1) * (x + 2))) :=
    one_div_le_one_div_of_le (by positivity) hle
  linarith

theorem tsum_le (M : ℕ) (hM : 3 ≤ M) :
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M) ≤ 1 + 2 / 2 ^ M := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hM

  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), 1 / ((i : ℝ) + 1) ^ (3 + m) +
      4 / 2 ^ (3 + m) / (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1)) ≤ 1 + 2 / 2 ^ (3 + m) := by
    intro N
    induction N with
    | zero =>
      apply le_of_eq
      norm_num
      ring
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := eventually_abs_le_half_add_of_doubling_bounds m ((N : ℝ) + 1) (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
      push_cast
      linarith
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro N
  cases N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  | succ N =>
    have h := hpart N
    have : (0 : ℝ) ≤ 4 / 2 ^ (3 + m) / (((N : ℝ) + 1) * ((N : ℝ) + 1 + 1)) := by positivity
    linarith

theorem log_tsum_le (M : ℕ) (hM : 3 ≤ M) :
    Real.log (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M) ≤ 2 / 2 ^ M := by
  have h1 := tsum_le M hM
  have h0 : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M := tsum_nonneg fun n => by positivity
  rcases h0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]
    positivity
  · linarith [Real.log_le_sub_one_of_pos h]

private lemma sum_Ioc_two_div_two_pow (n₀ k : ℕ) :
    ∑ M ∈ Finset.Ioc n₀ (n₀ + k), (2 : ℝ) / 2 ^ M = 2 / 2 ^ n₀ - 2 / 2 ^ (n₀ + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (Nat.le_add_right n₀ k), ih, pow_succ]
    field_simp
    ring

theorem geom_le (n₀ n : ℕ) : ∑ M ∈ Finset.Ioc n₀ n, (2 : ℝ) / 2 ^ M ≤ (2 : ℝ) ^ ((1 : ℤ) - n₀) := by
  rw [zpow_sub₀ two_ne_zero, zpow_one, zpow_natCast]
  rcases le_or_gt n n₀ with h | h
  · rw [Finset.Ioc_eq_empty_of_le h, Finset.sum_empty]
    positivity
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    rw [sum_Ioc_two_div_two_pow]
    have : (0 : ℝ) ≤ 2 / 2 ^ (n₀ + k) := by positivity
    linarith

theorem neg_log_prod_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ n₀ n : ℕ, 2 ≤ n₀ → -Real.log (∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M) ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) ∧ 0 < ∏ M ∈ Finset.Ioc n₀ n, Formalism.HermitianLatticesTheory.lValEta E M := by
  intro E _ _ _ hE n₀ n hn₀
  have hL : ∀ M : ℕ, 2 ≤ M → 0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta E M)| ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * Real.log (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ M) :=
    fun M hM => (Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound E hE M hM).2
  have hpos : ∀ M ∈ Finset.Ioc n₀ n, 0 < Formalism.HermitianLatticesTheory.lValEta E M := fun M hM =>
    (hL M (by have := (Finset.mem_Ioc.mp hM).1; omega)).1
  refine ⟨?_, Finset.prod_pos hpos⟩
  rw [Real.log_prod (fun M hM => (hpos M hM).ne'), ← Finset.sum_neg_distrib]
  have hf : (0 : ℝ) ≤ Formalism.HermitianLatticesTheory.fDeg E := by positivity
  calc ∑ M ∈ Finset.Ioc n₀ n, -Real.log (Formalism.HermitianLatticesTheory.lValEta E M)
      ≤ ∑ M ∈ Finset.Ioc n₀ n, (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 / 2 ^ M) := by
        apply Finset.sum_le_sum
        intro M hM
        have hM3 : 3 ≤ M := by have := (Finset.mem_Ioc.mp hM).1; omega
        calc -Real.log (Formalism.HermitianLatticesTheory.lValEta E M) ≤ |Real.log (Formalism.HermitianLatticesTheory.lValEta E M)| := neg_le_abs _
          _ ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * Real.log (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ M) := (hL M (by omega)).2
          _ ≤ (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * (2 / 2 ^ M) := mul_le_mul_of_nonneg_left (log_tsum_le M hM3) hf
    _ = (Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ∑ M ∈ Finset.Ioc n₀ n, (2 : ℝ) / 2 ^ M := by rw [Finset.mul_sum]
    _ ≤ Formalism.HermitianLatticesTheory.fDeg E * (2 : ℝ) ^ ((1 : ℤ) - n₀) := mul_le_mul_of_nonneg_left (geom_le n₀ n) hf

end GlobalTheory.FlagMeas.LProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotDvdAbsNormDifferent
section
noncomputable section

open scoped TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.FrameIntegral

theorem ef_one_of_split (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] (p : ℕ)
    (hall : ∀ W : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1)
    (Q : Ideal (𝓞 E)) (hQp : Q.IsPrime) (hQb : Q ≠ ⊥) (hpQ' : ((p : ℕ) : 𝓞 E) ∈ Q) :
    Q.ramificationIdx ℤ = 1 ∧ Q.inertiaDeg ℤ = 1 := by
  have hinjEL : Function.Injective (algebraMap (𝓞 E) (𝓞 L)) :=
    FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L)
  obtain ⟨W, -, hWp, hWQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 L) Q ⊥
    (by rw [Ideal.comap_bot_of_injective _ hinjEL]; exact bot_le)
  have hWb : W ≠ ⊥ := by
    intro h0; apply hQb; rw [← hWQ, h0, Ideal.comap_bot_of_injective _ hinjEL]
  have hpW : ((p : ℕ) : 𝓞 L) ∈ W := by
    have : algebraMap (𝓞 E) (𝓞 L) ((p : ℕ) : 𝓞 E) ∈ W := by
      rw [← Ideal.mem_comap, hWQ]; exact hpQ'
    simpa using this
  obtain ⟨h1, h2⟩ := hall ⟨W, hWp, hWb⟩ hpW
  have : W.LiesOver Q := ⟨hWQ.symm⟩
  have h1' : W.ramificationIdx ℤ = 1 := h1
  have h2' : W.inertiaDeg ℤ = 1 := h2
  rw [Ideal.ramificationIdx_tower (R := ℤ) Q W] at h1'
  rw [Ideal.inertiaDeg_tower (R := ℤ) Q W] at h2'
  exact ⟨(mul_eq_one.mp h1').1, (mul_eq_one.mp h2').1⟩

theorem not_dvd_absNorm_different (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (hram : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → ((p : ℕ) : 𝓞 K) ∈ P → P.ramificationIdx ℤ = 1) :
    ¬ p ∣ Ideal.absNorm (differentIdeal ℤ (𝓞 K)) := by
  have key : ∀ I : Ideal (𝓞 K), I ∣ differentIdeal ℤ (𝓞 K) → ¬ p ∣ Ideal.absNorm I := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ =>
      intro h
      exact absurd (zero_dvd_iff.1 h) (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K))
    | h₂ x hx =>
      intro _
      rw [Ideal.isUnit_iff.1 hx, Ideal.absNorm_top]
      exact hp.not_dvd_one
    | h₃ a P ha hP ih =>
      intro hdvd hpd
      rw [map_mul] at hpd
      rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
      · have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
        have hPb : P ≠ ⊥ := hP.ne_zero
        have hPm : P.IsMaximal := Ideal.IsPrime.isMaximal hPp hPb
        have hfin : Finite (𝓞 K ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hPb
        have hcard : Ideal.absNorm P = Nat.card (𝓞 K ⧸ P) := by
          rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
        rw [hcard] at h
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p h
        let _ : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
        have hx0 : x ≠ 0 := by
          rintro rfl; rw [addOrderOf_zero] at hx; exact hp.one_lt.ne hx
        have hpx : (p : 𝓞 K ⧸ P) * x = 0 := by
          rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
        have hp0 : (p : 𝓞 K ⧸ P) = 0 := (mul_eq_zero.1 hpx).resolve_right hx0
        have hpP : ((p : ℕ) : 𝓞 K) ∈ P := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hp0
        have he := hram P hPp hPb hpP
        have hun : Algebra.IsUnramifiedAt ℤ P := Ideal.ramificationIdx_eq_one_iff.mp he
        exact (not_dvd_differentIdeal_iff.2 hun) (dvd_of_mul_right_dvd hdvd)
      · exact ih (dvd_of_mul_left_dvd hdvd) h
  exact key _ dvd_rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem coprime_gi (i : Fin 2) : Nat.Coprime (Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F))) (D.host.g i) := by
  have hall : ∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal →
      W.asIdeal.ramificationIdx ℤ = 1 ∧ W.asIdeal.inertiaDeg ℤ = 1 := fun W hW =>
    (GlobalTheory.unramified_degree_one_of_ncard_placesOver D.host.E _ (D.host.g_prime i) (D.nd.g_split i) W hW).2
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (D.host.g_prime i)).2 ?_)
  refine not_dvd_absNorm_different D.host.F _ (D.host.g_prime i) fun P hPp hPb hpP => ?_
  exact (ef_one_of_split D.host.F D.host.E _ hall P hPp hPb hpP).1

end GlobalTheory.FrameIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiPolarDecompositionEquivariance
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.PsiPolarProof

variable {n : ℕ}

lemma exp_posDef_of_herm {X : Matrix (Fin n) (Fin n) ℂ} (h : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℝ) • X)ᴴ = (1 / 2 : ℝ) • X := by
    rw [Matrix.conjTranspose_smul, h]; simp
  have e : X = (1 / 2 : ℝ) • X + (1 / 2 : ℝ) • X := by rw [← add_smul]; norm_num
  have e2 : NormedSpace.exp X =
      (NormedSpace.exp ((1 / 2 : ℝ) • X))ᴴ * NormedSpace.exp ((1 / 2 : ℝ) • X) := by
    rw [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e]
  rw [e2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_exp _))

lemma mem_KC_of_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ KC ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, rfl⟩, hk.2⟩

lemma mul_mem_K {ε : Fin n → Bool} {k k' : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    (hk' : k' ∈ Kset ε) : k * k' ∈ Kset ε :=
  ⟨mul_mem hk.1 hk'.1, by rw [Matrix.mul_assoc, hk'.2, ← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]⟩

lemma star_mem_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have := congrArg Matrix.conjTranspose hk.2
  simpa [Matrix.conjTranspose_mul, Jm_conjTranspose] using this.symm

theorem psiPolar_of (hB : PsBasic) (hE : PsEquiv) : PsiPolar := by
  intro n ε lam W _ _ τ w hl hτ
  refine ⟨fun k hk X hX => Psi_unitary_mul ε lam τ w hk.1
    (exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)), ?_, ?_⟩
  · have h := Psi_unitary_mul ε lam τ w (one_mem _) (Matrix.PosDef.one (n := Fin n) (R := ℂ))
    rw [Matrix.mul_one] at h
    rw [h, (hB n ε lam W τ w hl hτ).2.2.2, hτ.2.1.1]
    rfl
  · intro k₁ h₁ k₂ h₂ g hg
    obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
    have hp := exp_posDef_of_herm (hermitian_of_mem_hermitian_part hX)
    set p := NormedSpace.exp X
    have hs : k₂ * k₂ᴴ = 1 := Unitary.mul_star_self_of_mem h₂.1
    have hc := mem_KC_of_mem_K (star_mem_K h₂)
    have hq : (k₂ᴴ * p * k₂).PosDef :=
      hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (mem_KC_of_mem_K h₂).1)
    have e : k₁ * (k * p) * k₂ = (k₁ * k * k₂) * (k₂ᴴ * p * k₂) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc k₂ k₂ᴴ, hs, Matrix.one_mul]
    have hk3 := mul_mem_K (mul_mem_K h₁ hk) h₂
    have he := hE n ε lam W τ w hl hτ p k₂ᴴ hp hc
    rw [Matrix.conjTranspose_conjTranspose] at he
    rw [e, Psi_unitary_mul ε lam τ w hk3.1 hq, Psi_unitary_mul ε lam τ w hk.1 hp, he,
      ← ContinuousLinearMap.comp_assoc]
    have hm : (τ (k₁ * k * k₂)).comp (τ k₂ᴴ) = (τ k₁).comp (τ k) := by
      have a := hτ.2.1.2 _ (mem_KC_of_mem_K hk3) _ hc
      have b := hτ.2.1.2 _ (mem_KC_of_mem_K h₁) _ (mem_KC_of_mem_K hk)
      rw [Matrix.mul_assoc, hs, Matrix.mul_one] at a
      exact a.symm.trans b
    rw [hm]
    rfl

end GlobalTheory.Dec.PsiPolarProof

theorem GlobalTheory.Dec.psiPolar : GlobalTheory.Dec.PsiPolar :=
  GlobalTheory.Dec.PsiPolarProof.psiPolar_of GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one GlobalTheory.T.psi_complexifiedK_equivariance
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeWeightTermDatumPosStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relative_weight_term_datum_pos : ∀ (D : D7) (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d0 d : LocNG.Datum P, (∃ t, LocNG.IsTermOver P d0 t) → (∃ t, LocNG.IsTermOver P d t) → 0 < LocNG.Datum.wt d0 d := by
  first | exact @GlobalTheory.WtPos.wt_pos | exact GlobalTheory.WtPos.wt_pos | (intros; apply GlobalTheory.WtPos.wt_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitTermWeightLeNearReferenceLatticeStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTermWeight_le_near_referenceLattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → N.om Λ ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * N.Del ^ r * (Ideal.absNorm 𝔠 : ℝ) ^ (2 * (3 * e + 11) * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.Weight.om_le | exact GlobalTheory.DegCnt.Weight.om_le | (intros; apply GlobalTheory.DegCnt.Weight.om_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialModChosenPrimesIffMemKgStatement
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_mod_chosen_primes_iff_mem_Kg : ∀ (I : AutInst) (N : ℕ) (g : Fin 2 → ℕ) (Pl : Fin 2 → Type) (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)) (fr : ∀ k v, PlFrame I N (g k) (w k v)), I.n = N → IsChoice I g Pl w → ∀ x ∈ I.Kset, (∀ k v (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), (fr k v).c ⟨_, h⟩ = (fr k v).c y) ↔ x ∈ I.Kg (g 0 * g 1) := by
  first | exact @GlobalTheory.RowLev.trivial_iff_mem_Kg | exact GlobalTheory.RowLev.trivial_iff_mem_Kg | (intros; apply GlobalTheory.RowLev.trivial_iff_mem_Kg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolumeStatement
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_lattice_fundamentalSet_volume : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Ψ : ι → W → Fin (k + 1) → ℂ), IsPlaces σ → Module.finrank K W = k + 1 → (∀ v x y, Ψ v (x + y) = Ψ v x + Ψ v y) → (∀ v (c : K) x, Ψ v (c • x) = σ v c • Ψ v x) → (∀ v x y, herm (Hb k) (Ψ v x) (Ψ v y) = σ v (HW.B x y)) → ∀ (L : Submodule (𝓞 K) W) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), IsUnimod HW L → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : W, x ∈ ipow 𝔡 n • L ∧ ((fun v => (ρ : ℂ) • Ψ v x) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  first | exact @GlobalTheory.UnimodCov.unimod_fund | exact GlobalTheory.UnimodCov.unimod_fund | (intros; apply GlobalTheory.UnimodCov.unimod_fund <;> assumption)
end

