import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0048
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionCongrEqTransposeMul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CmpB

theorem blk_transpose {R : Type} [CommRing R] (d k : ℕ) (u v : R) :
    (blk d k u v).transpose = blk d k u v := Matrix.diagonal_transpose _

theorem tau_dvd_entry {R : Type} [CommRing R] (t : R) {m n h : Type} [Fintype n]
    (A : Matrix m n R) (Y : Matrix n h R) (hA : ∀ i j, t ∣ A i j) (i : m) (j : h) :
    t ∣ (A * Y) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => dvd_mul_of_dvd_left (hA i l) _

theorem comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y Z : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U' → IsNil F.θ F.σ (U'.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U' * blk d k (p : F.B) 1) → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → Z.map F.σ = blk d k (p : F.B) 1 * U'.transpose * Z → (∀ i m, F.τ ∣ Z i m - Y i m) → Z = X.transpose * Y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U U' X Y Z hU' hn1 hn2 hX hX1 hY hZ hZY
  set P := blk d k (p : F.B) 1 with hP

  have hT : P * U'.transpose * X.transpose = (X.map F.σ).transpose * P * U.transpose := by
    have := congrArg Matrix.transpose hX
    simp only [Matrix.transpose_mul, hP, blk_transpose] at this
    simpa only [Matrix.mul_assoc] using this
  have hΔ : (Z - X.transpose * Y).map F.σ = P * U'.transpose * (Z - X.transpose * Y) := by
    have e1 : (X.transpose * Y).map F.σ = P * U'.transpose * (X.transpose * Y) := by
      rw [Matrix.map_mul, Matrix.transpose_map, hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, ← hT, Matrix.mul_assoc (P * U'.transpose)]
    rw [Matrix.map_sub _ (map_sub F.σ), hZ, e1, Matrix.mul_sub]
  have hdiv : ∀ i m, F.τ ∣ (Z - X.transpose * Y) i m := by
    intro i m
    have e : Z - X.transpose * Y = (Z - Y) - (X.transpose - 1) * Y := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, Matrix.sub_apply]
    refine dvd_sub (by simpa using hZY i m) (tau_dvd_entry _ _ _ (fun a b => ?_) i m)
    have h1 : (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) a b = (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) b a := by
      simp only [Matrix.one_apply, eq_comm]
    rw [Matrix.sub_apply, Matrix.transpose_apply, h1]
    exact hX1 b a
  have := (GlobalTheory.T.ainfSquareZeroFrame_invariant_eq_zero_of_tau_dvd p C v O hv ε hε F d k h U' hU' hn1 hn2).1 _ hΔ hdiv
  exact (sub_eq_zero.1 this)

end GlobalTheory.CmpB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSolutionMulCongrGmTranspose
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.CmpG.comparison : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U U' X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (u l : F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B) (W : Matrix (Fin d ⊕ Fin k) (Fin h) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → F.τ ∣ u - 1 → X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ → (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) → F.σ l = u * l → F.τ ∣ l - 1 → U * blk d k (p : F.B) 1 * Gm.transpose.map F.σ = (p : F.B) • Gm.transpose → U' * blk d k (p : F.B) 1 * W.map F.σ = ((p : F.B) * u) • W → (∀ i m, F.τ ∣ W i m - Gm m i) → X * W = l • Gm.transpose := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U U' X u l Gm W hU hN1 hN2 hu hX hXc hl hlc hG hW hWc
  classical
  haveI := ReciprocityTheory.PGsh.Ainf.O_local O hv
  obtain ⟨c, hc⟩ := hu
  have hue : u = 1 + F.τ * c := by rw [← hc]; ring
  set w : F.B := 1 - F.τ * c with hwdef
  have hwu : w * u = 1 := by rw [hue, hwdef]; linear_combination (-(c * c)) * F.τ_sq
  have hτ0 : F.θ F.τ = 0 := GlobalTheory.WinLift.theta_tau F hv hε
  have hθu : F.θ u = 1 := by rw [hue, map_add, map_one, map_mul, hτ0, zero_mul, add_zero]
  have hθw : F.θ w = 1 := by rw [hwdef, map_sub, map_one, map_mul, hτ0, zero_mul, sub_zero]
  have hwU : IsUnit w := ⟨⟨w, u, hwu, by rw [mul_comm]; exact hwu⟩, rfl⟩
  set P := blk d k (p : F.B) 1 with hP
  set D : Matrix (Fin d ⊕ Fin k) (Fin h) F.B := X * W - l • Gm.transpose with hDdef
  have hsm : (l • Gm.transpose).map F.σ = F.σ l • Gm.transpose.map F.σ :=
    Matrix.ext fun i j => by simp
  have hsub : D.map F.σ = (X * W).map F.σ - (l • Gm.transpose).map F.σ :=
    by rw [hDdef]; exact Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hD : U * P * D.map F.σ = ((p : F.B) * u) • D := by
    rw [hsub, Matrix.map_mul, hsm, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc, ← hX,
      Matrix.mul_assoc, hW, hG, hl, Matrix.mul_smul, smul_smul, hDdef, smul_sub, smul_smul]
    congr 1
    rw [show u * l * (p : F.B) = p * u * l by ring]
  set U₁ := w • U with hU₁
  have hD1 : U₁ * P * D.map F.σ = (p : F.B) • D := by
    rw [hU₁, Matrix.smul_mul, Matrix.smul_mul, hD, smul_smul,
      show w * ((p : F.B) * u) = p by linear_combination (p : F.B) * hwu]
  have hUdet : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).1 hU
  have hU₁u : IsUnit U₁ := by
    rw [Matrix.isUnit_iff_isUnit_det, hU₁, Matrix.det_smul]
    exact (hwU.pow _).mul hUdet
  have hinv : U₁.transpose⁻¹ = u • U.transpose⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hU₁, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hwu, one_smul,
      Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hUdet)]
  have hp : ¬IsUnit (p : O) := Fact.out
  have hN1' : IsNil F.θ F.σ (U₁.transpose⁻¹ * blk d k 1 (p : F.B)) := by
    refine GlobalTheory.WinLift.isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN1
    rw [hinv, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hθu, one_mul]
  have hN2' : IsNil F.θ F.σ (U₁ * P) := by
    refine GlobalTheory.WinLift.isNil_of_theta_eq p F.θ F.σ hp F.σ_pow _ _ (fun i j => ?_) hN2
    rw [hU₁, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, map_mul, hθw, one_mul]
  have key := (GlobalTheory.TauUniq.eq_zero_of_tau_dvd p C v O hv ε hε F d k h U₁ hU₁u hN1' hN2').2
  have hdec : D = (X - 1) * W + (W - Gm.transpose) - (l - 1) • Gm.transpose := by
    rw [hDdef, Matrix.sub_mul, Matrix.one_mul, sub_smul, one_smul]; abel
  have hτD : ∀ i m, F.τ ∣ D i m := by
    intro i m
    rw [hdec, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply]
    refine dvd_sub (dvd_add (Finset.dvd_sum fun j _ => ?_) (hWc i m)) (Dvd.dvd.mul_right hlc _)
    exact Dvd.dvd.mul_right (hXc i j) _
  have hD0 : D = 0 := by
    refine Matrix.ext fun i m => ?_
    have hcol := key (fun i => D i m) (funext fun i => by
      have := congrArg (fun M => M i m) hD1
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this) (fun i => hτD i m)
    exact congrFun hcol i
  exact sub_eq_zero.1 hD0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicNormalizedWeierstrassValuesCm
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgebraicitySecondEisenstein

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L →
    IsAlgebraic ℚ (s2 L / Ω ^ 2) ∧ ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
  intro L β Ω hst him hΩ
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => mem_algebraicClosure_iff.symm
  have intAlg : ∀ x : ℂ, IsIntegral ℤ x → x ∈ algebraicClosure ℚ ℂ := fun x hx =>
    (alg x).1 (hx.tower_top (A := ℚ)).isAlgebraic
  have natMem : ∀ k : ℕ, (k : ℂ) ∈ algebraicClosure ℚ ℂ := fun k => natCast_mem _ k
  have part2 : ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
    intro M P hM hP
    obtain ⟨h1, -⟩ := GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L β Ω M hst him hΩ hM
    obtain ⟨i1, i2⟩ := h1 P hP
    have a1 := intAlg _ i1
    have a2 := intAlg _ i2
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [mul_div_assoc] at a1 a2
    have c1 : (12 * (M : ℂ) ^ 2) = ((12 * M ^ 2 : ℕ) : ℂ) := by push_cast; ring
    have c2 : ((M : ℂ) ^ 3) = ((M ^ 3 : ℕ) : ℂ) := by push_cast; ring
    have n1 : (12 * (M : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hMc)
    have n2 : ((M : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ hMc
    constructor
    · rw [alg]
      have := div_mem a1 (c1 ▸ natMem (12 * M ^ 2))
      rwa [mul_div_cancel_left₀ _ n1] at this
    · rw [alg]
      have := div_mem a2 (c2 ▸ natMem (M ^ 3))
      rwa [mul_div_cancel_left₀ _ n2] at this
  refine ⟨?_, part2⟩
  have hβ0 : β ≠ 0 := by rintro rfl; simp at him
  obtain ⟨S, hS⟩ := kernel_reps_exist L β hβ0 hst
  have hcard := kernel_reps_card L β S hβ0 hst hS
  obtain ⟨t, n, ht, hn, hq⟩ := mul_stable_integral L β hst
  have hs2 := cm_s2 L β S hst him hS
  have hconj : MulStable L (conj β) := fun ω hω => by
    have e : conj β * ω = t • ω - β * ω := by rw [zsmul_eq_mul, ← ht]; ring
    rw [e]
    exact sub_mem (Submodule.smul_mem _ t hω) (hst ω hω)
  have hM : ((S.card + 1 : ℕ) : ℂ) = conj β * β := by
    rw [← Complex.normSq_eq_conj_mul_self]
    have := congrArg (fun r : ℝ => (r : ℂ)) hcard
    push_cast at this ⊢
    exact this
  have hP : ∀ P ∈ S, L.weierstrassP P / Ω ^ 2 ∈ algebraicClosure ℚ ℂ := fun P hP => by
    have hmem : ((S.card + 1 : ℕ) : ℂ) * P ∈ L.lattice := by
      rw [hM, mul_assoc]; exact hconj _ (hS.1 P hP).1
    exact (alg _).1 (part2 _ P (Nat.succ_pos _) hmem).1
  have hβint : IsIntegral ℤ β := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simpa using hq
  have hβm := intAlg _ hβint
  have hcm : conj β ∈ algebraicClosure ℚ ℂ := by
    have e : conj β = (t : ℂ) - β := by rw [← ht]; ring
    rw [e]; exact sub_mem (intCast_mem _ t) hβm
  rw [alg, hs2, div_div, mul_comm (β * _), ← div_div, Finset.sum_div]
  exact div_mem (sum_mem hP) (mul_mem hβm (sub_mem hβm hcm))

end GlobalTheory.AlgebraicitySecondEisenstein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticOnNhdOrbitPolStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticOnNhd_om_expt_and_iteratedDeriv_zero_eq : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ Z ∈ upq (p * r + q * s) (p * s + q * r), ∀ (P : Pol p q r s), AnalyticOnNhd ℝ (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) Set.univ ∧ ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => F.Om (T0.expt (t • Z)) (F.ι P)) 0 = F.ι ((omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) ^ k) P) := by
  first | exact @GlobalTheory.FockAlg.analyticOnNhd_orbit_pol | exact GlobalTheory.FockAlg.analyticOnNhd_orbit_pol | (intros; apply GlobalTheory.FockAlg.analyticOnNhd_orbit_pol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormGLContinuous
section
noncomputable section

open NumberField Topology

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf : Continuous (pInf E) :=
  (continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

omit [IsTotallyComplex E] in

theorem continuous_pFin : Continuous (pFin E) := continuous_snd

theorem continuous_mapInf : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pInf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf)

omit [IsTotallyComplex E] in

theorem continuous_mapFin : Continuous (Matrix.GeneralLinearGroup.map (n := Fin a) (pFin E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pFin)

theorem IsAutForm.continuous {φ : Sm E a} (h : IsAutForm φ) : Continuous φ.1 := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have hmul : Continuous fun g : GA E a => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hN : {g : GA E a | Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g) ∈ {k | finRep E a k φ = φ}} ∈ 𝓝 g₀ := by
    refine (h.level.preimage (continuous_mapFin.comp hmul)).mem_nhds ?_
    simp
  have heq : φ.1 =ᶠ[𝓝 g₀] fun g => chart φ.1 g₀ (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) := by
    filter_upwards [hN] with g hg
    rw [chart_val]
    have hk : ∀ x, φ.1 (x * finGL E a (Matrix.GeneralLinearGroup.map (pFin E) (g₀⁻¹ * g))) = φ.1 x :=
      fun x => congrArg (fun ψ : Sm E a => ψ.1 x) hg
    conv_lhs => rw [← mul_inv_cancel_left g₀ g, ← infGL_mul_finGL (g₀⁻¹ * g), ← mul_assoc, hk]
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (chart φ.1 g₀) (toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g₀)).val) :=
    (contDiffAt_chart φ.2 g₀ (val_mem_invSet _)).continuousAt
  exact ContinuousAt.comp (f := fun g : GA E a => toL (Matrix.GeneralLinearGroup.map (pInf E) (g₀⁻¹ * g)).val) hc
    (Units.continuous_val.comp (continuous_mapInf.comp hmul)).continuousAt

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGLHomConjPermMatrixOfBlocksMatch
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.Proof.BlockConj

theorem range_blockEnum {r d : ℕ} (b : Fin r → ℕ) (c : ℕ) (h : (block b c).card = d) (k : Fin r) :
    k ∈ Set.range (blockEnum b c h) ↔ b k = c := by
  have h1 : Set.range (blockEnum b c h) = (block b c : Set (Fin r)) :=
    Finset.range_orderEmbOfFin (block b c) h
  rw [h1]
  simp [block]

theorem blockHom_conj_permGL (F : Type) [Field F] (r : ℕ) (b b' : Fin r → ℕ) (w : Equiv.Perm (Fin r))
    (hw : ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j)) (i : Fin r) :
    (block b (b i)).card = (block b' (b' (w i))).card ∧
    ∀ (d : ℕ) (h : (block b (b i)).card = d) (h' : (block b' (b' (w i))).card = d),
      ∃ π : GL (Fin d) F, ∀ g : GL (Fin d) F,
        (blockHom F b' (b' (w i)) h' (π * g * π⁻¹) : GL (Fin r) F) * permGL F w =
          permGL F w * (blockHom F b (b i) h g : GL (Fin r) F) := by
  refine ⟨?_, fun d h h' => ?_⟩
  · refine Finset.card_equiv w fun k => ?_
    simp [block, hw k i]
  · set e := blockEnum b (b i) h with he
    set e' := blockEnum b' (b' (w i)) h' with he'
    have hr : ∀ k, k ∈ Set.range e ↔ w k ∈ Set.range e' := fun k => by
      rw [he, he', range_blockEnum, range_blockEnum, hw k i]
    have hex : ∀ a, ∃ a', e' a' = w (e a) := fun a => (hr (e a)).1 ⟨a, rfl⟩
    choose p hp using hex
    have hinj : Function.Injective p := fun a a' haa => by
      apply e.injective
      apply w.injective
      rw [← hp, ← hp, haa]
    let π₀ : Equiv.Perm (Fin d) := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj)
    have hπ : ∀ a, e' (π₀ a) = w (e a) := hp
    refine ⟨permGL F π₀, fun g => ?_⟩
    refine eq_mul_inv_iff_mul_eq.1 ?_
    ext k l
    obtain ⟨k, rfl⟩ := w.surjective k
    obtain ⟨l, rfl⟩ := w.surjective l
    rw [conj_permGL_apply]
    show extendMat e' ((permGL F π₀ * g * (permGL F π₀)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) (w k) (w l)
      = extendMat e (g : Matrix (Fin d) (Fin d) F) k l
    by_cases hkl : k ∈ Set.range e ∧ l ∈ Set.range e
    · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := hkl
      rw [← hπ, ← hπ, extendMat_in, extendMat_in, conj_permGL_apply]
    · rw [not_and_or] at hkl
      rw [extendMat_out _ _ _ _ hkl, extendMat_out _ _ _ _ (by rwa [← hr, ← hr])]
      simp [Matrix.one_apply]

end GlobalTheory.Proof.BlockConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDetEqLinearCombinationNatNodes
section
open NumberField GlobalTheory.CuspRep

noncomputable section

open Polynomial Finset

namespace GlobalTheory.CuspRep

theorem eval_eq_sum_lagrange_nodes (b : ℕ) (u : ℂ) (f : ℂ[X]) (hf : f.degree < ((b + 1 : ℕ) : WithBot ℕ)) :
    f.eval u = ∑ j : Fin (b + 1),
      (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u * f.eval ((j : ℕ) : ℂ) := by
  have hinj : Set.InjOn (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) (univ : Finset (Fin (b + 1))) := by
    intro x _ y _ h
    exact Fin.ext (by simpa using h)
  have e := Lagrange.eq_interpolate (s := univ) hinj (f := f) (by simpa using hf)
  conv_lhs => rw [e]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, mul_comm]

theorem cap_eq_sum_nodes (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (τ : E →+* ℂ) (u : ℂ) :
    ∃ w : Fin (b + 1) → ℂ, cap (a := b) τ u = ∑ j : Fin (b + 1), w j • cap (a := b) τ ((j : ℕ) : ℂ) := by
  obtain ⟨c, -, hc⟩ := GlobalTheory.qdet_polyMap_monic (Module.End ℂ (Sm E b)) b (Eop τ)
  have hcap : ∀ v : ℂ, cap (a := b) τ v =
      ∑ i ∈ range (b + 1), ((X + C (((b : ℂ) - 1) / 2)) ^ i).eval v • c i := by
    intro v
    rw [cap, hc]
    simp only [eval_pow, eval_add, eval_X, eval_C]
  refine ⟨fun j => (Lagrange.basis univ (fun j : Fin (b + 1) => ((j : ℕ) : ℂ)) j).eval u, ?_⟩
  simp_rw [hcap, smul_sum, smul_smul]
  rw [sum_comm]
  refine sum_congr rfl fun i hi => ?_
  rw [← sum_smul, ← eval_eq_sum_lagrange_nodes]
  have hi' : i < b + 1 := mem_range.1 hi
  rw [degree_pow, degree_X_add_C]
  simp only [nsmul_eq_mul, mul_one]
  exact_mod_cast hi'

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAugEqvOfIsIntegralHomOfStrictlyHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.IntDescent

theorem isIntegral_algClosure_residue (A : Type) [CommRing A] [IsLocalRing A] :
    Algebra.IsIntegral A (AlgebraicClosure (IsLocalRing.ResidueField A)) := by
  haveI : Algebra.IsIntegral A (IsLocalRing.ResidueField A) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId A (IsLocalRing.ResidueField A)) IsLocalRing.residue_surjective
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)) :=
    Algebra.IsAlgebraic.isIntegral
  exact Algebra.IsIntegral.trans (IsLocalRing.ResidueField A)

theorem isIntegral_tensor (A C B : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B]
    [Algebra.IsIntegral A C] [Algebra.IsIntegral A B] : Algebra.IsIntegral A (C ⊗[A] B) := by
  constructor
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact isIntegral_zero
  | tmul x y =>
      have h1 : IsIntegral A (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := C) (B := B) x) :=
        (Algebra.IsIntegral.isIntegral x).map _
      have h2 : IsIntegral A (Algebra.TensorProduct.includeRight (R := A) (A := C) (B := B) y) :=
        (Algebra.IsIntegral.isIntegral y).map _
      have := h1.mul h2
      simpa [Algebra.TensorProduct.tmul_mul_tmul] using this
  | add x y hx hy => exact hx.add hy

theorem L1 : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)],
    IsUnit (q : A) → ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B],
    Eqv (ZMod q) (spMap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom) (tw q i) := by
  intro q i A _ _ _ hq B _ _ _
  have hSH : SH A := ⟨inferInstance, inferInstance⟩
  obtain ⟨ζ0⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A hSH hq
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) := ζ0.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i (Spec (CommRingCat.of A)) ζ
  haveI := isIntegral_algClosure_residue A
  haveI := isIntegral_tensor A (AlgebraicClosure (IsLocalRing.ResidueField A)) B
  have hfin := GlobalTheory.T.tateTwist_finitary q i
  have hU := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A B hSH
  have hU' := GlobalTheory.T.integral_strictHenselian_acyclic_finitary (ZMod q) (tw q i) hfin A (AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B) hSH
  have hbij := GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian (ZMod q) A B
  exact GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) _ _ hgen (Spec (CommRingCat.of B)) _
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) _ hU hU' hbij

end GlobalTheory.EtC.IntDescent

namespace GlobalTheory.EtC

open IntDescent in

theorem cechAug_eqv_of_isIntegralHom_of_strictlyHenselian : ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of A)), IsIntegralHom g → Surjective g → Eqv _ (cechAug g) (tw q i) := by
  intro q i A _ hSH hq Y g hg hsurj
  obtain ⟨_, _⟩ := hSH
  set Ω := AlgebraicClosure (IsLocalRing.ResidueField A)
  set u : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ω)) with hu_def
  have hpb : IsPullback (pullback.fst g u) (pullback.snd g u) g u := IsPullback.of_hasPullback g u
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback _ _ _ _ (pullback.fst g u) (pullback.snd g u) g u hpb
  have hsq : ∀ (Z Z' : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of A)) (h' : Z' ⟶ Spec (CommRingCat.of Ω)) (φ : Z' ⟶ Z),
      IsIntegralHom h → IsPullback φ h' h u → Eqv (ZMod q) (sch.map φ) (tw q i) :=
    GlobalTheory.T.etaleCohomologyEquivalence_pullback_integral_affine (ZMod q) (tw q i) A Ω (fun B _ _ _ => L1 q i A hq B)
  have hEm : Eqv (ZMod q) m (tw q i) :=
    GlobalTheory.T.levelwiseEquivalence_isEquivalence (ZMod q) m (tw q i) (GlobalTheory.T.cechNerve_levelwise_equivalence_integral_pullback (ZMod q) (tw q i) _ _ _ _ _ _ g u hpb hg hsq m hm)
  have hEu : Eqv (ZMod q) (sch.map u) (tw q i) :=
    hsq _ _ (𝟙 _) (𝟙 _) u inferInstance (IsPullback.id_vert u)
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_point_algClosure_residueField_of_integral_surjective A Y g hg hsurj
  have hEs : Eqv (ZMod q) (cechAug (pullback.snd g u)) (tw q i) :=
    GlobalTheory.T.etaleCechAugmentation_equiv_of_section (ZMod q) (tw q i) _ _ (pullback.snd g u) (pullback.lift s (𝟙 _) (by rw [hs, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  obtain ⟨-, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have h1 : Eqv (ZMod q) (cechAug (pullback.snd g u) ≫ sch.map u) (tw q i) :=
    (hcomp _ _ _ _ _).1 hEs hEu
  rw [← hm.w] at h1
  exact (hcomp _ _ _ _ _).2.1 hEm h1

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCohomologyVanishesPositive
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_cohomology_vanishes_positive : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (A' : Type) [CommRing A'] [Algebra A A'],
  Module.Finite A A' → ∀ (k : ℕ) (s i : ℤ), 0 < s → Subsingleton (Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.cech_level_acyc) | (exact GlobalTheory.EtC.GmStep.cech_level_acyc) | (intros; apply GlobalTheory.EtC.GmStep.cech_level_acyc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelAcyclic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC
theorem sh_of_isSepClosed (Ω : Type) [Field Ω] [IsSepClosed Ω] : SH Ω := by
  refine ⟨inferInstance, ?_⟩
  haveI : Algebra.IsIntegral Ω (IsLocalRing.ResidueField Ω) :=
    Algebra.IsIntegral.of_surjective (Algebra.ofId Ω (IsLocalRing.ResidueField Ω)) IsLocalRing.residue_surjective
  exact Algebra.IsAlgebraic.isSepClosed (F := Ω)

theorem cech_level_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (m : ℕ), 0 < m → ∀ y : H R (disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌))) F m, y = 0 := by
  intro R _ F hF K Ω _ _ _ _ k m hm y
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have hf : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
    IsIntegralHom.SpecMap_iff.2 fun x => Algebra.IsIntegral.isIntegral x
  obtain ⟨Z, π, e, hπ, -⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsIntegralHom _ _ _ hf (op ⦋k⦌)
  haveI : IsIntegralHom π := hπ
  haveI : IsAffine Z := isAffine_of_isAffineHom π
  let φ : Ω →+* Γ(Z, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ π.appTop).hom
  letI : Algebra Ω Γ(Z, ⊤) := φ.toAlgebra
  have hint : (π.app ⊤).hom.IsIntegral := π.isIntegral_app ⊤ (isAffineOpen_top _)
  haveI : Algebra.IsIntegral Ω Γ(Z, ⊤) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨p, hp, h⟩ := hint b
    refine ⟨p.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom, hp.map _, ?_⟩
    have hc : (algebraMap Ω Γ(Z, ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom = (π.app ⊤).hom := by
      ext x
      change ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ π.app ⊤).hom x = _
      rw [Iso.hom_inv_id_assoc]
      rfl
    rw [Polynomial.eval₂_map, hc]
    exact h
  have hac : AcycF R (sp Γ(Z, ⊤)) F := GlobalTheory.T.integral_strictHenselian_acyclic_finitary R F hF Ω Γ(Z, ⊤) (sh_of_isSepClosed Ω)
  let i : sp Γ(Z, ⊤) ≅ disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌)) :=
    sch.mapIso Z.isoSpec.symm ≪≫ disc.mapIso e
  have heq : Eqv R i.hom F := (GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).1 _ _ i.hom inferInstance
  have hs := ((GlobalTheory.T.etaleCohomologyEquivalence_basic_properties R F).2.2.2 _ _ i.hom heq).1 hac (m : ℤ) (by exact_mod_cast hm)
  exact Subsingleton.elim _ _

end GlobalTheory.EtC

example : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (k : ℕ) (m : ℕ), 0 < m → ∀ y : H R (disc.obj ((cech (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))).obj (op ⦋k⦌))) F m, y = 0 := GlobalTheory.EtC.cech_level_acyclic
end

