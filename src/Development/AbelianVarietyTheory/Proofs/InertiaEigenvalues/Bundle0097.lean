import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSigmaStableProdLatticeExtSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallEqDominantIndexStatement
section
open Polynomial
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_roots_closedBall_dominant_coeff : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  first | exact @GlobalTheory.card_roots_closedBall_eq_dominantIndex | exact GlobalTheory.card_roots_closedBall_eq_dominantIndex | (intros; apply GlobalTheory.card_roots_closedBall_eq_dominantIndex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSigmaStableProdLatticeExtSqStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_sigma_stable_prod_lattice_ext_sq : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → ∀ (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A), M₁ ∈ B₁.Lin → M₂ ∈ B₂.Lin → Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧ ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ^ 2 = Nat.card {M : Submodule K.O (B₁.A × B₂.A) // (∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} := by
  first | exact @GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq | exact GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq | (intros; apply GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosEqIntegralAdditiveSystemStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h : ℕ) (ϖ : F) (lam π : Fin h → F), (∀ j, π j ≠ 0) → ∀ (L U : ℕ) (M : ℕ → Matrix (Fin h) (Fin h) F), (∀ z, gsum (p ^ h) (L + U) M z = 0 ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = 0) → Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam L U x r = 0} = Nat.card {z : Fin h → F // Integral z ∧ gsum (p ^ h) (L + U) M z = 0} := by
  first | exact @GlobalTheory.PMonE.winPt_card | exact GlobalTheory.PMonE.winPt_card | (intros; apply GlobalTheory.PMonE.winPt_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardWindowZerosInnerEqShiftedOuterStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (h K : ℕ) (ϖ : F), ϖ ≠ 0 → 1 ≤ K → ∀ lam π : Fin h → F, Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ h) ∧ ∀ r, rowT p ϖ lam K x r = 0} = Nat.card {x : Fin h → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam (K - 1) (K + 1) x r = 0} := by
  first | exact @GlobalTheory.PMonE.win_inner | exact GlobalTheory.PMonE.win_inner | (intros; apply GlobalTheory.PMonE.win_inner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyCompanionMatrixEtaleGeneratorSeparable
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem charpoly_companion_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F),
    A.IsGen τ p → (companion p).charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : CharZero F := hU.charZero
  set P := (companion p).charpoly with hP
  have hmon : P.Monic := Matrix.charpoly_monic _
  have hdeg : P.natDegree = r := by rw [hP, Matrix.charpoly_natDegree_eq_dim]; simp
  have hroot : Polynomial.aeval τ P = 0 := by
    apply Algebra.leftMulMatrix_injective (bas A hG)
    rw [map_zero, ← Polynomial.aeval_algHom_apply, leftMul_tau A hG]
    exact Matrix.aeval_self_charpoly _
  have hsmall : ∀ Q : Polynomial F, Q.natDegree < r → Polynomial.aeval τ Q = 0 → Q = 0 := by
    intro Q hQ h0
    rw [Polynomial.aeval_eq_sum_range' hQ] at h0
    rw [← Fin.sum_univ_eq_sum_range (fun i => Q.coeff i • τ ^ i) r] at h0
    have := Fintype.linearIndependent_iff.mp hG.1 (fun i => Q.coeff i) h0
    ext n
    by_cases hn : n < r
    · simpa using this ⟨n, hn⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  rw [PerfectField.separable_iff_squarefree]
  intro q hq
  obtain ⟨s, hs⟩ := hq
  by_contra hqu
  have hP0 : P ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hqdeg : 0 < q.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_ne_zero_of_nonunit hq0 hqu)
  have hQ0 : q * s ≠ 0 := mul_ne_zero hq0 hs0
  have hdegQ : (q * s).natDegree < r := by
    have : P.natDegree = q.natDegree + (q * s).natDegree := by
      rw [hs, mul_assoc, Polynomial.natDegree_mul hq0 hQ0]
    omega
  apply hQ0
  apply hsmall _ hdegQ
  have hnil : IsNilpotent (Polynomial.aeval τ (q * s)) := ⟨2, by
    rw [pow_two, ← map_mul]
    have : q * s * (q * s) = P * s := by rw [hs]; ring
    rw [this, map_mul, hroot, zero_mul]⟩
  exact hnil.eq_zero

end GlobalTheory.JR.LinDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEtaleGeneratorMulMatrixSeparable
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.Et.CharpolySep

theorem squarefree_minpoly {F K : Type} [Field F] [CommRing K] [Algebra F K] [IsReduced K] [Module.Finite F K]
    (τ : K) : Squarefree (minpoly F τ) := by
  intro x hx
  obtain ⟨h, hh⟩ := hx
  have hint : IsIntegral F τ := Algebra.IsIntegral.isIntegral τ
  have hm0 : minpoly F τ ≠ 0 := minpoly.ne_zero hint
  have hs : Polynomial.aeval τ (x * h) = 0 := by
    apply IsReduced.eq_zero
    refine ⟨2, ?_⟩
    have : (x * h) ^ 2 = minpoly F τ * h := by rw [hh]; ring
    rw [← map_pow, this, map_mul, minpoly.aeval, zero_mul]
  have hd : minpoly F τ ∣ x * h := minpoly.dvd F τ hs
  rw [hh] at hd
  have hxh : x * h ≠ 0 := by
    intro h0; apply hm0; rw [hh, mul_assoc, h0, mul_zero]
  have h2 : x * (x * h) ∣ 1 * (x * h) := by rw [one_mul, ← mul_assoc]; exact hd
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hxh).1 h2)

theorem charpoly_lmul_eq_minpoly {F K : Type} [Field F] [CommRing K] [Algebra F K] [Module.Finite F K] {r : ℕ}
    (τ : K) (hli : LinearIndependent F (fun i : Fin r => τ ^ (i : ℕ))) (hr : Module.finrank F K = r) :
    (Algebra.lmul F K τ).charpoly = minpoly F τ := by
  have hint : IsIntegral F τ := Algebra.IsIntegral.isIntegral τ
  have hmon := minpoly.monic hint
  have hcm := LinearMap.charpoly_monic (Algebra.lmul F K τ)
  have hcd : (Algebra.lmul F K τ).charpoly.natDegree = r := by rw [LinearMap.charpoly_natDegree, hr]
  have hCH : Polynomial.aeval τ (Algebra.lmul F K τ).charpoly = 0 := by
    have h1 := LinearMap.aeval_self_charpoly (Algebra.lmul F K τ)
    rw [Polynomial.aeval_algHom_apply] at h1
    have h2 := congrArg (fun f : Module.End F K => f 1) h1
    simpa using h2
  have hdvd : minpoly F τ ∣ (Algebra.lmul F K τ).charpoly := minpoly.dvd F τ hCH
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hcm hdvd ?_
  rw [hcd]
  by_contra hlt
  push_neg at hlt
  have hsum : ∑ i : Fin r, (minpoly F τ).coeff i • τ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (minpoly F τ).coeff i • τ ^ i) r,
      ← Polynomial.aeval_eq_sum_range' hlt, minpoly.aeval]
  have h0 := Fintype.linearIndependent_iff.1 hli (fun i => (minpoly F τ).coeff i) hsum
    ⟨(minpoly F τ).natDegree, hlt⟩
  simp only at h0
  have := hmon.coeff_natDegree
  rw [h0] at this
  exact zero_ne_one this

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p →
    ∀ (j : A.L ≃ₗ[E] (Fin r → E)) (B : Matrix (Fin r) (Fin r) E),
      (∀ z, j (algebraMap A.K A.L τ * z) = B *ᵥ j z) → B.charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hg j B hB
  haveI : CharZero F := hU.charZero
  have hb : IsBaseChange E (IsScalarTower.toAlgHom F A.K A.L).toLinearMap := A.push.out
  haveI : Module.Finite E A.L := Module.Finite.equiv hb.equiv
  haveI : Module.Free E A.L := hb.free
  have e : (Algebra.lmul E A.L (algebraMap A.K A.L τ)).charpoly =
      (Algebra.lmul F A.K τ).charpoly.map (algebraMap F E) := by
    rw [← LinearMap.charpoly_baseChange, ← hb.equiv.charpoly_conj]
    congr 1
    ext y
    obtain ⟨t, rfl⟩ := hb.equiv.surjective y
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [IsBaseChange.equiv_tmul, mul_smul_comm, map_mul]
    | add s t hs ht => simp only [map_add, hs, ht, mul_add]
  have hT : Matrix.toLin' B = j.conj (Algebra.lmul E A.L (algebraMap A.K A.L τ)) := by
    apply LinearMap.ext
    intro v
    have := hB (j.symm v)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [LinearEquiv.conj_apply, this]
  have hc : B.charpoly = (Matrix.toLin' B).charpoly := by
    rw [← LinearMap.charpoly_toMatrix (Matrix.toLin' B) (Pi.basisFun E (Fin r)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
  rw [hc, hT, LinearEquiv.charpoly_conj, e, charpoly_lmul_eq_minpoly τ hg.1 hg.2.1]
  exact (PerfectField.separable_iff_squarefree.2 (squarefree_minpoly τ)).map

end GlobalTheory.JR.Et.CharpolySep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleSplitOfContracting
section
noncomputable section
namespace GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

private theorem coe_powerSeries_smul_eq_smul {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] (a : k⟦X⟧) (x : V) : (a : k⸨X⸩) • x = a • x := by
  rw [← algebraMap_smul (k⸨X⸩) a x, LaurentSeries.coe_algebraMap]

private theorem powerSeries_smul_mem_of_mem {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] (N : Submodule k⟦X⟧ V) {x : V} (hx : x ∈ N)
    (a : k⟦X⟧) : (a : k⸨X⸩) • x ∈ N := by
  rw [coe_powerSeries_smul_eq_smul]; exact N.smul_mem a hx

private theorem mem_of_gmult_eq_zero_of_sub_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U]
    (T : Module.End k U) (P Q : Submodule k U) (x : k) (s : Set U) (hs : s.Finite)
    (hP : P ≤ Submodule.span k s ⊔ Q) (h0 : gmult T P Q x = 0) (y : U) (hy : y ∈ P)
    (hT : (T - algebraMap k (Module.End k U) x) y ∈ Q) : y ∈ Q := by
  set E : Submodule k U := P ⊓ ⨆ m : ℕ, Q.comap ((T - algebraMap k (Module.End k U) x) ^ m) with hE
  have hyE : y ∈ E := by
    refine Submodule.mem_inf.mpr ⟨hy, Submodule.mem_iSup_of_mem 1 ?_⟩
    rw [Submodule.mem_comap, pow_one]; exact hT
  let f : E →ₗ[k] U ⧸ Q := Q.mkQ ∘ₗ E.subtype
  let W : Submodule k (U ⧸ Q) := (Submodule.span k s).map Q.mkQ
  have hWfg : W.FG := (Submodule.fg_span hs).map _
  have : Module.Finite k W := Module.Finite.iff_fg.mpr hWfg
  have hrange : ∀ z : E, f z ∈ W := by
    intro z
    obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp (hP z.2.1)
    refine ⟨a, ha, ?_⟩
    show Q.mkQ a = Q.mkQ (z : U)
    have hc0 : Q.mkQ c = 0 := (Submodule.Quotient.mk_eq_zero Q).mpr hc
    rw [← hac, map_add, hc0, add_zero]
  have hker : LinearMap.ker f = Q.submoduleOf E := by
    ext z
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap]
  have hker' : LinearMap.ker (f.codRestrict W hrange) = Q.submoduleOf E := by
    rw [LinearMap.ker_codRestrict, hker]
  let g := (Q.submoduleOf E).liftQ (f.codRestrict W hrange) hker'.ge
  have hg : LinearMap.ker g = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ hker'.le
  have : IsNoetherian k W := IsNoetherian.iff_fg.mpr inferInstance
  have : Module.Finite k (E ⧸ Q.submoduleOf E) := Module.Finite.of_injective g (LinearMap.ker_eq_bot.mp hg)
  have hq : Module.finrank k (E ⧸ Q.submoduleOf E) = 0 := h0
  have := Module.finrank_zero_iff.mp hq
  have h1 : (Submodule.Quotient.mk (⟨y, hyE⟩ : E) : E ⧸ Q.submoduleOf E) = 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.mk_eq_zero] at h1
  exact h1

private theorem exists_finite_span_sup_shift_of_isLat {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]
    [IsScalarTower k k⟦X⟧ V] (N : Submodule k⟦X⟧ V) (hN : IsLat N) :
    ∃ s : Set V, s.Finite ∧ N.restrictScalars k ≤ Submodule.span k s ⊔ (sh 1 N).restrictScalars k := by
  obtain ⟨t, ht⟩ := hN.1
  refine ⟨↑t, t.finite_toSet, ?_⟩
  intro x hx
  rw [Submodule.restrictScalars_mem, ← ht] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.mem_sup_left (Submodule.subset_span hy)
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y hy0 hy =>
    have hyN : y ∈ N := by rw [ht] at hy0; exact hy0
    obtain ⟨a', ha'⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
      rw [PowerSeries.X_dvd_iff]; simp
    have hsplit : a = PowerSeries.C (PowerSeries.constantCoeff a) + PowerSeries.X * a' := by
      rw [← ha']; ring
    rw [hsplit, add_smul, mul_smul]
    refine add_mem ?_ (Submodule.mem_sup_right ?_)
    · have hc : (PowerSeries.C (PowerSeries.constantCoeff a) : k⟦X⟧) • y = (PowerSeries.constantCoeff a) • y := by
        rw [← algebraMap_smul (k⟦X⟧) (PowerSeries.constantCoeff a) y]; rfl
      rw [hc]; exact Submodule.smul_mem _ _ hy
    · rw [Submodule.restrictScalars_mem, mem_sh_iff_exists]
      exact ⟨a' • y, N.smul_mem a' hyN, by rw [zpow_one, vv_eq_coe_X, coe_powerSeries_smul_eq_smul]⟩

private theorem vv_pow_smul_mem_of_sen_eq_zero {k : Type} [Field k] {l : ℕ} (R : RingPG k l) {V : Type} [AddCommGroup V]
    [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V]
    [IsScalarTower k k⟦X⟧ V] (g : V →ₗ[k] V) (hg : Semi R.γ g) (N : Submodule k⟦X⟧ V) (hN : IsLat N)
    (s : ℕ) (hsen : sen g N (-((s + 1 : ℕ) : k)) = 0) (b : V) (hb : vv k ^ (s + 1) • b ∈ N)
    (hw : g b - b ∈ sh 1 N) : vv k ^ s • b ∈ N := by
  have hv : vv k ≠ 0 := vv_ne_zero k
  obtain ⟨κ, hκ0, hκ⟩ := R.γ_v
  obtain ⟨κ₁, hκ₁⟩ : PowerSeries.X ∣ κ - 1 := by
    rw [PowerSeries.X_dvd_iff]; simp [hκ0]
  have hE : ∀ t : ℕ, ∃ e : k⟦X⟧,
      (1 - κ * PowerSeries.X) ^ t - 1 + (t : k⟦X⟧) * PowerSeries.X = PowerSeries.X ^ 2 * e := by
    intro t
    induction t with
    | zero => exact ⟨0, by simp⟩
    | succ t ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨c * (1 - κ * PowerSeries.X) - κ₁ + (t : k⟦X⟧) * κ, ?_⟩
      push_cast
      linear_combination (1 - κ * PowerSeries.X) * hc - PowerSeries.X * hκ₁
  obtain ⟨e, he⟩ := hE (s + 1)
  have he' : (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) - 1 + ((s + 1 : ℕ) : k⸨X⸩) * vv k
      = vv k ^ 2 * (e : k⸨X⸩) := by
    have h := congrArg (HahnSeries.ofPowerSeries ℤ k) he
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_natCast] at h
    rw [← vv_eq_coe_X] at h
    exact h
  have hw' : (vv k)⁻¹ • (g b - b) ∈ N := by
    have h := (mem_sh_iff_smul_mem (a := 1)).mp hw
    rwa [zpow_neg_one] at h
  have hgy : g (vv k ^ (s + 1) • b) = (vv k * (1 - (κ : k⸨X⸩) * vv k)) ^ (s + 1) • g b := by
    rw [show g (vv k ^ (s + 1) • b) = R.γ (vv k ^ (s + 1)) • g b from hg _ _, map_pow, hκ]
  have hz : nab g (vv k ^ (s + 1) • b) + ((s + 1 : ℕ) : k) • (vv k ^ (s + 1) • b) ∈ sh 1 N := by
    rw [mem_sh_iff_smul_mem]
    have hid : vv k ^ (-(1 : ℤ)) • (nab g (vv k ^ (s + 1) • b) + ((s + 1 : ℕ) : k) • (vv k ^ (s + 1) • b))
        = (e : k⸨X⸩) • (vv k ^ (s + 1) • b) + (((1 - κ * PowerSeries.X) ^ (s + 1) * PowerSeries.X ^ s : k⟦X⟧) : k⸨X⸩) • ((vv k)⁻¹ • (g b - b)) := by
      rw [nab_apply_eq, hgy, Nat.cast_smul_eq_nsmul k, ← Nat.cast_smul_eq_nsmul k⸨X⸩]
      simp only [map_mul, map_pow, map_sub, map_one]
      rw [← vv_eq_coe_X, zpow_neg_one]
      have hvi : vv k * (vv k)⁻¹ = 1 := mul_inv_cancel₀ hv
      set vi := (vv k)⁻¹
      generalize ((s + 1 : ℕ) : k⸨X⸩) = c' at he' ⊢
      generalize (e : k⸨X⸩) = E at he' ⊢
      have hA : vi * (vi * (vv k * (1 - (κ : k⸨X⸩) * vv k)) ^ (s + 1))
          = (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s * vi := by
        rw [mul_pow]
        linear_combination (vi * (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s) * hvi
      have hB : E * vv k ^ (s + 1) = -(vi * (vi * vv k ^ (s + 1))) + vi * (c' * vv k ^ (s + 1))
          + (1 - (κ : k⸨X⸩) * vv k) ^ (s + 1) * vv k ^ s * vi := by
        linear_combination (-(vv k ^ s * vi)) * he' - (E * vv k ^ (s + 1) - vi * vv k ^ s) * hvi
      simp only [smul_add, smul_sub, smul_smul]
      rw [hA, hB]
      simp only [add_smul, neg_smul]
      abel
    rw [hid]
    exact add_mem (powerSeries_smul_mem_of_mem N hb _) (powerSeries_smul_mem_of_mem N hw' _)
  have hkey : vv k ^ (s + 1) • b ∈ sh 1 N := by
    obtain ⟨t, ht, hsp⟩ := exists_finite_span_sup_shift_of_isLat N hN
    exact mem_of_gmult_eq_zero_of_sub_mem (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
      (-((s + 1 : ℕ) : k)) t ht hsp hsen _ hb (by
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply, neg_smul, sub_neg_eq_add]; exact hz)
  have h := (mem_sh_iff_smul_mem (a := 1)).mp hkey
  rw [smul_smul, zpow_neg_one, pow_succ', inv_mul_cancel_left₀ hv] at h
  exact h

theorem cocycle_split_of_contracting : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (D : ModPG R n V), ∀ (N : ZMod n → Submodule k⟦X⟧ V) (J : ZMod n → ℕ), (∀ i, IsLat (N i)) → (∀ i, CondC (D.γ i) (N i)) → (∀ i, pull (D.φ i) (N (i - 1)) ≤ sh 1 (N i)) → (∀ i (j : ℕ), 1 ≤ j → j ≤ J i → sen (D.γ i) (N i) (-(j : k)) = 0) → ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i) → (∀ i, g i ∈ sh 1 (N i)) → (∀ i, b i ∈ sh (-(J i)) (N i)) → ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧ g i = D.γ i (m i) - m i := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D N J hlat hC hφ hsen b g hcoc hg hb
  have hsub : ∀ i, sh 1 (N i) ≤ N i := by
    intro i
    have h := sh_le_sh_of_le (a := 1) (b := 0) (by norm_num) (N i)
    rwa [sh_zero_eq] at h
  have hφ' : ∀ i, ∀ x ∈ N (i - 1), D.φ i x ∈ sh 1 (N i) := fun i x hx =>
    hφ i (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hw : ∀ i, D.γ i (b i) - b i ∈ sh 1 (N i) := by
    intro i
    rw [hcoc i]
    exact sub_mem (hφ' i _ (hsub (i - 1) (hg (i - 1)))) (hg i)
  have hbN : ∀ i, b i ∈ N i := by
    intro i
    have key : ∀ d, d ≤ J i → vv k ^ (J i - d) • b i ∈ N i := by
      intro d
      induction d with
      | zero => intro _; simpa using (mem_sh_iff_smul_mem).mp (hb i)
      | succ d ih =>
        intro hd
        have e : J i - d = (J i - (d + 1)) + 1 := by omega
        have h1 := ih (by omega)
        rw [e] at h1
        have h2 := hsen i (J i - d) (by omega) (by omega)
        rw [e] at h2
        exact vv_pow_smul_mem_of_sen_eq_zero R (D.γ i) (D.γ_semi i) (N i) (hlat i) _ h2 (b i) h1 (hw i)
    simpa using key (J i) le_rfl
  obtain ⟨m, hmN, hm⟩ := (one_sub_frob_bij R D N hlat hφ').1 b hbN
  have hhN : ∀ i, D.γ i (m i) - m i - g i ∈ N i := fun i =>
    sub_mem (hsub i (hC i (m i) (hmN i))) (hsub i (hg i))
  have hhφ : ∀ i, D.φ i (D.γ (i - 1) (m (i - 1)) - m (i - 1) - g (i - 1)) = D.γ i (m i) - m i - g i := by
    intro i
    have e1 : D.φ i (m (i - 1)) = b i + m i := by rw [← hm i]; abel
    have e2 : D.φ i (g (i - 1)) = D.γ i (b i) - b i + g i := by rw [hcoc i]; abel
    rw [map_sub, map_sub, D.comm, e1, e2, map_add]
    abel
  have h0 := (one_sub_frob_bij R D N hlat hφ').2 (fun i => D.γ i (m i) - m i - g i) hhN hhφ
  refine ⟨m, hmN, fun i => ⟨(hm i).symm, ?_⟩⟩
  have h3 := congrFun h0 i
  simp only [Pi.zero_apply] at h3
  exact (sub_eq_zero.mp h3).symm

end GlobalTheory.PhiGam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsCharpolyCoeffEqStatement
section
open GlobalTheory.JR Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.companionMatrixOfCoeffs_charpoly_coeff_eq : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := by
  first | exact @GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | exact GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring | (intros; apply GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois
section
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem norm_val_monoidHom_units_eq_one {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    ‖((ξ g : ℂˣ) : ℂ)‖ = 1 := by
  have h : (ξ g) ^ (Nat.card G) = 1 := by rw [← map_pow, pow_card_eq_one']; exact map_one ξ
  refine Complex.norm_eq_one_of_pow_eq_one (n := Nat.card G) ?_ Nat.card_pos.ne'
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem isIntegral_int_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) :
    IsIntegral ℤ z :=
  ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn.ne', by simp [h]⟩

theorem isIntegral_val_monoidHom_units {G : Type} [Group G] [Finite G] (ξ : G →* ℂˣ) (g : G) :
    IsIntegral ℤ ((ξ g : ℂˣ) : ℂ) := by
  refine isIntegral_int_of_pow_eq_one (n := Nat.card G) Nat.card_pos ?_
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]

theorem isIntegral_addChar_apply {k : Type} [Field k] [Fintype k] (ψ : AddChar k ℂ) (x : k) :
    IsIntegral ℤ (ψ x) := by
  refine isIntegral_int_of_pow_eq_one (n := Fintype.card k) Fintype.card_pos ?_
  rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]

theorem complexMatrixGaussSum_norm_integral_galois :
    ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → ∀ S : ℂ, S = (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))) → ‖S‖ ^ 2 = (Fintype.card k : ℝ) ^ (r ^ 2) ∧ IsIntegral ℤ S ∧ IsIntegral ℤ ((Fintype.card k : ℂ) ^ (r ^ 2) * S⁻¹) ∧ ∀ (τ : ℂ ≃+* ℂ) (ξ' : kˣ →* ℂˣ), (∀ x, ((ξ' x : ℂˣ) : ℂ) = τ ((ξ x : ℂˣ) : ℂ)) → ∃ a : kˣ, (∀ x, τ (ψ x) = ψ ((a : k) * x)) ∧ τ S = ((ξ' a : ℂˣ) : ℂ) ^ r * ∑ x : GL (Fin r) k, (((ξ' (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) := by
  intro k _ _ _ ψ ξ r hψ hξ S hS
  have hN := GlobalTheory.T.matrixGaussSum_mul_dual_eq_card_pow_sq k ℂ ψ ξ r hψ hξ
  simp only [Matrix.one_mul] at hN
  rw [← hS] at hN
  set D := ∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) *
    ψ⁻¹ (Matrix.trace (x : Matrix (Fin r) (Fin r) k)) with hD
  have hconj : D = starRingEnd ℂ S := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, AddChar.inv_apply, AddChar.map_neg_eq_conj, MonoidHom.inv_apply, inv_inv,
      Units.val_inv_eq_inv_val, map_inv₀,
      ← Complex.inv_eq_conj (norm_val_monoidHom_units_eq_one ξ _), inv_inv]
  have hDint : IsIntegral ℤ D := by
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (isIntegral_addChar_apply _ _)
    exact isIntegral_val_monoidHom_units _ _
  have hSint : IsIntegral ℤ S := by
    rw [hS]
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (isIntegral_addChar_apply _ _)
    rw [← map_inv]
    exact isIntegral_val_monoidHom_units _ _
  have hq0 : (Fintype.card k : ℂ) ^ (r ^ 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hS0 : S ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hN
    exact hq0 hN.symm
  refine ⟨?_, hSint, ?_, ?_⟩
  · rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hN
    exact_mod_cast hN
  · rw [← hN, mul_comm S D, mul_assoc, mul_inv_cancel₀ hS0, mul_one]
    exact hDint
  · intro τ ξ' hξ'

    let φ : AddChar k ℂ := (τ : ℂ →+* ℂ).toMonoidHom.compAddChar ψ
    have hbij : Function.Bijective (fun b : k => ψ.mulShift b) :=
      (Fintype.bijective_iff_injective_and_card _).mpr
        ⟨AddChar.to_mulShift_inj_of_isPrimitive hψ, AddChar.card_eq.symm⟩
    obtain ⟨b, hb⟩ := hbij.2 φ
    have hbφ : ∀ x, τ (ψ x) = ψ (b * x) := fun x => by
      have := DFunLike.congr_fun hb x
      simpa [φ, AddChar.mulShift_apply] using this.symm
    have hb0 : b ≠ 0 := by
      rintro rfl
      have h1 : ψ.mulShift 1 ≠ 1 := hψ one_ne_zero
      apply h1
      ext x
      have := hbφ x
      rw [zero_mul, AddChar.map_zero_eq_one, ← map_one τ] at this
      rw [AddChar.mulShift_apply, one_mul, AddChar.one_apply]
      exact τ.injective this
    have hξ'1 : ξ' ≠ 1 := by
      intro h1
      apply hξ
      ext x
      have := hξ' x
      rw [h1, MonoidHom.one_apply, Units.val_one, ← map_one τ] at this
      exact (τ.injective this).symm
    refine ⟨Units.mk0 b hb0, fun x => hbφ x, ?_⟩
    let g : GL (Fin r) k :=
      Units.map (Matrix.scalar (Fin r) : k →+* Matrix (Fin r) (Fin r) k).toMonoidHom (Units.mk0 b hb0)
    have hg : (g : Matrix (Fin r) (Fin r) k) = Matrix.scalar (Fin r) b := rfl
    have hdet : Matrix.GeneralLinearGroup.det g = (Units.mk0 b hb0) ^ r := by
      ext
      simp [hg, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]
    have key := (GlobalTheory.matrixGaussSum_singular_and_invertible k ℂ ψ ξ' r hψ hξ'1).2 g
    rw [hdet, map_pow, Units.val_pow_eq_pow_val] at key
    simp only [Matrix.one_mul] at key
    rw [← key, hS, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, hbφ, Units.val_inv_eq_inv_val, map_inv₀, ← hξ', ← Units.val_inv_eq_inv_val, hg,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceSubgroupsGLPadicStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruenceSubgroups_GL_padic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n], ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔ ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  first | exact @GlobalTheory.congruenceSubgroups_GL_padic | exact GlobalTheory.congruenceSubgroups_GL_padic | (intros; apply GlobalTheory.congruenceSubgroups_GL_padic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCohomologyVanishesOfPrimeToLNormalNoInStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousCohomology_vanishes_of_primeToL_normal_no_invariants : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousConstSMul R M] (ρ : Representation R Γ M) (l : ℕ) (J : Subgroup Γ), l.Prime → J.Normal → IsClosed (J : Set Γ) → (∀ U : Subgroup Γ, U.Normal → IsOpen (U : Set Γ) → ∀ j ∈ J, ∃ n, Nat.Coprime n l ∧ j ^ n ∈ U) → ContAction ρ → (∀ m : M, ∃ n, l ^ n • m = 0) → (∀ m : M, (∀ j ∈ J, ρ j m = m) → m = 0) → H0 ρ = ⊥ ∧ Subsingleton (H1 ρ) ∧ Subsingleton (H2 ρ) := by
  first | exact @GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes | exact GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes | (intros; apply GlobalTheory.PrimeToNormalVanishing.cohomology_vanishes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousEtaleHermitianPairNormAndMapZeroStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), Continuous A.NL ∧ A.NL 0 = 0 := by
  first | exact @GlobalTheory.etale_norm_continuous_and_zero | exact GlobalTheory.etale_norm_continuous_and_zero | (intros; apply GlobalTheory.etale_norm_continuous_and_zero <;> assumption)
end

