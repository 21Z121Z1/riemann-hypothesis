import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallDualLattices
section
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR.DualLattice

variable {F : Type} [NontriviallyNormedField F]

theorem stdChar_key {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F)
    (h : ∀ c : F, ‖c‖ ≤ 1 → ψ (c * y) = 1) : ‖y‖ ≤ 1 := by
  by_contra hy
  push Not at hy
  obtain ⟨x0, hx0, hx1⟩ := hψ.2
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
  have hinv : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy
  have := h _ (hx1 _ hinv)
  rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  exact hx0 this

theorem stdChar_continuous {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) : Continuous ψ := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_)
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : y = x + (y - x) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.1 (y - x) (by simpa [dist_eq_norm] using hy), mul_one]

variable {V : Type} [AddCommGroup V] [Module F V]

def box [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) : AddSubgroup V where
  carrier := {x | ∀ i, ‖e.repr x i‖ ≤ r}
  zero_mem' := by intro i; simpa using hr
  add_mem' := by
    intro a b ha hb i
    rw [map_add, Finsupp.add_apply]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
  neg_mem' := by
    intro a ha i
    simpa using ha i

theorem mem_box [IsUltrametricDist F] {ι : Type} (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    x ∈ box e r hr ↔ ∀ i, ‖e.repr x i‖ ≤ r := Iff.rfl

noncomputable def coordHomeo [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) : V ≃ₜ (ι → F) :=
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  { e.equivFun.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.equivFun.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.equivFun.symm.toLinearMap }

theorem box_eq [IsUltrametricDist F] [TopologicalSpace V] [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 ≤ r) :
    (box e r hr : Set V) = coordHomeo e ⁻¹' Metric.closedBall 0 r := by
  ext x
  rw [SetLike.mem_coe, mem_box, Set.mem_preimage, mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hr]
  rfl

theorem box_open_compact [IsUltrametricDist F] [LocallyCompactSpace F] [TopologicalSpace V]
    [IsModuleTopology F V] {ι : Type} [Fintype ι]
    (e : Module.Basis ι F V) (r : ℝ) (hr : 0 < r) :
    IsOpen (box e r hr.le : Set V) ∧ IsCompact (box e r hr.le : Set V) := by
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  rw [box_eq]
  exact ⟨(IsUltrametricDist.isOpen_closedBall _ hr.ne').preimage (coordHomeo e).continuous,
    (coordHomeo e).isCompact_preimage.2 (isCompact_closedBall _ _)⟩

theorem box_dual [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) {ι : Type} [Fintype ι]
    (e e' : Module.Basis ι F V) (B : V → V → F)
    (hB : ∀ x y, B x y = ∑ i, e.repr x i * e'.repr y i) (t : F) (ht : t ≠ 0) (y : V) :
    y ∈ box e' ‖t⁻¹‖ (norm_nonneg _) ↔ ∀ x ∈ box e ‖t‖ (norm_nonneg _), ψ (B x y) = 1 := by
  classical
  have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
  constructor
  · intro hy x hx
    apply hψ.1
    rw [hB]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    calc _ ≤ ‖t‖ * ‖t⁻¹‖ := mul_le_mul (hx i) (hy i) (norm_nonneg _) (norm_nonneg _)
      _ = 1 := by rw [← norm_mul, mul_inv_cancel₀ ht, norm_one]
  · intro h i
    have h1 : ‖t * e'.repr y i‖ ≤ 1 := by
      refine stdChar_key hψ _ fun c hc => ?_
      have hx : (c * t) • e i ∈ box e ‖t‖ (norm_nonneg _) := by
        intro j
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs
        · rw [smul_eq_mul, mul_one, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hc
        · simp
      have := h _ hx
      rw [hB, Finset.sum_eq_single i] at this
      · simpa [mul_assoc] using this
      · intro j _ hj
        simp [Finsupp.single_apply, hj.symm]
      · simp
    rw [norm_mul] at h1
    rw [norm_inv, ← one_div, le_div_iff₀ htp, mul_comm]
    exact h1

end GlobalTheory.JR.DualLattice

open GlobalTheory.JR.DualLattice in

theorem GlobalTheory.JR.exists_small_dual_lattices : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → Continuous (fun p : V × V => ψ (β p.1 p.2)) ∧ (∀ U ∈ 𝓝 (0 : V), ∃ M N : AddSubgroup V, (M : Set V) ⊆ U ∧ IsOpen (M : Set V) ∧ IsCompact (M : Set V) ∧ IsOpen (N : Set V) ∧ IsCompact (N : Set V) ∧ (∀ y, y ∈ N ↔ ∀ x ∈ M, ψ (β x y) = 1) ∧ (∀ x, x ∈ M ↔ ∀ y ∈ N, ψ (β x y) = 1)) := by
  intro F _ _ _ ψ hψ V _ _ _ _ _ β hs hβ
  classical
  let e := Module.finBasis F V
  let e' := β.dualBasis hβ e
  have hB : ∀ x y, β x y = ∑ i, e.repr x i * e'.repr y i := by
    intro x y
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, hs.eq]
  refine ⟨(stdChar_continuous hψ).comp ?_, fun U hU => ?_⟩
  · simp only [hB]
    refine continuous_finset_sum _ fun i _ => ?_
    exact (((continuous_apply i).comp (coordHomeo e).continuous).comp continuous_fst).mul
      (((continuous_apply i).comp (coordHomeo e').continuous).comp continuous_snd)
  · have h0 : (coordHomeo e).symm 0 = 0 := map_zero e.equivFun.symm
    have hU' : (coordHomeo e).symm ⁻¹' U ∈ 𝓝 (0 : Fin (Module.finrank F V) → F) :=
      (coordHomeo e).symm.continuous.continuousAt.preimage_mem_nhds (by rwa [h0])
    obtain ⟨ε, hε, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hU'
    obtain ⟨t, ht0, htε⟩ := NormedField.exists_norm_lt F hε
    have ht : t ≠ 0 := norm_pos_iff.1 ht0
    have hti : 0 < ‖t⁻¹‖ := norm_pos_iff.2 (inv_ne_zero ht)
    refine ⟨box e ‖t‖ (norm_nonneg _), box e' ‖t⁻¹‖ (norm_nonneg _), ?_,
      (box_open_compact e _ ht0).1, (box_open_compact e _ ht0).2,
      (box_open_compact e' _ hti).1, (box_open_compact e' _ hti).2,
      box_dual hψ e e' (fun x y => β x y) hB t ht, fun x => ?_⟩
    · rw [box_eq]
      intro x hx
      have := hsub (Metric.closedBall_subset_closedBall htε.le hx)
      simpa using this
    · have := box_dual hψ e' e (fun y x => β x y)
        (fun y x => by simp only [hB, mul_comm]) t⁻¹ (inv_ne_zero ht) x
      simpa only [inv_inv] using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitEtaleHermitianPairIsometry
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.JR.SplitEt

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem algebraMap_norm_eq_mul_star (z : E) : algebraMap F E (Algebra.norm F z) = z * star z := by
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let σ : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := starRingAut)
    (fun x => by rw [starRingAut_apply]; exact Unram.star_fix (E := E) x)
  have hσz : ∀ y, σ y = star y := fun y => rfl
  have hσ : (1 : E ≃ₐ[F] E) ≠ σ := by
    obtain ⟨y, hy⟩ := Unram.star_ne (F := F) (E := E)
    intro h
    apply hy
    rw [← hσz, ← h]
    rfl
  classical
  have hle := AlgEquiv.card_le (F := F) (K := E)
  have hge : ({1, σ} : Finset (E ≃ₐ[F] E)).card ≤ Fintype.card (E ≃ₐ[F] E) := Finset.card_le_univ _
  rw [Finset.card_pair hσ] at hge
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by omega
  haveI : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card, hcard, h2])
  have huniv : ({1, σ} : Finset (E ≃ₐ[F] E)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Finset.card_pair hσ, hcard])
  rw [Algebra.norm_eq_prod_automorphisms, ← huniv, Finset.prod_pair hσ, hσz]
  rfl

def piCoord {ι : Type} [Fintype ι] (b : Module.Basis ι F E) (r : ℕ) :
    (Fin r → E) ≃ₗ[Fin r → F] (ι → (Fin r → F)) where
  toFun y k i := b.repr (y i) k
  invFun c i := ∑ k, c k i • b k
  map_add' y y' := by ext k i; simp
  map_smul' x y := by ext k i; simp
  left_inv y := by funext i; simp [b.sum_repr]
  right_inv c := by classical ext k i; simp [Finsupp.single_apply]

theorem norm_pi_apply (r : ℕ) (y : Fin r → E) (i : Fin r) :
    Algebra.norm (Fin r → F) y i = Algebra.norm F (y i) := by
  have h2 : Module.finrank F E = 2 := Unram.finrank_eq
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  classical
  let b := Module.finBasis F E
  let B := Module.Basis.ofEquivFun (piCoord b r)
  have hB : ∀ k, B k = fun _ => b k := by
    intro k; rw [Module.Basis.coe_ofEquivFun]; funext i; simp [piCoord, Pi.single_apply, ite_apply, ite_smul]
  have hBr : ∀ z k, B.repr z k = fun i => b.repr (z i) k := fun z k => by
    rw [Module.Basis.ofEquivFun_repr_apply]; rfl
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det b]
  rw [show (det (Algebra.leftMulMatrix B y)) i = Pi.evalRingHom (fun _ => F) i (det _) from rfl, RingHom.map_det]
  congr 1
  ext k l
  simp [RingHom.mapMatrix_apply, Algebra.leftMulMatrix_eq_repr_mul, hB, hBr]

theorem trace_pi_apply (r : ℕ) (z : Fin r → E) : Algebra.trace E (Fin r → E) z = ∑ i, z i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E (Fin r))]
  simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul]

end GlobalTheory.JR.SplitEt

namespace GlobalTheory.JR.SplitEt

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]

theorem push_pi (r : ℕ) : Algebra.IsPushout F E (Fin r → F) (Fin r → E) := by
  refine ⟨?_⟩
  have h := IsBaseChange.finitePow (Fin r) (IsBaseChange.linearMap F E)
  have e : (IsScalarTower.toAlgHom F (Fin r → F) (Fin r → E)).toLinearMap = (Algebra.linearMap F E).compLeft (Fin r) :=
    LinearMap.ext fun _ => rfl
  rw [e]
  exact h

abbrev splitEt (r : ℕ) : Et F E :=
  haveI : LocallyCompactSpace F := Unram.lcF E
  letI : MeasurableSpace (Fin r → F) := borel (Fin r → F)
  haveI : BorelSpace (Fin r → F) := ⟨rfl⟩
  letI tL : TopologicalSpace (Fin r → E) := moduleTopology F (Fin r → E)
  letI : MeasurableSpace (Fin r → E) := borel (Fin r → E)
  haveI : BorelSpace (Fin r → E) := ⟨rfl⟩
  haveI : IsModuleTopology F (Fin r → E) := ⟨rfl⟩
  { K := Fin r → F
    L := Fin r → E
    push := push_pi F E r
    star_K := fun x => by funext i; exact Unram.star_fix (E := E) (x i)
    star_E := fun y => rfl }

end GlobalTheory.JR.SplitEt

theorem GlobalTheory.JR.exists_split_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), ∃ (A : Et F E) (e : A.K ≃ₐ[F] (Fin r → F)) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom 1 j ∧ ∀ y i, algebraMap F E (e (A.NL y) i) = j y i * star (j y i) := by
  intro F E _ _ _ _ _ r
  refine ⟨SplitEt.splitEt F E r, AlgEquiv.refl, LinearEquiv.refl E _, ?_, ?_⟩
  · intro y y'
    show star y ⬝ᵥ y' = Algebra.trace E (Fin r → E) (algebraMap (Fin r → F) (Fin r → E) 1 * star y * y')
    rw [map_one, one_mul, SplitEt.trace_pi_apply]
    simp [dotProduct]
  · intro y i
    show algebraMap F E (Algebra.norm (Fin r → F) y i) = y i * star (y i)
    rw [SplitEt.norm_pi_apply, SplitEt.algebraMap_norm_eq_mul_star]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubringEqOK
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Polynomial

noncomputable section

namespace GlobalTheory.JR.Et

theorem charpoly_dvd_pow_of_aeval_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := by
  set a : Matrix n n R[X] := algebraMap R[X] (Matrix n n R[X]) X with ha_def
  set b : Matrix n n R[X] := (Algebra.ofId R R[X]).mapMatrix M with hb_def
  have hab : Commute a b := Algebra.commutes X b
  have key : ∀ q : R[X], ∃ H, (a - b) * H = aeval a q - aeval b q := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨H1, h1⟩ := hp
      obtain ⟨H2, h2⟩ := hq
      exact ⟨H1 + H2, by rw [mul_add, h1, h2, map_add, map_add]; abel⟩
    | monomial k c =>
      refine ⟨algebraMap R (Matrix n n R[X]) c * ∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i), ?_⟩
      rw [aeval_monomial, aeval_monomial, ← mul_assoc, ← Algebra.commutes, mul_assoc, hab.mul_geom_sum₂,
        mul_sub]
  obtain ⟨H, hH⟩ := key p
  have hb : aeval b p = 0 := by
    rw [hb_def, aeval_algHom_apply, hp, map_zero]
  have ha : aeval a p = algebraMap R[X] (Matrix n n R[X]) p := by
    rw [ha_def, aeval_algebraMap_apply, aeval_X_left_apply]
  have hch : (a - b).det = M.charpoly := rfl
  refine ⟨H.det, ?_⟩
  rw [← hch, ← Matrix.det_mul, hH, hb, sub_zero, ha, Matrix.algebraMap_eq_diagonal, Matrix.det_diagonal]
  simp

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem aeval_self_charpoly_lmul (A : Et F E) (z : A.K) :
    aeval z (LinearMap.charpoly (Algebra.lmul F A.K z)) = 0 := by
  have h := LinearMap.aeval_self_charpoly (Algebra.lmul F A.K z)
  have h' : Algebra.lmul F A.K (aeval z (LinearMap.charpoly (Algebra.lmul F A.K z))) = 0 := by
    rw [← aeval_algHom_apply]; exact h
  simpa using congrArg (fun f : Module.End F A.K => f 1) h'

theorem mem_OK_iff_isIntegral [IsUltrametricDist F] (A : Et F E) (z : A.K) :
    z ∈ A.OK ↔ IsIntegral (NormedField.valuation (K := F)).integer z := by
  constructor
  · intro hz
    have hl : LinearMap.charpoly (Algebra.lmul F A.K z) ∈
        Polynomial.lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      refine ⟨⟨_, ?_⟩, rfl⟩
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
      exact_mod_cast hz i
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap F, hq]
    exact aeval_self_charpoly_lmul A z
  · rintro ⟨p, hpm, hp⟩ i
    have hp' : aeval z (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]; exact hp
    have h1 : aeval (Algebra.lmul F A.K z) (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, hp', map_zero]
    let bs := Module.finBasis F A.K
    have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z))
        (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, h1, map_zero]
    have h3 := charpoly_dvd_pow_of_aeval_zero _ _ h2
    have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z)).charpoly =
        LinearMap.charpoly (Algebra.lmul F A.K z) := LinearMap.charpoly_toMatrix _ bs
    rw [h4, ← Polynomial.map_pow] at h3
    have h5 := Polynomial.isIntegral_coeff_of_dvd _ _ (hpm.pow _) (LinearMap.charpoly_monic _) h3 i
    have h6 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h5
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h6
    exact_mod_cast h6

theorem OK_isSubring : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), ∃ R : Subring A.K, (R : Set A.K) = A.OK := by
  intro F E _ _ _ _ hU A
  haveI : IsUltrametricDist F := hU.ultraF
  refine ⟨(integralClosure (NormedField.valuation (K := F)).integer A.K).toSubring, ?_⟩
  ext z
  exact (mem_OK_iff_isIntegral A z).symm

end GlobalTheory.JR.Et
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTraceNeZeroFiniteLocalZmodPrimePow
section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.LocalTraceNonzero

theorem isUnit_of_cast_ne_zero (l b : ℕ) [Fact l.Prime] (hb : b ≠ 0) (x : ZMod (l ^ b))
    (hx : ZMod.castHom (dvd_pow_self l hb) (ZMod l) x ≠ 0) : IsUnit x := by
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x] at hx ⊢
  rw [map_natCast, ne_eq, ZMod.natCast_eq_zero_iff] at hx
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right _ ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hx))

theorem henselian_of_finite (A : Type) [CommRing A] [Finite A] [IsLocalRing A] :
    HenselianLocalRing A := by
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map _)

theorem exists_trace_ne_zero_adjoinRoot (l : ℕ) [Fact l.Prime] (p : (ZMod l)[X]) (hp : Irreducible p) :
    ∃ z : AdjoinRoot p, Algebra.trace (ZMod l) (AdjoinRoot p) z ≠ 0 := by
  haveI : Fact (Irreducible p) := ⟨hp⟩
  haveI : FiniteDimensional (ZMod l) (AdjoinRoot p) := (AdjoinRoot.powerBasis hp.ne_zero).finite
  haveI : Algebra.IsSeparable (ZMod l) (AdjoinRoot p) := inferInstance
  obtain ⟨z, hz⟩ := Algebra.trace_surjective (ZMod l) (AdjoinRoot p) 1
  exact ⟨z, by rw [hz]; exact one_ne_zero⟩

theorem exists_trace_ne_zero : ∀ (l b e : ℕ) [Fact l.Prime] (B : Type) [CommRing B] [Finite B] [Algebra (ZMod (l ^ b)) B] (π : B), 0 < e → (∀ x : B, ¬ IsUnit x ↔ π ∣ x) → Ideal.span {((l : ℕ) : B)} = Ideal.span {π ^ e} → Nat.card B = Nat.card (B ⧸ Ideal.span {π}) ^ (b * e) → ¬ l ^ b ∣ e → ∃ c : B, Algebra.trace (ZMod (l ^ b)) B c ≠ 0 := by
  intro l b e _ B _ _ _ π he hunit hspan hcard hdvd
  have hb : b ≠ 0 := by rintro rfl; exact hdvd (by simp)
  have hl := (Fact.out : l.Prime)
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact (hunit 0).2 (dvd_zero π) (by rw [Subsingleton.elim (0 : B) 1]; exact isUnit_one)
  have hnon : ∀ x : B, x ∈ nonunits B ↔ π ∣ x := fun x => hunit x
  haveI : IsLocalRing B := IsLocalRing.of_nonunits_add
    (fun a c ha hc => (hnon _).2 (dvd_add ((hnon a).1 ha) ((hnon c).1 hc)))
  have hmax : IsLocalRing.maximalIdeal B = Ideal.span {π} := by
    ext x; rw [IsLocalRing.mem_maximalIdeal, hnon, Ideal.mem_span_singleton]
  set K := IsLocalRing.ResidueField B
  have hlmax : ((l : ℕ) : B) ∈ IsLocalRing.maximalIdeal B := by
    rw [hmax, Ideal.mem_span_singleton]
    have : ((l : ℕ) : B) ∈ Ideal.span {π ^ e} := hspan ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_span_singleton] at this
    exact (dvd_pow_self π he.ne').trans this
  haveI : CharP K l := by
    rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue B),
      IsLocalRing.residue_eq_zero_iff]
    exact hlmax
  letI : Algebra (ZMod l) K := ZMod.algebra K l
  haveI : Finite K := Finite.of_surjective _ IsLocalRing.residue_surjective
  obtain ⟨a, p, hpm, hpirr, hpa, hpa', hgen, hcardK⟩ := GlobalTheory.T.exists_separable_generator_card_eq_pow_natDegree l K
  set g : ZMod (l ^ b) →+* ZMod l := ZMod.castHom (dvd_pow_self l hb) (ZMod l) with hg
  have hgs : Function.Surjective g := ZMod.ringHom_surjective g
  obtain ⟨h, hhp, hdeg, hmon⟩ :=
    lifts_and_natDegree_eq_and_monic ((mem_lifts p).2 (map_surjective g hgs p)) hpm
  have hcomp : (algebraMap B K).comp (algebraMap (ZMod (l ^ b)) B) =
      (algebraMap (ZMod l) K).comp g := RingHom.ext_zmod _ _
  have key : ∀ q : (ZMod (l ^ b))[X],
      aeval a (q.map (algebraMap (ZMod (l ^ b)) B)) = aeval a (q.map g) := by
    intro q
    simp only [aeval_def, eval₂_map, hcomp]
  haveI : HenselianLocalRing B := henselian_of_finite B
  have H2 := ((HenselianLocalRing.TFAE B).out 0 1).mp ‹_›
  obtain ⟨ω, hω, hωa⟩ := H2 (h.map (algebraMap _ B)) (hmon.map _) a
    (by rw [key, hhp]; exact hpa)
    (by rw [derivative_map, key, ← derivative_map, hhp]; exact hpa')
  have hω' : eval₂ (algebraMap (ZMod (l ^ b)) B) ω h = 0 := by
    rw [← eval_map]; exact hω

  set C := AdjoinRoot h
  let φ : C →+* B := AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω'
  have hsurj : ∀ x : B, ∃ y : C, x - φ y ∈ Ideal.span {π} := by
    intro x
    obtain ⟨q, hq⟩ := hgen (IsLocalRing.residue B x)
    obtain ⟨q', rfl⟩ := map_surjective g hgs q
    refine ⟨AdjoinRoot.mk h q', ?_⟩
    rw [← hmax, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hq]
    show _ = IsLocalRing.residue B (AdjoinRoot.lift (algebraMap (ZMod (l ^ b)) B) ω hω' (AdjoinRoot.mk h q'))
    rw [AdjoinRoot.lift_mk, hom_eval₂, hωa, ← key, aeval_def, eval₂_map]
    rfl
  have hlb : ((l : ℕ) : B) ^ b = 0 := by
    rw [← Nat.cast_pow, ← map_natCast (algebraMap (ZMod (l ^ b)) B), ZMod.natCast_self, map_zero]
  have hpe : π ^ e ∈ Ideal.span {φ (l : C)} := by
    rw [map_natCast, hspan]; exact Ideal.mem_span_singleton_self _
  have hE := GlobalTheory.T.exists_sum_mul_pow_of_residue_surjective_of_nilpotent C B φ π (l : C) e b hsurj hpe (by rw [map_natCast]; exact hlb)

  letI : Algebra C B := φ.toAlgebra
  have hsmul : ∀ (c : C) (x : B), c • x = φ c * x := fun c x => Algebra.smul_def c x
  let T : (Fin e → C) →ₗ[C] B := Fintype.linearCombination C (fun j : Fin e => π ^ (j : ℕ))
  have hTsurj : Function.Surjective T := by
    intro x
    obtain ⟨c, hc⟩ := hE x
    refine ⟨c, ?_⟩
    rw [Fintype.linearCombination_apply, hc]
    simp only [hsmul]
  let pb := AdjoinRoot.powerBasis' hmon
  have hcardC : Nat.card C = (l ^ b) ^ p.natDegree := by
    rw [Nat.card_congr pb.basis.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin, AdjoinRoot.powerBasis'_dim, hdeg]
  have hcardB : Nat.card B = Nat.card (Fin e → C) := by
    rw [Nat.card_fun, hcardC, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin, hcard, ← hmax]
    change Nat.card K ^ (b * e) = _
    rw [hcardK, ← pow_mul, ← pow_mul, ← pow_mul]
    ring_nf
  haveI : NeZero (l ^ b) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : Module.Finite (ZMod (l ^ b)) C := pb.finite
  haveI : Finite C := Module.finite_of_finite (ZMod (l ^ b))
  have hTbij : Function.Bijective T := hTsurj.bijective_of_nat_card_le hcardB.ge
  let bB : Module.Basis (Fin e) C B := Module.Basis.ofEquivFun (LinearEquiv.ofBijective T hTbij).symm
  haveI : IsScalarTower (ZMod (l ^ b)) C B := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have htr : ∀ y : C, Algebra.trace (ZMod (l ^ b)) B (φ y) = (e : ZMod (l ^ b)) * Algebra.trace (ZMod (l ^ b)) C y := by
    intro y
    rw [← Algebra.trace_trace_of_basis pb.basis bB]
    change Algebra.trace (ZMod (l ^ b)) C (Algebra.trace C B (algebraMap C B y)) = _
    rw [Algebra.trace_algebraMap_of_basis bB, map_nsmul, Fintype.card_fin, nsmul_eq_mul]

  have hirr' : Irreducible (h.map g) := hhp ▸ hpirr
  obtain ⟨z, hz⟩ := exists_trace_ne_zero_adjoinRoot l (h.map g) hirr'
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨q', rfl⟩ := map_surjective g hgs q
  have hmap : AdjoinRoot.map g h (h.map g) dvd_rfl (AdjoinRoot.mk h q') =
      AdjoinRoot.mk (h.map g) (q'.map g) := by
    rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← AdjoinRoot.aeval_eq, aeval_def, eval₂_map,
      AdjoinRoot.algebraMap_eq]
  have hu : IsUnit (Algebra.trace (ZMod (l ^ b)) C (AdjoinRoot.mk h q')) := by
    apply isUnit_of_cast_ne_zero l b hb
    rw [← hg, GlobalTheory.T.map_trace_adjoinRoot_eq_trace_map _ _ g h hmon, hmap]; exact hz
  refine ⟨φ (AdjoinRoot.mk h q'), ?_⟩
  rw [htr]
  intro h0
  exact hdvd ((ZMod.natCast_eq_zero_iff _ _).1 (hu.mul_left_eq_zero.1 h0))

end GlobalTheory.LocalTraceNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteEtaleHermitianLinearEquivContinuous
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem et_equiv_continuous (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous j ∧ Continuous j.symm := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : CompleteSpace F := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace
  haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  haveI : FiniteDimensional F (Fin r → E) := inferInstance
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : ContinuousSMul F A.L := IsModuleTopology.toContinuousSMul F A.L
  refine ⟨?_, ?_⟩
  · exact IsModuleTopology.continuous_of_linearMap (R := F) (j.toLinearMap.restrictScalars F)
  · exact LinearMap.continuous_of_finiteDimensional (j.symm.toLinearMap.restrictScalars F)

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenEigenMultiplicityQuotientAdditiveChainStatement
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genEigenMultiplicityQuotient_additive_chain : ∀ {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (P Q S : Submodule k U), S ≤ Q → Q ≤ P → (∀ x ∈ P, T x ∈ P) → (∀ x ∈ Q, T x ∈ Q) → (∀ x ∈ S, T x ∈ S) → FiniteDimensional k (↥P ⧸ S.submoduleOf P) → ∀ x : k, gmult T P S x = gmult T P Q x + gmult T Q S x := by
  first | exact @GlobalTheory.PhiGam.GmultAdd.main | exact GlobalTheory.PhiGam.GmultAdd.main | (intros; apply GlobalTheory.PhiGam.GmultAdd.main <;> assumption)
end

