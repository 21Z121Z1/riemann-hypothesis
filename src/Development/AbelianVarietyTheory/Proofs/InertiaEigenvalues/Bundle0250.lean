import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1BallCocycleLogCyclotomic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0237
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0238
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubMulSurjective
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.ArtinSchreierWitt

open Polynomial

theorem frob_sub_mul_surjective (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p]
    [PerfectRing k p] (h : ∀ c y : k, ∃ x : k, x ^ p - c * x = y) (c y : WittVector p k) :
    ∃ β : WittVector p k, WittVector.frobenius β - c * β = y := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) (WittVector p k) := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := WittVector p k), Ideal.map_span,
      Set.image_singleton, map_natCast]
    infer_instance
  let f : WittVector p k →ₗ[ℤ] WittVector p k :=
    (WittVector.frobenius (p := p) (R := k)).toAddMonoidHom.toIntLinearMap
      - (AddMonoidHom.mulLeft c).toIntLinearMap
  have hf : ∀ β, f β = WittVector.frobenius β - c * β := fun β => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    obtain ⟨x, hx⟩ := h (c.coeff 0) (g.coeff 0)
    refine ⟨WittVector.teichmuller p x, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have h0 : (WittVector.frobenius (WittVector.teichmuller p x)
        - c * WittVector.teichmuller p x - g) ∈ Ideal.span {(p : WittVector p k)} := by
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_sub, map_mul]
      simp only [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
        WittVector.teichmuller_coeff_zero]
      rw [hx, sub_self]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h0
    rw [hu]
    have : (p : WittVector p k) * u = (p : ℤ) • u := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨β, hβ⟩ := hs y
  exact ⟨β, (hf β).symm.trans hβ⟩

theorem monic_as (p : ℕ) [hp : Fact p.Prime] {k : Type} [CommRing k] [Nontrivial k] (c y : k) :
    (X ^ p - (C c * X + C y) : k[X]).Monic ∧ (X ^ p - (C c * X + C y) : k[X]).degree = p := by
  have h1 : (C c * X + C y : k[X]).degree < (p : WithBot ℕ) :=
    lt_of_le_of_lt degree_linear_le (by exact_mod_cast hp.out.one_lt)
  refine ⟨monic_X_pow_sub h1, ?_⟩
  rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]

theorem exists_root_field (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K]
    (c y : K) : ∃ x : K, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ p - (C c * X + C y) : K[X]) (by
    rw [(monic_as p c y).2]; exact_mod_cast hp.out.ne_zero)
  refine ⟨x, ?_⟩
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_add, eval_mul, eval_C] at hx
  linear_combination hx

theorem exists_root_ring (p : ℕ) [hp : Fact p.Prime] {O K : Type} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [IsAlgClosed K]
    (c y : O) : ∃ x : O, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := exists_root_field p (algebraMap O K c) (algebraMap O K y)
  have hi : IsIntegral O x := by
    refine ⟨X ^ p - (C c * X + C y), (monic_as p c y).1, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    linear_combination hx
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  refine ⟨z, IsFractionRing.injective O K ?_⟩
  rw [map_sub, map_pow, map_mul, hx]

theorem fixed_frob (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (b : WittVector p K)
    (hb : WittVector.map (frobenius K p) b = b) : ∃ z : ℤ_[p], b = zlW p K z := by
  have h : ∀ n, ∃ a : ZMod p, ZMod.castHom (dvd_refl p) K a = b.coeff n := by
    intro n
    have h1 : (b.coeff n) ^ p = b.coeff n := by
      have := congrArg (fun w => WittVector.coeff w n) hb
      simpa [WittVector.map_coeff, frobenius_def] using this
    have h2 := (Subfield.mem_bot_iff_pow_eq_self K p).2 h1
    have h3 : (⊥ : Subfield K) ≤ (ZMod.castHom (dvd_refl p) K).fieldRange := bot_le
    exact h3 h2
  choose a ha using h
  refine ⟨WittVector.equiv p (WittVector.mk p a), ?_⟩
  ext n
  simp [zlW, WittVector.map_coeff, ← ha]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∀ y : WCb l, ∃ b, frobW l b - b = y) ∧ (∀ b : WCb l, frobW l b = b → ∃ z : ℤ_[l], b = algebraMap ℤ_[l] (WCb l) z) ∧ ∀ (c p : Ainf l), ∃ β : Ainf l, WittVector.frobenius β - c * β = p := by
  intro l _
  obtain ⟨hK, hV⟩ := GlobalTheory.T.isAlgClosed_tiltField_and_valuationRing l
  refine ⟨fun y => ?_, fun b hb => fixed_frob l (Cb l) b hb, fun c p => ?_⟩
  · obtain ⟨β, hβ⟩ := frob_sub_mul_surjective l (Cb l) (exists_root_field l) 1 y
    refine ⟨β, ?_⟩
    rw [one_mul, WittVector.frobenius_eq_map_frobenius] at hβ
    exact hβ
  · exact frob_sub_mul_surjective l (OCb l) (exists_root_ring l (K := Cb l)) c p

end GlobalTheory.ArtinSchreierWitt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityTensorAinfCoefficients
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FrobIntegralCoeff

section Generic

variable {R O : Type} [CommRing R] [CommRing O] [Algebra R O] {I : Type} [Fintype I] [DecidableEq I]
  (b : Module.Basis I R O)

def regRep (W : Type) [CommRing W] [Algebra R W] : O ⊗[R] W →ₐ[R] Matrix I I W :=
  Algebra.TensorProduct.lift
    ((AlgHom.mapMatrix (Algebra.ofId R W)).comp (Algebra.leftMulMatrix b))
    (IsScalarTower.toAlgHom R W (Matrix I I W))
    (fun _ w => (Algebra.commutes w _).symm)

variable {W W' : Type} [CommRing W] [Algebra R W] [CommRing W'] [Algebra R W']

theorem regRep_tmul (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = Algebra.leftMulMatrix b o i j • w := by
  erw [Algebra.TensorProduct.lift_tmul]
  simp [Algebra.smul_def, Matrix.algebraMap_eq_diagonal, Matrix.mul_diagonal, mul_comm]

theorem regRep_map (f : W →ₐ[R] W') (z : O ⊗[R] W) (i j : I) :
    regRep b W' (Algebra.TensorProduct.map (AlgHom.id O O) f z) i j = f (regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, regRep_tmul, regRep_tmul, map_smul]
  | add x y hx hy => simp [map_add, Matrix.add_apply, hx, hy]

private theorem regRep_tmul' (o : O) (w : W) (i j : I) :
    regRep b W (o ⊗ₜ w) i j = b.repr (o * b j) i • w := by
  rw [regRep_tmul, Algebra.leftMulMatrix_eq_repr_mul]

theorem eq_sum_regRep (z : O ⊗[R] W) :
    z = ∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] regRep b W z i j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [regRep_tmul', ← TensorProduct.smul_tmul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, ← TensorProduct.sum_tmul, b.sum_repr, TensorProduct.smul_tmul',
      ← TensorProduct.sum_tmul]
    congr 1
    simp_rw [← mul_smul_comm, ← Finset.mul_sum, b.sum_repr, mul_one]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp [map_add, Matrix.add_apply, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib]

theorem mem_range_of_regRep (f : W →ₐ[R] W') (z : O ⊗[R] W')
    (h : ∀ i j, regRep b W' z i j ∈ Set.range f) :
    z ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  choose g hg using h
  refine ⟨∑ i, ∑ j, b.repr 1 j • (b i ⊗ₜ[R] g i j), ?_⟩
  conv_rhs => rw [eq_sum_regRep b z]
  simp_rw [TensorProduct.smul_tmul', map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hg]

def blow {p q : Type} (Z : Matrix p q (O ⊗[R] W)) : Matrix (p × I) (q × I) W :=
  Matrix.of fun x y => regRep b W (Z x.1 y.1) x.2 y.2

theorem blow_map {p q : Type} (f : W →ₐ[R] W') (Z : Matrix p q (O ⊗[R] W)) :
    blow b (Z.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) = (blow b Z).map f := by
  ext x y
  simp [blow, regRep_map]

theorem blow_add {p q : Type} (Z Z' : Matrix p q (O ⊗[R] W)) :
    blow b (Z + Z') = blow b Z + blow b Z' := by
  ext x y
  simp [blow, map_add]

theorem blow_mul {p q r : Type} [Fintype q] (Z : Matrix p q (O ⊗[R] W))
    (Z' : Matrix q r (O ⊗[R] W)) : blow b (Z * Z') = blow b Z * blow b Z' := by
  ext x y
  simp [blow, Matrix.mul_apply, map_sum, Matrix.sum_apply, Fintype.sum_prod_type]

omit b [Fintype I] [DecidableEq I] in

theorem integrality_baseChange [Module.Free R O] [Module.Finite R O] (f : W →ₐ[R] W')
    (φ : W' →ₐ[R] W')
    (H : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q W') (S : Matrix p p W)
      (S' : Matrix q q W) (Y : Matrix p q W),
      Z.map φ = S.map f * Z * S'.map f + Y.map f → ∀ a b, Z a b ∈ Set.range f)
    (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (O ⊗[R] W')) (S : Matrix p p (O ⊗[R] W))
    (S' : Matrix q q (O ⊗[R] W)) (Y : Matrix p q (O ⊗[R] W))
    (h : Z.map (Algebra.TensorProduct.map (AlgHom.id O O) φ) =
      S.map (Algebra.TensorProduct.map (AlgHom.id O O) f) * Z *
        S'.map (Algebra.TensorProduct.map (AlgHom.id O O) f) +
      Y.map (Algebra.TensorProduct.map (AlgHom.id O O) f)) (x : p) (y : q) :
    Z x y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id O O) f) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R (O ⊗[R] W')
    exact ⟨0, Subsingleton.elim _ _⟩
  classical
  let c := Module.Free.chooseBasis R O
  have key := congrArg (blow c) h
  rw [blow_map, blow_add, blow_mul, blow_mul, blow_map, blow_map, blow_map] at key
  apply mem_range_of_regRep c f (Z x y)
  intro i j
  exact H _ _ (blow c Z) (blow c S) (blow c S') (blow c Y) key (x, i) (y, j)

private theorem module_free_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Free ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  have : Module.IsTorsionFree ℤ_[l] K := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  exact IsIntegralClosure.module_free ℤ_[l] ℚ_[l] K _

private theorem module_finite_zpadic_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    Module.Finite ℤ_[l] ↥(OL LL) := by
  obtain ⟨K, hK⟩ := LL
  delta OL
  exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] K _

end Generic

theorem frobenius_integrality_coeff : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q (RW LL)) (S : Matrix p p (RA LL)) (S' : Matrix q q (RA LL)) (Y : Matrix p q (RA LL)), Z.map (φRW LL) = S.map (inclR LL) * Z * S'.map (inclR LL) + Y.map (inclR LL) → ∀ a b, Z a b ∈ Set.range (inclR LL) := by
  intro l _ LL p q _ _ Z S S' Y h a b
  unfold RW RA inclR φRW at *
  have := module_free_zpadic_OL l LL
  have := module_finite_zpadic_OL l LL
  exact integrality_baseChange (R := ℤ_[l]) (O := OL LL) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.T.frobeniusIntegrality_wittTilt_ainf l p q Z S S' Y h) p q Z S S' Y h a b

end GlobalTheory.FrobIntegralCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.LAdic

def Good (p : ℕ) (R : Type) [CommRing R] : Prop :=
  (∀ x : R, (p : R) * x = 0 → x = 0) ∧ (∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → R, ∃ s, ∀ k : ℕ, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r

theorem good_of_complete (p : ℕ) (R : Type) [CommRing R] (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    [hc : IsAdicComplete (Ideal.span {(p : R)}) R] : Good p R := by
  have mem : ∀ (k : ℕ) (x : R), x ∈ (Ideal.span {(p : R)} ^ k • ⊤ : Submodule R R) ↔
      ∃ r, x = (p : R) ^ k * r := by
    intro k x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rfl
  refine ⟨h, fun x hx => ?_, fun x => ?_⟩
  · refine IsHausdorff.haus (I := Ideal.span {(p : R)}) hc.toIsHausdorff x fun k => ?_
    rw [SModEq.zero, mem]
    exact hx k
  · obtain ⟨s, hs⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R)}) hc.toIsPrecomplete
      (f := fun k => ∑ i ∈ Finset.range k, (p : R) ^ i * x i) (by
        intro m n hmn
        rw [SModEq.sub_mem, mem]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        refine ⟨-∑ i ∈ Finset.range k, (p : R) ^ i * x (m + i), ?_⟩
        rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
        simp only [pow_add, mul_assoc]
        ring)
    refine ⟨s, fun k => ?_⟩
    have := (hs k).symm
    rwa [SModEq.sub_mem, mem] at this

theorem good_tensor {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
    (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W] (p : ℕ) (h : Good p W) :
    Good p (O ⊗[Z] W) := by
  have hp : ∀ (k : ℕ) (i : I) (x : O ⊗[Z] W),
      crd b i ((p : O ⊗[Z] W) ^ k * x) = (p : W) ^ k * crd b i x := by
    intro k i x
    rw [← Nat.cast_pow, crd_natCast_mul, Nat.cast_pow]
  refine ⟨fun x hx => ext_crd b fun i => ?_, fun x hx => ext_crd b fun i => ?_, fun x => ?_⟩
  · rw [map_zero]
    apply h.1
    rw [← crd_natCast_mul, hx, map_zero]
  · rw [map_zero]
    refine h.2.1 _ fun k => ?_
    obtain ⟨r, hr⟩ := hx k
    exact ⟨crd b i r, by rw [← hp, ← hr]⟩
  · choose s r hs using fun i => h.2.2 fun k => crd b i (x k)
    refine ⟨∑ j, b j ⊗ₜ[Z] s j, fun k => ⟨∑ j, b j ⊗ₜ[Z] r j k, ext_crd b fun i => ?_⟩⟩
    rw [map_sub, hp, crd_sum, crd_sum b (fun j => r j k), map_sum, ← hs]
    simp only [hp]

theorem good_witt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Good p (WittVector p k) :=
  good_of_complete p _ fun x hx => WittVector.eq_zero_of_p_mul_eq_zero x (by rw [mul_comm]; exact hx)

theorem ladic_RW (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ x : RW LL, (l : RW LL) * x = 0 → x = 0) ∧
    (∀ x : RW LL, (∀ k : ℕ, ∃ r, x = (l : RW LL) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → RW LL, ∃ s, ∀ k : ℕ, ∃ r,
      s - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r :=
  good_tensor (W := WCb l) (basisO LL) l (good_witt l (Cb l))

end GlobalTheory.Decompl.LAdic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1BallCocycleLogCyclotomicStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_eq_log_cyclotomic_smul_add_coboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ s : ℕ, Lev l s → (∀ c : GQ l → PadicComplex l, CocOn (Gj K s) (fun g y => act g y) {y | ‖y‖ ≤ 1} c → ∃ α ∈ inC (Ks K s), ‖α‖ ≤ (l : ℝ) ^ (1 + s) ∧ ∃ b : PadicComplex l, ∀ σ ∈ Gj K s, c σ = algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * α + (act σ b - b)) ∧ ∀ α ∈ inC (Ks K s), ∀ b : PadicComplex l, (∀ σ ∈ Gj K s, algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * α = act σ b - b) → α = 0 := by
  first | exact @GlobalTheory.Cyc.LogClass.image_H1_logChi | exact GlobalTheory.Cyc.LogClass.image_H1_logChi | (intros; apply GlobalTheory.Cyc.LogClass.image_H1_logChi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightNonnegOfIdempotentGlnPrStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (n : ℕ) (a : MonoidAlgebra ℂ (Gn g n)), a * a = a → 0 ≤ (a.coeff 1).re → ∀ f, 0 ≤ wtC L a f := by
  first | exact @GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime | exact GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime | (intros; apply GlobalTheory.Adopt.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateBasisOfIsDecompletionAtLevelStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  first | exact @GlobalTheory.Cyc.htBasis_of_isDec | exact GlobalTheory.Cyc.htBasis_of_isDec | (intros; apply GlobalTheory.Cyc.htBasis_of_isDec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZeroStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_to_characterLine_eq_zero : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), -1 ≤ e → e < Dt.t → ∀ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ (chr (M.ω ^ (-e))) p → p = 0 := by
  first | exact @GlobalTheory.Models.ModTh.hom_chr_eq_zero | exact GlobalTheory.Models.ModTh.hom_chr_eq_zero | (intros; apply GlobalTheory.Models.ModTh.hom_chr_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem tmul_gen_cancel (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    (e : T.V) (he : e ≠ 0) (heT : e ∈ T.L.T) (e₀ : ↥T.L.T) (h₀ : Submodule.span O {e₀} = ⊤)
    {R : Type} [CommRing R] [Algebra O R] (r r' : R)
    (h : (r ⊗ₜ[O] e₀ : TW R T) = r' ⊗ₜ[O] e₀) : r = r' := by
  have hne : (e₀ : T.V) ≠ 0 := by
    intro h0
    have hm : (⟨e, heT⟩ : ↥T.L.T) ∈ Submodule.span O {e₀} := by rw [h₀]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    apply he
    have := congrArg Subtype.val hc
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro c hc
      have h1 : c • (e₀ : T.V) = 0 := congrArg Subtype.val hc
      rw [← algebraMap_smul LL c, smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact hO (by rw [h1, map_zero])
      · exact absurd h1 hne
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h₀]
  let φ := LinearEquiv.ofBijective _ hb
  have hφ : φ.symm e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [φ]
  have := congrArg (fun z => TensorProduct.rid O R (LinearMap.lTensor R φ.symm.toLinearMap z)) h
  simpa [hφ] using this

theorem etTie_io_act (hO : Function.Injective (algebraMap O LL)) {W : LocWach PD LL O v n}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {incl : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW incl φR gR πA) (g : G) (a : LetA O n) :
    incl (E.io (W.γA (W.resΓ g) a)) = gR g (incl (E.io a)) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
  have h1 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by
    simp [TWact, hact]
  have h2 := E.jD_act W.one g (algebraMap (LetA O n) W.EE a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, hj, TWact_smul, h1, W.γE_ext, E.ioE_ext,
    E.ioE_ext, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h2
  exact tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

end Generic

set_option synthInstance.maxHeartbeats 400000 in

theorem io_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  intro l _ P AI K s LL h W E g a
  exact etTie_io_act Subtype.val_injective E.tie g a

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescentStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_restrict_galois_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.DeRhamDescent.isDR_of_restrict | exact GlobalTheory.DeRhamDescent.isDR_of_restrict | (intros; apply GlobalTheory.DeRhamDescent.isDR_of_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial NumberField
open scoped Classical

namespace GlobalTheory.FixedPlaceSplit

theorem host_conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply]
  simp

theorem isSplitPl_of_not_isConjPl (D : Formalism.BasicNotions.D7) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))
    (h : ¬ Formalism.BasicNotions.IsConjPl D.host w w) : Formalism.BasicNotions.IsSplitPl D.host w := by
  by_contra hs
  apply h
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      x ∈ w.asIdeal → y ∈ w.asIdeal := by
    intro x y hxy hx
    by_contra hy
    apply hs
    refine ⟨x, hx, fun y' hy' => ?_⟩
    have : y' = y := by
      apply RingOfIntegers.ext
      exact hy'.trans hxy.symm
    rwa [this]
  intro x y hxy
  refine ⟨key x y hxy, key y x ?_⟩
  rw [hxy, host_conj_conj]

theorem isSplitPl_plGw : ∀ (D : Formalism.BasicNotions.D7) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.BasicNotions.IsSplitPl D.host (D.naut.plGw k v) :=
  fun D k v => isSplitPl_of_not_isConjPl D _ (D.naut.plGw_nconj k v v)

end GlobalTheory.FixedPlaceSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalSelmer
section
namespace GlobalTheory.Proof.LocalGlobalSelmer

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i) (k : ℕ) (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)), InR' D.nd r S 1 → UnrOut i r Xs → ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → v ∉ D.nd.S i → v ∉ D.nd.Q i → resIne i (cocW i r S Xs ψ) v = ⊥ := by
  intro D i r Xs S k ψ hone hU v h1 h2 h3
  have hY : ∀ γ, InY D.nd r S (yg D.nd r S γ) := fun γ =>
    ⟨1, fun _ => 1, fun _ => γ, fun _ => hone, by simp⟩
  have hy : ∀ γ x', yg D.nd r S γ x' = (rTwO D.nd i r (S.p x') γ - 1) * Eel D.nd S x' := by
    intro γ x'
    simp [yg, rTwO, twistM, sub_mul]
  rw [resIne, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, -, h0, rfl⟩, rfl⟩
  funext γ
  exact h0 _ (hY γ.1) fun x' hx => by rw [hy, hU v h1 h2 h3 _ hx γ.1 γ.2]; simp

end GlobalTheory.Proof.LocalGlobalSelmer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationAlgebraMapEqStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedValuation_algebraMap_eq : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (l : ℕ) (x : O), Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (algebraMap O O' x) = Formalism.MainNotions.BlochKatoReduction.Gen.nval O l x := by
  first | exact @GlobalTheory.nval_algebraMap_eq | exact GlobalTheory.nval_algebraMap_eq | (intros; apply GlobalTheory.nval_algebraMap_eq <;> assumption)
end

