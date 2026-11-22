import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0519
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import GroundTheory.AutomorphicForms.Reduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitRepresentativesSplitPrimeStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unit_representatives_split_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Splits q → Over P q → ∃ R : Finset (P.adicCompletion E)ˣ, R.card + 1 = Ideal.absNorm q.asIdeal ∧ (∀ r ∈ R, Valued.v (r : P.adicCompletion E) = 1) ∧ ∀ y : (Af E)ˣ, (∀ P', Over P' q → Valued.v ((y : Af E) P') = 1) → ∃! r, r ∈ R ∧ LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) := by
  first | exact @GlobalTheory.CMVal.Euler.Resid.exists_representatives | exact GlobalTheory.CMVal.Euler.Resid.exists_representatives | (intros; apply GlobalTheory.CMVal.Euler.Resid.exists_representatives <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMeasurablePartitionOfUnityUnitLogTranslateStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∃ p : (I → ℝ) → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧ (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) ∧ ∃ R : ℝ, ∀ y, p y ≠ 0 → ∀ i j, y i - y j ≤ R := by
  first | exact @GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | exact GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates | (intros; apply GlobalTheory.exists_measurable_nonneg_hasSum_ulog_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermTransportModularFamiliesValuesStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_transport_modular_families_values : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N : ℕ) (m : S → ℕ) (f f' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → (∀ s, IsFam act (m s) (f s)) → (∀ s i, QConj g N (f s i) (f' s i)) → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∃ ρ : Equiv.Perm ι, ∀ s i, g (f s i τ₀ / ω₀ ^ m s) = f' s (ρ i) τ₁ / ω₁ ^ m s := by
  first | exact @GlobalTheory.QFam.exists_perm_transport_families | exact GlobalTheory.QFam.exists_perm_transport_families | (intros; apply GlobalTheory.QFam.exists_perm_transport_families <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfLargeAdelicDegreeStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_large_adelic_degree : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∃ γ : ℕ, ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → (n : ℤ) * γ < deg g → ∃ p : Fin n → F, p ≠ 0 ∧ ∀ (v : Place k F) (i : Fin n), v.1 ((g v).mulVec p i) ≤ 1 := by
  first | exact @GlobalTheory.Nef.exists_section_of_large_deg | exact GlobalTheory.Nef.exists_section_of_large_deg | (intros; apply GlobalTheory.Nef.exists_section_of_large_deg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetDiagNormOne
section
open NumberField MeasureTheory Matrix
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section

namespace GlobalTheory.SiegelDiagNormOne

theorem exists_siegelSet_diag_normOne : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ ω : Set (AdelicGLn.AdelicGL K n),
    IsCompact ω ∧ ω ⊆ ((adelicBorel (K := K) (n := n) : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)) ∧
    (∀ b ∈ ω, ∀ i, ∃ u : IdeleGroup K, (b : Matrix (Fin n) (Fin n) 𝔸[K]) i i = u ∧ (ideleModule K u : ℝ) = 1) ∧
    ∃ t : ℝ, 0 < t ∧ ∀ g : AdelicGLn.AdelicGL K n, ∃ γ : GL (Fin n) K,
      AdelicGLn.diagonal K n γ * g ∈ Reduction.siegelSet n ω t := by
  intro K _ _ n
  classical
  obtain ⟨t₀, ht₀, hred⟩ := exists_reduced (K := K)
  obtain ⟨D, hD, hDmem⟩ := exists_isCompact_add_mem (K := K)
  obtain ⟨S, hS, hS1, hSmem⟩ := exists_isCompact_normOneSubgroup K
  set d : ℕ := Module.finrank ℚ K with hd
  have hd0 : 0 < d := Module.finrank_pos
  set FN : Set (AdelicGLn.AdelicGL K n) :=
    unitriangularGL n '' (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D) with hFN
  set FT : Set (AdelicGLn.AdelicGL K n) := diagUnits n '' (Set.pi Set.univ fun _ => S) with hFT
  have hFNc : IsCompact FN := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hD).image
    (continuous_unitriangularGL n)
  have hFTc : IsCompact FT := (isCompact_univ_pi fun _ => hS).image (continuous_diagUnits n)
  refine ⟨FN * FT, hFNc.mul hFTc, ?_, ?_, t₀ ^ ((d : ℝ)⁻¹), Real.rpow_pos_of_pos ht₀ _, fun g => ?_⟩
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, -, rfl⟩, rfl⟩
    exact mul_mem (unitriangularGL_mem_adelicBorel n p) (diagUnits_mem_adelicBorel n e)
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, he, rfl⟩, rfl⟩ i
    refine ⟨e i, ?_, ?_⟩
    · rw [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal]
      change unitriangular p i i * _ = _
      simp [unitriangular]
    · have h1 := hS1 (he i (Set.mem_univ _))
      rw [normOneSubgroup, SetLike.mem_coe, MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  obtain ⟨γ, b, hb, k, hk, hγ, hratio⟩ := hred n g
  set B : Matrix (Fin n) (Fin n) 𝔸[K] := (b : Matrix (Fin n) (Fin n) 𝔸[K]) with hB
  set dU : Fin n → IdeleGroup K := fun i => (isUnit_apply_self_of_mem_adelicBorel hb i).unit
    with hdU
  have hdUv : ∀ i, ((dU i : IdeleGroup K) : 𝔸[K]) = B i i := fun i => IsUnit.unit_spec _
  set r : Fin n → ℝ := fun i => (ideleModule K (dU i) : ℝ) ^ ((d : ℝ)⁻¹) with hr
  have hrpos : ∀ i, 0 < r i := fun i => Real.rpow_pos_of_pos (ideleModule K (dU i)).2 _
  have hrd : ∀ i, r i ^ d = ideleModule K (dU i) := fun i =>
    Real.rpow_inv_natCast_pow (ideleModule K (dU i)).2.le hd0.ne'
  have heqmod : ∀ i, ideleModule K (dU i) = ideleModule K (posIdele (r i) (hrpos i)) := fun i =>
    Subtype.ext (by rw [ideleModule_posIdele, ← hd, hrd i])
  have hnorm : ∀ i, dU i * (posIdele (r i) (hrpos i))⁻¹ ∈ normOneSubgroup K := fun i => by
    rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, heqmod i, mul_inv_cancel]
  choose c hc using fun i => hSmem _ (hnorm i)
  set σ : Fin n → IdeleGroup K :=
    fun i => IdeleGroup.diagonal K (c i) * (dU i * (posIdele (r i) (hrpos i))⁻¹) with hσ
  set e : Fin n → IdeleGroup K := fun i => IdeleGroup.diagonal K (c i) with he
  set δA : AdelicGLn.AdelicGL K n := diagUnits n e with hδA
  have hδ : AdelicGLn.diagonal K n (diagUnits n c) = δA := diagonal_diagUnits n c
  set u : AdelicGLn.AdelicGL K n := δA * b * (diagUnits n dU)⁻¹ * δA⁻¹ with hu
  have hu_apply : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝔸[K]) i j =
      (e i : 𝔸[K]) * B i j * (((dU j)⁻¹ : IdeleGroup K) : 𝔸[K]) * (((e j)⁻¹ : IdeleGroup K) : 𝔸[K]) := by
    intro i j
    rw [hu, ← map_inv, ← map_inv]
    simp only [Units.val_mul, hδA, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.inv_apply]
    rfl
  have huu : IsUnitriangular (u : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hu_apply, show B i j = 0 from hb hij]
      simp
    · rw [hu_apply, ← hdUv i]
      calc (e i : 𝔸[K]) * (dU i : 𝔸[K]) * (((dU i)⁻¹ : IdeleGroup K) : 𝔸[K]) *
            (((e i)⁻¹ : IdeleGroup K) : 𝔸[K])
          = ((e i * dU i * (dU i)⁻¹ * (e i)⁻¹ : IdeleGroup K) : 𝔸[K]) := by simp [Units.val_mul]
        _ = 1 := by rw [mul_inv_cancel_right, mul_inv_cancel, Units.val_one]
  obtain ⟨ν, hν, hνD⟩ := exists_unitriangular_mul_mem hDmem n _ huu
  set νGL : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero ν
    (by rw [hν.det_eq_one]; exact one_ne_zero) with hνGL
  set νA : AdelicGLn.AdelicGL K n := AdelicGLn.diagonal K n νGL with hνA
  have hνAmat : (νA : Matrix (Fin n) (Fin n) 𝔸[K]) = ν.map (algebraMap K 𝔸[K]) := rfl
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := let ⟨k₀, hk₀⟩ := hDmem 0; ⟨_, hk₀⟩
  set p : Fin n → Fin n → 𝔸[K] := fun i j =>
    if i < j then ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j else d₀
    with hp
  have hpD : p ∈ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D := by
    intro i _ j _
    simp only [hp]
    split_ifs with hij
    · rw [Units.val_mul, hνAmat]
      exact hνD i j hij
    · exact hd₀
  have hνu : νA * u = unitriangularGL n p := by
    refine Units.ext ?_
    have h1 : IsUnitriangular ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
      rw [Units.val_mul, hνAmat]
      exact IsUnitriangular.mul ⟨fun i j hij => by simp [hν.1 hij],
        fun i => by simp [hν.2 i]⟩ huu
    rw [h1.eq_unitriangular]
    change unitriangular _ = unitriangular p
    ext i j
    simp only [unitriangular, of_apply, hp]
    split_ifs <;> rfl
  have hdiag : δA * diagUnits n dU = diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) := by
    rw [hδA, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, hσ, he]
    group
  refine ⟨νGL * diagUnits n c * γ, unitriangularGL n p * diagUnits n σ,
    ⟨_, ⟨p, hpD, rfl⟩, _, ⟨σ, fun i _ => hc i, rfl⟩, rfl⟩,
    diagUnits n (fun i => posIdele (r i) (hrpos i)), ⟨r, hrpos, fun i j hij => ?_, rfl⟩, k, hk, ?_⟩
  · have h := hratio i j hij
    rw [← hdUv j, ← hdUv i, adeleAbs_units, adeleAbs_units, ← hrd i, ← hrd j] at h
    have hrj := (hrpos j).le
    have hri := (hrpos i).le
    have ht : (t₀ ^ ((d : ℝ)⁻¹)) ^ d = t₀ := Real.rpow_inv_natCast_pow ht₀.le hd0.ne'
    have htn : 0 ≤ t₀ ^ ((d : ℝ)⁻¹) := (Real.rpow_pos_of_pos ht₀ _).le
    rw [← pow_le_pow_iff_left₀ (mul_nonneg htn hrj) hri hd0.ne', mul_pow, ht]
    exact h
  · have h1 : δA * b = u * (δA * diagUnits n dU) := by
      rw [hu]; group
    calc AdelicGLn.diagonal K n (νGL * diagUnits n c * γ) * g
        = νA * δA * (AdelicGLn.diagonal K n γ * g) := by
          rw [map_mul, map_mul, hδ, ← hνA]; simp only [mul_assoc]
      _ = νA * (δA * b) * k := by rw [hγ]; simp only [mul_assoc]
      _ = νA * u * (δA * diagUnits n dU) * k := by rw [h1]; simp only [mul_assoc]
      _ = (νA * u) * diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) * k := by
          rw [hdiag]; simp only [mul_assoc]
      _ = _ := by rw [hνu]

end GlobalTheory.SiegelDiagNormOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallerUnitaryGroupEmbeddingStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smaller_unitary_group_embedding : GlobalTheory.SatakeWeyl.EmbExists := by
  first | exact @GlobalTheory.SatakeWeyl.embExists | exact GlobalTheory.SatakeWeyl.embExists | (intros; apply GlobalTheory.SatakeWeyl.embExists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSubalgebraContainingFinsetCharZero
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_smooth_subalgebra_of_finset : ∀ (F K : Type) [Field F] [CharZero F] [Field K]
    [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧
      Algebra.Smooth F R := by
  intro F K _ _ _ _ s
  haveI : PerfectField F := PerfectField.ofCharZero
  let C : Subalgebra F K := Algebra.adjoin F (↑s : Set K)
  haveI : Algebra.FiniteType F C :=
    ⟨(Subalgebra.fg_top C).mpr (Subalgebra.fg_adjoin_finset s)⟩
  obtain ⟨f, hf0, hsm, -⟩ := GlobalTheory.SS.exists_smooth_free_away F C C
  have hinjC : Function.Injective (algebraMap C K) := Subtype.val_injective
  have hfK : IsUnit (algebraMap C K f) := by
    refine isUnit_iff_ne_zero.mpr ?_
    intro h
    exact hf0 (hinjC (by simpa using h))
  let g : Localization.Away f →ₐ[F] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => by
        show IsLocalization.Away.lift f hfK (algebraMap F (Localization.Away f) r) = algebraMap F K r
        rw [IsScalarTower.algebraMap_apply F C (Localization.Away f),
          IsLocalization.Away.lift_eq]
        rfl }
  have hginj : Function.Injective g := by
    show Function.Injective (IsLocalization.Away.lift f hfK)
    rw [IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      rw [IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0) h]
    · intro h
      have : x = y := hinjC h
      rw [this]
  refine ⟨g.range, ?_, ?_⟩
  · intro x hx
    refine ⟨algebraMap C (Localization.Away f) ⟨x, Algebra.subset_adjoin hx⟩, ?_⟩
    show IsLocalization.Away.lift f hfK _ = x
    rw [IsLocalization.Away.lift_eq]
    rfl
  · exact Algebra.Smooth.of_equiv (AlgEquiv.ofInjective g hginj)
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceUniformiserIdele
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem exists_split_unif_idele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)) (x : OF E),
    Splits v → (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) →
    ∃ π : (Af E)ˣ, (∀ P, Over P v → (π : Af E) P = iota x P) ∧ (∀ P, ¬ Over P v → (π : Af E) P = 1) ∧
      modF π = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ ^ 2 ∧ ∀ χ : HChar E, TrivOnF χ → finPart χ π = 1 := by
  classical
  intro E _ _ _ v x hv hx
  obtain ⟨h2, hN⟩ := GlobalTheory.T.splitsInCMField_two_primes_degree_one E v hv
  obtain ⟨P₁, P₂, hne, hP₁, hP₂⟩ := hv
  have hx0 : (x : maximalRealSubfield E) ≠ 0 := fun h => by
    have h0 : x = 0 := Subtype.ext h
    have h1 := hx P₁ hP₁
    rw [h0, iota_zero, zero_coord, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  let k : (maximalRealSubfield E)ˣ := Units.mk0 (x : maximalRealSubfield E) hx0
  let y : (Af E)ˣ := Units.map (algebraMap E (Af E)).toMonoidHom (Formalism.L2.Host.upF (maximalRealSubfield E) k)
  have hy : (y : Af E) = iota x := rfl
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hmem : ∀ P, P ∈ S ↔ Over P v := fun P => mem_aboveF P v
  have hin : ∀ P, Over P v → ((∏ P ∈ S, single P (coord P y) : (Af E)ˣ) : Af E) P = iota x P := fun P hP => by
    rw [Fibre.prod_single_apply, if_pos ((hmem P).2 hP), hy]
  have hout : ∀ P, ¬ Over P v → ((∏ P ∈ S, single P (coord P y) : (Af E)ˣ) : Af E) P = 1 := fun P hP => by
    rw [Fibre.prod_single_apply, if_neg (fun h => hP ((hmem P).1 h))]
  refine ⟨∏ P ∈ S, single P (coord P y), hin, hout, ?_, fun χ hχ => ?_⟩
  · have hS2 : S = {P₁, P₂} := by
      ext R
      rw [hmem, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨h2 P₁ P₂ hP₁ hP₂ hne R, fun h => by rcases h with rfl | rfl <;> assumption⟩
    unfold modF
    rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ (fun P hP => by
      by_contra h
      refine hP ?_
      beta_reduce
      rw [hout P (fun h' => h ((hmem P).2 h'))]
      simp)]
    rw [Finset.prod_congr rfl (g := fun _ => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) (fun P hP => by
      rw [hin P ((hmem P).1 hP), hx P ((hmem P).1 hP), WithZero.log_exp, (hN P ((hmem P).1 hP)).1, zpow_neg_one])]
    rw [Finset.prod_const, hS2, Finset.card_pair hne]
  · have h1 := hχ.1 v k
    unfold Formalism.L2.Host.HChar.resFin at h1
    rw [MonoidHom.finsetProd_apply] at h1
    rw [map_prod, ← h1]
    exact Finset.prod_congr rfl fun P _ => rfl

end GlobalTheory.CMVal.Euler
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableBoundHilbertEisensteinTermsStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summable_bound_hilbert_eisenstein_terms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ), IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → ∃ M : F → ℝ, Summable M ∧ ∀ (ξ : F) (z : Emb F → ℂ), (∀ i, 1 / 2 ≤ ‖1 + z i * c‖ ∧ τ.im / 2 ≤ (τ + t * z i / (1 + z i * c)).im) → ‖a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))‖ ≤ M ξ := by
  first | exact @GlobalTheory.HilbFam.exists_summable_bound_terms | exact GlobalTheory.HilbFam.exists_summable_bound_terms | (intros; apply GlobalTheory.HilbFam.exists_summable_bound_terms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsorModelFilteredColimitStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsor_model_filtered_colimit : ∀ (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Type) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j),
    (∀ i (h : i ≤ i), f i i h = RingHom.id (R i)) →
    (∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk)) →
    ∀ (B : Type) [CommRing B] (g : ∀ i, R i →+* B),
    (∀ i j (h : i ≤ j), (g j).comp (f i j h) = g i) →
    (∀ b : B, ∃ i x, g i x = b) →
    (∀ i x, g i x = 0 → ∃ j, ∃ h : i ≤ j, f i j h x = 0) →
    ∀ (q : ℕ), 0 < q →
    ∀ (D : Type) [CommRing D] [Algebra B D] (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ i, letI : Algebra (R i) B := (g i).toAlgebra
      ∃ (Di : Type) (_ : CommRing Di) (_ : Algebra (R i) Di)
        (acti : Multiplicative (ZMod q) →* (Di ≃ₐ[R i] Di)),
        GlobalTheory.KeyOriginCut.IsZTorsor (R i) Di q acti ∧ Nonempty (TensorProduct (R i) B Di ≃ₐ[B] D) := by
  first | (exact @GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements) | (exact GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements) | (intros; apply GlobalTheory.TorsorColimElem.exists_torsor_model_of_elements  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformiserSplitPlaceCmOrderNonunit
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler

theorem span_sup_pow_eq_of_notMem_sq {R : Type} [CommRing R] [IsDedekindDomain R] (v : HeightOneSpectrum R) {x : R}
    (hx : x ∈ v.asIdeal) (hx2 : x ∉ v.asIdeal ^ 2) (n : ℕ) : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) = v.asIdeal := by
  have hd : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) ∣ v.asIdeal ^ (n + 1) := Ideal.dvd_iff_le.2 le_sup_right
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow v.prime _).1 hd
  rw [associated_iff_eq] at hi
  have hle : Ideal.span {x} ⊔ v.asIdeal ^ (n + 1) ≤ v.asIdeal :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hx) (Ideal.pow_le_self (by omega))
  have hxi : x ∈ v.asIdeal ^ i := hi ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)
  rw [hi] at hle ⊢
  match i, hle, hxi with
  | 0, hle, _ => exact absurd (top_le_iff.1 (by simpa using hle)) v.isPrime.ne_top
  | 1, _, _ => exact pow_one _
  | i + 2, _, hxi => exact absurd (Ideal.pow_le_pow_right (by omega) hxi) hx2

theorem eq_exp_neg_one_of_le_of_not_le {g : WithZero (Multiplicative ℤ)} (h1 : g ≤ WithZero.exp (-1 : ℤ))
    (h2 : ¬ g ≤ WithZero.exp (-2 : ℤ)) : g = WithZero.exp (-1 : ℤ) := by
  have h0 : g ≠ 0 := fun h => h2 (h ▸ zero_le')
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  omega

theorem locIn_succ_nonunit_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (OF E)), Splits v → ∃ x : OF E, (∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ)) ∧ ∀ (n : ℕ) (π y : (Af E)ˣ), (∀ P, Over P v → (π : Af E) P = iota x P) → (LocIn n v ((π⁻¹ * y : (Af E)ˣ) : Af E) ↔ LocIn (n + 1) v (y : Af E) ∧ ¬ ∀ P, Over P v → Valued.v ((y : Af E) P) = 1) := by
  intro E _ _ _ v hv
  have he := fun P hP => ((GlobalTheory.T.splitsInCMField_two_primes_degree_one E v hv).2 P hP).2.1
  obtain ⟨x, hx1, hx2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  have hval : ∀ P, Over P v → Valued.v (iota x P) = WithZero.exp (-1 : ℤ) := fun P hP =>
    eq_exp_neg_one_of_le_of_not_le (by simpa using val_iota_le_of_mem hP 1 hx1)
      (fun h => hx2 ((he P hP x 2).1 ((val_iota_le_iff P 2 x).1 (by simpa using h))))
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  refine ⟨x, hval, fun n π y hπ => ?_⟩
  have hx0 : ∀ P, Over P v → iota x P ≠ 0 := fun P hP h => by
    have := hval P hP
    rw [h, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hq : ∀ P, Over P v → ((π⁻¹ * y : (Af E)ˣ) : Af E) P = (iota x P)⁻¹ * (y : Af E) P := fun P hP => by
    rw [Units.val_mul, mul_coord, inv_coord, hπ P hP]
  constructor
  · intro h
    refine ⟨?_, fun hu => ?_⟩
    · obtain ⟨b, hb⟩ := h
      refine ⟨x * b, fun P hP => ?_⟩
      have h0 := hx0 P hP
      have : (y : Af E) P - iota (x * b) P = iota x P * (((π⁻¹ * y : (Af E)ˣ) : Af E) P - iota b P) := by
        rw [hq P hP, iota_mul, mul_coord]; field_simp
      rw [this, map_mul, hval P hP]
      refine (mul_le_mul' le_rfl (hb P hP)).trans_eq ?_
      rw [← WithZero.exp_add]; congr 1; push_cast; ring
    · obtain ⟨P, -, -, hP, -⟩ := hv
      have h1 := h.val_le hP
      rw [hq P hP, map_mul, map_inv₀, hval P hP, hu P hP, mul_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at h1
      omega
  · rintro ⟨h, hu⟩
    push Not at hu
    obtain ⟨Q, hQ, hyQ⟩ := hu
    have hyQ' : Valued.v ((y : Af E) Q) < 1 := lt_of_le_of_ne (h.val_le hQ) hyQ
    obtain ⟨a, ha⟩ := h
    have hav : a ∈ v.asIdeal := by
      have h2 : Valued.v ((y : Af E) Q - iota a Q) < 1 :=
        ((ha Q hQ).trans (WithZero.exp_le_exp.2 (by push_cast; omega))).trans_lt hlt
      have h3 := Valuation.map_sub_lt _ hyQ' h2
      rw [sub_sub_cancel] at h3
      have h4 : Valued.v (iota a Q) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
        by_cases h0 : Valued.v (iota a Q) = 0
        · rw [h0]; exact zero_le'
        · rw [← WithZero.exp_log h0] at h3 ⊢
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
          rw [WithZero.exp_le_exp]; push_cast; omega
      simpa using (he Q hQ a 1).1 ((val_iota_le_iff Q 1 a).1 h4)
    rw [← span_sup_pow_eq_of_notMem_sq v (by simpa using hx1) hx2 n] at hav
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.1 hav
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    refine ⟨b, fun P hP => ?_⟩
    have h0 := hx0 P hP
    have : ((π⁻¹ * y : (Af E)ˣ) : Af E) P - iota b P =
        (iota x P)⁻¹ * (((y : Af E) P - iota (b * x + t) P) + iota t P) := by
      rw [hq P hP, iota_add, iota_mul, add_coord, mul_coord]; field_simp; ring
    rw [this, map_mul, map_inv₀, hval P hP]
    refine (mul_le_mul' le_rfl (Valuation.map_add_le _ (ha P hP) (val_iota_le_of_mem hP (n + 1) ht))).trans_eq ?_
    rw [← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; push_cast; ring

end GlobalTheory.CMVal.Euler
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIndexLeftRightCosetSumsEqStatement
section
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_index_left_right_coset_sums_eq : GlobalTheory.SatakeWeyl.UnimodFin := by
  first | exact @GlobalTheory.SatakeWeyl.unimodFin | exact GlobalTheory.SatakeWeyl.unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimodFin <;> assumption)
end

