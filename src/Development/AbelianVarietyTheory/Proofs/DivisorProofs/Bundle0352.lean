import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeTgt

variable {R : Type} [CommRing R]

theorem cls_eq' {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeTgt

private theorem coe_zcomp {R : Type} [CommRing R] {K L M : Cx R} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) :
    ((zcomp a b h : Cocycle K M k) : Cochain K M k) = a.1.comp b.1 h := rfl

private theorem cohomologyClass_mk_eq_zero_of_eq_δ {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (x : Cocycle K L n)
    (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m) (h : (x : Cochain K L n) = δ m n β) :
    CohomologyClass.mk x = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
  exact ⟨β, h.symm⟩

theorem GlobalTheory.EtC.coneSeqTgt_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  intro R _ K I J f n
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · obtain ⟨y, rfl⟩ := c.mk_surjective
    constructor
    · intro hy
      simp only [cpush, cpost_mk] at hy
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
      obtain ⟨γ, hγ⟩ := hy
      rw [coe_zcomp] at hγ
      have ha : δ n (n + 1) (γ.comp (mappingCone.fst f).1 (by omega : n - 1 + 1 = n)) = 0 := by
        rw [δ_comp γ (mappingCone.fst f).1 _ n 2 (n + 1) rfl (by omega) rfl,
          Cocycle.δ_eq_zero, hγ]
        simp [Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl ha), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n - 1) (by omega)
        (-(γ.comp (mappingCone.snd f) (add_zero _))) ?_
      rw [coe_zcomp, δ_neg, δ_comp_zero_cochain _ _ _ (by omega), mappingCone.δ_snd, hγ]
      simp [Cochain.comp_assoc_of_second_is_zero_cochain,
        Cochain.comp_assoc_of_third_is_zero_cochain, mappingCone.inr_snd]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨x, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ (n + -1) (by omega) (x.1.comp (mappingCone.inl f) rfl) ?_
      rw [δ_comp x.1 (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl (neg_add_cancel 1),
        mappingCone.δ_inl, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp]
  · obtain ⟨z, rfl⟩ := c.mk_surjective
    constructor
    · intro hz
      rw [cpost_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨c₀, hc₀⟩ := hz
      rw [coe_zcomp] at hc₀
      have hy : δ n (n + 1) (z.1.comp (mappingCone.snd f) (add_zero n) +
          c₀.comp (Cochain.ofHom f) (add_zero n)) = 0 := by
        rw [δ_add, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, δ_comp_ofHom, hc₀,
          Cocycle.δ_eq_zero]
        simp [Cochain.comp_assoc_of_third_is_zero_cochain]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hy), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n + -1) (by omega)
        (c₀.comp (mappingCone.inl f) rfl) ?_
      rw [coe_zcomp, δ_comp c₀ (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl
        (neg_add_cancel 1), mappingCone.δ_inl, hc₀]
      rw [mappingCone.ext_cochain_to_iff _ n (n + 1) rfl]
      constructor
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.add_comp]
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain,
          Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.add_comp]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨y, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl 0 ?_
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
  · obtain ⟨w, rfl⟩ := c.mk_surjective
    constructor
    · intro hw
      simp only [cpush, cpost_mk] at hw
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hw
      obtain ⟨b, hb⟩ := hw
      rw [coe_zcomp] at hb
      refine ⟨CohomologyClass.mk (mappingCone.liftCocycle f w (-b) rfl
        (by rw [δ_neg, hb]; simp)), ?_⟩
      rw [cpost_mk]
      congr 1
      apply Cocycle.ext
      rw [coe_zcomp]
      simp [mappingCone.liftCochain_fst]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨z, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl (-(z.1.comp (mappingCone.snd f) (add_zero n))) ?_
      rw [δ_neg, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_third_is_zero_cochain]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.BiprodCls

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull {K L M : _root_.GlobalTheory.EtC.Cx R} (f : K ⟶ L)
    (g : L ⟶ M) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    _root_.GlobalTheory.EtC.cpull f I n (_root_.GlobalTheory.EtC.cpull g I n x) =
      _root_.GlobalTheory.EtC.cpull (f ≫ g) I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_add {K L : _root_.GlobalTheory.EtC.Cx R} (f g : K ⟶ L)
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (f + g) I n x =
      _root_.GlobalTheory.EtC.cpull f I n x + _root_.GlobalTheory.EtC.cpull g I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.add_comp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_zero {K L : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_zero]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_id {K : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    _root_.GlobalTheory.EtC.cpull (𝟙 K) I n x = x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

end GlobalTheory.EtC.BiprodCls

namespace GlobalTheory.EtC
open BiprodCls

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cpull_biprod_bijective : ∀ (R : Type) [CommRing R]
    (K L I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ),
    Function.Bijective fun x : CohomologyClass (K ⊞ L) I n =>
      (_root_.GlobalTheory.EtC.cpull (biprod.inl : K ⟶ K ⊞ L) I n x,
        _root_.GlobalTheory.EtC.cpull (biprod.inr : L ⟶ K ⊞ L) I n x) := by
  intro R _ K L I n
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y => _root_.GlobalTheory.EtC.cpull (biprod.fst : K ⊞ L ⟶ K) I n y.1 +
    _root_.GlobalTheory.EtC.cpull (biprod.snd : K ⊞ L ⟶ L) I n y.2, fun x => ?_, fun y => ?_⟩
  · simp only [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, ← _root_.GlobalTheory.EtC.BiprodCls.cpull_add,
      biprod.total, _root_.GlobalTheory.EtC.BiprodCls.cpull_id]
  · obtain ⟨a, b⟩ := y
    simp only [map_add, _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_fst, biprod.inl_snd,
      biprod.inr_fst, biprod.inr_snd, _root_.GlobalTheory.EtC.BiprodCls.cpull_id,
      _root_.GlobalTheory.EtC.BiprodCls.cpull_zero, add_zero, zero_add]

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryGroupHaarIsMulRightInvariant
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem haar_UJ_isMulRightInvariant : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro n ε μ _
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by rw [Measure.map_smul, hR.map_mul_right_eq_self]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndefiniteUnitaryLieAlgebraMemIffEntries
section
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem pcLieEntry : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z ↔ ∀ a b, (starRingEnd ℂ) (Z a b) = -((if ε a then (1 : ℂ) else -1) * (if ε b then (1 : ℂ) else -1) * Z b a) := by
  intro n ε Z
  have key : ∀ a b, (Zᴴ * Jm ε + Jm ε * Z) a b = (starRingEnd ℂ) (Z b a) * (if ε b then (1 : ℂ) else -1) + (if ε a then (1 : ℂ) else -1) * Z a b := by
    intro a b
    simp [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  unfold inG
  constructor
  · intro h a b
    have hb := congrFun (congrFun h b) a
    rw [key] at hb
    simp only [Matrix.zero_apply] at hb
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb
  · intro h
    ext a b
    rw [key]
    simp only [Matrix.zero_apply]
    have hb := h b a
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLengthStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_finite_length : GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  first | exact @GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard | exact GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard | (intros; apply GlobalTheory.JacquetBlocks.jacquetFiniteLength_of_standard <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureZmodTorsorGenericFibreData
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ClosureData

open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth

section
variable (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]

theorem algebraMap_mem_nonZeroDivisors [Module.Flat A R] {a : A} (ha : a ≠ 0) :
    algebraMap A R a ∈ nonZeroDivisors R := by
  have h : IsSMulRegular R a :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha)
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx => h ?_
  simp only [Algebra.smul_def, smul_zero]
  rw [mul_comm, mul_zero]; exact hx

theorem genFib_injective [Module.Flat A R] : Function.Injective (algebraMap R (GenFib A R)) := by
  apply IsLocalization.injective (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A))
  rintro _ ⟨a, ha, rfl⟩
  exact algebraMap_mem_nonZeroDivisors A R (nonZeroDivisors.ne_zero ha)

theorem isUnit_genFib {a : A} (ha : a ≠ 0) :
    IsUnit (algebraMap R (GenFib A R) (algebraMap A R a)) :=
  IsLocalization.map_units (M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (GenFib A R)
    ⟨algebraMap A R a, ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩⟩
end

section
variable {A R D : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
  [Algebra (GenFib A R) D]

theorem baseHom_apply (r : R) :
    baseHom A R D r = algebraMap (GenFib A R) D (algebraMap R (GenFib A R) r) := rfl

theorem map_mem (σ : D →ₐ[GenFib A R] D) {d : D} (hd : d ∈ closure A R D) :
    σ d ∈ closure A R D := by
  letI := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact IsIntegral.map (σ.restrictScalars R) (show IsIntegral R d from hd)

def restr (σ : D ≃ₐ[GenFib A R] D) :
    letI := closureAlg A R D
    closure A R D ≃ₐ[R] closure A R D :=
  letI := closureAlg A R D
  { toFun := fun c => ⟨σ c.1, map_mem σ.toAlgHom c.2⟩
    invFun := fun c => ⟨σ.symm c.1, map_mem σ.symm.toAlgHom c.2⟩
    left_inv := fun c => Subtype.ext (σ.symm_apply_apply (c : D))
    right_inv := fun c => Subtype.ext (σ.apply_symm_apply (c : D))
    map_mul' := fun c c' => Subtype.ext (map_mul σ (c : D) (c' : D))
    map_add' := fun c c' => Subtype.ext (map_add σ (c : D) (c' : D))
    commutes' := fun r => Subtype.ext (σ.commutes (algebraMap R (GenFib A R) r)) }

@[simp] theorem restr_coe (σ : D ≃ₐ[GenFib A R] D) (c : closure A R D) :
    ((letI := closureAlg A R D; restr σ c : closure A R D) : D) = σ c := rfl

end

section
variable {A R D : Type} [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
  [Algebra (GenFib A R) D]

theorem trace_mem (hIC : ∀ f : GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GenFib A R) r = f)
    (hinj : Function.Injective (algebraMap (GenFib A R) D))
    (τ : D →ₗ[GenFib A R] GenFib A R) (q : ℕ) [NeZero q]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[GenFib A R] D))
    (hτ : ∀ d, algebraMap _ D (τ d) = ∑ g, act g d) {c : D} (hc : c ∈ closure A R D) :
    ∃ r : R, algebraMap R (GenFib A R) r = τ c := by
  apply hIC
  letI := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GenFib A R) D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R (GenFib A R) D) hinj]
  show IsIntegral R (algebraMap (GenFib A R) D (τ c))
  rw [hτ]
  exact (sum_mem fun g _ => map_mem (act g).toAlgHom hc : ∑ g, act g c ∈ GlobalTheory.KeyOriginNoeth.closure A R D)

theorem smul_coe (r : R) (c : closure A R D) :
    ((letI := closureAlg A R D; r • c : closure A R D) : D) =
      algebraMap R (GenFib A R) r • (c : D) := by
  letI := closureAlg A R D
  rw [Algebra.smul_def, Algebra.smul_def]; rfl

end

theorem closureData : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    [Nontrivial R] [Module.Flat A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    (∀ f : GlobalTheory.LocAcyc.GenFib A R, IsIntegral R f → ∃ r : R, algebraMap R (GlobalTheory.LocAcyc.GenFib A R) r = f) →
    ∀ (q : ℕ) [NeZero q] (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] D)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) D q act →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    ∃ (act' : Multiplicative (ZMod q) →* (GlobalTheory.KeyOriginNoeth.closure A R D ≃ₐ[R] GlobalTheory.KeyOriginNoeth.closure A R D))
      (T : GlobalTheory.KeyOriginNoeth.closure A R D →ₗ[R] R),
      (∀ c, algebraMap R _ (T c) = ∑ g, act' g c) ∧
      (∃ a : A, a ≠ 0 ∧ ∃ (n : ℕ) (x y : Fin n → GlobalTheory.KeyOriginNoeth.closure A R D),
        ∀ g, ∑ i, x i * act' g (y i) = if g = 1 then algebraMap R _ (algebraMap A R a) else 0) ∧
      GlobalTheory.GoodEtale.TorsionFreeOver A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Algebra.IsIntegral R (GlobalTheory.KeyOriginNoeth.closure A R D) ∧
      Nontrivial (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ _ _ _ hHart hIC q _ D _ _ act hT
  classical
  letI := closureAlg A R D
  obtain ⟨hinj, ⟨τ, hτ⟩, n, x, y, hxy⟩ := GlobalTheory.TorsorTrace.injective_trace_galoisData _ D q act hT
  have hRinj := genFib_injective A R
  have htr : ∀ c ∈ closure A R D, ∃ r : R, algebraMap R (GenFib A R) r = τ c :=
    fun c hc => trace_mem hIC hinj τ q act hτ hc
  haveI : Module.Finite (GenFib A R) D := hT.1
  obtain ⟨a, ha, hmem⟩ := GlobalTheory.T.exists_mul_mem_integralClosureOverGenericFibre A R D (Finset.univ.image x ∪ Finset.univ.image y)
  set b := baseHom A R D (algebraMap A R a) with hbdef
  have hb : ∀ g, act g b = b := fun g => (act g).commutes _
  let x' : Fin n → closure A R D := fun i => ⟨b * x i, hmem _ (by simp)⟩
  let y' : Fin n → closure A R D := fun i => ⟨b * y i, hmem _ (by simp)⟩
  let act' : Multiplicative (ZMod q) →* (closure A R D ≃ₐ[R] closure A R D) :=
    { toFun := fun g => restr (act g)
      map_one' := by ext c; simp
      map_mul' := fun g h => by ext c; simp [map_mul] }
  have hact' : ∀ g c, ((act' g c : closure A R D) : D) = act g c := fun _ _ => rfl
  let Tf : closure A R D → R := fun c => Classical.choose (htr c c.2)
  have hT' : ∀ c, algebraMap R (GenFib A R) (Tf c) = τ c := fun c => Classical.choose_spec (htr c c.2)
  let T : closure A R D →ₗ[R] R :=
    { toFun := Tf
      map_add' := fun c c' => hRinj (by simp [hT'])
      map_smul' := fun r c => hRinj (by
        rw [hT', smul_coe, map_smul, smul_eq_mul, RingHom.id_apply, smul_eq_mul, map_mul, hT']) }
  have key : ∀ g, ∑ i, (x' i : D) * act g (y' i) = b * b * ∑ i, x i * act g (y i) := by
    intro g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show b * x i * act g (b * y i) = _
    rw [map_mul, hb]; ring
  have h1 : ∀ g, ∑ i, (x' i : D) * act g (y' i) = if g = 1 then b * b else 0 := by
    intro g; rw [key, hxy]; split_ifs <;> simp
  have hbb : b * b = baseHom A R D (algebraMap A R (a * a)) := by simp [hbdef, map_mul]
  refine ⟨act', T, ?_, ⟨a * a, mul_ne_zero ha ha, n, x', y', ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro c
    apply Subtype.ext
    show baseHom A R D (Tf c) = _
    rw [baseHom_apply, hT', hτ]
    simp [hact']
  · intro g
    apply Subtype.ext
    split_ifs with hg
    · simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, hact']
      rw [h1, if_pos hg, hbb]
      rfl
    · simp only [AddSubmonoidClass.coe_finset_sum, Subring.coe_mul, hact']
      rw [h1, if_neg hg]
      rfl
  · intro a' ha' c hc
    apply Subtype.ext
    have h1 := congrArg Subtype.val hc
    rw [smul_coe, Algebra.smul_def] at h1
    simpa using ((isUnit_genFib A R ha').map (algebraMap (GenFib A R) D)).mul_right_eq_zero.mp h1
  · refine GlobalTheory.T.integralClosureOverGenericFibre_hartogs A R hHart hRinj D τ htr (a * a) (mul_ne_zero ha ha) n
      (fun i => (x' i : D)) (fun i => (y' i : D)) (fun i => (y' i).2) ?_
    intro d
    have e1 : ∀ i, algebraMap (GenFib A R) D (τ ((y' i : D) * d)) = ∑ g, act g (y' i) * act g d := by
      intro i; rw [hτ]; simp [map_mul]
    simp only [e1, Finset.mul_sum]
    rw [Finset.sum_comm]
    have e2 : ∀ g, ∑ i, (x' i : D) * (act g (y' i) * act g d) =
        (if g = 1 then b * b else 0) * act g d := by
      intro g
      rw [← h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl fun g _ => e2 g]
    simp [hbb]
  · refine ⟨fun c => ?_⟩
    letI := (baseHom A R D).toAlgebra
    let f : closure A R D →ₐ[R] D := { (closure A R D).subtype with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).mp c.2
  · haveI : Nontrivial (GenFib A R) := hRinj.nontrivial
    haveI : Nontrivial D := hinj.nontrivial
    exact ⟨⟨0, 1, fun h => zero_ne_one (α := D) (by simpa using congrArg Subtype.val h)⟩⟩

end GlobalTheory.ClosureData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFunctionalExtensionStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_functional_extension : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (X : Type) [AddCommGroup X] [Module C X] [Module O X] [IsScalarTower O C X] (L : Submodule O X) (S : Submodule C X) (f : X →ₗ[C] C), v.Integers O → L.FG → (∀ x ∈ L, x ∈ S → f x ∈ (algebraMap O C).range) → ∃ F : X →ₗ[C] C, (∀ x ∈ L, F x ∈ (algebraMap O C).range) ∧ ∀ x ∈ L, x ∈ S → F x = f x := by
  first | exact @GlobalTheory.integral_form_extend_of_saturated | exact GlobalTheory.integral_form_extend_of_saturated | (intros; apply GlobalTheory.integral_form_extend_of_saturated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseUnipotentVolumeConjDiagonalUnitsGLMulStatement
section
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseUnipotentVolume_conj_diagonalUnitsGL_mul : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d e : n ⊕ Fin c → kˣ), invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) = invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) * invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  first | exact @GlobalTheory.FunObj.invVol_conj_diagGL_mul | exact GlobalTheory.FunObj.invVol_conj_diagGL_mul | (intros; apply GlobalTheory.FunObj.invVol_conj_diagGL_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbertSchemeRepresentableOfOpenCoverStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchemeRepresentable_of_open_cover : ∀ (S Z : Scheme.{0}) (z : Z ⟶ S), IsFinite z → Flat z → LocallyOfFinitePresentation z → ∀ r : ℕ, (∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsHilbRep (z ∣_ W) r) → IsHilbRep z r := by
  first | (exact @GlobalTheory.HilbGlue.isHilbRep_of_cover) | (exact GlobalTheory.HilbGlue.isHilbRep_of_cover) | (intros; apply GlobalTheory.HilbGlue.isHilbRep_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenStabilizerSchwartzBruhatStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_stabilizer_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar β → ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), IsOpen {h : GL (Fin d) k | GlobalTheory.SplitFlip.omA ν β 1 h Φ = Φ} := by
  first | exact @GlobalTheory.OmAStab.isOpen_omA_stab | exact GlobalTheory.OmAStab.isOpen_omA_stab | (intros; apply GlobalTheory.OmAStab.isOpen_omA_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualBicharacterPairingOfSymmBilinFormStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualBicharacterPairing_of_symmBilinForm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] [TopologicalSpace V] [IsModuleTopology F V] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (β : V →ₗ[F] V →ₗ[F] F), (∀ x y, β x y = β y x) → (∀ y, (∀ x, β x y = 0) → y = 0) → IsPair fun x y => ψ (β x y) := by
  first | exact @GlobalTheory.KSp.isPair_addChar_form | exact GlobalTheory.KSp.isPair_addChar_form | (intros; apply GlobalTheory.KSp.isPair_addChar_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAffineHilbertTensorPullbackEqMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_affineHilbertTensor_pullback_eq_map : ∀ (A B C : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C] (J : Ideal (C ⊗[A] B)) (Z : Scheme.{0}) (h : Z ⟶ Spec (CommRingCat.of C)) (U : Z.affineOpens), letI := (GlobalTheory.HilbAff.secAlg A (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) U).toAlgebra; ∃ φ : C →ₐ[A] Γ(Z, U), φ.toRingHom = GlobalTheory.HilbAff.secAlg C h U ∧ RingHom.ker (GlobalTheory.HilbAff.kappa A B (h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) ((GlobalTheory.HilbAff.xI A B C J).comap (GlobalTheory.HilbAff.bc A B (Spec.map (CommRingCat.ofHom (algebraMap A C))) h)) U) = J.map (Algebra.TensorProduct.map φ (AlgHom.id A B)) := by
  first | (exact @GlobalTheory.HilbAff.ker_kappa_xI_comap) | (exact GlobalTheory.HilbAff.ker_kappa_xI_comap) | (intros; apply GlobalTheory.HilbAff.ker_kappa_xI_comap <;> assumption)
end

