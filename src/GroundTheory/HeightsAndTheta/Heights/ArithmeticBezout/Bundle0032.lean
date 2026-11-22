import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMassOfFibre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.FiniteSupportLogCoeffGaussNorm
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace VerticalPartGauss

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)

section Places

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

end Places

section Generic

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {n : ℕ}

abbrev constUnits (n : ℕ) : Submonoid (MvPolynomial (Fin n) ℤ) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)

theorem algebraMap_eq : algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) =
    map (Int.castRingHom ℚ) := by
  rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]

theorem genericIdeal_eq (P : Ideal (MRing (PBlk n))) :
    genericIdeal P = (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map
      (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) := by
  rw [algebraMap_eq]
  rfl

theorem finIdeal_isPrime {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).IsPrime := by
  have := hP.2.1.1
  unfold IndefiniteRowSideFullHecke.ArithBezout.finIdeal
  infer_instance

theorem disjoint_constUnits {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    Disjoint (constUnits n : Set (MvPolynomial (Fin n) ℤ)) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, hk, rfl⟩ hmem
  have hk0 : k ≠ 0 := nonZeroDivisors.ne_zero hk
  have h1 : (C k : MRing (PBlk n)) ∈ P := by
    simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, rename_C] using hmem
  have h2 : k ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := h1
  rw [hP.2.2.1] at h2
  exact hk0 ((Submodule.mem_bot ℤ).mp h2)

theorem map_mem_genericIdeal_iff {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    (x : MvPolynomial (Fin n) ℤ) :
    map (Int.castRingHom ℚ) x ∈ genericIdeal P ↔ x ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
  have h := IsLocalization.under_map_of_isPrime_disjoint (constUnits n) (MvPolynomial (Fin n) ℚ)
    (finIdeal_isPrime hP) (disjoint_constUnits hP)
  rw [genericIdeal_eq, ← algebraMap_eq]
  constructor
  · intro hx
    rw [← h]
    exact hx
  · exact Ideal.mem_map_of_mem _

theorem genericIdeal_isPrime {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (genericIdeal P).IsPrime := by
  rw [genericIdeal_eq]
  exact IsLocalization.isPrime_of_isPrime_disjoint (constUnits n) _ _ (finIdeal_isPrime hP)
    (disjoint_constUnits hP)

def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv := fun ⟨(), _⟩ => rfl

theorem isHomogeneous_of_isMultiHomog {s : MRing (PBlk n)} {a : Unit → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    (map (Int.castRingHom ℚ) (rename (blkEquiv n).symm s)).IsHomogeneous (a ()) := by
  refine IsHomogeneous.map ?_ _
  refine IsHomogeneous.rename_isHomogeneous ?_
  intro m hm
  have h := hs m (mem_support_iff.mpr hm) ()
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Fintype.sum_unique]
  simpa using h

theorem finIdeal_eq_span {P : Ideal (MRing (PBlk n))} {S : Set (MRing (PBlk n))}
    (hS : P = Ideal.span S) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = Ideal.span (rename (blkEquiv n).symm '' S) := by
  have hre : ∀ x : MvPolynomial (Fin n) ℤ, rename (blkEquiv n).symm (rename (fun i : Fin n =>
      (⟨(), i⟩ : Σ _ : Unit, PBlk n ())) x) = x := fun x => by
    rw [rename_rename]
    exact rename_id_apply x
  have hre' : ∀ s : MRing (PBlk n), rename (fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ()))
      (rename (blkEquiv n).symm s) = s := fun s => by
    rw [rename_rename]
    convert rename_id_apply s
    funext p
    rcases p with ⟨⟨⟩, i⟩
    rfl
  apply le_antisymm
  · intro x hx
    have hx' : rename (fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ())) x ∈ Ideal.span S := by
      rw [← hS]; exact hx
    have := Ideal.mem_map_of_mem (rename (blkEquiv n).symm : MRing (PBlk n) →ₐ[ℤ] _).toRingHom hx'
    rw [Ideal.map_span] at this
    simpa [hre] using this
  · rw [Ideal.span_le]
    rintro _ ⟨s, hs, rfl⟩
    change rename _ (rename (blkEquiv n).symm s) ∈ P
    rw [hre', hS]
    exact Ideal.subset_span hs

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem genericIdeal_isHomog {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hSh, hS⟩ := hP.2.1.2.1
  have hspan : genericIdeal P = Ideal.span ((fun s => map (Int.castRingHom ℚ)
      (rename (blkEquiv n).symm s)) '' S) := by
    rw [ObjectsChow.genericIdeal, finIdeal_eq_span hS, Ideal.map_span, ← Set.image_comp]
    rfl
  have hhom : (genericIdeal P).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
    rw [hspan]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hSh s hs
    exact ⟨a (), (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_of_isMultiHomog ha)⟩
  intro f hf i
  have := hhom i hf
  rwa [← decomposition.decompose'_apply]

theorem genericIdeal_isRelevant {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsRelevant (genericIdeal P) := by
  obtain ⟨j, hj⟩ := (ObjectsChow.isRelevant_finIdeal_iff P).mpr hP.2.1.2.2
  refine ⟨j, fun h => hj ((map_mem_genericIdeal_iff hP (X j)).mp ?_)⟩
  rwa [map_X]

theorem isProjPrime_genericIdeal {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsProjPrime (genericIdeal P) :=
  ⟨genericIdeal_isPrime hP, genericIdeal_isHomog hP, genericIdeal_isRelevant hP⟩

theorem linForm_not_mem_genericIdeal {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    {u : Fin n → ℤ} (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    linForm (fun j => (u j : ℚ)) ∉ genericIdeal P := by
  intro h
  have hmap : linForm (fun j => (u j : ℚ)) = map (Int.castRingHom ℚ) (linForm u) := by
    simp [linForm, map_sum]
  rw [hmap, map_mem_genericIdeal_iff hP, ObjectsChow.linForm_mem_finIdeal] at h
  exact hu h

end Generic

theorem isChowForm_genericIdeal {n e δ : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P (e + 1))
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) :
    IsChowForm (genericIdeal P) (e + 1) f := by
  obtain ⟨c, hc, g, hcg, hg⟩ := ObjectsChow.ComplexChowFormToChowForm.proof n e δ P _ hP hf
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hg.1
  have hcoef := congrArg (coeff m) hcg
  rw [coeff_map, coeff_C_mul, coeff_map] at hcoef
  have hm' : ((g.coeff m : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hm
  have hcq : c = ((f.coeff m / g.coeff m : ℚ) : ℂ) := by
    rw [Rat.cast_div, eq_div_iff hm']
    simpa using hcoef.symm
  have hfq : f = C (f.coeff m / g.coeff m) * g := by
    apply map_injective (Rat.castHom ℂ) (Rat.castHom ℂ).injective
    rw [hcg, map_mul, map_C, hcq]
    rfl
  have hq : f.coeff m / g.coeff m ≠ 0 := by
    intro h
    apply hc
    rw [hcq, h, Rat.cast_zero]
  rw [hfq]
  exact ObjectsChow.isChowForm_C_mul hg hq

end VerticalPartGauss

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFiniteFibreDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped Matrix

noncomputable section

theorem exists_mem_zeroSet_mulVec_eq {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {B : Matrix (Fin d) (Fin n) ℂ} (hB : ComplexSets.IsFiniteProjection J B) (x : Fin d → ℂ) :
    ∃ z ∈ ComplexSets.zeroSet J, B *ᵥ z = x := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (ComplexSets.projHom J B).toRingHom.toAlgebra
  have _ : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ⟨fun y => hB.finite.to_isIntegral y⟩
  have _ : (RingHom.ker (eval x)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (eval x)) (by
      intro q hq
      have hq0 : q = 0 := hB.injective (by rw [RingHom.mem_ker] at hq; exact hq.trans (map_zero _).symm)
      rw [hq0]; exact Ideal.zero_mem _)
  have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨z, hz⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.1 hQ'
  have hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q ↔ eval z q = 0 := fun q => by
    rw [← Ideal.mem_comap, hz, mem_vanishingIdeal_singleton_iff]; rfl
  refine ⟨z, fun q hq => (hmem q).1 ?_, funext fun i => ?_⟩
  · rw [Ideal.Quotient.eq_zero_iff_mem.2 hq]; exact Q.zero_mem
  · have hi : X i - C (x i) ∈ RingHom.ker (eval x) := by simp [RingHom.mem_ker]
    rw [← hQP, Ideal.mem_comap] at hi
    change ComplexSets.projHom J B (X i - C (x i)) ∈ Q at hi
    have h1 : ComplexSets.projHom J B (X i - C (x i)) =
        Ideal.Quotient.mk J (ComplexSets.linPoly B i - C (x i)) := by
      simp [ComplexSets.projHom, ComplexSets.pullback]
    rw [h1, hmem, map_sub, eval_C, sub_eq_zero] at hi
    rw [← hi]
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem ConeFiniteFibreDim.proof : ConeFiniteFibreDim.Statement := by
  intro n m h J hJ _ _ hae
  have _ := hJ.isPrime

  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ n := by
    have := ringKrullDim_le_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    rwa [ComplexSets.ringKrullDim_mvPolynomial_complex] at this
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ J)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = D at h0 hle
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (not_le.2 (WithBot.coe_lt_coe.2 (ENat.coe_lt_top n)))
      | coe d => exact ⟨d, rfl⟩
  rw [hd]
  by_contra hlt
  have hmd : m < d := by push_neg at hlt; exact_mod_cast hlt
  obtain ⟨k, rfl⟩ : ∃ k, d = m + k := ⟨d - m, by omega⟩
  have hk : 0 < k := by omega

  obtain ⟨W, ⟨S, rfl⟩, ⟨A₀, p, hpS, hp⟩, hW⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (m + k) J inferInstance hd

  set N : Matrix (Fin n) (Fin n) ℂ := (h.mat)ᵀ⁻¹
  have hdet : IsUnit (h.mat)ᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hMN : (h.mat)ᵀ * N = 1 := Matrix.mul_nonsing_inv _ hdet

  let blk : ((Fin m × Fin n) ⊕ (Fin k × Fin n) → ℂ) → Matrix (Fin (m + k)) (Fin n) ℂ :=
    fun v i j => Fin.addCases (motive := fun _ => ℂ) (fun a => v (.inl (a, j))) (fun b => v (.inr (b, j))) i
  let g : Fin (m + k) × Fin n → MvPolynomial ((Fin m × Fin n) ⊕ (Fin k × Fin n)) ℂ := fun ij =>
    ∑ l, Fin.addCases (motive := fun _ => MvPolynomial ((Fin m × Fin n) ⊕ (Fin k × Fin n)) ℂ)
      (fun a => X (.inl (a, l))) (fun b => X (.inr (b, l))) ij.1 * C (N l ij.2)
  have heval : ∀ v, eval v (bind₁ g p) = eval (fun ij => (blk v * N) ij.1 ij.2) p := by
    intro v
    change eval₂Hom (RingHom.id ℂ) v (bind₁ g p) = eval₂Hom (RingHom.id ℂ) _ p
    rw [eval₂Hom_bind₁]
    refine congrArg (fun f => eval₂Hom (RingHom.id ℂ) f p) (funext fun ij => ?_)
    obtain ⟨i, j⟩ := ij
    change eval v (g (i, j)) = (blk v * N) i j
    simp only [g, blk, Matrix.mul_apply, map_sum, map_mul, eval_C]
    refine Finset.sum_congr rfl fun l _ => ?_
    induction i using Fin.addCases <;> simp
  have hP0 : bind₁ g p ≠ 0 := by
    intro h0'
    let v₀ : (Fin m × Fin n) ⊕ (Fin k × Fin n) → ℂ :=
      Sum.elim (fun aj => (A₀ * (h.mat)ᵀ) (Fin.castAdd k aj.1) aj.2)
        (fun bj => (A₀ * (h.mat)ᵀ) (Fin.natAdd m bj.1) bj.2)
    have hv₀ : blk v₀ = A₀ * (h.mat)ᵀ := by
      ext i j
      induction i using Fin.addCases <;> simp [blk, v₀]
    have := heval v₀
    rw [h0', map_zero, hv₀, Matrix.mul_assoc, hMN, Matrix.mul_one] at this
    exact hp this.symm

  have h1 := ConeFibreDegree.ae_eval_ne_zero_univ _ hP0
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin m × Fin n) ⊕ (Fin k × Fin n) => ℂ)).quasiMeasurePreserving.ae h1
  have h3 := Measure.ae_ae_of_ae_prod h2
  have h4 : ∀ᵐ a : Fin m × Fin n → ℂ, ∃ b : Fin k × Fin n → ℂ,
      eval ((MeasurableEquiv.sumPiEquivProdPi _).symm (a, b)) (bind₁ g p) ≠ 0 :=
    h3.mono fun a ha => ha.exists
  have h5 := (measurePreserving_curry_matrix m n).symm.quasiMeasurePreserving.ae h4
  have _ : (ae (volume : Measure (Fin m → Fin n → ℂ))).NeBot := by
    refine ae_neBot.2 (Measure.measure_univ_ne_zero.1 ?_)
    rw [volume_pi, Measure.pi_univ]
    exact Finset.prod_ne_zero_iff.2 fun i _ => Measure.measure_univ_ne_zero.2 (NeZero.ne _)
  obtain ⟨π, hπ, b, hb⟩ := (hae.and h5).exists
  set v := (MeasurableEquiv.sumPiEquivProdPi fun _ : (Fin m × Fin n) ⊕ (Fin k × Fin n) => ℂ).symm
    ((MeasurableEquiv.curry (Fin m) (Fin n) ℂ).symm π, b)
  have hrow : ∀ (u : Fin n → ℂ) (i : Fin m), (blk v *ᵥ u) (Fin.castAdd k i) = ∑ j, π i j * u j := by
    intro u i
    simp [blk, v, Matrix.mulVec, dotProduct, MeasurableEquiv.coe_curry_symm]
    rfl
  have hfin : ComplexSets.IsFiniteProjection J (blk v * N) := hW ⟨p, hpS, by rw [← heval]; exact hb⟩

  obtain ⟨w, hw⟩ := hπ.exists
  apply hw
  have key : ∀ c : ℂ, ∃ y : EuclideanSpace ℂ (Fin n), (y ∈ coneSet h J ∧ linProj π y = w) ∧
      (blk v *ᵥ fun j => y j) (Fin.natAdd m ⟨0, hk⟩) = c := by
    intro c
    obtain ⟨z, hz, hBz⟩ := exists_mem_zeroSet_mulVec_eq hfin
      (Fin.addCases (motive := fun _ => ℂ) (fun a => w a) (fun _ => c))
    rw [← Matrix.mulVec_mulVec] at hBz
    have hpt : h.pointOf (WithLp.toLp 2 (N *ᵥ z)) = z := by
      simp [HermNorm.pointOf, Matrix.mulVec_mulVec, hMN]
    refine ⟨WithLp.toLp 2 (N *ᵥ z), ⟨fun q hq => ?_, ?_⟩, ?_⟩
    · rw [hpt]; exact hz q hq
    · ext i
      have := congrFun hBz (Fin.castAdd k i)
      rw [hrow] at this
      simpa [linProj] using this
    · have := congrFun hBz (Fin.natAdd m ⟨0, hk⟩)
      rw [Fin.addCases_right] at this
      exact this
  choose y hy hyc using key
  have hinj : Function.Injective y := fun c₁ c₂ he => by
    rw [← hyc c₁, ← hyc c₂, he]
  exact (Set.infinite_of_injective_forall_mem hinj hy).encard_eq

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeKrullDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ConeKrullDimLe.proof (hDim : ConeFiniteFibreDim.Statement) : ConeKrullDimLe.Statement :=
  fun n m h J hJ hm hmn hae => hDim n m h J hJ hm hmn hae

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLocalMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

def HermNorm.pointOfₗ (h : HermNorm n) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun y := WithLp.toLp 2 (h.pointOf y)
  map_add' v w := by rw [HermNorm.pointOf_add']; rfl
  map_smul' c v := by rw [HermNorm.pointOf_smul']; rfl

theorem HermNorm.pointOfₗ_injective (h : HermNorm n) : Function.Injective h.pointOfₗ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  apply h.pointOf_eq_zero
  have := congrArg WithLp.ofLp hy
  simpa [HermNorm.pointOfₗ] using this

def HermNorm.pointOfL (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearEquiv.ofInjectiveEndo h.pointOfₗ h.pointOfₗ_injective).toContinuousLinearEquiv

theorem mem_coneSet_iff_pointOfL (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (y : EuclideanSpace ℂ (Fin n)) : y ∈ coneSet h J ↔ h.pointOfL y ∈ zeroSetEuc J :=
  Iff.rfl

theorem hausdorffMeasure_coneSet_ball_le (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (R : ℝ) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J ∩ Metric.ball 0 R) ≤
      ((‖(h.pointOfL.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖₊ : ℝ≥0∞) ^
          ((2 * d : ℕ) : ℝ)) *
        Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J ∩
          Metric.ball 0 (‖(h.pointOfL : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by
  set e := h.pointOfL
  have hsub : coneSet h J ∩ Metric.ball 0 R ⊆ e.symm '' (zeroSetEuc J ∩
      Metric.ball 0 (‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by
    rintro y ⟨hy, hyR⟩
    refine ⟨e y, ⟨(mem_coneSet_iff_pointOfL h J y).1 hy, ?_⟩, e.symm_apply_apply y⟩
    rw [mem_ball_zero_iff] at hyR ⊢
    calc ‖e y‖ = ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) y‖ := rfl
      _ ≤ ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R := by
        gcongr
      _ < _ := lt_add_one _
  calc _ ≤ Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (e.symm '' (zeroSetEuc J ∩
        Metric.ball 0 (‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1))) :=
        measure_mono hsub
    _ ≤ _ := e.symm.lipschitz.hausdorffMeasure_image_le (by positivity) _

theorem ConeLocalMass.proof (hDim : ConeFiniteFibreDim.Statement) (hMass : MassFinite.Statement)
    (hNull : NullSmaller.Statement) : ConeLocalMass.Statement := by
  intro n m h J hJ hm hmn hfib R
  have hle := hDim n m h J hJ hm hmn hfib
  refine lt_of_le_of_lt (hausdorffMeasure_coneSet_ball_le h J m R) ?_
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.coe_ne_top) ?_
  rcases hle.lt_or_eq with hlt | heq
  · rw [measure_mono_null Set.inter_subset_left (hNull n m J hlt)]
    exact ENNReal.zero_lt_top
  · exact hMass n m J hJ.isPrime heq _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLeadPlaneJac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open Module

theorem det_linProj_comp_zeroExt {m k : ℕ} (π : Fin m → Fin (m + k) → ℂ) :
    LinearMap.det ((linProjₗ π).comp (zeroExt m k)) = (coordPlaneBlock π).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin m) ℂ).toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp [linProjₗ, linProj_zeroExt, Matrix.mulVec, dotProduct]

theorem LeadPlaneJac.proof : LeadPlaneJac.Statement := by
  intro m k π
  have hmem : ∀ x, zeroExt m k x ∈ leadCoordPlane (m + k) m := fun x j hj => zeroExt_apply_of_le x j hj
  let e : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] leadCoordPlane (m + k) m := (zeroExt m k).codRestrict (leadCoordPlane (m + k) m) hmem
  let eᵢ : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] leadCoordPlane (m + k) m :=
    { toLinearMap := e, norm_map' := fun x => norm_zeroExt m k x }
  have he_surj : Function.Surjective e := by
    rintro ⟨y, hy⟩
    exact ⟨_, Subtype.ext (eq_zeroExt_of hy).symm⟩
  have hrank : finrank ℂ (EuclideanSpace ℂ (Fin m)) = finrank ℂ (leadCoordPlane (m + k) m) :=
    (LinearEquiv.ofBijective e ⟨eᵢ.injective, he_surj⟩).finrank_eq
  have hcomp : ((linProjₗ π).comp (leadCoordPlane (m + k) m).subtype).comp e = (linProjₗ π).comp (zeroExt m k) := rfl
  have he1 : LinearMap.normDet (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) e = 1 := by
    have h := LinearIsometry.normDet_eq_one (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m) eᵢ
    exact h
  have key := LinearMap.normDet_comp_of_finrank_eq (𝕜 := ℂ) (U := EuclideanSpace ℂ (Fin m)) (V := leadCoordPlane (m + k) m)
    (W := EuclideanSpace ℂ (Fin m)) e ((linProjₗ π).comp (leadCoordPlane (m + k) m).subtype) hrank
  rw [hcomp, he1, mul_one, LinearMap.normDet_eq_norm_det, det_linProj_comp_zeroExt] at key
  unfold tangentJac
  rw [← key]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGenericFibreDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

def GenericFibreDim.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P d →
    ringKrullDim (MvPolynomial (Fin n) ℚ ⧸ genericIdeal P) = ((d : ℕ) : WithBot ℕ∞)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

