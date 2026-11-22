import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntPoly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal)

def ComplexChowFormToChowForm.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsArithVar P (e + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ g →
      ∃ c : ℂ, c ≠ 0 ∧ ∃ f : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
        g = C c * map (Rat.castHom ℂ) f ∧ IsChowForm (genericIdeal P) (e + 1) f

def ChowFormToComplexChowForm.Statement : Prop :=
  ∀ (n e δ : ℕ) (P : Ideal (MRing (PBlk n))) (f : MvPolynomial (Fin (e + 1) × Fin n) ℚ),
    IsArithVar P (e + 1) → IsChowForm (genericIdeal P) (e + 1) f → IsMultiHomog δ f →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
        (map (Rat.castHom ℂ) f)

open Classical in

def DivCycleGeneric.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
    IsArithVar P (e + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      divCycle (genericIdeal P) (fun j => (u j : ℚ)) =
        ((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).filter IsHorizontal).mapDomain
          genericIdeal

def VertPartEq.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ),
    IsArithVar P (e + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      vertTerm (genericIdeal P) (e + 1) (fun j => ((u j : ℤ) : 𝓞 ℚ)) =
        IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemMinimalPrimesOfMemFundCycleSupport
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar ptsIntegral pot)

def ConeIntegralPts.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (u : Fin n → ℂ),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      cycleIntegral (ObjectsHeight.ofPointMatrix S hS) (fundCycle (complexFibreIdeal P)) e
          (fsLog (ObjectsHeight.ofPointMatrix S hS) u) =
        ptsIntegral P (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
          (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u)

theorem mem_minimalPrimes_of_mem_fundCycle_support {n : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W ∈ (fundCycle J).support) : W ∈ J.minimalPrimes := by
  have h := Finsupp.support_onFinset_subset hW
  rwa [Set.Finite.mem_toFinset] at h

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFibreDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

noncomputable section

namespace ConeFibreDegree

theorem ae_eval_ne_zero_univ {ι : Type*} [Fintype ι] (g : MvPolynomial ι ℂ) (hg : g ≠ 0) :
    ∀ᵐ u : ι → ℂ, eval u g ≠ 0 := by
  have hU : (⋃ r : ℕ, LogInt.polydisc ι r) = Set.univ := by
    refine Set.eq_univ_of_forall fun u => ?_
    obtain ⟨r, hr⟩ := exists_nat_ge ‖u‖
    refine Set.mem_iUnion.mpr ⟨r, Set.mem_univ_pi.mpr fun i => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_pi_norm u i).trans hr
  have h := (ae_restrict_iUnion_iff (fun r : ℕ => LogInt.polydisc ι r) (fun u => eval u g ≠ 0)).mpr
    fun r => LogInt.ae_eval_ne_zero g hg r
  rwa [hU, Measure.restrict_univ] at h

theorem ae_eval_matrix_ne_zero {k n : ℕ} (g : MvPolynomial (Fin k × Fin n) ℂ) (hg : g ≠ 0) :
    ∀ᵐ π : Fin k → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) g ≠ 0 := by
  have hmap : (volume : Measure (Fin k → Fin n → ℂ)) =
      (volume : Measure (Fin k × Fin n → ℂ)).map (MeasurableEquiv.curry (Fin k) (Fin n) ℂ) := by
    rw [ObjectsHeight.map_curry_volume]
    rfl
  rw [hmap, (MeasurableEquiv.curry (Fin k) (Fin n) ℂ).measurableEmbedding.ae_map_iff]
  exact ae_eval_ne_zero_univ g hg

theorem ae_eval_euclid_ne_zero {m : ℕ} (g : MvPolynomial (Fin m) ℂ) (hg : g ≠ 0) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), eval (WithLp.ofLp w) g ≠ 0 := by
  let L : EuclideanSpace ℂ (Fin m) ≃L[ℝ] (Fin m → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin m => ℂ)
  have hac : (volume : Measure (EuclideanSpace ℂ (Fin m))).map L ≪ volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h : ∀ᵐ u ∂(volume : Measure (EuclideanSpace ℂ (Fin m))).map L, eval u g ≠ 0 :=
    hac.ae_le (ae_eval_ne_zero_univ g hg)
  rw [ae_map_iff L.continuous.measurable.aemeasurable] at h
  · exact h
  · exact (isClosed_eq (continuous_eval g) continuous_const).isOpen_compl.measurableSet

theorem fibreCount_eq {k n : ℕ} (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (π : Fin k → Fin n → ℂ) (w : EuclideanSpace ℂ (Fin k)) :
    fibreCount h W π w =
      (ComplexSets.fibre W (Matrix.of π * (h.matᵀ)⁻¹) (WithLp.ofLp w)).encard := by
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hinj : Function.Injective h.pointOf := by
    intro y y' hyy
    have hv := congrArg (fun v => (h.matᵀ)⁻¹ *ᵥ v) hyy
    simp only [HermNorm.pointOf, mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec] at hv
    exact WithLp.ofLp_injective 2 hv
  have hπ : ∀ y : EuclideanSpace ℂ (Fin n),
      (Matrix.of π * (h.matᵀ)⁻¹) *ᵥ h.pointOf y = WithLp.ofLp (linProj π y) := by
    intro y
    rw [HermNorm.pointOf, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]
    ext i
    simp [linProj, mulVec, dotProduct]
  rw [fibreCount, ← hinj.injOn.encard_image]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, ComplexSets.fibre, ComplexSets.zeroSet, coneSet]
  constructor
  · rintro ⟨y, ⟨hy, rfl⟩, rfl⟩
    exact ⟨hy, hπ y⟩
  · rintro ⟨hx, hxw⟩
    have hpt : h.pointOf (WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = x := by
      simp [HermNorm.pointOf, mulVec_mulVec, mul_nonsing_inv _ hu]
    refine ⟨WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x), ⟨?_, ?_⟩, hpt⟩
    · rw [hpt]; exact hx
    · apply WithLp.ofLp_injective 2
      rw [← hπ, hpt, hxw]

theorem proof (hD : ConeDimOfChowForm.Statement)
    (hG : ComplexSets.GenericProjectionFinite.Statement)
    (hC : ComplexSets.DiscriminantCover.Statement) (hP : ProjDegreeChow.Statement) :
    ConeFibreDegree.Statement := by
  intro n e δ h W f hW hf hδ
  have hdim := hD ℂ n (e + 1) W f hW hf
  obtain ⟨⟨U, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hUfin⟩, -, -, -⟩ := hG n (e + 1) W hW.isPrime hdim
  rw [hS] at hA₀
  obtain ⟨p, hpS, hp⟩ := hA₀
  have hu : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  set B := (h.matᵀ)⁻¹ with hB
  set q : MvPolynomial (Fin (e + 1) × Fin n) ℂ :=
    bind₁ (fun ij => ∑ k, X (ij.1, k) * C (B k ij.2)) p with hqdef
  have hq : ∀ π : Fin (e + 1) → Fin n → ℂ,
      eval (fun ij => π ij.1 ij.2) q = eval (fun ij => (Matrix.of π * B) ij.1 ij.2) p := by
    intro π
    show eval₂Hom (RingHom.id ℂ) _ q = eval₂Hom (RingHom.id ℂ) _ p
    rw [hqdef, eval₂Hom_bind₁]
    congr 2
    funext ij
    simp [Matrix.mul_apply]
  have hq0 : q ≠ 0 := by
    intro h0
    have h1 := hq fun i j => (A₀ * h.matᵀ) i j
    have hA : Matrix.of (fun i j => (A₀ * h.matᵀ) i j) * B = A₀ := by
      rw [hB, show Matrix.of (fun i j => (A₀ * h.matᵀ) i j) = A₀ * h.matᵀ from rfl, Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
    rw [h0, map_zero, hA] at h1
    exact hp h1.symm
  filter_upwards [ae_eval_matrix_ne_zero q hq0] with π hπ
  have hfin : ComplexSets.IsFiniteProjection W (Matrix.of π * B) := by
    have hmem : Matrix.of π * B ∈ {A : Matrix (Fin (e + 1)) (Fin n) ℂ |
        ∃ p ∈ S, eval (fun ij => A ij.1 ij.2) p ≠ 0} := ⟨p, hpS, by rw [← hq]; exact hπ⟩
    rw [← hS] at hmem
    exact hUfin _ hmem
  obtain ⟨P, hP0, hPy⟩ := hC n (e + 1) W (Matrix.of π * B) hW.isPrime hdim hfin
  filter_upwards [ae_eval_euclid_ne_zero P hP0] with w hw
  obtain ⟨hfinite, hcard, -⟩ := hPy _ hw
  rw [fibreCount_eq, ← hfinite.cast_ncard_eq, hcard, hP n e δ W f _ hW hf hδ hfin]

end ConeFibreDegree

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealSeparate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealSeparate.proof (hZ : IncidenceZeroLocus.Statement) (hT : FormsThroughPoint.Statement)
    (hD : IncIdealNeBotDim.Statement) : IncIdealSeparate.Statement := by
  intro F _ n k P Q hP hQ hne hle q hqQ
  by_contra hqP
  have := hP.isPrime

  obtain ⟨φ, hφ⟩ : ∃ φ : (MvPolynomial (Fin n) F ⧸ P) →ₐ[F] AlgebraicClosure F,
      φ (Ideal.Quotient.mk P q) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqP (Ideal.Quotient.eq_zero_iff_mem.mp
      (FGNullstellensatz.proof F (MvPolynomial (Fin n) F ⧸ P) (Ideal.Quotient.mk P q) h))
  let x : Fin n → AlgebraicClosure F := fun j => φ (Ideal.Quotient.mk P (X j))
  have hev : ∀ g, aeval x g = φ (Ideal.Quotient.mk P g) := by
    intro g
    have h : (aeval x : MvPolynomial (Fin n) F →ₐ[F] AlgebraicClosure F) =
        φ.comp (Ideal.Quotient.mkₐ F P) := by
      ext j
      simp [x]
    rw [h]
    rfl
  have hxq : aeval x q ≠ 0 := by rw [hev]; exact hφ
  have hx0 : x ≠ 0 := by
    intro h0
    apply hxq
    have hc : constantCoeff q = 0 := by
      by_contra hc
      have hmem := hQ.isHomog q hqQ 0
      rw [homogeneousComponent_zero, ← constantCoeff_eq] at hmem
      exact hQ.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit hc).map C))
    rw [h0, aeval_zero, hc, map_zero]

  obtain ⟨u, hux, huQ⟩ := hT F n k Q hQ (hD F n k Q hQ hne) x hx0 ⟨q, hqQ, hxq⟩
  apply huQ
  refine hZ F n k Q hQ.isHomog (AlgebraicClosure F) u fun g hg => ?_
  have hgP := hle hg
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hgP
  refine hgP u ⟨x, hx0, fun g' hg' => ?_, hux⟩
  rw [hev, Ideal.Quotient.eq_zero_iff_mem.mpr hg', map_zero]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLocalSectionLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module Submodule
open scoped Pointwise

namespace LocalSectionLengthSum

theorem length_quot_smul_top_eq {B : Type*} [CommRing B] (I : Ideal B) (f : B) :
    Module.length B ((B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I))) =
      Module.length B (B ⧸ (I ⊔ Ideal.span {f})) := by
  let g : B →ₗ[B] (B ⧸ I) ⧸ (f • ⊤ : Submodule B (B ⧸ I)) :=
    (f • ⊤ : Submodule B (B ⧸ I)).mkQ ∘ₗ I.mkQ
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : LinearMap.ker g = I ⊔ Ideal.span {f} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
      Quotient.mk_eq_zero, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul] at hy
      have hx : x = f * b - (f * b - x) := by ring
      rw [hx]
      exact sub_mem (mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
        (mem_sup_left hy)
    · intro hx
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have h : f * a - (y + a * f) = -y := by ring
      rw [h]
      exact neg_mem hy
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq]

theorem length_pi_quot_smul_top_eq {B ι : Type*} [CommRing B] [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)] (f : B) :
    Module.length B ((Π i, M i) ⧸ (f • ⊤ : Submodule B (Π i, M i))) =
      ∑ i, Module.length B (M i ⧸ (f • ⊤ : Submodule B (M i))) := by
  let g : (Π i, M i) →ₗ[B] (Π i, M i ⧸ (f • ⊤ : Submodule B (M i))) :=
    LinearMap.pi fun i => (f • ⊤ : Submodule B (M i)).mkQ ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by simp [g, hx i]⟩
  have hker : LinearMap.ker g = f • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, mem_smul_pointwise_iff_exists, mem_top, true_and]
    constructor
    · intro h
      have hx : ∀ i, ∃ y : M i, f • y = x i := fun i => by
        have h' := congrFun h i
        simpa [g, mem_smul_pointwise_iff_exists] using h'
      choose y hy using hx
      exact ⟨y, funext hy⟩
    · rintro ⟨y, rfl⟩
      funext i
      exact (Quotient.mk_eq_zero _).mpr (smul_mem_pointwise_smul (y i) f ⊤ mem_top)
  rw [← hker, (g.quotKerEquivOfSurjective hg).length_eq, Module.length_pi_of_fintype]

end LocalSectionLengthSum

theorem LocalSectionLengthSum.proof (hPi : PiQuotCokerFiniteLength.Statement) :
    LocalSectionLengthSum.Statement := by
  intro B _ _ _ J f hJ hf hQ
  obtain ⟨hinj, hfin⟩ := hPi B J hJ hQ
  have hfinite := J.finite_minimalPrimes_of_isNoetherianRing B
  let _ : Fintype J.minimalPrimes := hfinite.fintype
  have hreg : Function.Injective fun x : ((P : J.minimalPrimes) → B ⧸ (P : Ideal B)) => f • x := by
    intro x y hxy
    funext P
    have : (P : Ideal B).IsPrime := P.2.1.1
    have h : f • x P = f • y P := congrFun hxy P
    rw [Algebra.smul_def, Algebra.smul_def] at h
    refine mul_left_cancel₀ ?_ h
    rw [Ne, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hf P P.2
  have e1 := Model.TorsionFreeQuotientLength.length_quot_smul_eq (quotToPiMinimalPrimes J) hinj
    hreg hfin
  rw [← LocalSectionLengthSum.length_quot_smul_top_eq J f, ← e1,
    LocalSectionLengthSum.length_pi_quot_smul_top_eq]
  simp_rw [LocalSectionLengthSum.length_quot_smul_top_eq]
  exact (Finset.sum_subtype (p := (· ∈ J.minimalPrimes)) hfinite.toFinset
    (fun P => hfinite.mem_toFinset)
    (fun P : Ideal B => Module.length B (B ⧸ (P ⊔ Ideal.span {f})))).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSecRankSpecialize
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SecRankSpecialize

open Vertical

def secMap {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    SecAlg Q y →ₐ[R] SecAlg (Q.map (MvPolynomial.map (algebraMap R S))) (algebraMap R S ∘ y) :=
  Ideal.quotientMapₐ _ (MvPolynomial.mapAlgHom (Algebra.ofId R S))
    (by rw [SecAlgFieldChange.secIdeal_map]; exact Ideal.le_comap_map)

theorem secMap_mk {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (p : MvPolynomial (Fin n) R) :
    secMap S Q y (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap R S) p) := rfl

theorem mem_maximalIdeal_smul_of_secMap_eq_zero {R : Type*} [CommRing R] [IsLocalRing R]
    (κ : Type*) [Field κ] [Algebra R κ] (hsurj : Function.Surjective (algebraMap R κ)) {n e : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) (x : SecAlg Q y)
    (hx : secMap κ Q y x = 0) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (SecAlg Q y)) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hker : RingHom.ker (algebraMap R κ) = IsLocalRing.maximalIdeal R := by
    have := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact IsLocalRing.eq_maximalIdeal this
  have hp : p ∈ secIdeal Q y ⊔ Ideal.map C (IsLocalRing.maximalIdeal R) := by
    rw [secMap_mk, Ideal.Quotient.eq_zero_iff_mem, SecAlgFieldChange.secIdeal_map,
      ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective _ (MvPolynomial.map_surjective _ hsurj),
      ← RingHom.ker_eq_comap_bot, MvPolynomial.ker_map, hker] at hx
    exact hx
  have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk (secIdeal Q y)) hp
  rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_map] at hm
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
  have he : (Ideal.Quotient.mk (secIdeal Q y)).comp C = algebraMap R (SecAlg Q y) :=
    RingHom.ext fun _ => rfl
  rwa [he] at hm

end SecRankSpecialize

open SecRankSpecialize in

theorem SecRankSpecialize.proof : SecRankSpecialize.Statement := by
  intro R K κ _ _ _ _ _ _ _ _ n e Q y hsurj hfin
  classical
  let ρ := secMap κ Q y
  let ι := secMap K Q y
  have hρ : Function.Surjective ρ := by
    intro z
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ hsurj q
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have : Module.Finite R
      (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)) :=
    Module.Finite.of_surjective ρ.toLinearMap hρ
  have : Module.Finite κ
      (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)) :=
    Module.Finite.of_restrictScalars_finite R κ _
  let v := Module.finBasis κ
    (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y))
  choose b hb using fun i => hρ (v i)

  have htop : Submodule.span R (Set.range b) = ⊤ := by
    refine top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) ?_)
    intro x _
    choose r hr using fun i => hsurj (v.repr (ρ x) i)
    have hsum : ∑ i, r i • ρ (b i) = ρ x := by
      conv_rhs => rw [← v.sum_repr (ρ x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb, ← hr i, algebraMap_smul]
    have hz : ρ (x - ∑ i, r i • b i) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul]
      rw [hsum, sub_self]
    have hm := mem_maximalIdeal_smul_of_secMap_eq_zero κ hsurj Q y _ hz
    have hx : x = ∑ i, r i • b i + (x - ∑ i, r i • b i) := by abel
    rw [hx]
    exact Submodule.add_mem_sup
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)) hm

  have hB : ∀ x, ι x ∈ Submodule.span K (Set.range fun i => ι (b i)) := by
    intro x
    have hx : x ∈ Submodule.span R (Set.range b) := htop ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
    | smul c u _ hu => rw [map_smul, ← algebraMap_smul K]; exact Submodule.smul_mem _ _ hu
  have hspan : Submodule.span K (Set.range fun i => ι (b i)) = ⊤ := by
    refine eq_top_iff.mpr fun z hz => ?_
    clear hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on' with
    | monomial u a =>
      have hmon : (Ideal.Quotient.mk _ (monomial u a) :
          Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y)) =
          a • ι (Ideal.Quotient.mk _ (monomial u 1)) := by
        rw [secMap_mk, MvPolynomial.map_monomial, map_one, ← Ideal.Quotient.mkₐ_eq_mk K,
          ← map_smul, smul_monomial, smul_eq_mul, mul_one]
      rw [hmon]
      exact Submodule.smul_mem _ _ (hB _)
    | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  calc Module.finrank K
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R K))) (algebraMap R K ∘ y))
        = Module.finrank K (Submodule.span K (Set.range fun i => ι (b i))) := by
          rw [hspan, finrank_top]
      _ ≤ Fintype.card (Fin (Module.finrank κ
          (Vertical.SecAlg (Q.map (MvPolynomial.map (algebraMap R κ))) (algebraMap R κ ∘ y)))) :=
          finrank_range_le_card _
      _ = _ := Fintype.card_fin _

end

end GroundTheory.Heights₂.Heights
end

