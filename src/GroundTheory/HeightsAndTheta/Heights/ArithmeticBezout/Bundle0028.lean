import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.AevalGenericIdealIff
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk conePts)
open ChowFormExtend (incidenceIdeal coordPoly coeff_coordPoly coordPoly_C_mul_map coordPoly_mem_of_mem_map
  mem_zeroLocus_incidenceIdeal vanishes_incidence_iff incidenceIdeal_map radical_map_eq coordSupport
  sum_coordPoly coordPoly_sum)

namespace ComplexChowFormToChowForm

section Descent

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}

theorem mem_of_map_mem (T : Ideal (MvPolynomial Y K)) {x : MvPolynomial Y K}
    (hx : map (algebraMap K L) x ∈ T.map (map (algebraMap K L))) : x ∈ T := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  obtain ⟨c, hc⟩ : ∃ c, b.coord c 1 ≠ 0 := by
    by_contra! h
    have h0 : b.repr 1 = 0 := Finsupp.ext fun c => by rw [← Module.Basis.coord_apply]; exact h c
    exact one_ne_zero (b.repr.map_eq_zero_iff.mp h0)
  have hmem := coordPoly_mem_of_mem_map b T hx c
  have e := coordPoly_C_mul_map (b.coord c) (1 : L) x
  rw [C_1, one_mul] at e
  rw [e] at hmem
  have := T.mul_mem_left (C (b.coord c 1)⁻¹) hmem
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at this

theorem dvd_of_map_dvd {f h : MvPolynomial Y K}
    (hd : map (algebraMap K L) f ∣ map (algebraMap K L) h) : f ∣ h := by
  rw [← Ideal.mem_span_singleton] at hd ⊢
  apply mem_of_map_mem (L := L)
  rwa [Ideal.map_span, Set.image_singleton]

end Descent

variable {n : ℕ}

theorem aeval_genericIdeal_iff (P : Ideal (MRing (PBlk n))) (x : Fin n → ℂ) :
    (∀ q ∈ (genericIdeal P).map (map (algebraMap ℚ ℂ)), aeval x q = 0) ↔
      ∀ h ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P, eval x (map (Int.castRingHom ℂ) h) = 0 := by
  have hc : (map (algebraMap ℚ ℂ)).comp (map (Int.castRingHom ℚ)) =
      (map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) :=
    RingHom.ext fun p => by rw [RingHom.comp_apply, map_map]; congr 1
  rw [genericIdeal, Ideal.map_map, hc]
  constructor
  · intro H h hh
    exact H _ (Ideal.mem_map_of_mem _ hh)
  · intro H q hq
    have hle : (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (map (Int.castRingHom ℂ)) ≤
        RingHom.ker (eval x) := by
      rw [Ideal.map_le_iff_le_comap]
      intro h hh
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact H h hh
    exact RingHom.mem_ker.mp (hle hq)

theorem vanishes_cone_iff {k : ℕ} (P : Ideal (MRing (PBlk n))) (p : MvPolynomial (Fin k × Fin n) ℂ) :
    (∀ v : Fin k × Fin n → ℂ, (∃ z ∈ conePts (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P),
        ∀ i, ∑ j, v (i, j) * z j = 0) → eval v p = 0) ↔
      ∀ j, X (Sum.inr j) * rename Sum.inl p ∈
        (incidenceIdeal ((genericIdeal P).map (map (algebraMap ℚ ℂ))) k).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_incidenceIdeal, aeval_genericIdeal_iff]
  constructor
  · rintro h j z ⟨hI, hlin⟩
    rw [map_mul, aeval_X, aeval_rename]
    by_cases hx : z ∘ Sum.inr = 0
    · rw [show z (Sum.inr j) = 0 from congrFun hx j, zero_mul]
    · rw [aeval_eq_eval, h (z ∘ Sum.inl) ⟨z ∘ Sum.inr, ⟨hx, hI⟩, hlin⟩, mul_zero]
  · rintro h v ⟨x, ⟨hx, hI⟩, hlin⟩
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
    have := h j (Sum.elim v x) ⟨by simpa using hI, by simpa using hlin⟩
    rw [map_mul, aeval_X, aeval_rename, aeval_eq_eval] at this
    simpa [hj] using this

theorem vanishes_zero_iff_dvd {σ : Type*} [Finite σ] {g p : MvPolynomial σ ℂ} (hg : Squarefree g) :
    (∀ v, eval v g = 0 → eval v p = 0) ↔ g ∣ p := by
  have hrad : (Ideal.span {g}).radical = Ideal.span {g} :=
    (isRadical_iff_span_singleton.mp hg.isRadical).radical
  rw [← Ideal.mem_span_singleton, ← hrad, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_iff, aeval_eq_eval]
  constructor
  · intro h v hv
    exact h v (hv g (Ideal.mem_span_singleton_self g))
  · intro h v hv
    refine h v fun q hq => ?_
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    rw [map_mul, hv, zero_mul]

theorem proof : ComplexChowFormToChowForm.Statement := by
  intro n e δ P g _ hg
  obtain ⟨-, hsq, hzero⟩ := hg
  set R := (incidenceIdeal (genericIdeal P) (e + 1)).radical with hR
  have hradC : (incidenceIdeal ((genericIdeal P).map (map (algebraMap ℚ ℂ))) (e + 1)).radical =
      R.map (map (algebraMap ℚ ℂ)) := by
    rw [incidenceIdeal_map, radical_map_eq RadicalBaseChange.proof]
  have hZ : ∀ v : Fin (e + 1) × Fin n → ℂ, eval v g = 0 ↔
      ∃ z ∈ conePts (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P), ∀ i, ∑ j, v (i, j) * z j = 0 :=
    fun v => hzero (fun i j => v (i, j))
  have hC : ∀ p : MvPolynomial (Fin (e + 1) × Fin n) ℂ,
      g ∣ p ↔ ∀ j, X (Sum.inr j) * rename Sum.inl p ∈ R.map (map (algebraMap ℚ ℂ)) := by
    intro p
    rw [← vanishes_zero_iff_dvd hsq, ← hradC, ← vanishes_cone_iff]
    exact forall_congr' fun v => by rw [hZ v]
  have hQ : ∀ h : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
      (∀ u ∈ incidence (genericIdeal P) (e + 1), aeval u h = 0) ↔ g ∣ map (algebraMap ℚ ℂ) h := by
    intro h
    refine (vanishes_incidence_iff _ _ h).trans ?_
    rw [hC]
    refine forall_congr' fun j => ?_
    rw [show X (Sum.inr j) * rename Sum.inl (map (algebraMap ℚ ℂ) h) =
        map (algebraMap ℚ ℂ) (X (Sum.inr j) * rename Sum.inl h) by rw [map_mul, map_X, map_rename]]
    exact ⟨fun hm => Ideal.mem_map_of_mem _ hm, mem_of_map_mem R⟩
  have hg0 : g ≠ 0 := hsq.ne_zero
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hg0
  classical
  let b := Module.Basis.ofVectorSpace ℚ ℂ
  obtain ⟨c, hc⟩ : ∃ c, b.coord c (coeff m g) ≠ 0 := by
    by_contra! h
    have h0 : b.repr (coeff m g) = 0 := Finsupp.ext fun c => by rw [← Module.Basis.coord_apply]; exact h c
    exact hm (b.repr.map_eq_zero_iff.mp h0)
  have hcS : c ∈ coordSupport b g :=
    Finset.mem_biUnion.2 ⟨m, mem_support_iff.2 hm,
      Finsupp.mem_support_iff.2 (by rwa [← Module.Basis.coord_apply])⟩
  set h := coordPoly (b.coord c) g with hh_def
  have hh : g ∣ map (algebraMap ℚ ℂ) h := by
    refine (hQ h).mp ((vanishes_incidence_iff _ _ h).mpr fun j => ?_)
    have e' : X (Sum.inr j) * rename Sum.inl g = ∑ c' ∈ coordSupport b g,
        C (b c') * map (algebraMap ℚ ℂ) (X (Sum.inr j) * rename Sum.inl (coordPoly (b.coord c') g)) := by
      conv_lhs => rw [← sum_coordPoly b g]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [map_mul, rename_C, map_mul, map_X, map_rename]
      ring
    have hmem := coordPoly_mem_of_mem_map b R (e' ▸ (hC g).mp dvd_rfl j) c
    rwa [coordPoly_sum, if_pos hcS] at hmem
  obtain ⟨q, hq⟩ := hh
  have hmh : coeff m (map (algebraMap ℚ ℂ) h) ≠ 0 := by
    rw [coeff_map, hh_def, coeff_coordPoly]
    exact (map_ne_zero _).mpr hc
  have hmh0 : map (algebraMap ℚ ℂ) h ≠ 0 := fun h0 => hmh (by rw [h0, coeff_zero])
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hmh0 hq
  have hsupp : (map (algebraMap ℚ ℂ) h).support ⊆ g.support := by
    intro m' hm'
    rw [mem_support_iff] at hm' ⊢
    intro h0
    rw [coeff_map, hh_def, coeff_coordPoly, h0, map_zero, map_zero] at hm'
    exact hm' rfl
  have hdeg : q.totalDegree = 0 := by
    have h1 := totalDegree_mul_of_isDomain hg0 hq0
    have h2 := totalDegree_le_of_support_subset hsupp
    rw [← hq] at h1
    omega
  rw [totalDegree_eq_zero_iff_eq_C] at hdeg
  set a := q.coeff 0
  have ha : a ≠ 0 := fun h0 => hq0 (by rw [hdeg, h0, C_0])
  have hgm : g = C a⁻¹ * map (algebraMap ℚ ℂ) h := by
    rw [hq, hdeg, mul_comm g, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]
  have hu : IsUnit (C a⁻¹ : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero ha)).map C
  refine ⟨a⁻¹, inv_ne_zero ha, h, ?_, ?_⟩
  · rw [show Rat.castHom ℂ = algebraMap ℚ ℂ from Subsingleton.elim _ _]
    exact hgm
  · refine ⟨fun h0 => hmh0 (by rw [h0, map_zero]), fun h' => ?_⟩
    refine (hQ h').trans ?_
    rw [hgm, hu.mul_left_dvd]
    exact ⟨dvd_of_map_dvd, map_dvd _⟩

end ComplexChowFormToChowForm

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.IsHomogeneousOfIsMultiHomog
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

theorem squarefree_of_isChowForm {F : Type*} [Field F] {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) : Squarefree f := by
  rintro x ⟨h, rfl⟩
  have hxh : x * x * h ∣ x * h := by
    refine (hf.2 (x * h)).1 fun u hu => ?_
    have h0 := (hf.2 (x * x * h)).2 dvd_rfl u hu
    simp only [map_mul] at h0 ⊢
    have h2 : aeval u x * aeval u h * (aeval u x * aeval u h) = 0 := by
      calc _ = aeval u x * aeval u x * aeval u h * aeval u h := by ring
        _ = 0 := by rw [h0, zero_mul]
    exact mul_self_eq_zero.mp h2
  have hne : x * h ≠ 0 := fun h0 => hf.1 (by rw [mul_assoc, h0, mul_zero])
  have h1 : x * (x * h) ∣ 1 * (x * h) := by rwa [one_mul, ← mul_assoc]
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hne).mp h1)

theorem isHomogeneous_of_isMultiHomog {n : ℕ} {s : MRing (PBlk n)} {a : Unit → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) : s.IsHomogeneous (a ()) := by
  intro m hm
  rw [← hs m (mem_support_iff.mpr hm) ()]
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_sigma]

section Homog

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isHomogIdeal_genericIdeal {n d : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P d) :
    IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hS, rfl⟩ := hP.2.1.2.1
  let E : MRing (PBlk n) ≃+* MvPolynomial (Fin n) ℤ :=
    (renameEquiv ℤ (Equiv.uniqueSigma (PBlk n))).toRingEquiv
  have hfin : IndefiniteRowSideFullHecke.ArithBezout.finIdeal (Ideal.span S) = (Ideal.span S).map E := by
    rw [← Ideal.comap_symm]
    rfl
  have hhom : IsHomogIdeal (IndefiniteRowSideFullHecke.ArithBezout.finIdeal (Ideal.span S)) := by
    rw [isHomogIdeal_iff, hfin, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hS s hs
    exact ⟨a (), (mem_homogeneousSubmodule _ _).mpr
      ((isHomogeneous_of_isMultiHomog ha).rename_isHomogeneous)⟩
  exact isHomogIdeal_map (Int.castRingHom ℚ) hhom

end Homog

theorem ChowFormToComplexChowForm.proof (hZ : IncidenceZeroLocus.Statement) : ChowFormToComplexChowForm.Statement := by
  intro n e δ P f hP hf hδ
  have hcast : Rat.castHom ℂ = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  have hC := ChowFormExtend.isChowForm_map (L := ℂ) RadicalBaseChange.proof (genericIdeal P) f hf
  rw [← hcast] at hC
  refine ⟨(isMultihomog_map_iff (Rat.castHom ℂ).injective f).mpr ((isMultiHomog_iff f).mp hδ),
    squarefree_of_isChowForm hC, fun u => ⟨fun hu => ?_, fun ⟨z, hz, hzu⟩ => ?_⟩⟩
  ·
    have hv : ∀ g ∈ incIdeal (genericIdeal P) (e + 1), aeval (fun p => u p.1 p.2) g = 0 := by
      intro g hg
      simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker] at hg
      obtain ⟨h, rfl⟩ := (hf.2 g).1 fun w hw => hg w hw
      rw [map_mul, aeval_def, ← hcast, ← eval_map, hu, zero_mul]
    obtain ⟨y, hy0, hyQ, hyu⟩ := hZ ℚ n (e + 1) (genericIdeal P) (isHomogIdeal_genericIdeal hP) ℂ
      (fun p => u p.1 p.2) hv
    refine ⟨y, ⟨hy0, fun q hq => ?_⟩, fun j => hyu j⟩
    rw [eval_map, RingHom.ext_int (Int.castRingHom ℂ) ((algebraMap ℚ ℂ).comp (Int.castRingHom ℚ)),
      ← eval₂_map, ← aeval_def]
    exact hyQ _ (Ideal.mem_map_of_mem _ hq)
  ·
    set ι := algebraMap ℂ (AlgebraicClosure ℂ)
    have hle : (genericIdeal P).map (map (Rat.castHom ℂ)) ≤
        RingHom.ker (aeval (ι ∘ z) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] AlgebraicClosure ℂ) := by
      rw [genericIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, map_map,
        RingHom.ext_int ((Rat.castHom ℂ).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ),
        aeval_algebraMap_apply]
      exact (congrArg ι (hz.2 q hq)).trans (map_zero ι)
    have h1 := (hC.2 (map (Rat.castHom ℂ) f)).2 dvd_rfl (ι ∘ fun p => u p.1 p.2)
      ⟨ι ∘ z, fun h0 => hz.1 (funext fun i => ι.injective (by simpa using congrFun h0 i)),
        fun g hg => hle hg, fun j => by simpa [map_sum, map_mul] using congrArg ι (hzu j)⟩
    rw [aeval_algebraMap_apply] at h1
    exact ι.injective (h1.trans (map_zero ι).symm)

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LinFormOneZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp Xc)

def GenericFibreIdeal.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P d →
    IsProjPrime (genericIdeal P) ∧
      (genericIdeal P).comap (MvPolynomial.map (Int.castRingHom ℚ)) = IndefiniteRowSideFullHecke.ArithBezout.finIdeal P

def DivSuppHorizontalArithVar.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℤ) (H : Ideal (MRing (PBlk n))),
    IsArithVar P (d + 1) → IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
      H ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) → IsHorizontal H → IsArithVar H d

def IntChowFormExists.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n))), IsArithVar P (e + 1) →
    ∃ (δ : ℕ) (f : MvPolynomial (Fin (e + 1) × Fin n) ℤ), IndefiniteRowSideFullHecke.ArithBezout.IsIntChowForm P e δ f

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChowFormDimLe

theorem coeff_zero_eq_zero_of_mem {F : Type} [Field F] {n : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    (hI : IsProjPrime I) {g : MvPolynomial (Fin n) F} (hg : g ∈ I) : coeff 0 g = 0 := by
  by_contra h
  have h0 := hI.isHomog g hg 0
  rw [homogeneousComponent_zero] at h0
  exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

theorem exists_prime_liesOver {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : ∀ g ∈ I, coeff 0 g = 0) :
    ∃ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime ∧
      P ≤ RingHom.ker (eval (0 : Fin n → K)) ∧
      P.comap (MvPolynomial.map (algebraMap F K)) = I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : Module.Flat (MvPolynomial (Fin n) F) (MvPolynomial (Fin n) K) :=
    Module.Flat.isBaseChange F (MvPolynomial (Fin n) F) K (MvPolynomial (Fin n) K)
      (Algebra.IsPushout.out (R := F) (S := MvPolynomial (Fin n) F) (R' := K)
        (S' := MvPolynomial (Fin n) K))
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K))
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  have hle : I ≤ Q.under (MvPolynomial (Fin n) F) := by
    intro g hg
    rw [Ideal.under, Ideal.mem_comap, MvPolynomial.algebraMap_def, RingHom.mem_ker, eval_map,
      eval₂_zero_apply, constantCoeff_eq, hI g hg, map_zero]
  obtain ⟨P, hPQ, hP, hPI⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  refine ⟨P, hP, hPQ, ?_⟩
  rw [P.over_def I]
  rfl

theorem ringKrullDim_eq_of_comap {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F))
    (P : Ideal (MvPolynomial (Fin n) K)) (hPI : P.comap (MvPolynomial.map (algebraMap F K)) = I) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : P.LiesOver I := ⟨hPI.symm⟩
  exact GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
    (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) F ⧸ I) (MvPolynomial (Fin n) K ⧸ P))

theorem exists_ne_zero_common_zero {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] (hPQ : P ≤ RingHom.ker (eval (0 : Fin n → K)))
    (hdim : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸ P))
    (u : Fin k × Fin n → K) :
    ∃ x : Fin n → K, x ≠ 0 ∧ (∀ g ∈ P, eval x g = 0) ∧ ∀ i, ∑ j, u (i, j) * x j = 0 := by
  classical
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K)) with hQdef
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  let mk := Ideal.Quotient.mk P
  let ℓ : Fin k → MvPolynomial (Fin n) K := fun i => ∑ j, C (u (i, j)) * X j
  have hℓQ : ∀ i, ℓ i ∈ Q := by
    intro i
    simp [Q, ℓ, RingHom.mem_ker]
  set Mb : Ideal (MvPolynomial (Fin n) K ⧸ P) := Q.map mk
  have : Mb.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPQ)
  let s : Finset (MvPolynomial (Fin n) K ⧸ P) := Finset.univ.image (fun i => mk (ℓ i))
  have hsM : Ideal.span (s : Set (MvPolynomial (Fin n) K ⧸ P)) ≤ Mb := by
    rw [Ideal.span_le]
    intro y hy
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact Ideal.mem_map_of_mem _ (hℓQ i)
  obtain ⟨q, hqmin, hqM⟩ := Ideal.exists_minimalPrimes_le hsM
  have : q.IsPrime := hqmin.1.1
  have hqht : q.height ≤ k := by
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hqmin).trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hMht : (Mb.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ P) := by
    have h := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient K Mb
    have hF : IsField ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient Mb).mp inferInstance
    have h0 : ringKrullDim ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) = 0 := by
      have h00 := ringKrullDim_eq_zero_of_isField (F := (MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) hF
      convert h00 using 2
    rwa [h0, add_zero] at h
  have hqne : q ≠ Mb := by
    intro hq
    rw [hq] at hqht
    have h1 : ((Mb.height : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hqht
    rw [hMht] at h1
    exact absurd h1 (not_le.mpr (by exact_mod_cast hdim))
  set Q' := q.comap mk
  have : Q'.IsPrime := Ideal.comap_isPrime mk q
  have hQQ' : ¬ Q ≤ Q' := by
    intro h
    apply hqne
    refine le_antisymm hqM ?_
    calc Mb = Q.map mk := rfl
      _ ≤ Q'.map mk := Ideal.map_mono h
      _ = q := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q
  have hnull := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q'
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ zeroLocus K Q', x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hQQ'
    intro g hg
    rw [← hnull, mem_vanishingIdeal_iff]
    intro x hx
    rw [hcon x hx]
    simpa [Q, RingHom.mem_ker] using hg
  refine ⟨x, hx0, fun g hg => ?_, fun i => ?_⟩
  · have hgQ' : g ∈ Q' := by
      show mk g ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      exact q.zero_mem
    simpa using (mem_zeroLocus_iff.mp hx) g hgQ'
  · have hmem : ℓ i ∈ Q' := by
      show mk (ℓ i) ∈ q
      exact hqmin.1.2 (Ideal.subset_span (by simp [s]))
    simpa [ℓ] using (mem_zeroLocus_iff.mp hx) _ hmem

theorem proof : ChowFormDimLe.Statement := by
  intro F _ n k I f hI hf
  by_contra hdim
  rw [not_le] at hdim
  have := hI.isPrime
  obtain ⟨P, hP, hPQ, hPI⟩ := exists_prime_liesOver (AlgebraicClosure F) I
    (fun g hg => coeff_zero_eq_zero_of_mem hI hg)
  have hdimP : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure F) ⧸ P) := by
    rw [ringKrullDim_eq_of_comap (AlgebraicClosure F) I P hPI]
    exact_mod_cast hdim
  have hall : ∀ u : Fin k × Fin n → AlgebraicClosure F, u ∈ incidence I k := by
    intro u
    obtain ⟨x, hx0, hxP, hxu⟩ := exists_ne_zero_common_zero P hPQ hdimP u
    refine ⟨x, hx0, fun g hg => ?_, hxu⟩
    have hgP : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) g ∈ P := by
      rw [← hPI] at hg
      exact hg
    have := hxP _ hgP
    rwa [eval_map, ← aeval_def] at this
  apply hf.1
  apply map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective
  apply MvPolynomial.funext
  intro u
  rw [eval_map, ← aeval_def, ((hf.2 f).mpr dvd_rfl) u (hall u), map_zero, map_zero]

end ChowFormDimLe

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj ptsIntegralAt pot)

def ConeIntegralChart.Statement : Prop :=
  ∀ (n e : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (P : Ideal (MRing (PBlk n)))
    (u : Fin n → ℂ) (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      IsGoodProj P Ψ →
      coneIntegral (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) e
          (fsLog (ObjectsHeight.ofPointMatrix S hS) u) =
        ptsIntegralAt P Ψ (pot fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
          (IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS u)

end GroundTheory.Heights₂.Heights
end
end

