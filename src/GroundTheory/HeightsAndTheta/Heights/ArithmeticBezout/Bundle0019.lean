import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0013
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.SmoothOfRegular
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace PointLine

variable {n : ℕ}

def pairing (y : Fin n → ℂ) : MvPolynomial (Fin 1 × Fin n) ℂ :=
  ∑ j, C (y j) * X ((0 : Fin 1), j)

theorem eval_pairing (y : Fin n → ℂ) (u : Fin 1 × Fin n → ℂ) :
    eval u (pairing y) = ∑ j, y j * u (0, j) := by
  simp [pairing]

theorem coeff_pairing (y : Fin n → ℂ) (j : Fin n) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (pairing y) = y j := by
  classical
  simp [pairing, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_eq_single_iff]

theorem exists_ne_zero {y : Fin n → ℂ} (hy : y ≠ 0) : ∃ a, y a ≠ 0 := by
  by_contra h
  push Not at h
  exact hy (funext h)

theorem eval_smul_of_isHomogeneous {φ : MvPolynomial (Fin n) ℂ} {m : ℕ} (hφ : φ.IsHomogeneous m)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ m * eval x φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem smul_mem_zeroSet {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W)
    {x : Fin n → ℂ} (hx : ∀ q ∈ W, eval x q = 0) (t : ℂ) : ∀ q ∈ W, eval (t • x) q = 0 := by
  intro q hq
  rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

theorem pairing_dvd_of_vanish {y : Fin n → ℂ} (hy : y ≠ 0) (f : MvPolynomial (Fin 1 × Fin n) ℂ)
    (hf : ∀ u, eval u (pairing y) = 0 → eval u f = 0) : pairing y ∣ f := by
  obtain ⟨a, ha⟩ := exists_ne_zero hy
  set ℓ := pairing y with hℓ
  let c : Fin 1 × Fin n → ℂ := Pi.single ((0 : Fin 1), a) (y a)⁻¹
  let s : Fin 1 × Fin n → MvPolynomial (Fin 1 × Fin n) ℂ := fun ij => X ij - C (c ij) * ℓ
  have hsum : ∀ L : ℂ, ∑ j, y j * c (0, j) * L = L := by
    intro L
    rw [← Finset.sum_mul]
    have : ∑ j, y j * c (0, j) = y a * (y a)⁻¹ := by
      rw [Finset.sum_eq_single a]
      · simp [c]
      · intro j _ hj
        simp [c, hj]
      · simp
    rw [this, mul_inv_cancel₀ ha, one_mul]
  have hs0 : bind₁ s f = 0 := by
    apply MvPolynomial.funext
    intro u
    rw [map_zero]
    have he : eval u (bind₁ s f) = eval (fun ij => eval u (s ij)) f := by
      simp only [eval, eval₂Hom_bind₁]
    rw [he]
    apply hf
    rw [eval_pairing]
    simp only [s, map_sub, map_mul, eval_X, eval_C, mul_sub, Finset.sum_sub_distrib]
    have h2 : ∀ j, y j * (c (0, j) * eval u ℓ) = y j * c (0, j) * eval u ℓ := fun j => by ring
    simp only [h2, hsum]
    rw [hℓ, eval_pairing, sub_self]
  have hmem : f - bind₁ s f ∈ Ideal.span {ℓ} := by
    have hcomp : (Ideal.Quotient.mkₐ ℂ (Ideal.span {ℓ})).comp (bind₁ s) =
        Ideal.Quotient.mkₐ ℂ (Ideal.span {ℓ}) := by
      apply MvPolynomial.algHom_ext
      intro ij
      simp only [AlgHom.comp_apply, bind₁_X_right, s, Ideal.Quotient.mkₐ_eq_mk, map_sub, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ℓ), mul_zero, sub_zero]
    have h := DFunLike.congr_fun hcomp f
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
    exact Ideal.Quotient.eq.mp h.symm
  rw [hs0, sub_zero, Ideal.mem_span_singleton] at hmem
  exact hmem

theorem irreducible_pairing {y : Fin n → ℂ} (hy : y ≠ 0) : Irreducible (pairing y) := by
  obtain ⟨a, ha⟩ := exists_ne_zero hy
  have hne : pairing y ≠ 0 := fun h => ha (by rw [← coeff_pairing y a, h, coeff_zero])
  have hhom : (pairing y).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _
  refine irreducible_of_totalDegree_eq_one (hhom.totalDegree hne) fun c hc => ?_
  have h := hc (Finsupp.single ((0 : Fin 1), a) 1)
  rw [coeff_pairing] at h
  exact isUnit_iff_ne_zero.mpr (by rintro rfl; exact ha (zero_dvd_iff.mp h))

theorem eq_smul_of_associated {x y : Fin n → ℂ} (h : Associated (pairing y) (pairing x)) :
    ∃ t : ℂ, x = t • y := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, -, hc⟩ := (isUnit_iff_eq_C_of_isReduced).mp u.isUnit
  refine ⟨c, funext fun j => ?_⟩
  have h := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) hu
  rw [hc, mul_comm, coeff_C_mul, coeff_pairing, coeff_pairing] at h
  rw [← h, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem chowForm_vanish {W : Ideal (MvPolynomial (Fin n) ℂ)} {g : MvPolynomial (Fin 1 × Fin n) ℂ}
    (hg : IsChowForm W 1 g) {y : Fin n → ℂ} (hy0 : y ≠ 0) (hy : ∀ q ∈ W, eval y q = 0)
    (u : Fin 1 × Fin n → ℂ) (hu : eval u (pairing y) = 0) : eval u g = 0 := by
  set φ := algebraMap ℂ (AlgebraicClosure ℂ) with hφ
  have hu' : ∑ j, u (0, j) * y j = 0 := by
    rw [eval_pairing] at hu
    simpa [mul_comm] using hu
  have hinc : (φ ∘ u) ∈ incidence W 1 := by
    refine ⟨φ ∘ y, ?_, ?_, ?_⟩
    · intro h
      apply hy0
      funext j
      have := congrFun h j
      simpa using this
    · intro q hq
      rw [aeval_algebraMap_apply]
      simp [hy q hq]
    · intro i
      obtain rfl := Subsingleton.elim i 0
      simp only [Function.comp_apply, ← map_mul, ← map_sum, hu', map_zero]
  have h := (hg.2 g).mpr dvd_rfl _ hinc
  rw [aeval_algebraMap_apply] at h
  simpa using h

end PointLine

open PointLine in

theorem PointLine.proof : PointLine.Statement := by
  classical
  intro n W g hW hg
  have := hW.isPrime
  set V : Set (Fin n → ℂ) := {x | ∀ q ∈ W, eval x q = 0} with hV
  have hNS : ∀ q, q ∈ W ↔ ∀ x ∈ V, eval x q = 0 := by
    intro q
    rw [← SetLike.ext_iff.mp (MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) W) q,
      mem_vanishingIdeal_iff]
    have hae : ∀ (x : Fin n → ℂ) (p : MvPolynomial (Fin n) ℂ), aeval x p = eval x p := fun _ _ => rfl
    simp only [mem_zeroLocus_iff, hae, hV, Set.mem_ofPred_eq]
  have hcone : ∀ x ∈ V, ∀ t : ℂ, t • x ∈ V := fun x hx t => smul_mem_zeroSet hW.isHomog hx t
  have hdvd : ∀ x ∈ V, x ≠ 0 → pairing x ∣ g := fun x hx hx0 =>
    pairing_dvd_of_vanish hx0 g (chowForm_vanish hg hx0 hx)
  have hrel : ∀ S : Set (Fin n → ℂ), vanishingIdeal ℂ S ≤ W → ∃ y ∈ S, y ≠ 0 := by
    intro S hS
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hW.isRelevant
    refine hj (hS ?_)
    rw [mem_vanishingIdeal_iff]
    intro x hx
    simp [h x hx]
  obtain ⟨y₀, hy₀, hy₀0⟩ := hrel V (fun q hq => (hNS q).mpr fun x hx => by
    simpa using (mem_vanishingIdeal_iff.mp hq) x hx)
  let T := (UniqueFactorizationMonoid.factors g).toFinset
  let S : MvPolynomial (Fin 1 × Fin n) ℂ → Set (Fin n → ℂ) :=
    fun p => {x | x ∈ V ∧ (x = 0 ∨ Associated (pairing x) p)}
  have hcover : ∏ p ∈ T, vanishingIdeal ℂ (S p) ≤ W := by
    intro q hq
    rw [hNS]
    intro x hx
    obtain ⟨p, hpT, hxp⟩ : ∃ p ∈ T, x ∈ S p := by
      by_cases hx0 : x = 0
      · obtain ⟨p, hp, -⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hg.1
          (irreducible_pairing hy₀0) (hdvd y₀ hy₀ hy₀0)
        exact ⟨p, Multiset.mem_toFinset.mpr hp, hx, Or.inl hx0⟩
      · obtain ⟨p, hp, hxp⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hg.1
          (irreducible_pairing hx0) (hdvd x hx hx0)
        exact ⟨p, Multiset.mem_toFinset.mpr hp, hx, Or.inr hxp⟩
    have hq' : q ∈ vanishingIdeal ℂ (S p) := (Ideal.prod_le_inf.trans (Finset.inf_le hpT)) hq
    simpa using (mem_vanishingIdeal_iff.mp hq') x hxp
  obtain ⟨p, -, hpW⟩ := (Ideal.IsPrime.prod_le hW.isPrime).mp hcover
  obtain ⟨y, ⟨hyV, hyp⟩, hy0⟩ := hrel (S p) hpW
  have hyp' : Associated (pairing y) p := hyp.resolve_left hy0
  have hline : ∀ q, q ∈ W ↔ ∀ t : ℂ, eval (t • y) q = 0 := by
    intro q
    refine ⟨fun hq t => hcone y hyV t q hq, fun hq => hpW ?_⟩
    rw [mem_vanishingIdeal_iff]
    rintro x ⟨-, hx⟩
    rcases hx with rfl | hx
    · simpa using hq 0
    · obtain ⟨t, rfl⟩ := eq_smul_of_associated (hyp'.trans hx.symm)
      simpa using hq t
  refine ⟨y, hy0, fun x => ⟨fun hx => ?_, ?_⟩, hline⟩
  · obtain ⟨a, ha⟩ := exists_ne_zero hy0
    refine ⟨x a / y a, funext fun b => ?_⟩
    have hmem : C (y a) * X b - C (y b) * X a ∈ W := (hline _).mpr fun t => by
      simp only [map_sub, map_mul, eval_C, eval_X, Pi.smul_apply, smul_eq_mul]
      ring
    have h := hx _ hmem
    simp only [map_sub, map_mul, eval_C, eval_X] at h
    rw [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h
  · rintro ⟨t, rfl⟩
    exact hcone y hyV t

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGenerators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module IsLocalRing

noncomputable section

theorem PolyLocalGenerators.proof : PolyLocalGenerators.Statement := by
  intro n m J hJ hdim p hp htan
  classical

  have H := exists_polyDiff_basis J p
  rw [htan] at H
  obtain ⟨q, hqJ, hli, hspan⟩ := H
  have hqp : ∀ i, eval p (q i) = 0 := fun i => hp _ (hqJ i)
  have htq : polyTangent (Set.range q) p = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p := by
    refine polyTangent_eq_of_subset _ _ p (by rintro _ ⟨i, rfl⟩; exact hqJ i) fun f hf => ?_
    have := hspan f hf
    rwa [Set.range_comp] at this

  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval p) with hMdef
  have hevsurj : Function.Surjective (eval p : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    fun c => ⟨C c, by simp⟩
  have hMmax : M.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevsurj
  have : J.IsPrime := hJ
  let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ := Ideal.Quotient.lift J (eval p) (fun x hx => hp x hx)
  set N : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := RingHom.ker ev with hNdef
  have hevsurj' : Function.Surjective ev :=
    fun c => ⟨Ideal.Quotient.mk J (C c), by simp [ev]⟩
  have hNmax : N.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevsurj'
  have hNM : N.comap (Ideal.Quotient.mk J) = M := by
    ext x
    simp only [Ideal.mem_comap, hNdef, hMdef, RingHom.mem_ker, ev, Ideal.Quotient.lift_mk]

  let P := Localization.AtPrime M
  let S := Localization.AtPrime N
  let ψ : P →+* S := Localization.localRingHom M N (Ideal.Quotient.mk J) hNM.symm
  let _ : Algebra P S := ψ.toAlgebra
  have halg : ∀ x, algebraMap P S x = ψ x := fun _ => rfl
  have hψmk : ∀ x, ψ (algebraMap (MvPolynomial (Fin n) ℂ) P x) =
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S (Ideal.Quotient.mk J x) :=
    fun x => Localization.localRingHom_to_map M N (Ideal.Quotient.mk J) hNM.symm x
  have hsurj : Function.Surjective (algebraMap P S) := by
    intro z
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq N.primeCompl z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin n) ℂ ⧸ J)
    have hyM : y ∈ M.primeCompl := by
      intro hyM'
      have hyN : y ∈ N.comap (Ideal.Quotient.mk J) := by rw [hNM]; exact hyM'
      apply t.2
      rw [← hy]
      exact hyN
    refine ⟨IsLocalization.mk' P x ⟨y, hyM⟩, ?_⟩
    rw [halg, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hy

  have hdimS : ringKrullDim S = m := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height N S,
      NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) N hNmax, hdim]

  let f : Fin (n - m) → P := fun i => algebraMap (MvPolynomial (Fin n) ℂ) P (q i)
  have hf : ∀ i, f i ∈ RingHom.ker (algebraMap P S) := by
    intro i
    rw [RingHom.mem_ker, halg, hψmk, Ideal.Quotient.eq_zero_iff_mem.2 (hqJ i), map_zero]
  have hmP : maximalIdeal P = M.map (algebraMap (MvPolynomial (Fin n) ℂ) P) :=
    (Localization.AtPrime.map_eq_maximalIdeal (I := M)).symm

  have hJcov : J ≤ Ideal.span (Set.range q) ⊔ M ^ 2 := fun x hx =>
    mem_span_sup_sq_of_polyDiff_mem p q hqp (hp x hx) (hspan x hx)
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range (polyDiff p ∘ q)))
  have hfinD : finrank ℂ (Submodule.span ℂ (Set.range (polyDiff p ∘ q))) = n - m := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hmn : m ≤ n := by
    rw [← htan]
    exact (Submodule.finrank_le _).trans (Module.finrank_fin_fun ℂ).le
  have hfinC : finrank ℂ Cc = m := by
    have := Submodule.finrank_add_eq_of_isCompl hCc
    rw [hfinD, Module.finrank_fin_fun] at this
    omega
  let c := Module.finBasisOfFinrankEq ℂ Cc hfinC
  let y : Fin m → MvPolynomial (Fin n) ℂ := fun k => tanLinPoly p (c k)
  have hMcov : M ≤ Ideal.span (Set.range (Sum.elim q y)) ⊔ M ^ 2 := by
    intro x hx
    refine mem_span_sup_sq_of_polyDiff_mem p (Sum.elim q y) ?_ (RingHom.mem_ker.1 hx) ?_
    · rintro (i | k)
      · exact hqp i
      · exact eval_tanLinPoly p _
    · have htop : Submodule.span ℂ (Set.range (polyDiff p ∘ Sum.elim q y)) = ⊤ := by
        rw [eq_top_iff, ← hCc.sup_eq_top]
        apply sup_le
        · apply Submodule.span_mono
          rintro _ ⟨i, rfl⟩
          exact ⟨Sum.inl i, rfl⟩
        · intro v hv
          have hCspan : Cc = Submodule.span ℂ (Set.range (Cc.subtype ∘ c)) := by
            rw [Set.range_comp, Submodule.span_image, c.span_eq, Submodule.map_subtype_top]
          rw [hCspan] at hv
          refine Submodule.span_mono ?_ hv
          rintro _ ⟨k, rfl⟩
          exact ⟨Sum.inr k, by simp [y, polyDiff_tanLinPoly]⟩
      rw [htop]
      exact Submodule.mem_top

  let φ : MvPolynomial (Fin n) ℂ →+* S :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S).comp (Ideal.Quotient.mk J)
  have hmS : maximalIdeal S = M.map φ := by
    calc maximalIdeal S = N.map (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S) :=
          (Localization.AtPrime.map_eq_maximalIdeal (I := N)).symm
      _ = (M.map (Ideal.Quotient.mk J)).map (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S) := by
          rw [← hNM, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
      _ = M.map φ := Ideal.map_map _ _
  have hφq : ∀ i, φ (q i) = 0 := by
    intro i
    simp [φ, Ideal.Quotient.eq_zero_iff_mem.2 (hqJ i)]
  have hS_le : maximalIdeal S ≤ Ideal.span (Set.range (φ ∘ y)) := by
    refine maximalIdeal_le_span_of_le_sup_sq (R := S) (Set.range (φ ∘ y)) ?_
    rw [hmS]
    have h1 := Ideal.map_mono (f := φ) hMcov
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow] at h1
    refine h1.trans (sup_le_sup ?_ ?_)
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨_, ⟨i | k, rfl⟩, rfl⟩
      · simp [hφq]
      · exact Ideal.subset_span ⟨k, rfl⟩
    · exact le_rfl
  have hμ : (maximalIdeal S).spanFinrank ≤ m := by
    have heq : maximalIdeal S = Ideal.span (Set.range (φ ∘ y)) := by
      refine le_antisymm hS_le (Ideal.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, hmS]
      exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (eval_tanLinPoly p _))
    rw [heq]
    calc (Ideal.span (Set.range (φ ∘ y))).spanFinrank ≤ (Set.range (φ ∘ y)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ (Set.univ : Set (Fin m)).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ = m := by simp [Set.ncard_univ]

  have hcov : RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2 := by
    intro z hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M.primeCompl z
    have hx0 : algebraMap P S (algebraMap (MvPolynomial (Fin n) ℂ) P x) = 0 := by
      rw [← IsLocalization.mk'_spec P x s, map_mul, RingHom.mem_ker.1 hz, zero_mul]
    rw [halg, hψmk] at hx0
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff N.primeCompl S _).1 hx0
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin n) ℂ ⧸ J)
    have hwx : w * x ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw, ht]
    have hwJ : w ∉ J := by
      intro hwJ
      apply t.2
      rw [← hw, Ideal.Quotient.eq_zero_iff_mem.2 hwJ]
      exact zero_mem _
    have hxJ : x ∈ J := (hJ.mem_or_mem hwx).resolve_left hwJ
    have hx' : algebraMap (MvPolynomial (Fin n) ℂ) P x ∈
        Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2 := by
      have h1 := Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) ℂ) P) (hJcov hxJ)
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, ← hmP, ← Set.range_comp] at h1
      exact h1
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hx'

  have hker := GroundTheory.Arith.Jacobian.ker_le_span_of_spanFinrank_le (P := P) (S := S) hsurj f hf hcov
    m hμ hdimS.ge

  have hloc : ∀ x ∈ J, ∃ s ∈ M.primeCompl, s * x ∈ Ideal.span (Set.range q) := by
    intro x hx
    have hx1 : algebraMap (MvPolynomial (Fin n) ℂ) P x ∈ Ideal.span (Set.range f) := by
      apply hker
      rw [RingHom.mem_ker, halg, hψmk, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    have hspanf : Ideal.span (Set.range f) =
        (Ideal.span (Set.range q)).map (algebraMap (MvPolynomial (Fin n) ℂ) P) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [hspanf] at hx1
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff M.primeCompl P).1 hx1
    rw [← map_mul, IsLocalization.eq_iff_exists M.primeCompl P] at e
    obtain ⟨c', hc'⟩ := e
    refine ⟨c' * s, M.primeCompl.mul_mem c'.2 hs, ?_⟩
    have e2 : (c' : MvPolynomial (Fin n) ℂ) * s * x = c' * a := by
      rw [← hc']
      ring
    rw [e2]
    exact Ideal.mul_mem_left _ _ ha
  choose! σ hσM hσ using hloc
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing J
  have hsJ : ∀ x ∈ s, x ∈ J := fun x hx => by
    rw [← hs]
    exact Submodule.subset_span hx
  refine ⟨q, ∏ x ∈ s, σ x, hqJ, ?_, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun x hx h0 => ?_
    exact hσM x (hsJ x hx) (RingHom.mem_ker.2 h0)
  · rw [htq, htan]
  · intro r hr
    have hle : J ≤ Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin n) ℂ) (∏ x ∈ s, σ x))
        (Ideal.span (Set.range q)) := by
      rw [← hs]
      refine Submodule.span_le.2 fun x hx => ?_
      have hxJ := hsJ x hx
      show (∏ x ∈ s, σ x) * x ∈ Ideal.span (Set.range q)
      rw [← Finset.mul_prod_erase s σ hx,
        show σ x * (∏ y ∈ s.erase x, σ y) * x = (∏ y ∈ s.erase x, σ y) * (σ x * x) by ring]
      exact Ideal.mul_mem_left _ _ (hσ x hxJ)
    exact hle hr

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem specFirstVar_isWeightedHomogeneous {k n : ℕ} (u : Fin n → ℂ) (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    have h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0 := by
      funext i
      simp [groupWeight, Fin.succ_ne_zero i]
    rw [h0]
    simpa [specFirstVar] using isWeightedHomogeneous_C (groupWeight k n) (u j)
  | succ i' =>
    have h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j) := by
      funext i
      simp [groupWeight, Pi.single_apply]
    rw [h1]
    simpa [specFirstVar] using isWeightedHomogeneous_X ℂ (groupWeight k n) (i', j)

theorem SpecFirstHomog.proof : SpecFirstHomog.Statement := by
  intro n k δ f u hf
  unfold IsMultiHomog specFirst
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous u ij).pow _

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSupportCycleSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem mem_support_cycleSection_iff {n : ℕ} (Z : ProjCycle ℂ n) (u : Fin n → ℂ)
    (W' : Ideal (MvPolynomial (Fin n) ℂ)) :
    W' ∈ (cycleSection Z u).support ↔ ∃ W ∈ Z.support, W' ∈ (divCycle W u).support := by
  simp only [Finsupp.mem_support_iff, cycleSection, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, ne_eq, Finset.sum_eq_zero_iff, not_forall, mul_eq_zero, not_or, exists_prop]
  constructor <;> rintro ⟨W, h⟩ <;> exact ⟨W, by tauto⟩

theorem SupportCycleSection.proof : SupportCycleSection.Statement := by
  intro n Z u
  refine ⟨fun W hW W' hW' => (mem_support_cycleSection_iff Z u W').mpr ⟨W, hW, hW'⟩,
    fun W' hW' => (mem_support_cycleSection_iff Z u W').mp hW'⟩

end GroundTheory.Heights₂.Heights
end

