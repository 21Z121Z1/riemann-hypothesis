import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

variable {n d : ℕ}

namespace FibreBound

theorem eval_pullback (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) (P : MvPolynomial (Fin d) ℂ) :
    eval x (pullback A P) = eval (A.mulVec x) P := by
  have h : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [pullback]
    · intro i; simp [pullback, linPoly, Matrix.mulVec, dotProduct]
  exact congrArg (fun f : MvPolynomial (Fin d) ℂ →+* ℂ => f P) h

theorem exists_linear_injOn (T : Finset (Fin n → ℂ)) :
    ∃ c : Fin n → ℂ, Set.InjOn (fun x : Fin n → ℂ => ∑ j, c j * x j) T := by
  classical
  let p : (Fin n → ℂ) → (Fin n → ℂ) → Polynomial ℂ := fun x x' =>
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (x j - x' j)
  have hp : ∀ x x', x ≠ x' → p x x' ≠ 0 := by
    intro x x' hne h
    apply hne
    funext j
    have hc := congrArg (fun q => Polynomial.coeff q (j : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [sub_eq_zero] using hc
    · intro b _ hb; rw [if_neg]; exact fun h => hb (Fin.ext h)
    · simp
  have hev : ∀ x x' (t : ℂ), (p x x').eval t = ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) := by
    intro x x' t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    (((T ×ˢ T).filter (fun z => z.1 ≠ z.2)).biUnion (fun z => (p z.1 z.2).roots.toFinset))
  refine ⟨fun j => t ^ (j : ℕ), ?_⟩
  intro x hx x' hx' hxx'
  by_contra hne
  apply ht
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
  refine ⟨(x, x'), ⟨⟨Finset.mem_coe.mp hx, Finset.mem_coe.mp hx'⟩, hne⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp x x' hne), Polynomial.IsRoot, hev]
  have hs : ∑ j : Fin n, (x j - x' j) * t ^ (j : ℕ) =
      (∑ j : Fin n, t ^ (j : ℕ) * x j) - ∑ j : Fin n, t ^ (j : ℕ) * x' j := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; exact sub_eq_zero.mpr hxx'

theorem exists_monic_aeval_eq_zero (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection J A) (s : MvPolynomial (Fin n) ℂ ⧸ J) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
      (projHom J A).toRingHom.toAlgebra
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ),
      g.Monic ∧ g.natDegree ≤ projDegree J A ∧ Polynomial.aeval s g = 0 := by
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  obtain ⟨f, hfm, hf⟩ := Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) s
  have : IsScalarTower (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J)) := TensorProduct.isScalarTower_left
  have : Module.Free (FractionRing (MvPolynomial (Fin d) ℂ))
      (TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J)) := Module.Free.of_divisionRing _ _
  let t : TensorProduct (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
      (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.TensorProduct.includeRight s
  have hq : minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t ∣
      f.map (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hf,
      map_zero]
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing (MvPolynomial (Fin d) ℂ)) hfm hq
  have hqm : (minpoly (FractionRing (MvPolynomial (Fin d) ℂ)) t).Monic :=
    minpoly.monic (IsIntegral.of_finite _ t)
  rw [hqm.leadingCoeff, Polynomial.C_1, mul_one] at hg
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))) :=
    IsFractionRing.injective _ _
  refine ⟨g, Polynomial.monic_of_injective hinj (hg ▸ hqm), ?_, ?_⟩
  · rw [← Polynomial.natDegree_map_eq_of_injective hinj, hg]
    exact minpoly.natDegree_le t
  · have h1 : TensorProduct.mk (MvPolynomial (Fin d) ℂ) (FractionRing (MvPolynomial (Fin d) ℂ))
        (MvPolynomial (Fin n) ℂ ⧸ J) 1 (Polynomial.aeval s g) = 0 := by
      rw [TensorProduct.mk_apply, ← Algebra.TensorProduct.includeRight_apply,
        ← Polynomial.aeval_algHom_apply,
        ← Polynomial.aeval_map_algebraMap (FractionRing (MvPolynomial (Fin d) ℂ)), hg]
      exact minpoly.aeval _ t
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (MvPolynomial (Fin d) ℂ))
      (TensorProduct.mk _ (FractionRing (MvPolynomial (Fin d) ℂ)) _ 1)).mp h1
    rw [Submonoid.smul_def, Algebra.smul_def] at hc
    refine (mul_eq_zero.mp hc).resolve_left ?_
    intro h0
    apply nonZeroDivisors.coe_ne_zero c
    apply hA.injective
    rw [map_zero]
    exact h0

theorem proof : FibreBound.Statement := by
  intro n d J A hJ _ hA y
  have := hJ
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (projHom J A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.of_finite _ _
  have hbound : ∀ T : Finset (Fin n → ℂ), (↑T : Set (Fin n → ℂ)) ⊆ fibre J A y →
      T.card ≤ projDegree J A := by
    intro T hT
    obtain ⟨c, hc⟩ := exists_linear_injOn T
    obtain ⟨g, hgm, hgd, hg⟩ :=
      exists_monic_aeval_eq_zero J A hA (Ideal.Quotient.mk J (∑ j, C (c j) * X j))
    have hgy : (g.map (MvPolynomial.eval y)).Monic := hgm.map _
    have hroot : ∀ x ∈ T, (∑ j, c j * x j) ∈ (g.map (MvPolynomial.eval y)).roots.toFinset := by
      intro x hx
      obtain ⟨hxJ, hxA⟩ := hT (Finset.mem_coe.mpr hx)
      let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ :=
        Ideal.Quotient.lift J (eval x) (fun q hq => hxJ q hq)
      have hev : ev.comp (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)) =
          MvPolynomial.eval y := by
        refine RingHom.ext fun P => ?_
        change ev (Ideal.Quotient.mk J (pullback A P)) = _
        rw [Ideal.Quotient.lift_mk, eval_pullback, hxA]
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hgy.ne_zero, Polynomial.IsRoot.def,
        Polynomial.eval_map]
      have h := congrArg ev hg
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hev, map_zero] at h
      have hs : ev (Ideal.Quotient.mk J (∑ j, C (c j) * X j)) = ∑ j, c j * x j := by
        change eval x (∑ j, C (c j) * X j) = _
        simp
      rw [hs] at h
      exact h
    calc T.card = (T.image fun x => ∑ j, c j * x j).card := (Finset.card_image_of_injOn hc).symm
      _ ≤ (g.map (MvPolynomial.eval y)).roots.toFinset.card := Finset.card_le_card (by
          intro v hv
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
          exact hroot x hx)
      _ ≤ Multiset.card (g.map (MvPolynomial.eval y)).roots := Multiset.toFinset_card_le _
      _ ≤ (g.map (MvPolynomial.eval y)).natDegree := Polynomial.card_roots' _
      _ = g.natDegree := hgm.natDegree_map _
      _ ≤ projDegree J A := hgd
  have hne : (fibre J A y).Nonempty := by
    have hmax : (RingHom.ker (MvPolynomial.eval y)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, eval_C _⟩)
    obtain ⟨Q, hQ, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := MvPolynomial (Fin n) ℂ ⧸ J) (RingHom.ker (MvPolynomial.eval y)) (by
        intro P hP
        have hP0 : P = 0 := hA.injective (by rw [map_zero]; exact hP)
        rw [hP0]; exact Ideal.zero_mem _)
    have := hQ
    have hQ' : (Q.comap (Ideal.Quotient.mk J)).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hQ'
    have hmem : ∀ q, Ideal.Quotient.mk J q ∈ Q → eval x q = 0 := by
      intro q hq
      have hq' : q ∈ Q.comap (Ideal.Quotient.mk J) := hq
      rw [hx] at hq'
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq'
    refine ⟨x, fun q hq => hmem q (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq]; exact Q.zero_mem), ?_⟩
    funext i
    have h1 : X i - C (y i) ∈ RingHom.ker (MvPolynomial.eval y) := by simp [RingHom.mem_ker]
    rw [← hQc] at h1
    have h2 := hmem (pullback A (X i - C (y i))) h1
    rw [eval_pullback] at h2
    simpa [sub_eq_zero] using h2
  have hfin : (fibre J A y).Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (projDegree J A + 1)
    have := hbound T hT
    omega
  refine ⟨hne, hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact hbound _ (by simp)

end FibreBound

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreRadical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem map_inf_eq_of_sup_inf_ker_le {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (I J : Ideal R)
    (h : (I ⊔ J) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (I ⊔ J)) :
    (I ⊓ J).map φ = I.map φ ⊓ J.map φ := by
  refine le_antisymm (Ideal.map_inf_le φ) ?_
  rintro y ⟨hyI, hyJ⟩
  obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hyI
  obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hyJ
  have hmem : a - b ∈ (I ⊔ J) ⊓ RingHom.ker φ :=
    ⟨Ideal.sub_mem _ (Ideal.mem_sup_left ha) (Ideal.mem_sup_right hb),
      RingHom.mem_ker.2 (by rw [map_sub, hab, sub_self])⟩
  have h2 : a - b ∈ RingHom.ker φ * I ⊔ RingHom.ker φ * J := by
    rw [← Ideal.mul_sup]; exact h hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h2
  have hu' : u ∈ RingHom.ker φ ⊓ I := Ideal.mul_le_inf hu
  have hv' : v ∈ RingHom.ker φ ⊓ J := Ideal.mul_le_inf hv
  refine (Ideal.mem_map_iff_of_surjective φ hφ).2 ⟨a - u, ⟨Ideal.sub_mem _ ha hu'.2, ?_⟩, ?_⟩
  · have e : a - u = b + v := by linear_combination -huv
    rw [e]
    exact Ideal.add_mem _ hb hv'.2
  · rw [map_sub, RingHom.mem_ker.1 hu'.1, sub_zero]

theorem GenericFibreRadical.proof (hT : GenericFibreTor.Statement)
    (hP : GenericFibreRadicalPrime.Statement) : GenericFibreRadical.Statement := by
  intro σ _ ι _ K hK
  have hsurj : ∀ t : σ → ℂ, Function.Surjective
      (MvPolynomial.map (eval t) : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) :=
    fun t => MvPolynomial.map_surjective _ (fun c => ⟨C c, eval_C c⟩)
  classical
  have key : ∀ s : Finset (Ideal (MvPolynomial ι (MvPolynomial σ ℂ))), (∀ p ∈ s, p.IsPrime) →
      ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
        ((s.inf id).map (MvPolynomial.map (eval t))).IsRadical := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨1, one_ne_zero, fun t _ => ?_⟩
      rw [Finset.inf_empty, Ideal.map_top]
      exact fun _ _ => Submodule.mem_top
    | insert p s hps ih =>
      intro hs
      obtain ⟨F₁, hF₁, h₁⟩ := ih (fun q hq => hs q (Finset.mem_insert_of_mem hq))
      obtain ⟨F₂, hF₂, h₂⟩ := hP σ ι p (hs p (Finset.mem_insert_self p s))
      obtain ⟨F₃, hF₃, h₃⟩ := hT σ ι (p ⊔ s.inf id)
      refine ⟨F₁ * F₂ * F₃, mul_ne_zero (mul_ne_zero hF₁ hF₂) hF₃, fun t ht => ?_⟩
      simp only [map_mul, ne_eq, mul_eq_zero, not_or] at ht
      obtain ⟨⟨ht₁, ht₂⟩, ht₃⟩ := ht
      rw [Finset.inf_insert, id, map_inf_eq_of_sup_inf_ker_le _ (hsurj t) _ _ (h₃ t ht₃)]
      exact (h₂ t ht₂).inf (h₁ t ht₁)
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing _ K
  obtain ⟨F, hF, hFt⟩ := key hfin.toFinset (fun p hp => ((hfin.mem_toFinset).1 hp).1.1)
  refine ⟨F, hF, fun t ht => ?_⟩
  have hK' : K = hfin.toFinset.inf id := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset, Ideal.sInf_minimalPrimes]
    exact le_antisymm Ideal.le_radical hK
  rw [hK']
  exact hFt t ht

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFibreTor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem GenericFibreTor.mem_of_smul_mem {σ ι : Type*} (t : σ → ℂ)
    (L : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) {x : MvPolynomial ι (MvPolynomial σ ℂ)} (hx : x ∈ L)
    {u : MvPolynomial σ ℂ} (hu : eval t u ≠ 0)
    (h : u • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L) :
    x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
  set J := (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L
  rw [smul_eq_C_mul] at h
  have h1 : C (u - MvPolynomial.C (eval t u)) * x ∈ J :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])) hx
  have h2 : C (MvPolynomial.C (eval t u)) * x ∈ J := by
    have := J.sub_mem h h1
    rwa [← sub_mul, ← map_sub, sub_sub_cancel] at this
  have hunit : IsUnit (C (MvPolynomial.C (eval t u)) : MvPolynomial ι (MvPolynomial σ ℂ)) :=
    (hu.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial σ ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ))
  exact (Ideal.unit_mul_mem_iff_mem J hunit).1 h2

theorem GenericFibreTor.proof (hGF : GenericFreeness.Statement.{0, 0, 0}) :
    GenericFibreTor.Statement := by
  classical
  intro σ _ ι _ L
  obtain ⟨F, hF0, hfree⟩ := hGF (MvPolynomial σ ℂ) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
    (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  refine ⟨F, hF0, fun t ht x hx => ?_⟩
  rw [MvPolynomial.ker_map] at hx ⊢
  obtain ⟨hxL, hxI⟩ := Ideal.mem_inf.1 hx
  rw [MvPolynomial.mem_map_C_iff] at hxI
  have hflat' : Module.Flat (Localization.Away F)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    @Module.Flat.of_free _ _ _ _ _ hfree
  have hflatS : Module.Flat (MvPolynomial σ ℂ) (Localization.Away F) := IsLocalization.flat _ (Submonoid.powers F)
  have : Module.Flat (MvPolynomial σ ℂ)
      (LocalizedModule (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)) :=
    Module.Flat.trans (MvPolynomial σ ℂ) (Localization.Away F) _
  let g := LocalizedModule.mkLinearMap (Submonoid.powers F) (MvPolynomial ι (MvPolynomial σ ℂ) ⧸ L)
  let π := (Ideal.Quotient.mkₐ (MvPolynomial σ ℂ) L).toLinearMap
  let a : x.support → MvPolynomial σ ℂ := fun m => coeff m.1 x
  let e : x.support → MvPolynomial ι (MvPolynomial σ ℂ) := fun m => monomial m.1 1
  have hsum : ∑ m, a m • e m = x := by
    calc ∑ m, a m • e m = ∑ m : x.support, monomial m.1 (coeff m.1 x) :=
          Finset.sum_congr rfl fun m _ => by simp [a, e, smul_monomial]
      _ = x := by
          rw [Finset.sum_coe_sort x.support (fun v => monomial v (coeff v x))]
          exact (MvPolynomial.as_sum x).symm
  have hrel : ∑ m, a m • g (π (e m)) = 0 := by
    simp_rw [← map_smul, ← map_sum, hsum]
    simp [g, π, Ideal.Quotient.eq_zero_iff_mem.2 hxL]
  have htriv : Module.IsTrivialRelation a (fun m => g (π (e m))) :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  obtain ⟨k, A, y, hy, hA⟩ := htriv
  obtain ⟨b, hb⟩ := IsLocalizedModule.exist_integer_multiples_of_finite (Submonoid.powers F) g y
  choose q hq using hb
  choose r hr using fun j => Ideal.Quotient.mk_surjective (q j)
  have hm : ∀ m, ∃ c : Submonoid.powers F,
      c • π ((b : MvPolynomial σ ℂ) • e m) = c • π (∑ j, A m j • r j) := by
    intro m
    apply IsLocalizedModule.exists_of_eq (S := Submonoid.powers F) (f := g)
    rw [map_smul, map_smul, show g (π (e m)) = ∑ j, A m j • y j from hy m, Finset.smul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm, ← hq j, ← hr j, map_smul, map_smul]
    rfl
  choose c hc using hm
  set V : MvPolynomial σ ℂ := ∏ m, (c m : MvPolynomial σ ℂ)
  have hD : ∀ m, (V * b) • e m - ∑ j, (V * A m j) • r j ∈ L := by
    intro m
    have h1 := hc m
    rw [← sub_eq_zero, ← smul_sub, ← map_sub, Submonoid.smul_def, ← map_smul] at h1
    have h2 : (c m : MvPolynomial σ ℂ) • ((b : MvPolynomial σ ℂ) • e m - ∑ j, A m j • r j) ∈ L :=
      Ideal.Quotient.eq_zero_iff_mem.1 h1
    have h3 := Submodule.smul_of_tower_mem L (∏ m' ∈ Finset.univ.erase m, (c m' : MvPolynomial σ ℂ)) h2
    convert h3 using 1
    rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ m), smul_sub, smul_smul,
      Finset.smul_sum]
    simp_rw [smul_smul]
    rfl
  have hzero : ∑ m, a m • ∑ j, (V * A m j) • r j = 0 := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul]
    have : ∑ m, a m * (V * A m j) = V * ∑ m, a m * A m j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; ring
    rw [this, hA j, mul_zero, zero_smul]
  have hkey : (V * b) • x = ∑ m, a m • ((V * b) • e m - ∑ j, (V * A m j) • r j) := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, hzero, sub_zero, ← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm]
  have hJ : (V * b) • x ∈ (RingHom.ker (eval t : MvPolynomial σ ℂ →+* ℂ)).map
      (C : MvPolynomial σ ℂ →+* MvPolynomial ι (MvPolynomial σ ℂ)) * L := by
    rw [hkey]
    refine Ideal.sum_mem _ fun m _ => ?_
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hxI m.1)) (hD m)
  have hpow : ∀ u ∈ Submonoid.powers F, eval t u ≠ 0 := by
    rintro u ⟨n, rfl⟩
    rw [map_pow]
    exact pow_ne_zero n ht
  have hVb : V * b ∈ Submonoid.powers F :=
    (Submonoid.powers F).mul_mem (Submonoid.prod_mem _ fun m _ => (c m).2) b.2
  exact GenericFibreTor.mem_of_smul_mem t L hxL (hpow _ hVb) hJ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericFreeness
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

universe u v w

namespace GenericFreeness

theorem isGenericallyFree_of_primes {A : Type u} [CommRing A] [IsDomain A] {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Algebra A R] (hq : ∀ p : PrimeSpectrum R, IsGenericallyFree A (R ⧸ p.asIdeal))
    (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M] [Module.Finite R M] :
    IsGenericallyFree A M := by
  refine IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R (M := M) inferInstance
    (motive := fun N _ _ _ ↦ ∀ (_ : Module A N) (_ : IsScalarTower A R N), IsGenericallyFree A N)
    ?_ ?_ ?_ ‹Module A M› ‹IsScalarTower A R M›
  · intro N _ _ _ _ _ _
    exact ⟨1, one_ne_zero, inferInstance⟩
  · intro N _ _ _ p e _ _
    exact (hq p).of_linearEquiv (e.restrictScalars A).symm
  · intro N₁ _ _ _ N₂ _ _ _ N₃ _ _ _ f g hf hg hfg h₁ h₃ _ _
    letI : Module A N₁ := Module.compHom N₁ (algebraMap A R)
    letI : Module A N₃ := Module.compHom N₃ (algebraMap A R)
    have t₁ : IsScalarTower A R N₁ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    have t₃ : IsScalarTower A R N₃ := ⟨fun a r n ↦ by
      show (a • r) • n = algebraMap A R a • r • n
      rw [Algebra.smul_def, mul_smul]⟩
    exact IsGenericallyFree.of_exact (f.restrictScalars A) (g.restrictScalars A) hf hg hfg
      (h₁ inferInstance t₁) (h₃ inferInstance t₃)

theorem isGenericallyFree_of_comap_ne_bot {A : Type u} [CommRing A] {σ : Type*} (q : Ideal (MvPolynomial σ A))
    (h : q.comap (C : A →+* MvPolynomial σ A) ≠ ⊥) : IsGenericallyFree A (MvPolynomial σ A ⧸ q) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine isGenericallyFree_of_smul_eq_zero a ha0 fun d ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have e : a • Ideal.Quotient.mk q x = Ideal.Quotient.mk q (a • x) :=
    (map_smul (Ideal.Quotient.mkₐ A q) a x).symm
  rw [e, Ideal.Quotient.eq_zero_iff_mem, smul_eq_C_mul]
  exact q.mul_mem_right x ha

theorem isGenericallyFree_quotient_bot {A : Type u} [CommRing A] [IsDomain A] (σ : Type*) :
    IsGenericallyFree A (MvPolynomial σ A ⧸ (⊥ : Ideal (MvPolynomial σ A))) :=
  (isGenericallyFree_of_free (M := MvPolynomial σ A)).of_linearEquiv
    (AlgEquiv.quotientBot A (MvPolynomial σ A)).toLinearEquiv.symm

theorem isGenericallyFree_quotient (hNN : GenericNoetherNormalisation.Statement.{u}) (n : ℕ) :
    ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (q : Ideal (MvPolynomial (Fin n) A)),
      q.IsPrime → IsGenericallyFree A (MvPolynomial (Fin n) A ⧸ q) := by
  induction n with
  | zero =>
    intro A _ _ _ q _
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin 0) A) = ⊥
    · have hq : q = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have hx' : C (coeff 0 x) ∈ q := by rwa [← eq_C_of_isEmpty x]
        have : coeff 0 x ∈ q.comap (C : A →+* MvPolynomial (Fin 0) A) := hx'
        rw [hc, Ideal.mem_bot] at this
        rw [Ideal.mem_bot, eq_C_of_isEmpty x, this, map_zero]
      subst hq
      exact isGenericallyFree_quotient_bot _
    · exact isGenericallyFree_of_comap_ne_bot q hc
  | succ n ih =>
    intro A _ _ _ q hqp
    by_cases hc : q.comap (C : A →+* MvPolynomial (Fin (n + 1)) A) = ⊥
    · by_cases hq : q = ⊥
      · subst hq
        exact isGenericallyFree_quotient_bot _
      obtain ⟨a, ha, z, s, hspan⟩ := hNN A n q hqp hq hc
      let D := MvPolynomial (Fin (n + 1)) A ⧸ q
      let Rn := MvPolynomial (Fin n) A
      letI : Algebra Rn D := (aeval z : Rn →ₐ[A] D).toRingHom.toAlgebra
      have : IsScalarTower A Rn D := IsScalarTower.of_algebraMap_eq fun x ↦ ((aeval z).commutes x).symm
      let N : Submodule Rn D := Submodule.span Rn (s : Set D)
      have hN : IsGenericallyFree A N :=
        isGenericallyFree_of_primes (R := Rn) (fun p ↦ ih A p.asIdeal p.isPrime) N
      refine hN.of_injective (N.subtype.restrictScalars A) Subtype.val_injective a ha fun d ↦ ?_
      obtain ⟨k, c, hk⟩ := hspan d
      refine ⟨k, ⟨⟨a ^ k • d, ?_⟩, rfl⟩⟩
      rw [hk]
      exact Submodule.sum_mem _ fun t ht ↦ Submodule.smul_mem _ (c t) (Submodule.subset_span ht)
    · exact isGenericallyFree_of_comap_ne_bot q hc

end GenericFreeness

theorem GenericFreeness.proof (hNN : GenericNoetherNormalisation.Statement.{u}) :
    GenericFreeness.Statement.{u, v, w} := by
  intro A _ _ _ B _ _ _ M _ _ _ _ _
  obtain ⟨n, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType A B›
  letI : Algebra (MvPolynomial (Fin n) A) B := g.toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin n) A) M := Module.compHom M (algebraMap (MvPolynomial (Fin n) A) B)
  have : IsScalarTower (MvPolynomial (Fin n) A) B M := ⟨fun x b m ↦ by
    show (g x * b) • m = g x • b • m
    rw [mul_smul]⟩
  have : IsScalarTower A (MvPolynomial (Fin n) A) M := ⟨fun a x m ↦ by
    show g (a • x) • m = a • g x • m
    rw [map_smul, smul_assoc]⟩
  have : Module.Finite (MvPolynomial (Fin n) A) B := RingHom.Finite.of_surjective g.toRingHom hg
  have : Module.Finite (MvPolynomial (Fin n) A) M := Module.Finite.trans B M
  exact GenericFreeness.isGenericallyFree_of_primes (R := MvPolynomial (Fin n) A)
    (fun p ↦ GenericFreeness.isGenericallyFree_quotient hNN n A p.asIdeal p.isPrime) M

end GroundTheory.Heights₂.Heights
end

