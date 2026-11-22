import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem exists_mul_transpose_eq_one {F : Type} [Field F] {n N : ℕ} (B : Matrix (Fin n) (Fin N) F)
    (hB : LinearIndependent F B) : ∃ D : Matrix (Fin n) (Fin N) F, D * B.transpose = 1 := by
  have hinj : LinearMap.ker B.transpose.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro v w h
    have h' : B.transpose.mulVec v = B.transpose.mulVec w := h
    rw [Matrix.mulVec_transpose, Matrix.mulVec_transpose] at h'
    exact Matrix.vecMul_injective_iff.2 hB h'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have hl : Matrix.toLin' B.transpose = B.transpose.mulVecLin := rfl
  rw [← LinearMap.toMatrix'_toLin' B.transpose, ← LinearMap.toMatrix'_comp, hl, hg, LinearMap.toMatrix'_id]

section Bundle

variable {K : Type} {ι : K → Type}

theorem projBundleMap_rename_inlV (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (g : MRing ι) :
    projBundleMap P B (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) g) =
      C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P g)) := by
  have key : (projBundleMap P B).comp
      (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom =
      (C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
        ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
    · have hC := RingHom.ext_int
        (((projBundleMap P B).comp
          (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) : MRing ι →ₐ[ℤ] MRing (PBlk ι N1)).toRingHom).comp C)
        (((C : FnField P →+* MvPolynomial (Fin n) (FnField P)).comp
          ((algebraMap (MRing ι ⧸ P) (FnField P)).comp (Ideal.Quotient.mk P))).comp C)
      exact RingHom.congr_fun hC r
    · obtain ⟨k, i⟩ := p
      simp [projBundleMap, inlV, genPt]
  exact RingHom.congr_fun key g

def projBundleAlgHom (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    MRing (PBlk ι N1) →ₐ[ℤ] MvPolynomial (Fin n) (FnField P) :=
  ⟨projBundleMap P B, fun r => by simp⟩

theorem trdeg_projBundle (P : Ideal (MRing ι)) [P.IsPrime] (hPz : IsHorizontal P) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hB : LinearIndependent (FnField P) B) :
    Algebra.trdeg ℤ (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) =
      Algebra.trdeg ℤ (MRing ι ⧸ P) + n := by
  classical
  set F := projBundleAlgHom P B
  have hker : RingHom.ker F = projBundleIdeal P B := rfl
  let e : (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) ≃ₐ[ℤ] F.range :=
    AlgEquiv.ofRingEquiv (f := ((Ideal.quotientEquivAlgOfEq ℤ hker.symm).trans
      (Ideal.quotientKerEquivRange F)).toRingEquiv) fun x => Subtype.ext (by simp)
  rw [AlgEquiv.trdeg_eq (R := ℤ) (A := MRing (PBlk ι N1) ⧸ projBundleIdeal P B) (A' := F.range) e]
  set S := F.range
  have hmemS : ∀ g : MRing ι,
      (C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P g)) : MvPolynomial (Fin n) (FnField P)) ∈ S :=
    fun g => ⟨rename (inlV (ι₂ := fun _ : Unit => Fin N1)) g, projBundleMap_rename_inlV P B g⟩
  have hlin : ∀ j, (∑ a, C (B a j) * X a : MvPolynomial (Fin n) (FnField P)) ∈ S :=
    fun j => ⟨X ⟨Sum.inr (), j⟩, projBundleMap_X_inr P B () j⟩
  have halgS : ∀ x ∈ S, IsAlgebraic S x := fun x hx => isAlgebraic_algebraMap (⟨x, hx⟩ : S)
  have halgC : ∀ φ : FnField P, IsAlgebraic S (C φ : MvPolynomial (Fin n) (FnField P)) := by
    intro φ
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι ⧸ P) φ
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    have hs0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FnField P) hs
    have hC0 : (C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P s)) :
        MvPolynomial (Fin n) (FnField P)) ≠ 0 := by
      rw [Ne, C_eq_zero]
      exact hs0
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hC0) (halgS _ (hmemS s)) ?_
    rw [← C_mul, mul_div_cancel₀ _ hs0]
    exact halgS _ (hmemS a)
  obtain ⟨D, hD⟩ := exists_mul_transpose_eq_one B hB
  have halgX : ∀ b, IsAlgebraic S (X b : MvPolynomial (Fin n) (FnField P)) := by
    intro b
    have h1 : ∀ a, ∑ j, D b j * B a j = if b = a then 1 else 0 := fun a => by
      have := congrFun (congrFun hD b) a
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    have hX : (X b : MvPolynomial (Fin n) (FnField P)) = ∑ j, C (D b j) * ∑ a, C (B a j) * X a := by
      simp_rw [Finset.mul_sum, ← mul_assoc, ← C_mul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, ← map_sum, h1]
      simp
    rw [hX]
    exact (Subalgebra.mem_algebraicClosure S _).1 (Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ ((Subalgebra.mem_algebraicClosure S _).2 (halgC _))
        ((Subalgebra.mem_algebraicClosure S _).2 (halgS _ (hlin j))))
  have hall : ∀ p : MvPolynomial (Fin n) (FnField P), p ∈ Subalgebra.algebraicClosure S _ := fun p =>
    MvPolynomial.induction_on p (fun φ => halgC φ) (fun _ _ hp hq => Subalgebra.add_mem _ hp hq)
      (fun _ b hp => Subalgebra.mul_mem _ hp (halgX b))
  have hAlg : Algebra.IsAlgebraic S (MvPolynomial (Fin n) (FnField P)) := ⟨fun p => hall p⟩

  have hA : Function.Injective (algebraMap ℤ (MRing ι ⧸ P)) := algebraMap_int_injective P hPz
  have hΦ : Function.Injective (algebraMap ℤ (FnField P)) := by
    rw [show algebraMap ℤ (FnField P) = (algebraMap (MRing ι ⧸ P) (FnField P)).comp (algebraMap ℤ _) from
      RingHom.ext_int _ _]
    exact (IsFractionRing.injective (MRing ι ⧸ P) (FnField P)).comp hA
  have hM : Function.Injective (algebraMap ℤ (MvPolynomial (Fin n) (FnField P))) := by
    rw [show algebraMap ℤ (MvPolynomial (Fin n) (FnField P)) = (C : FnField P →+* _).comp (algebraMap ℤ _) from
      RingHom.ext_int _ _]
    exact (C_injective _ _).comp hΦ
  have := (faithfulSMul_iff_algebraMap_injective ℤ (MRing ι ⧸ P)).2 hA
  have := (faithfulSMul_iff_algebraMap_injective (MRing ι ⧸ P) (FnField P)).2
    (IsFractionRing.injective (MRing ι ⧸ P) (FnField P))
  have := (faithfulSMul_iff_algebraMap_injective ℤ (FnField P)).2 hΦ
  have := (faithfulSMul_iff_algebraMap_injective (FnField P) (MvPolynomial (Fin n) (FnField P))).2
    (C_injective _ _)
  have := (faithfulSMul_iff_algebraMap_injective S (MvPolynomial (Fin n) (FnField P))).2 Subtype.val_injective
  have := (faithfulSMul_iff_algebraMap_injective ℤ S).2 fun a b h => hM (by
    rw [IsScalarTower.algebraMap_apply ℤ S (MvPolynomial (Fin n) (FnField P)) a,
      IsScalarTower.algebraMap_apply ℤ S (MvPolynomial (Fin n) (FnField P)) b, h])
  have : Algebra.IsAlgebraic (MRing ι ⧸ P) (FnField P) := IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have e1 := trdeg_add_eq ℤ S (A := MvPolynomial (Fin n) (FnField P))
  have e2 := trdeg_add_eq ℤ (FnField P) (A := MvPolynomial (Fin n) (FnField P))
  have e3 := trdeg_add_eq ℤ (MRing ι ⧸ P) (A := FnField P)
  rw [trdeg_eq_zero (R := S) (A := MvPolynomial (Fin n) (FnField P)), add_zero] at e1
  rw [trdeg_eq_zero (R := MRing ι ⧸ P) (A := FnField P), add_zero] at e3
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fin] at e2
  rw [e1, ← e2, e3]

end Bundle

theorem ProjBundleDim.proof (hInt : IntDomainDim.Statement) : ProjBundleDim.Statement := by
  intro K _ ι _ N1 n P d B hP hB
  obtain ⟨-, ⟨hPr, -, -⟩, hPz, -⟩ := hP
  have hHor : IsHorizontal (projBundleIdeal P B) := by
    ext z
    rw [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h
      have h2 : (C z : MRing ι) ∈ P := (rename_inlV_mem_projBundleIdeal_iff P B (C z)).1 (by simpa using h)
      have h3 : z ∈ P.comap (C : ℤ →+* MRing ι) := h2
      rw [hPz] at h3
      exact h3
    · rintro rfl
      simp
  have hprime : (projBundleIdeal P B).IsPrime := RingHom.ker_isPrime _
  rw [hInt _ (algebraMap_int_injective _ hHor), hInt _ (algebraMap_int_injective P hPz),
    trdeg_projBundle P hPz B hB, map_add, map_natCast]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOver
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Over

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {n : ℕ}

def ptsOver (P' : Ideal (MRing ι')) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (w : ((k : K) → ι k) → ℂ) :
    Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧
    (Ψ (segre fun p => z' (v p)) 0)⁻¹ • segre (fun p => z' (v p)) = w}

end Over

def GenericPointsCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (i : ∀ k : FibreBlock κ, ι' k.1)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsGoodProj (imageZ v P') Ψ → (∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0) →
    ∀ᵐ y : Fin n → ℂ, ∀ w ∈ fibre (imageZ v P') Ψ y,
      (ptsOver P' v Ψ w).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
        (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩))

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PullWMemFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

namespace IntersectionWithSection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem comp_mem_mcPts {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' : Ideal (MRing ι')} {z' : (Σ k', ι' k') → ℂ} (hz : z' ∈ mcPts P') :
    (fun p => z' (v p)) ∈ mcPts (imageZ v P') := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
    obtain ⟨pk, pi⟩ := p
    simp only at h2
    subst h2
    exact ⟨pi, show z' (v ⟨pk, pi⟩) ≠ 0 by rw [hp]; exact hi'⟩
  · have h := hz.2 _ (Ideal.mem_comap.mp hf)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h
    exact h

theorem pullW_mem_fibre {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {P' J' : Ideal (MRing ι')} {n : ℕ} (hP : IsArithVar (imageZ v P') (n + 1)) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x : R.X}
    (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) : pullW R v Ψ x ∈ fibre (imageZ v P') Ψ (pullQ R v Ψ x) := by
  classical
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (pullPt R v x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (pullPt R v x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * pullPt R v x p,
    mcPts_smul hP.2.1.2.1 c hc (comp_mem_mcPts hv (R.mem x x (R.mem_U x))), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [pullW, h0]
    · simp only [pullW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, pullQ]
      rw [div_eq_inv_mul]

end IntersectionWithSection

open IntersectionWithSection in

theorem IntersectionWithSection.proof (hE : ResExistsStatement) (hPush : pullbackPushforward_holds.Statement)
    (hCount : PullbackDegreeCount.Statement) (hDens : pullbackDensity_holds.Statement) : IntersectionWithSection.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G J L L' A A' s hv hP' hP hJ hL hLL' hA hAA' hs
  classical
  have hA' := ArithmeticIntersectionIntegral.isSmoothHerm_pull hv hA hAA'
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j => ArithmeticIntersectionIntegral.isSmoothHerm_pull hv (hL j) (hLL' j)
  have hs' : IsSectionOn P' A' (rename v s) := by
    obtain ⟨a, hAa, hsa, hsP⟩ := hs
    refine ⟨Function.extend κ a 0, fun k' => ?_, ArithmeticIntersectionIntegral.isMultiHomog_rename hv hsa,
      fun h => hsP (Ideal.mem_comap.mpr h)⟩
    rw [hAA'.1, pullDeg]
    by_cases h : ∃ k, κ k = k'
    · obtain ⟨k, rfl⟩ := h
      rw [hv.1.extend_apply, hv.1.extend_apply, hAa k]
    · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  obtain ⟨J', ⟨R⟩⟩ := exists_anLogRes hE hP'
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι (imageZ v P') n hP
  obtain ⟨hnull, hfin⟩ := hPush K ι K' ι' κ v P' J' n R Ψ hv hP' hP hΨ
  rw [ptsIntegral_eq_mInt' hE resBridge R hP' hL' hA' hs', ptsIntegral_eq_at hE resBridge hP hΨ hL hA hs,
    pushForward_null R.A _ (fun j => potOf_isPotential R (L' j) (hL' j)) (pullQ R v Ψ) (pullBad R v Ψ) hnull
      (fun x hx j hj => by
        by_contra h
        exact hx (Or.inr ⟨j, hj, h⟩)) hfin _ (brIntegrable R L' A' (rename v s) hP' hL' hA' hs'),
    ptsIntegralAt, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hCount K ι K' ι' κ v P' J' n G J R Ψ hv hP' hP hJ hΨ,
    hDens K ι K' ι' κ v P' J' n R Ψ L L' A A' s hv hP' hP hΨ hL hLL' hA hAA' hs] with y hc hd
  have hSf := hfin y
  have hFf := fibreFinite K ι (imageZ v P') n Ψ hP hΨ y
  have hmaps : ∀ x ∈ hSf.toFinset, pullW R v Ψ x ∈ hFf.toFinset := by
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    have h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx.2 (Or.inl (Or.inr h))
    have hw := pullW_mem_fibre hv hP R Ψ h0
    rwa [show pullQ R v Ψ x = y from hx.1] at hw
  rw [finsum_mem_eq_finite_toFinset_sum _ hSf, finsum_mem_eq_finite_toFinset_sum _ hFf, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun x hx => hd x ((Set.Finite.mem_toFinset hSf).mp hx)).trans ?_
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hset : ({x | pullQ R v Ψ x = y ∧ pullW R v Ψ x = w} \ pullBad R v Ψ) =
      ↑(hSf.toFinset.filter fun x => pullW R v Ψ x = w) := by
    ext x
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_preimage,
      Set.mem_singleton_iff]
    tauto
  have hcw := hc w ((Set.Finite.mem_toFinset hFf).mp hw)
  rw [hset, Set.ncard_coe_finset] at hcw
  exact_mod_cast hcw

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsBlockRatioAlg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def BlockRatioAlg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    ∀ q c : Σ k', ι' k', q.1 = c.1 → (X c : MRing ι') ∉ P' →
      ∃ (m : ℕ) (A : Fin (m + 1) → MRing ι) (a : K → ℕ), (∀ j, IsMultiHomog (A j) a) ∧
        A (Fin.last m) ∉ imageZ v P' ∧
        ∑ j : Fin (m + 1), rename v (A j) * X q ^ (j : ℕ) * X c ^ (m - j : ℕ) ∈ P'

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreBij
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFFibreBij.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d e : ℕ)
    (G : GenFibre v P') (s : MRing ι'),
    IsBlockMap κ v → IsArithVar P' e → IsArithVar (imageZ v P') d →
    Set.BijOn (fibreOf κ G) {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'}
      (divSupp (fibreIdeal κ G) (baseSubst κ G s))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreMult
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def PFFibreMult.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d e : ℕ)
    (G : GenFibre v P') (s : MRing ι') (W : Ideal (MRing ι')),
    IsBlockMap κ v → IsArithVar P' e → IsArithVar (imageZ v P') d →
    W ∈ divSupp P' s → IsHorizontal W → imageZ v W = imageZ v P' →
    multAt (fibreIdeal κ G ⊔ Ideal.span {baseSubst κ G s}) (fibreOf κ G W) = multAt (P' ⊔ Ideal.span {s}) W

end

end GroundTheory.Heights₂.Heights.Inter
end

