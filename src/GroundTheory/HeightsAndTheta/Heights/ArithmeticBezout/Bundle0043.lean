import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0118
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSheetParam
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Filter Topology Set
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj IsSheet fibre segre mcPts
  IsMultiHomogIdeal mcPts_smul)

section OneBlock

variable {n : ℕ}

theorem segre_pblk_apply (z : (Σ k, PBlk n k) → ℂ) (i : (k : Unit) → PBlk n k) :
    segre z i = z ⟨(), i ()⟩ := by
  simp [segre]

theorem segre_pblk_injective : Function.Injective (segre : ((Σ k, PBlk n k) → ℂ) → _) := by
  intro z z' h
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  have := congrFun h fun _ => i
  simpa [segre_pblk_apply] using this

theorem segre_pblk_smul (t : ℂ) (z : (Σ k, PBlk n k) → ℂ) :
    segre (fun p => t * z p) = t • segre z := by
  funext i
  simp [segre_pblk_apply]

theorem eval_map_rename_pblk (z' : (Σ k, PBlk n k) → ℂ) (g : MvPolynomial (Fin n) ℤ) :
    eval z' (map (Int.castRingHom ℂ) (rename (fun i : Fin n => (⟨(), i⟩ : Σ k, PBlk n k)) g)) =
      eval (fun i => z' ⟨(), i⟩) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]
  rfl

theorem eval_complexFibreIdeal_of_forall {P : Ideal (MRing (PBlk n))} {z' : (Σ k, PBlk n k) → ℂ}
    (hz : ∀ f ∈ P, eval z' (map (Int.castRingHom ℂ) f) = 0) :
    ∀ q ∈ complexFibreIdeal P, eval (fun i => z' ⟨(), i⟩) q = 0 := by
  intro q hq
  have hle : complexFibreIdeal P ≤ RingHom.ker (eval fun i => z' ⟨(), i⟩) := by
    unfold complexFibreIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, ← eval_map_rename_pblk]
    exact hz _ hg
  exact hle hq

theorem forall_eval_of_complexFibreIdeal {P : Ideal (MRing (PBlk n))} {z : Fin n → ℂ}
    (hz : ∀ q ∈ complexFibreIdeal P, eval z q = 0) :
    ∀ f ∈ P, eval (fun p : Σ k, PBlk n k => z p.2) (map (Int.castRingHom ℂ) f) = 0 := by
  intro f hf
  have hre : rename (fun i : Fin n => (⟨(), i⟩ : Σ k, PBlk n k))
      (rename (fun p : Σ k, PBlk n k => p.2) f) = f := by
    rw [rename_rename]
    exact rename_id_apply f
  have hg : rename (fun p : Σ k, PBlk n k => p.2) f ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
    rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, hre]
    exact hf
  have h := hz _ (Ideal.mem_map_of_mem (MvPolynomial.map (Int.castRingHom ℂ)) hg)
  rw [← hre, eval_map_rename_pblk]
  exact h

end OneBlock

theorem ConeSheetParam.proof (hCov : ConeSheetCover.Statement)
    (hHyp : ConeProjHyperplaneNull.Statement) : ConeSheetParam.Statement := by
  classical
  intro n e S hS P Ψ hP hΨ
  obtain ⟨U, D, N, s, hUD, hdisj, hnull, hfib, hrest⟩ := hCov n e P Ψ hP hΨ
  have hhyp := hHyp n e P Ψ hP hΨ
  have hMH : IsMultiHomogIdeal P := hP.2.1.2.1
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS

  have hval : ∀ k j x, x ∈ U k → Ψ (segre (s k j x)) = Fin.cons 1 x ∧ s k j x ∈ mcPts P := by
    intro k j x hx
    have h2 := (((hfib k x hx).2.2 j).1).2.self_of_nhds
    exact ⟨h2.2.2, h2.2.1⟩

  have hpt : ∀ (t : ℂ) (v : Fin n → ℂ),
      (ObjectsHeight.ofPointMatrix S hS).pointOf (t • WithLp.toLp 2 (S *ᵥ v)) = t • v := by
    intro t v
    simp only [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose]
    change S⁻¹ *ᵥ (t • (S *ᵥ v)) = t • v
    rw [mulVec_smul, mulVec_mulVec, nonsing_inv_mul S hdet, one_mulVec]
  refine ⟨U, D, N, s, hUD, hdisj, hnull, hfib, ?_, ?_, ?_⟩
  ·
    rintro ⟨⟨k, j⟩, x, t⟩ ⟨hx, ht⟩ ⟨⟨k', j'⟩, x', t'⟩ ⟨hx', ht'⟩ heq
    simp only at hx ht hx' ht' heq
    have hv := congrArg (ObjectsHeight.ofPointMatrix S hS).pointOf heq
    rw [hpt, hpt] at hv
    have hz : (fun p : Σ k, PBlk n k => t * s k j x p) = fun p => t' * s k' j' x' p := by
      funext p
      obtain ⟨⟨⟩, i⟩ := p
      exact congrFun hv i
    have hΨz := congrArg (fun z => Ψ (segre z)) hz
    simp only [segre_pblk_smul, map_smul, (hval k j x ((hUD k).2.2.1 hx)).1,
      (hval k' j' x' ((hUD k').2.2.1 hx')).1] at hΨz
    have htt : t = t' := by simpa using congrFun hΨz 0
    subst htt
    have hxx : x = x' := by
      funext i
      have := congrFun hΨz i.succ
      simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul] at this
      exact mul_left_cancel₀ ht this
    subst hxx
    have hss : s k j x = s k' j' x := by
      funext p
      exact mul_left_cancel₀ ht (congrFun hz p)
    have hkk : k = k' := by
      by_contra hk
      exact Set.disjoint_left.1 (hdisj hk) hx hx'
    subst hkk
    have hjj : j = j' := (hfib k x ((hUD k).2.2.1 hx)).2.1 (congrArg segre hss)
    subst hjj
    rfl
  ·
    rintro y ⟨⟨⟨k, j⟩, x, t⟩, ⟨hx, ht⟩, rfl⟩
    simp only at hx ht
    intro q hq
    rw [hpt]
    have hm : (fun p : Σ k, PBlk n k => t * s k j x p) ∈ mcPts P :=
      mcPts_smul hMH (fun _ => t) (fun _ => ht) (hval k j x ((hUD k).2.2.1 hx)).2
    exact eval_complexFibreIdeal_of_forall hm.2 q hq
  ·
    set F := fun q : (Σ k, Fin (N k)) × (Fin e → ℂ) × ℂ =>
      q.2.2 • WithLp.toLp 2 (S *ᵥ fun i => s q.1.1 q.1.2 q.2.1 ⟨(), i⟩) with hF
    let Lₗ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
      { toFun := fun z => WithLp.toLp 2 (S *ᵥ fun i => z i)
        map_add' := by
          intro a b
          change WithLp.toLp 2 (S *ᵥ (fun i => a i + b i)) = _
          rw [show (fun i => a i + b i) = (fun i => a i) + fun i => b i from rfl, mulVec_add]
          rfl
        map_smul' := by
          intro c a
          change WithLp.toLp 2 (S *ᵥ (c • fun i => a i)) = _
          rw [mulVec_smul]
          rfl }
    let L := LinearMap.toContinuousLinearMap Lₗ
    set A1 := {z : EuclideanSpace ℂ (Fin n) |
      (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
        Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0} with hA1
    set A2 := {z : EuclideanSpace ℂ (Fin n) |
      (∀ q ∈ complexFibreIdeal P, eval (fun i => z i) q = 0) ∧
        Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 ≠ 0 ∧
        (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ •
            Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∉ ⋃ k, D k} with hA2
    have hsub : coneSet (ObjectsHeight.ofPointMatrix S hS) (complexFibreIdeal P) \ F ''
        {q | q.2.1 ∈ D q.1.1 ∧ q.2.2 ≠ 0} ⊆ L '' (A1 ∪ A2) := by
      rintro y ⟨hyC, hyF⟩
      set z : Fin n → ℂ := S⁻¹ *ᵥ fun i => y i with hz
      have hyz : y = L (WithLp.toLp 2 z) := by
        change y = WithLp.toLp 2 (S *ᵥ (S⁻¹ *ᵥ fun i => y i))
        rw [mulVec_mulVec, mul_nonsing_inv S hdet, one_mulVec]
      have hzC : ∀ q ∈ complexFibreIdeal P, eval z q = 0 := by
        intro q hq
        have := hyC q hq
        simpa [HermNorm.pointOf, ObjectsHeight.ofPointMatrix, transpose_transpose] using this
      refine ⟨WithLp.toLp 2 z, ?_, hyz.symm⟩
      by_cases h0 : Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 = 0
      · exact Or.inl ⟨hzC, h0⟩
      by_cases hxD : (Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0)⁻¹ •
          Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) ∈ ⋃ k, D k
      swap
      · exact Or.inr ⟨hzC, h0, hxD⟩
      exfalso
      apply hyF

      have hzm : (fun p : Σ k, PBlk n k => z p.2) ∈ mcPts P := by
        refine ⟨fun _ => ?_, forall_eval_of_complexFibreIdeal hzC⟩
        by_contra hne
        push Not at hne
        apply h0
        have : (fun p : Σ k, PBlk n k => z p.2) = 0 := by
          funext p
          obtain ⟨⟨⟩, i⟩ := p
          exact hne i
        rw [this]
        have hs0 : segre (0 : (Σ k, PBlk n k) → ℂ) = 0 := by
          funext i
          simp [segre_pblk_apply]
        rw [hs0, map_zero]
        rfl
      set t := Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 with ht
      set x := t⁻¹ • Fin.tail (Ψ (segre fun p : Σ k, PBlk n k => z p.2)) with hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 hxD

      have hwm : (fun p : Σ k, PBlk n k => t⁻¹ * z p.2) ∈ mcPts P :=
        mcPts_smul hMH (fun _ => t⁻¹) (fun _ => inv_ne_zero h0) hzm
      have hwΨ : Ψ (segre fun p : Σ k, PBlk n k => t⁻¹ * z p.2) = Fin.cons 1 x := by
        rw [segre_pblk_smul, map_smul]
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Pi.smul_apply, Fin.cons_zero, smul_eq_mul]
          exact inv_mul_cancel₀ h0
        · simp only [Pi.smul_apply, Fin.cons_succ, smul_eq_mul, hx, Fin.tail]
      have hwf : segre (fun p : Σ k, PBlk n k => t⁻¹ * z p.2) ∈ fibre P Ψ x :=
        ⟨_, hwm, rfl, hwΨ⟩
      rw [(hfib k x ((hUD k).2.2.1 hk)).1] at hwf
      obtain ⟨j, hj⟩ := hwf
      have hsj : s k j x = fun p : Σ k, PBlk n k => t⁻¹ * z p.2 := segre_pblk_injective hj
      refine ⟨⟨⟨k, j⟩, x, t⟩, ⟨hk, h0⟩, ?_⟩
      rw [hyz]
      simp only [hF, hsj]
      change t • WithLp.toLp 2 (S *ᵥ (t⁻¹ • z)) = WithLp.toLp 2 (S *ᵥ z)
      rw [mulVec_smul, WithLp.toLp_smul, smul_smul, mul_inv_cancel₀ h0, one_smul]
    have hA : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (A1 ∪ A2) = 0 :=
      measure_union_null hhyp hrest
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ zero_le
    calc Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (L '' (A1 ∪ A2))
        ≤ (‖L‖₊ : ENNReal) ^ (((2 * (e + 1) : ℕ) : ℝ)) *
            Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (A1 ∪ A2) :=
          L.lipschitz.hausdorffMeasure_image_le (Nat.cast_nonneg _) _
      _ = 0 := by rw [hA, mul_zero]

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PObjectsVertPartEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial NumberField VerticalPartMultiplicity
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk)

theorem finsum_finset_sum_comm {α β : Type*} (T : Finset α) (g : β → α → ℝ)
    (h : ∀ a ∈ T, (Function.support fun b => g b a).Finite) :
    ∑ᶠ b, ∑ a ∈ T, g b a = ∑ a ∈ T, ∑ᶠ b, g b a := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have h' : ∀ a' ∈ T, (Function.support fun b => g b a').Finite :=
      fun a' h'' => h a' (Finset.mem_insert_of_mem h'')
    simp_rw [Finset.sum_insert ha]
    rw [finsum_add_distrib (h a (Finset.mem_insert_self _ _)), ih h']
    refine (T.finite_toSet.biUnion fun a' h'' => h' a' h'').subset ?_
    intro b hb
    obtain ⟨a', ha', hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    exact Set.mem_biUnion ha' hne

theorem isMultiHomog_linearForm {n : ℕ} (u : Fin n → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Xc, C_mul_X_eq_monomial] at hi
  have hm' := MvPolynomial.support_monomial_subset hi
  rw [Finset.mem_singleton] at hm'
  subst hm'
  cases k
  simp [Finsupp.single_apply]

theorem C_charOf_mem {n : ℕ} (W : Ideal (MRing (PBlk n))) :
    (C ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) : MRing (PBlk n)) ∈ W := by
  have hg := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing (PBlk n)))
  obtain ⟨c, hc⟩ : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing (PBlk n))) ∣
      ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have : ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing (PBlk n)) := by
    rw [hc]
    exact Ideal.mul_mem_right _ _ hg
  exact this

theorem VertPartEq.proof (hCD : ChowDegreeGeoNum.Statement) : VertPartEq.Statement := by
  classical
  intro n e P u hP hu
  have hPp : P.IsPrime := hP.2.1.1
  have hPh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal P := hP.2.2.1
  haveI := hPp
  have hJ : integralModel (genericIdeal P) ⊔ Ideal.span {linForm (fun j => ((u j : ℤ) : 𝓞 ℚ))} =
      (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}).map
        (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)) := by
    rw [integralModel_genericIdeal P hPh, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
      RingEquiv.coe_toRingHom, Ψ_linForm]
  have hinj : Function.Injective
      (Ideal.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) := by
    intro W₁ W₂ h
    rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv] at h
    exact Ideal.comap_injective_of_surjective _ (Ψ n).symm.surjective h
  set D := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).toFinset with hD
  have hDmem : ∀ W, W ∈ D ↔ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) :=
    fun W => Set.Finite.mem_toFinset _
  have hvert : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
      vertComps (genericIdeal P) (fun j => ((u j : ℤ) : 𝓞 ℚ)) v =
        Ideal.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)) ''
          ↑(D.filter fun W => (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
            (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) = v.asIdeal) := by
    intro v
    ext W'
    simp only [vertComps, relComps, hJ, Set.mem_setOf_eq, minimalPrimes_map_equiv, Set.mem_image,
      Finset.coe_filter, hDmem, ReciprocityTheory.ChartRestriction.G.Geo.divSupp]
    constructor
    · rintro ⟨⟨⟨W, hW, rfl⟩, hrel⟩, hv⟩
      exact ⟨W, ⟨⟨hW, (isRelevant_map_iff W).mp hrel⟩, hv⟩, rfl⟩
    · rintro ⟨W, ⟨⟨hW, hrel⟩, hv⟩, rfl⟩
      exact ⟨⟨⟨W, hW, rfl⟩, (isRelevant_map_iff W).mpr hrel⟩, hv⟩
  let G : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) → Ideal (MRing (PBlk n)) → ℝ := fun v W =>
    if (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) = v.asIdeal then
      (localMult ((P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}).map
          (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)))
          (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) : ℝ) *
        chowDegree (reduceMod v (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))))
          (e + 1) * Real.log (Ideal.absNorm v.asIdeal)
    else 0
  have hLv : ∀ v, vertTermAt (genericIdeal P) (e + 1) (fun j => ((u j : ℤ) : 𝓞 ℚ)) v =
      ∑ W ∈ D, G v W := by
    intro v
    rw [vertTermAt, hJ, hvert v, finsum_mem_image hinj.injOn, finsum_mem_coe_finset,
      Finset.sum_filter]
  have hfin : ∀ W ∈ D, (Function.support fun v => G v W).Finite := by
    intro W _
    refine Set.Subsingleton.finite (s := {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) |
      v.asIdeal = (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ))}) ?_ |>.subset ?_
    · intro v₁ h₁ v₂ h₂
      exact IsDedekindDomain.HeightOneSpectrum.ext (h₁.trans h₂.symm)
    · intro v hv
      rw [Function.mem_support] at hv
      by_contra hne
      exact hv (if_neg fun h => hne h.symm)
  have hL : vertTerm (genericIdeal P) (e + 1) (fun j => ((u j : ℤ) : 𝓞 ℚ)) =
      ∑ W ∈ D, ∑ᶠ v, G v W := by
    rw [vertTerm]
    simp_rw [hLv]
    exact finsum_finset_sum_comm D G hfin
  have hR : IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u) =
      ∑ W ∈ D, (ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
        (if ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W then 0 else
          (ReciprocityTheory.ChartRestriction.G.Geo.geoNum e W (fun _ _ => 1) : ℝ) *
            Real.log (ReciprocityTheory.ChartRestriction.G.Geo.charOf W)) := by
    rw [IndefiniteRowSideFullHecke.ArithBezout.vertPart, ← finsum_mem_coe_finset, hD, Set.Finite.coe_toFinset]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun W hW => ?_
  have hWd := (hDmem W).mp hW
  have hsec : ReciprocityTheory.ChartRestriction.G.Geo.IsSectionOn P (ReciprocityTheory.ChartRestriction.G.Geo.fsLine n)
      (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := ⟨fun _ => 1, fun _ => rfl, isMultiHomog_linearForm u, hu⟩
  have hWp : W.IsPrime := hWd.1.1.1
  haveI := hWp
  by_cases hor : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W
  · have h0 := (isHorizontal_iff W).mp hor
    rw [if_pos hor, mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun v => if_neg fun h => v.ne_bot ?_
    rw [← h, h0]
  · obtain ⟨hmpp, hcp, hdim⟩ := (ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith Unit (PBlk n) P e
      (ReciprocityTheory.ChartRestriction.G.Geo.fsLine n) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) W hP hsec hWd).2 hor
    rw [Fintype.card_unit] at hdim
    rw [if_neg hor]
    haveI hWΨ : (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).IsPrime :=
      Ideal.map_isPrime_of_equiv _
    set 𝔭 := (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
      (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) with h𝔭
    have h𝔭ne : 𝔭 ≠ ⊥ := fun h => hor ((isHorizontal_iff W).mpr h)
    let v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) := ⟨𝔭, Ideal.comap_isPrime _ _, h𝔭ne⟩
    rw [finsum_eq_single (fun v => G v W) v₀ fun v hv =>
      if_neg fun h => hv (IsDedekindDomain.HeightOneSpectrum.ext h.symm)]
    simp only [G]
    rw [if_pos rfl]
    haveI : v₀.asIdeal.IsMaximal := v₀.isMaximal
    set F := v₀.asIdeal.ResidueField
    have hsurj : Function.Surjective (Int.castRingHom F) := by
      have h1 : Function.Surjective (algebraMap (𝓞 ℚ) F) := by
        rw [IsScalarTower.algebraMap_eq (𝓞 ℚ) (𝓞 ℚ ⧸ v₀.asIdeal) F, RingHom.coe_comp]
        exact (Ideal.bijective_algebraMap_quotient_residueField v₀.asIdeal).2.comp
          Ideal.Quotient.mk_surjective
      intro x
      obtain ⟨y, rfl⟩ := h1 x
      refine ⟨ι.symm y, ?_⟩
      have : (algebraMap (𝓞 ℚ) F).comp (ι : ℤ →+* 𝓞 ℚ) = Int.castRingHom F := RingHom.ext_int _ _
      rw [← this, RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
    have hp0 : (((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) : F) = 0 := by
      have hmem : (ι ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ) : 𝓞 ℚ) ∈ v₀.asIdeal := by
        show _ ∈ 𝔭
        rw [h𝔭, Ideal.mem_comap, ← Ψ_C]
        exact Ideal.mem_map_of_mem _ (C_charOf_mem W)
      have : (algebraMap (𝓞 ℚ) F) (ι ((ReciprocityTheory.ChartRestriction.G.Geo.charOf W : ℕ) : ℤ)) = 0 :=
        Ideal.algebraMap_residueField_eq_zero.mpr hmem
      rwa [ι_apply, map_intCast] at this
    have hcd := hCD n e (ReciprocityTheory.ChartRestriction.G.Geo.charOf W) W F hcp hmpp (C_charOf_mem W) hdim hsurj hp0
    have hred : reduceMod v₀ (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
        (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map (MvPolynomial.map (Int.castRingHom F)) :=
      reduceMod_map v₀ W
    have hnorm : Ideal.absNorm v₀.asIdeal = ReciprocityTheory.ChartRestriction.G.Geo.charOf W := by
      show Ideal.absNorm 𝔭 = _
      rw [h𝔭, comap_C_map, absNorm_map_comap_C]
    rw [hred, hnorm, localMult_map_eq_multAt]
    have hcdR : ((chowDegree ((IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map
        (MvPolynomial.map (Int.castRingHom F))) (e + 1) : ℕ) : ℝ) =
        ((ReciprocityTheory.ChartRestriction.G.Geo.geoNum e W (fun _ _ => 1) : ℤ) : ℝ) := by
      rw [← hcd]
      norm_cast
    rw [hcdR]
    ring

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPrimePairMeetImage
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem PrimePairMeetImage.projHom_not_injective (hF : FiniteFibresDimLe.Statement) {n d : ℕ}
    {Q Q' P : Ideal (MvPolynomial (Fin n) ℂ)} (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hQ' : Q'.IsPrime) (hne : Q ≠ Q') (hfin : ∀ y, (ComplexSets.fibre Q A y).Finite)
    (hfin' : ∀ y, (ComplexSets.fibre Q' A y).Finite) (hP : P.IsPrime) (hle : Q ⊔ Q' ≤ P) :
    ¬ Function.Injective (ComplexSets.projHom P A) := by
  intro hinj
  obtain ⟨R, hR, hRfin, hlt⟩ :
      ∃ R : Ideal (MvPolynomial (Fin n) ℂ), R.IsPrime ∧ (∀ y, (ComplexSets.fibre R A y).Finite) ∧ R < P := by
    by_cases h : Q = P
    · refine ⟨Q', hQ', hfin', lt_of_le_of_ne (le_sup_right.trans hle) ?_⟩
      intro h'
      exact hne (h.trans h'.symm)
    · exact ⟨Q, hQ, hfin, lt_of_le_of_ne (le_sup_left.trans hle) h⟩

  have hlow : ((d : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := by
    have h := ImageDimLe.proof n d P (ComplexSets.linPoly A) hP
    have hker : RingHom.ker ((Ideal.Quotient.mkₐ ℂ P).comp (aeval (ComplexSets.linPoly A))) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 hinj
    rw [hker, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    simpa using h

  have hup := hF n d R A hR hRfin
  have hdrop := Order.coheight_add_one_le (a := (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)))
    (b := ⟨R, hR⟩) hlt
  rw [ringKrullDim_quotient_eq_coheight] at hlow hup
  have h1 : ((d : ℕ) : ℕ∞) ≤ Order.coheight (⟨P, hP⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)) := by
    exact_mod_cast hlow
  have h2 : Order.coheight (⟨R, hR⟩ : PrimeSpectrum (MvPolynomial (Fin n) ℂ)) ≤ ((d : ℕ) : ℕ∞) := by
    exact_mod_cast hup
  have h3 := (add_le_add h1 (le_refl (1 : ℕ∞))).trans (hdrop.trans h2)
  exact lt_irrefl _ ((ENat.add_one_le_iff (ENat.natCast_ne_top d)).1 h3)

theorem PrimePairMeetImage.proof (hF : FiniteFibresDimLe.Statement) : PrimePairMeetImage.Statement := by
  classical
  intro n d Q Q' A hQ hQ' hne hfin hfin'
  have hker : ∀ P ∈ (Q ⊔ Q').minimalPrimes,
      ∃ e : MvPolynomial (Fin d) ℂ, e ≠ 0 ∧ ComplexSets.pullback A e ∈ P := by
    intro P hPm
    have hni := PrimePairMeetImage.projHom_not_injective hF A hQ hQ' hne hfin hfin' hPm.1.1 hPm.1.2
    rw [injective_iff_map_eq_zero] at hni
    obtain ⟨e, he0, hne0⟩ : ∃ e, ComplexSets.projHom P A e = 0 ∧ e ≠ 0 := by
      by_contra hc
      exact hni fun e he => by_contra fun h => hc ⟨e, he, h⟩
    exact ⟨e, hne0, Ideal.Quotient.eq_zero_iff_mem.1 he0⟩
  choose! f hf0 hfP using hker
  have hfs := Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) (Q ⊔ Q')
  refine ⟨∏ P ∈ hfs.toFinset, f P,
    Finset.prod_ne_zero_iff.2 fun P hP => hf0 P (hfs.mem_toFinset.1 hP), ?_⟩
  rintro x ⟨hx, hx'⟩
  have hmx : Q ⊔ Q' ≤ RingHom.ker (eval x) :=
    sup_le (fun q hq => RingHom.mem_ker.2 (hx q hq)) (fun q hq => RingHom.mem_ker.2 (hx' q hq))
  have : (RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hmx
  have hPs : P ∈ hfs.toFinset := hfs.mem_toFinset.2 hP
  have hmem : ComplexSets.pullback A (∏ P ∈ hfs.toFinset, f P) ∈ P := by
    rw [← Finset.prod_erase_mul _ _ hPs, map_mul]
    exact P.mul_mem_left _ (hfP P hP)
  rw [← ComplexSets.eval_pullback]
  exact RingHom.mem_ker.1 (hPle hmem)

end GroundTheory.Heights₂.Heights
end
end

