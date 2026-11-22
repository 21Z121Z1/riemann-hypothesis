import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0092
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0078
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0049
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0091

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubmodules
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubmodules

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_of_weighted {q : MRingOver S ι} {c : K → ℤ}
    (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) :
    IsMultiHomog q (fun k => (c k).toNat) := by
  by_cases h0 : q = 0
  · intro m hm
    simp [h0] at hm
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    refine (QuotPartGraded.isMultiHomog_iff q _).2 ?_
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rw [hcc]
    exact hq

theorem smul_mem_of_weighted {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    {c e : K → ℤ} (hq : IsWeightedHomogeneous (QuotPartGraded.blockWeight ι) q c) {m : M} (hm : m ∈ 𝓜 e) :
    q • m ∈ 𝓜 (e + c) := by
  by_cases h0 : q = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · have hc := QuotPartGraded.nonneg_of_isWeightedHomogeneous hq h0
    have h := hM.2 _ e q m (isMultiHomog_of_weighted hq) hm
    have hcc : (fun k => (((c k).toNat : ℕ) : ℤ)) = c := funext fun k => Int.toNat_of_nonneg (hc k)
    rwa [hcc] at h

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical in

theorem component_smul_eq_zero {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜)
    {f : MRingOver S ι} (hf : f ∈ Module.annihilator (MRingOver S ι) M) (i : K → ℤ) {e : K → ℤ} {m : M}
    (hm : m ∈ 𝓜 e) :
    ((DirectSum.decompose (weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)) f i :
      MRingOver S ι)) • m = 0 := by
  set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
  set s := (DirectSum.decompose 𝒜 f).support
  have hsum : ∑ c ∈ s, ((DirectSum.decompose 𝒜 f c : MRingOver S ι)) • m = 0 := by
    rw [← Finset.sum_smul, DirectSum.sum_support_decompose 𝒜 f]
    exact Module.mem_annihilator.1 hf m
  obtain ⟨g, hg⟩ : ∃ g : (K → ℤ) → MRingOver S ι, ∀ c, g c = (DirectSum.decompose 𝒜 f c : MRingOver S ι) :=
    ⟨_, fun _ => rfl⟩
  have hgm : ∀ c, g c ∈ 𝒜 c := fun c => (hg c).symm ▸ (DirectSum.decompose 𝒜 f c).2
  simp only [← hg] at hsum
  suffices h : g i • m = 0 by rw [hg] at h; exact h
  by_cases hi : i ∈ s
  · have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero 𝓜).1 hM.1.submodule_iSupIndep
    have hinj : Set.InjOn (fun c : K → ℤ => e + c) s := fun a _ b _ h => add_left_cancel h
    have key := hind (s.image fun c => e + c)
      (fun d => g (d - e) • m)
      (by
        intro d hd
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hd
        rw [add_sub_cancel_left]
        exact smul_mem_of_weighted hM ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (hgm c)) hm)
      (by
        rw [Finset.sum_image hinj]
        simpa only [add_sub_cancel_left] using hsum)
      (e + i) (Finset.mem_image_of_mem _ hi)
    simpa only [add_sub_cancel_left] using key
  · rw [hg, DFinsupp.notMem_support_iff.1 hi, ZeroMemClass.coe_zero, zero_smul]

theorem mem_annihilator_of_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {q : MRingOver S ι}
    (hq : ∀ e, ∀ m ∈ 𝓜 e, q • m = 0) : q ∈ Module.annihilator (MRingOver S ι) M := by
  refine Module.mem_annihilator.2 fun m => ?_
  have hm : m ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction 𝓜 (motive := fun x => q • x = 0) hm (fun e x hx => hq e x hx) (smul_zero q) ?_
  intro x y hx hy
  rw [smul_add, hx, hy, add_zero]

def prodSet (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) : Set M :=
  {y | ∃ (p : MRingOver S ι) (a : K → ℕ) (m : M) (c : K → ℤ), IsMultiHomog p a ∧ p ∈ P ∧ m ∈ 𝓜 c ∧ y = p • m}

theorem prodSet_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) :
    ∀ y ∈ prodSet 𝓜 P, ∃ c, y ∈ 𝓜 c := by
  rintro _ ⟨p, a, m, c, hp, -, hm, rfl⟩
  exact ⟨_, hM.2 a c p m hp hm⟩

theorem smul_top_eq_span {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)}
    (hP : IsMultiHomogIdeal P) :
    (P • ⊤ : Submodule (MRingOver S ι) M) = Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
  apply le_antisymm
  · obtain ⟨T, hT, hPT⟩ := hP
    rw [Submodule.smul_le]
    intro r hr n _
    rw [hPT] at hr
    induction hr using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨a, ha⟩ := hT t ht
      have htP : t ∈ P := hPT ▸ Ideal.subset_span ht
      have hn : n ∈ ⨆ e, 𝓜 e := by rw [hM.1.submodule_iSup_eq_top]; exact Submodule.mem_top
      have h0 : t • (0 : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := by
        rw [smul_zero]
        exact Submodule.zero_mem _
      refine Submodule.iSup_induction 𝓜
        (motive := fun x => t • x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P))
        hn (fun e x hx => Submodule.subset_span ⟨t, a, x, e, ha, htP, hx, rfl⟩) h0 ?_
      intro x y hx hy
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | zero => rw [zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.span_le]
    rintro _ ⟨p, a, m, c, -, hp, -, rfl⟩
    exact Submodule.smul_mem_smul hp Submodule.mem_top

theorem mem_iSup_span_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {x : M} (hx : x ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, (Submodule.span (MRingOver S ι) H).restrictScalars S ⊓ 𝓜 c := by
  have hx' := GradedSubquot.span_le_span_monTimes (S := S) (ι := ι) H hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := GradedSubquot.monTimes_homog hM hH hy
    exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.2 ⟨GradedSubquot.monTimes_subset_span H hy, hc⟩)
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul s y _ hy => exact Submodule.smul_mem _ s hy

end GradedSubmodules

open GradedSubmodules in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in
open Classical in

theorem GradedSubmodules.proof : GradedSubmodules.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hM
  refine ⟨?_, fun P hP => ?_⟩
  ·
    set 𝒜 := weightedHomogeneousSubmodule S (QuotPartGraded.blockWeight ι)
    refine ⟨{q | (∃ a, IsMultiHomog q a) ∧ q ∈ Module.annihilator (MRingOver S ι) M}, fun q hq => hq.1, ?_⟩
    apply le_antisymm
    · intro f hf
      rw [← DirectSum.sum_support_decompose 𝒜 f]
      refine Ideal.sum_mem _ fun i _ => Ideal.subset_span ⟨⟨_, isMultiHomog_of_weighted
        ((mem_weightedHomogeneousSubmodule _ _ _ _).1 (DirectSum.decompose 𝒜 f i).2)⟩, ?_⟩
      exact mem_annihilator_of_homog hM fun e m hm => component_smul_eq_zero hM hf i hm
    · exact Ideal.span_le.2 fun q hq => hq.2
  · have hspan := smul_top_eq_span hM hP
    refine ⟨?_, ?_⟩
    · have hind1 : iSupIndep (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) :=
        GradedSubquot.iSupIndep_comap hM.1.submodule_iSupIndep
          ((P • ⊤ : Submodule (MRingOver S ι) M).subtype.restrictScalars S) (fun a b h => Subtype.ext h)
      have hsup1 : ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c = ⊤ := by
        refine eq_top_iff.mpr fun x _ => ?_
        have hx : (x : M) ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ x.2
        have h := GradedSubquot.mem_iSup_inf hM (prodSet_homog hM P) hspan.ge x hx
        exact (show (⨆ c, ((Submodule.span (MRingOver S ι) (prodSet 𝓜 P)).comap
            (P • ⊤ : Submodule (MRingOver S ι) M).subtype).restrictScalars S ⊓
            subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c) ≤
              ⨆ c, subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M) c from
          iSup_mono fun c => inf_le_right) h
      exact ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind1 hsup1,
        fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩
    · set L := (P • ⊤ : Submodule (MRingOver S ι) M) with hLdef
      set f := L.mkQ.restrictScalars S with hfdef
      have hker : LinearMap.ker f = L.restrictScalars S := by
        ext x
        simp [hfdef]
      have hind := hM.1.submodule_iSupIndep
      have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ 𝓜 c) := by
        rw [hker]
        intro x hx
        have hx' : x ∈ Submodule.span (MRingOver S ι) (prodSet 𝓜 P) := hspan ▸ hx
        have := mem_iSup_span_inf hM (prodSet_homog hM P) hx'
        rwa [← hspan] at this
      have hind2 := GradedSubquot.iSupIndep_map_of_ker_le hind f hL
      have hsup2 : ⨆ c, quotGrading 𝓜 L c = ⊤ := by
        change ⨆ c, (𝓜 c).map f = ⊤
        rw [← Submodule.map_iSup, hM.1.submodule_iSup_eq_top, Submodule.map_top, LinearMap.range_eq_top]
        exact Submodule.mkQ_surjective L
      refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
      rintro a c p _ hp ⟨x, hx, rfl⟩
      exact ⟨p • x, hM.2 a c p x hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial BlockImageHilb

noncomputable section

namespace PullConeDegree

section Lemmas

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [CharZero Ω]

omit [CharZero Ω] in

theorem isWeightedHomogeneous_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsMultiHomog f a) : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a := by
  intro m hm
  funext k
  rw [weight_blockWeight_apply]
  exact hf m (mem_support_iff.mpr hm) k

omit [CharZero Ω] in

theorem isMultiHomog_of_isWeightedHomogeneous {f : MvPolynomial (Σ k, ι k) ℚ} {a : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f a) : IsMultiHomog f a := by
  intro m hm k
  rw [← weight_blockWeight_apply, hf (mem_support_iff.mp hm)]

omit [DecidableEq K] [CharZero Ω] in

theorem prod_X_pow_eq_monomial (a : K → ℕ) :
    (∏ k, MvPolynomial.X k ^ a k : MvPolynomial K Ω) = monomial (Finsupp.equivFunOnFinite.symm a) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp

theorem coeff_mConeMapQ (y : (Σ k, ι k) → Ω) (f : MvPolynomial (Σ k, ι k) ℚ) (n : K → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm n) (mConeMapQ y f) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) n f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m r =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m r rfl
    rw [mConeMapQ_eq y hm, prod_X_pow_eq_monomial, C_mul_monomial, mul_one, coeff_monomial,
      weightedHomogeneousComponent_of_mem (n := Finsupp.weight (NumbersDVR.blockWeight ι) m) hm]
    by_cases h : n = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm), map_zero]
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]

omit [DecidableEq K] [CharZero Ω] in

theorem exists_dvd_monomial (N : ℕ) (hne : ∀ k, Nonempty (ι k)) (μ : (Σ k, ι k) →₀ ℕ)
    (hμ : ∀ k, N * Fintype.card (ι k) ≤ ∑ i, μ ⟨k, i⟩) (r : ℚ) :
    ∃ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∣ monomial μ r := by
  have hc : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra h
    simp only [not_exists, not_le] at h
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty (α := ι k)) (fun i _ => h i)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at hlt
    exact absurd (hμ k) (not_le.mpr hlt)
  choose c hc using hc
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp), Fintype.prod_sigma, ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans
    (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℚ) ^ μ ⟨k, i⟩) (Finset.mem_univ (c k)))

end Lemmas

theorem proof : PullConeDegree.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L N hy hL hN d g hg hd
  have hne : ∀ k, Nonempty (ι k) := fun k => (hy k).elim fun i _ => ⟨i⟩

  have hgI : g ∈ coneNullIdeal y L := by
    rw [g.as_sum]
    refine Ideal.sum_mem _ fun μ hμ => ?_
    obtain ⟨c, hc⟩ := exists_dvd_monomial N hne μ
      (fun k => by rw [hg μ hμ k]; have := hd k; omega) (coeff μ g)
    exact Ideal.mem_of_dvd _ hc (hN c)
  have hI : coneNullIdeal y L = RingHom.ker (mConeMapQ y) ⊔
      Ideal.span (Set.range fun j => map (Int.castRingHom ℚ) (L j)) := by
    rw [coneNullIdeal, Ideal.span_union, ← map_mCoordIdeal]
    rfl
  rw [hI, Submodule.mem_sup] at hgI
  obtain ⟨u, hu, v, hv, huv⟩ := hgI
  obtain ⟨b, hb⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv

  have hmapL : ∀ j, mConeMapQ y (map (Int.castRingHom ℚ) (L j)) =
      monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    intro j
    have h : IsMultiHomog (map (Int.castRingHom ℚ) (L j)) e := fun m hm => hL j m (support_map_subset _ _ hm)
    rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog h), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
      ← algebraMap_int_eq, aeval_map_algebraMap]
  have hψg : mConeMapQ y g =
      ∑ j, mConeMapQ y (b j) * monomial (Finsupp.equivFunOnFinite.symm e) (aeval y (L j)) := by
    rw [← huv, map_add, RingHom.mem_ker.mp hu, zero_add, ← hb, map_sum]
    simp only [map_mul, hmapL]

  refine ⟨fun j => weightedHomogeneousComponent (NumbersDVR.blockWeight ι) (d - e) (b j),
    fun j => isMultiHomog_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous _ _), ?_⟩
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) hψg
  rw [mConeMapQ_eq y (isWeightedHomogeneous_of_isMultiHomog hg), prod_X_pow_eq_monomial, C_mul_monomial, mul_one,
    coeff_monomial, if_pos rfl, coeff_sum] at hc
  rw [hc]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hle : Finsupp.equivFunOnFinite.symm e ≤ Finsupp.equivFunOnFinite.symm d :=
    Finsupp.le_def.mpr fun k => by simp only [Finsupp.coe_equivFunOnFinite_symm]; have := hd k; omega
  have hsub : Finsupp.equivFunOnFinite.symm d - Finsupp.equivFunOnFinite.symm e =
      Finsupp.equivFunOnFinite.symm (d - e) := by
    ext k
    simp
  rw [coeff_mul_monomial', if_pos hle, hsub, coeff_mConeMapQ]

end PullConeDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix

noncomputable section

namespace SupBoundCount

theorem main {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ f : MRing ι, IsMultiHomog f (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f)
    {r : ℕ} {b : Fin r → MvPolynomial (Σ k, ι k) ℚ} (hb : IsSecBasisM d.y d.k₀ n b) :
    (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * c ^ 2 ∧
      -(1 / 2) * Real.log (blockGram d n b).det - (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) *
          Real.log (c * Real.sqrt (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)))) ≤
        smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n := by
  classical
  rw [finrank_secM hb]
  have hb' := hb
  choose f hf hbf using hb.1
  have hbe : b = fun j => map (Int.castRingHom ℚ) (f j) := funext hbf
  subst hbe
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb'.2.1
    simpa [aeval_map_int] using this
  have hG := gram_posDef d n f hf hli hc hsup
  refine ⟨rank_le d n f hf hli hc hsup, ?_⟩

  set Q : (Fin r → ℤ) → ℝ := fun m => (fun k => (m k : ℝ)) ⬝ᵥ
    (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ)) with hQ
  set P : (Fin r → ℤ) → Prop := fun m =>
    IsSmallH (mCoordIdeal d.y) d.y d.A n (aeval d.y (∑ k, m k • f k)) with hPdef
  have hP1 : ∀ m, Q m ≤ (1 / c) ^ 2 → P m := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    refine (isSmallH_iff d n hF).2 fun z hz => ?_
    have h1 := hsup _ hF z hz
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    have h2 : Real.sqrt (Q m) ≤ 1 / c := by
      calc Real.sqrt (Q m) ≤ Real.sqrt ((1 / c) ^ 2) := Real.sqrt_le_sqrt hm
        _ = 1 / c := Real.sqrt_sq (by positivity)
    have h3 : c * Real.sqrt (Q m) ≤ 1 := by
      calc c * Real.sqrt (Q m) ≤ c * (1 / c) := mul_le_mul_of_nonneg_left h2 hc.le
        _ = 1 := by field_simp
    have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
    exact (div_le_one hp).1 (h1.trans h3)
  have hP2 : ∀ m, P m → Q m ≤ 1 := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    have h1 := blockL2Norm_le_one_of_sup_bound d n hF ((isSmallH_iff d n hF).1 hm)
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    by_contra h
    push_neg at h
    have := Real.sqrt_lt_sqrt zero_le_one h
    rw [Real.sqrt_one] at this
    linarith
  obtain ⟨-, hcount⟩ := count_of_gram hG (by positivity : (0 : ℝ) < 1 / c) P hP1 hP2

  have hmem : ∀ m : Fin r → ℤ, aeval d.y (∑ k, m k • f k) ∈ secM d.y (blockDeg d.k₀ n) := by
    intro m
    rw [← hb'.2.2]
    simp only [map_sum, map_zsmul]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, by simp [aeval_map_int]⟩)
  have hinj : Function.Injective fun m : Fin r → ℤ => aeval d.y (∑ k, m k • f k) := by
    intro m m' h
    have h0 : ∑ k, (m k - m' k) • aeval d.y (f k) = 0 := by
      simp only [map_sum, map_zsmul] at h
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 h
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 k)
  let E : {m // P m} → {s : secM d.y (blockDeg d.k₀ n) // IsSmallH (mCoordIdeal d.y) d.y d.A n (s : Ω)} :=
    fun m => ⟨⟨_, hmem m.1⟩, m.2⟩
  have hE : Function.Bijective E := by
    refine ⟨fun m m' h => Subtype.ext (hinj (congrArg (fun s => ((s.1 : secM d.y _) : Ω)) h)), ?_⟩
    rintro ⟨⟨s, hs⟩, hsm⟩
    have hs' := hs
    rw [← hb'.2.2] at hs'
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hs'
    have hms : aeval d.y (∑ k, m k • f k) = s := by
      rw [← hm]
      simp [map_sum, aeval_map_int]
    refine ⟨⟨m, ?_⟩, ?_⟩
    · show IsSmallH _ _ _ _ _
      rw [hms]
      exact hsm
    · exact Subtype.ext (Subtype.ext hms)
  have hcard := Nat.card_congr (Equiv.ofBijective E hE)
  simp only [smallSectionCount]
  rw [← hcard]

  have hV : (r : ℝ) * Real.log (2 / Real.sqrt r) ≤ Real.log (unitBallVolume r) := by
    have hpos : 0 < (2 / Real.sqrt r) ^ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · simp [h0]
      · exact pow_pos (div_pos two_pos (Real.sqrt_pos.2 (by exact_mod_cast h0))) r
    rw [← Real.log_pow]
    exact Real.log_le_log hpos (MinkowskiCount.cube_le_unitBallVolume r)
  have halg : (r : ℝ) * Real.log (2 / Real.sqrt r) + r * Real.log (1 / c / 2) =
      -((r : ℝ) * Real.log (c * Real.sqrt r)) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · simp [h0]
    · have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast h0)
      rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
      have : 2 / Real.sqrt r * (1 / c / 2) = (c * Real.sqrt r)⁻¹ := by
        field_simp
      rw [this, Real.log_inv]
      ring
  linarith

end SupBoundCount

theorem SupBoundCount.proof : SupBoundCount.Statement := by
  intro D K _ _ ι _ Ω _ _ d n c hc hsup
  have hex := SupBoundCount.exists_isSecBasisM d.y d.k₀ n
  have h := SupBoundCount.main d n hc hsup hex.choose_spec
  refine ⟨h.1, ?_⟩
  rw [blockChi, dif_pos hex]
  exact h.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionFormsIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionFormsIndependent.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ) (n r : ℕ)
    (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ a : Fin r → ℂ,
    (∀ y : d.R.X, ∑ k, a k * eval (resPt d y) (map (algebraMap ℚ ℂ) (b k)) = 0) → a = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTranscRatioDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TranscRatioDeg.Statement : Prop :=
  ∀ (ι : Type) (E : Type) [Field E] [CharZero E] (u : ι → E) (D : ℕ) (e : Fin (D + 1) → ι) (w : Fin (D + 1) → E)
    (i₀ : ι) (Φ : Type) [Field Φ] [Algebra Φ E],
    u i₀ ≠ 0 → (∀ k, u (e k) ≠ 0) → (∀ k, w k * u (e 0) = w 0 * u (e k)) →
    Transcendental (Algebra.adjoin ℤ (Set.range u)) (w 0) →
    (algebraMap Φ E).fieldRange = Subfield.closure (Set.range w) →
    Module.finrank Φ (IntermediateField.adjoin Φ (Set.range fun i => u i / u i₀)) = projDeg u e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

