import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0046
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsBoundedAtOfIsBoundedH
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogX
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def H1VanishingDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι (KH.quotPart S P) (e + c • N) 1)) →
    ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsMultiHomogSumSmulMap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

namespace SectionL2Lattice

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem measurableSet_mcPts (P : Ideal (MRing ι)) : MeasurableSet (mcPts P) := by
  have h1 : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have h2 : IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ =>
      isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  exact h1.measurableSet.inter h2.measurableSet

omit [Fintype K] in

theorem isMultiHomog_sum_smul_map {r : ℕ} {e : K → ℕ} {g : Fin r → MRing ι} (hg : ∀ i, IsMultiHomog (g i) e)
    (c : Fin r → ℂ) : IsMultiHomog (∑ i, c i • map (Int.castRingHom ℂ) (g i)) e := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
  exact hg i m (MvPolynomial.support_map_subset _ _ (MvPolynomial.support_smul hi)) k

variable {Ω : Type} [Field Ω]

omit [∀ k, Fintype (ι k)] in

theorem chartLat_le_chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ :=
  fun _ hs c hc => isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hs c hc⟩)

omit [∀ k, Fintype (ι k)] in

theorem finite_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (hfin : Module.Finite ℤ (chartLatNm y a τ)) :
    Module.Finite ℤ (chartLat y a τ) ∧
      Module.finrank ℤ (chartLat y a τ) ≤ Module.finrank ℤ (chartLatNm y a τ) := by
  let f : chartLat y a τ →ₗ[ℤ] chartLatNm y a τ :=
    (AddSubgroup.inclusion (chartLat_le_chartLatNm y a τ)).toIntLinearMap
  have hf : Function.Injective f := AddSubgroup.inclusion_injective (chartLat_le_chartLatNm y a τ)
  have : Module.Finite ℤ (chartLat y a τ) := Module.Finite.of_injective f hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_injective hf⟩

end SectionL2Lattice

open SectionL2Lattice in

theorem SectionL2Lattice.proof (hV : SectionPointValue.Statement) (hF : RealFormsOnPoints.Statement)
    (hG : L2GramLattice.Statement) (hN : NmSectionsRankBound.Statement) (hB : SectionSupBound.Statement) :
    SectionL2Lattice.Statement := by
  intro K _ ι _ Ω _ _ y D A har hbir hcont μ _ hμ hZ
  obtain ⟨w, hwc, hwrep, hwnorm, hwmul, hwden⟩ := hV K ι Ω y A har.2.1.2.2 hcont
  obtain ⟨hfin, C, -, hC⟩ := hN K ι Ω y D A.a har hbir
  have hae : ∀ᵐ z ∂μ, z ∈ mcPts (mCoordIdeal y) := hμ
  have hrest : μ.restrict (mcPts (mCoordIdeal y)) = μ := Measure.restrict_eq_self_of_ae_mem hae
  have hmeas : ∀ (n : ℕ) (s : chartLat y A.a n), AEStronglyMeasurable (w n s) μ := fun n s => by
    rw [← hrest]; exact (hwc n s).aestronglyMeasurable (measurableSet_mcPts _)
  have hbdd : ∀ (n : ℕ) (s : chartLat y A.a n), ∃ c : ℝ, ∀ᵐ z ∂μ, ‖w n s z‖ ≤ c := fun n s => by
    obtain ⟨c, -, hc⟩ := hB K ι Ω y A n s hcont s.2
    refine ⟨Real.exp c, hae.mono fun z hz => ?_⟩
    rw [← hwnorm n s z hz]
    exact secNormAt_le (Real.exp_pos c).le (isBoundedAt_of_isBoundedH hc hz)
  have hint : ∀ (n : ℕ) (s : chartLat y A.a n), Integrable (fun z => ‖w n s z‖ ^ 2) μ := fun n s => by
    obtain ⟨c, hc⟩ := hbdd n s
    refine (integrable_const (c ^ 2)).mono' ((hmeas n s).norm.pow 2) (hc.mono fun z hz => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  have key : ∀ n : ℕ, ∃ φ : chartLat y A.a n →+ EuclideanSpace ℝ (Fin (Module.finrank ℤ (chartLat y A.a n))),
      Function.Injective φ ∧ DiscreteTopology (imageLattice φ) ∧
      (∀ [DiscreteTopology (imageLattice φ)], IsZLattice ℝ (imageLattice φ)) ∧
      ∀ s, ‖φ s‖ = Real.sqrt (∫ z, ‖w n s z‖ ^ 2 ∂μ) := by
    intro n
    have : Module.Finite ℤ (chartLat y A.a n) := (finite_chartLat y A.a n (hfin n)).1
    have : Module.Free ℤ (chartLat y A.a n) := Module.free_of_finite_type_torsion_free'
    refine hG _ _ μ (w n) (hmeas n) (hbdd n) ?_
    intro r x hx c hc
    obtain ⟨e, e', h, g, hh, hg, he, hy, hgy⟩ := hwden n r x
    refine hF K ι Ω y (D + 1) e r g har hg ?_ c ?_
    · have h1 : LinearIndependent ℤ (fun i => (x i : Ω)) :=
        hx.map' (chartLat y A.a n).subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
      have h2 := h1.map' (LinearMap.mulRight ℤ (aeval y h))
        (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hy))
      convert h2 using 1 <;> first | rfl | (funext i; simp [hgy i])
    · intro z hz
      have hF' := hZ e (∑ i, (c i : ℂ) • map (Int.castRingHom ℂ) (g i)) (isMultiHomog_sum_smul_map hg _) ?_ z hz
      · simpa only [map_sum, smul_eval] using hF'
      · filter_upwards [hc, hae] with z hz0 hzP
        rw [map_sum]
        simp only [smul_eval]
        calc ∑ i, (c i : ℂ) * eval z (map (Int.castRingHom ℂ) (g i))
            = ∑ i, (c i : ℂ) * (w n (x i) z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hwrep n (x i) e e' (g i) h z (hg i) hh he (hgy i) hzP]
          _ = (∑ i, (c i : ℂ) * w n (x i) z) * (eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
          _ = 0 := by rw [hz0, zero_mul]
  choose φ hinj hdisc hlat hnorm using key
  refine ⟨fun n => Module.finrank ℤ (chartLat y A.a n), φ, hinj, hdisc, fun n _ => hlat n, ?_, ?_, ?_, ?_⟩
  · intro n c s hc hs
    rw [hnorm, ← Real.sqrt_sq hc]
    refine Real.sqrt_le_sqrt ?_
    calc ∫ z, ‖w n s z‖ ^ 2 ∂μ ≤ ∫ _, c ^ 2 ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) (integrable_const _)
            (hae.mono fun z hz => by
              show ‖w n s z‖ ^ 2 ≤ c ^ 2
              rw [← hwnorm n s z hz]
              exact pow_le_pow_left₀ (secNormAt_nonneg _ _ _ _ _)
                (secNormAt_le hc (isBoundedAt_of_isBoundedH hs hz)) 2)
      _ = c ^ 2 := by simp
  · intro n k s t st ht hst
    rw [hnorm, hnorm]
    refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) (hint n s)
      (hae.mono fun z hz => ?_))
    have h1 : ‖w k t z‖ ≤ 1 := by
      rw [← hwnorm k t z hz]
      refine secNormAt_le zero_le_one fun dg dh g h hg hh hd he => ?_
      rw [one_mul]
      exact ht dg dh g h z hg hh hd he hz
    show ‖w (n + k) st z‖ ^ 2 ≤ ‖w n s z‖ ^ 2
    rw [hwmul n k s t st hst z hz, norm_mul, mul_pow]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) h1)
  · exact ⟨C, fun n => le_trans (by exact_mod_cast (finite_chartLat y A.a n (hfin n)).2) (hC n)⟩
  · intro n s
    rw [hnorm, sectionL2Norm]
    congr 1
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    simp only [hwnorm n s z hz]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace BirationalModelExists

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_zero' (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem isMultiHomog_add' {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]

theorem isMultiHomog_neg' {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm
  rw [support_neg] at hm
  exact hf m hm

theorem aeval_scale {S : Type*} [CommRing S] [Algebra ℤ S] {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a)
    (z : (Σ k, ι k) → S) (u : K → S) :
    aeval (fun p => z p * u p.1) g = aeval z g * ∏ k, u k ^ a k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (z p * u p.1) ^ m p = (∏ p, z p ^ m p) * ∏ k, u k ^ a k := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, u k ^ m ⟨k, i⟩ = u k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem hom_aeval {S T : Type*} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (z : (Σ k, ι k) → S) (g : MRing ι) :
    φ (aeval z g) = aeval (fun p => φ (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

variable (P : Ideal (MRing ι)) [P.IsPrime]

def coordClass (p : Σ k, ι k) : FractionRing (MRing ι ⧸ P) :=
  algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (X p))

theorem aeval_coordClass (g : MRing ι) :
    aeval (coordClass P) g = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp only [map_mul, hp, aeval_X, coordClass]

theorem aeval_coordClass_eq_zero (g : MRing ι) : aeval (coordClass P) g = 0 ↔ g ∈ P := by
  rw [aeval_coordClass, map_eq_zero_iff _ (IsFractionRing.injective (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P))),
    Ideal.Quotient.eq_zero_iff_mem]

def fnField : Subfield (FractionRing (MRing ι ⧸ P)) where
  carrier := {s | ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval (coordClass P) h ≠ 0 ∧ aeval (coordClass P) g = s * aeval (coordClass P) h}
  zero_mem' := ⟨0, 0, 1, isMultiHomog_zero' 0, isMultiHomog_one, by simp, by simp⟩
  one_mem' := ⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, by simp, by simp⟩
  add_mem' := by
    rintro s t ⟨d, g, h, hg, hh, h0, hs⟩ ⟨d', g', h', hg', hh', h0', ht⟩
    refine ⟨d + d', g * h' + h * g', h * h',
      isMultiHomog_add' (isMultiHomog_mul hg hh') (isMultiHomog_mul hh hg'), isMultiHomog_mul hh hh',
      by simp [h0, h0'], ?_⟩
    simp only [map_add, map_mul, hs, ht]
    ring
  mul_mem' := by
    rintro s t ⟨d, g, h, hg, hh, h0, hs⟩ ⟨d', g', h', hg', hh', h0', ht⟩
    refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh', by simp [h0, h0'], ?_⟩
    simp only [map_mul, hs, ht]
    ring
  neg_mem' := by
    rintro s ⟨d, g, h, hg, hh, h0, hs⟩
    exact ⟨d, -g, h, isMultiHomog_neg' hg, hh, h0, by simp [hs]⟩
  inv_mem' := by
    rintro s ⟨d, g, h, hg, hh, h0, hs⟩
    by_cases s0 : s = 0
    · subst s0
      exact ⟨0, 0, 1, isMultiHomog_zero' 0, isMultiHomog_one, by simp, by simp⟩
    · refine ⟨d, h, g, hh, hg, ?_, ?_⟩
      · rw [hs]
        exact mul_ne_zero s0 h0
      · rw [hs, ← mul_assoc, inv_mul_cancel₀ s0, one_mul]

variable {P}

theorem coordClass_ne_zero {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ P) : coordClass P p ≠ 0 := by
  have h := (aeval_coordClass_eq_zero P (X p)).not.2 hp
  rwa [aeval_X] at h

open Classical in

def birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (p : Σ k, ι k) : fnField P :=
  ⟨coordClass P p / coordClass P ⟨p.1, c p.1⟩,
    ⟨Pi.single p.1 1, X p, X ⟨p.1, c p.1⟩, isMultiHomog_X' p.1 p.2, isMultiHomog_X' p.1 (c p.1),
      by rw [aeval_X]; exact coordClass_ne_zero (hc p.1),
      by rw [aeval_X, aeval_X, div_mul_cancel₀ _ (coordClass_ne_zero (hc p.1))]⟩⟩

theorem coe_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (p : Σ k, ι k) :
    (birPoint c hc p : FractionRing (MRing ι ⧸ P)) = coordClass P p / coordClass P ⟨p.1, c p.1⟩ := rfl

theorem coe_aeval_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) {g : MRing ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) :
    ((aeval (birPoint c hc) g : fnField P) : FractionRing (MRing ι ⧸ P)) =
      aeval (coordClass P) g * ∏ k, (coordClass P ⟨k, c k⟩)⁻¹ ^ a k := by
  have h := hom_aeval (fnField P).subtype (birPoint c hc) g
  have hf : (fun p => (fnField P).subtype (birPoint c hc p)) =
      fun p => coordClass P p * (fun k => (coordClass P ⟨k, c k⟩)⁻¹) p.1 := by
    funext p
    exact div_eq_mul_inv _ _
  rw [hf] at h
  exact h.trans (aeval_scale hg (coordClass P) fun k => (coordClass P ⟨k, c k⟩)⁻¹)

theorem prod_inv_ne_zero (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (a : K → ℕ) :
    ∏ k, (coordClass P ⟨k, c k⟩)⁻¹ ^ a k ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (coordClass_ne_zero (hc k)))

theorem eval_mConeMap_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (f : MRing ι) :
    eval₂ (fnField P).subtype (fun k => coordClass P ⟨k, c k⟩) (mConeMap (birPoint c hc) f) =
      aeval (coordClass P) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have e1 := map_intCast (eval₂Hom (fnField P).subtype (fun k => coordClass P ⟨k, c k⟩)) a
    simp only [coe_eval₂Hom] at e1
    simpa [mConeMap] using e1
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p n hp =>
    have hX : mConeMap (birPoint c hc) (X n) = C (birPoint c hc n) * X n.1 := by simp [mConeMap]
    have e : (fnField P).subtype (birPoint c hc n) * coordClass P ⟨n.1, c n.1⟩ = coordClass P n :=
      div_mul_cancel₀ _ (coordClass_ne_zero (hc n.1))
    rw [map_mul, eval₂_mul, hp, hX, eval₂_mul, eval₂_C, eval₂_X, map_mul, aeval_X, e]

theorem mCoordIdeal_birPoint (hP : IsMultiHomogIdeal P) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) : mCoordIdeal (birPoint c hc) = P := by
  apply le_antisymm
  · intro f hf
    rw [mCoordIdeal, RingHom.mem_ker] at hf
    have h := eval_mConeMap_birPoint c hc f
    rw [hf, eval₂_zero] at h
    exact (aeval_coordClass_eq_zero P f).1 h.symm
  · obtain ⟨S, hS, rfl⟩ := hP
    rw [Ideal.span_le]
    intro g hgS
    obtain ⟨a, ha⟩ := hS g hgS
    have hgP : aeval (coordClass (Ideal.span S)) g = 0 :=
      (aeval_coordClass_eq_zero _ g).2 (Ideal.subset_span hgS)
    have hy : aeval (birPoint c hc) g = 0 := by
      apply Subtype.ext
      rw [coe_aeval_birPoint c hc ha, hgP, zero_mul]
      rfl
    show g ∈ RingHom.ker (mConeMap (birPoint c hc))
    rw [RingHom.mem_ker]
    show aeval (fun p => C (birPoint c hc p) * X p.1) g = 0
    refine (aeval_scale ha (fun p => C (birPoint c hc p)) X).trans ?_
    rw [← hom_aeval C, hy, map_zero, zero_mul]

theorem birational_birPoint (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) :
    Birational (birPoint c hc) := by
  rintro ⟨s, d, g, h, hg, hh, h0, hs⟩
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · intro h'
    have := congrArg (fun t : fnField P => (t : FractionRing (MRing ι ⧸ P))) h'
    simp only [coe_aeval_birPoint c hc hh, ZeroMemClass.coe_zero] at this
    exact mul_ne_zero h0 (prod_inv_ne_zero c hc d) this
  · apply Subtype.ext
    rw [Subfield.coe_mul, coe_aeval_birPoint c hc hg, coe_aeval_birPoint c hc hh]
    show _ = s * _
    rw [hs, mul_assoc]

end BirationalModelExists

theorem BirationalModelExists.proof : BirationalModelExists.Statement := by
  intro K _ ι _ P d hP
  obtain ⟨_, ⟨hprime, hhom, hrel⟩, _, _⟩ := hP
  choose c hc using hrel
  have := hprime
  exact ⟨BirationalModelExists.fnField P, inferInstance, BirationalModelExists.birPoint c hc,
    BirationalModelExists.mCoordIdeal_birPoint hhom c hc, BirationalModelExists.birational_birPoint c hc⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem chartLat_subset_chartLatQ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLat y a n) :
    s ∈ chartLatQ y a n := by
  intro c hc
  have hle : chartRingZ y c ≤ (chartRingQ y c).restrictScalars ℤ :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := ℚ))
  exact hle (hs c hc)

theorem ChartLatRank.proof (hfin : SectionLatticeFinite.Statement) : ChartLatRank.Statement := by
  intro K _ ι _ Ω _ _ y a n hy
  classical
  set M := AddSubgroup.toIntSubmodule (chartLat y a n) with hM
  have hfg : M.FG := (Submodule.fg_iff_addSubgroup_fg M).mpr (hfin K ι Ω y a n hy)
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr hfg
  obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  set v : Fin r → Ω := fun i => ((b i : M) : Ω) with hv
  have hvZ : LinearIndependent ℤ v := b.linearIndependent.map' M.subtype M.ker_subtype
  have hvQ : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hvZ
  have hspan : Submodule.span ℚ (Set.range v) = chartLatQ y a n := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact chartLat_subset_chartLatQ y a n (b i).2
    · intro s hs
      obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y a n s hs
      have hmemM : (⟨(N : Ω) * s, hNs⟩ : M) ∈ Submodule.span ℤ (Set.range b) := b.mem_span _
      have hmemZ : (N : Ω) * s ∈ Submodule.span ℤ (Set.range v) := by
        have h := Submodule.mem_map_of_mem (f := M.subtype) hmemM
        rw [Submodule.map_span, ← Set.range_comp] at h
        exact h
      have hmemQ : (N : Ω) * s ∈ Submodule.span ℚ (Set.range v) :=
        Submodule.span_le_restrictScalars ℤ ℚ _ hmemZ
      have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
        rw [Rat.smul_def]
        push_cast
        field_simp
      rw [hs']
      exact Submodule.smul_mem _ _ hmemQ
  rw [Module.finrank_eq_card_basis b, ← hspan, finrank_span_eq_card hvQ]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Module

theorem CovolumeLeGram.proof : CovolumeLeGram.Statement := by
  intro n L _ _ ι _ _ x hxL hx hcard
  have hcard' : Fintype.card ι = finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [hcard, finrank_euclideanSpace_fin]
  let B : Basis ι ℝ (EuclideanSpace ℝ (Fin n)) := basisOfLinearIndependentOfCardEqFinrank' x hx hcard'
  have hB : ⇑B = x := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  have hML : Submodule.span ℤ (Set.range B) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; rw [hB]; exact hxL i)
  have hcovM : ZLattice.covolume (Submodule.span ℤ (Set.range B)) = Real.sqrt (Matrix.gram ℝ x).det := by
    rw [GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram _ (B.restrictScalars ℤ)]
    congr 3
    funext i
    simp [Basis.restrictScalars_apply, hB]
  have hdiv := ZLattice.covolume_div_covolume_eq_relIndex' _ L hML
  have hposM := ZLattice.covolume_pos (Submodule.span ℤ (Set.range B))
  have hposL := ZLattice.covolume_pos L
  have hne : (Submodule.span ℤ (Set.range B)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hdiv
    exact (div_pos hposM hposL).ne' hdiv
  have h1 : (1 : ℝ) ≤ ZLattice.covolume (Submodule.span ℤ (Set.range B)) / ZLattice.covolume L := by
    rw [hdiv]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  rw [← hcovM]
  rwa [le_div_iff₀ hposL, one_mul] at h1

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSectionsPower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

theorem EuclideanSectionsPower.proof (hL : SectionL2Lattice.Statement) (hP : TensorPowerL2Degree.Statement) :
    EuclideanSectionsPower.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hc
  obtain ⟨μ, m, hμ, hcon, hZ, hm, hdeg⟩ := hP K ι Ω y D A P0 II hD hII har hb hA hc
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, hnorm⟩ :=
    hL K ι Ω y D A har hb hA.semipos.1.continuousOn μ hμ hcon hZ
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, hmul, hrank, m, hm, fun ε hε => ?_⟩
  filter_upwards [hdeg ε hε] with q hq
  intro _ _
  exact hq (r (m * q)) (φ (m * q)) (hinj _) (hnorm _)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNonzeroSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def GeneratedNonzeroSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (n : K → ℤ),
    KH.GeneratedV ℚ (KH.genIdeal y) n → ∃ s ∈ chartLat y n 1, s ≠ 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

