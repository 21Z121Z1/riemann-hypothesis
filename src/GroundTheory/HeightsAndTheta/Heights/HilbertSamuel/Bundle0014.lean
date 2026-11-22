import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegre

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexTaylorTwo
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Topology Asymptotics ReciprocityTheory.AnForm Matrix Metric

noncomputable section

theorem taylor_two_isLittleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (fun z => f (x + z) - f x - fderiv ℝ f x z - fderiv ℝ (fderiv ℝ f) x z z / 2)
      =o[𝓝 0] fun z => ‖z‖ ^ 2 := by
  set L := fderiv ℝ f x
  set H := fderiv ℝ (fderiv ℝ f) x with hHdef
  have hsymm : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  have hH : HasFDerivAt (fderiv ℝ f) H x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have ho := hasFDerivAt_iff_isLittleO_nhds_zero.1 hH
  have htend : Tendsto (fun z : E => x + z) (𝓝 0) (𝓝 x) := by
    have : Continuous fun z : E => x + z := continuous_const.add continuous_id
    simpa using this.tendsto (0 : E)
  have hdiff : ∀ᶠ z in 𝓝 (0 : E), DifferentiableAt ℝ f (x + z) :=
    htend.eventually ((hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp))
  refine isLittleO_iff.2 fun ε hε => ?_
  have hb := (isLittleO_iff.1 ho hε).and hdiff
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hb
  filter_upwards [ball_mem_nhds (0 : E) hδ] with z hz
  set g : E → ℝ := fun w => f (x + w) - f x - L w - (2 : ℝ)⁻¹ • H w w with hg
  have hderiv : ∀ w ∈ ball (0 : E) δ, HasFDerivAt g (fderiv ℝ f (x + w) - L - H w) w := by
    intro w hw
    have h1 : HasFDerivAt (fun w => f (x + w)) ((fderiv ℝ f (x + w)).comp
        (ContinuousLinearMap.id ℝ E)) w :=
      (hball w hw).2.hasFDerivAt.comp w ((hasFDerivAt_id w).const_add x)
    have h2 : HasFDerivAt (fun w => H w w) ((H w).comp (ContinuousLinearMap.id ℝ E) + H.flip w) w :=
      H.hasFDerivAt.clm_apply (hasFDerivAt_id w)
    have h3 := ((h1.sub_const (f x)).sub L.hasFDerivAt).sub (h2.const_smul (2 : ℝ)⁻¹)
    refine h3.congr_fderiv ?_
    ext v
    simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, _root_.smul_apply, _root_.add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    have := hsymm v w
    rw [← hHdef] at this
    rw [this]
    ring
  have hz' : ‖z‖ < δ := by simpa using hz
  have hsub : closedBall (0 : E) ‖z‖ ⊆ ball 0 δ := closedBall_subset_ball hz'
  have hbound : ∀ w ∈ closedBall (0 : E) ‖z‖, ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖z‖ := by
    intro w hw
    have hw' := (hball w (hsub hw)).1
    have hwz : ‖w‖ ≤ ‖z‖ := by simpa using hw
    calc ‖fderiv ℝ f (x + w) - L - H w‖ ≤ ε * ‖w‖ := hw'
      _ ≤ ε * ‖z‖ := by gcongr
  have hz0 : z ∈ closedBall (0 : E) ‖z‖ := by simp
  have hmvt := (convex_closedBall (0 : E) ‖z‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw => (hderiv w (hsub hw)).hasFDerivWithinAt) hbound
    (mem_closedBall_self (norm_nonneg z)) hz0
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero] at hmvt
  have : g z = f (x + z) - f x - L z - H z z / 2 := by
    simp only [hg, smul_eq_mul]; ring
  rw [← this, norm_pow, norm_norm]
  calc ‖g z‖ ≤ ε * ‖z‖ * ‖z‖ := hmvt
    _ = ε * ‖z‖ ^ 2 := by ring

def complexLinearCoeffs {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) : Fin D → ℂ :=
  fun j => (L (Pi.single j 1) : ℂ) - Complex.I * (L (Complex.I • Pi.single j 1) : ℂ)

theorem re_complexLinearCoeffs_dot {D : ℕ} (L : (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (complexLinearCoeffs L ⬝ᵥ z).re = L z := by
  have hz : z = ∑ j, ((z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ))) := by
    ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  conv_rhs => rw [hz]
  simp only [map_sum, map_add, map_smul, dotProduct, Complex.re_sum, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [complexLinearCoeffs, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

def complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    Matrix (Fin D) (Fin D) ℂ :=
  fun j k =>
    let ej : Fin D → ℂ := Pi.single j 1
    let ek : Fin D → ℂ := Pi.single k 1
    ((H ej ek - H (Complex.I • ej) (Complex.I • ek) : ℝ) -
      Complex.I * ((H ej (Complex.I • ek) + H (Complex.I • ej) ek : ℝ))) / 4

theorem re_dot_complexQuadMatrix {D : ℕ} (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ)
    (z : Fin D → ℂ) :
    (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re = (H z z - H (Complex.I • z) (Complex.I • z)) / 4 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin D → (Fin D → ℂ), c = fun j => (z j).re • (Pi.single j 1 : Fin D → ℂ) +
      (z j).im • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : Fin D → (Fin D → ℂ), d = fun j =>
      (z j).re • (Complex.I • (Pi.single j 1 : Fin D → ℂ)) +
      (-(z j).im) • (Pi.single j 1 : Fin D → ℂ) := ⟨_, rfl⟩
  have hz : z = ∑ j, c j := by
    rw [hc]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have hIz : Complex.I • z = ∑ j, d j := by
    rw [hd]; ext k
    apply Complex.ext <;> simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib]
  have expand : ∀ c : Fin D → (Fin D → ℂ),
      H (Finset.sum Finset.univ c) (Finset.sum Finset.univ c) = ∑ i, ∑ k, H (c i) (c k) := by
    intro c
    simp only [map_sum, _root_.sum_apply]
    rw [Finset.sum_comm]
  have e1 : H z z = ∑ i, ∑ k, H (c i) (c k) := by
    calc H z z = H (∑ j, c j) (∑ j, c j) := by rw [← hz]
      _ = _ := expand c
  have e2 : H (Complex.I • z) (Complex.I • z) = ∑ i, ∑ k, H (d i) (d k) := by
    rw [hIz]; exact expand d
  have hR : (z ⬝ᵥ (complexQuadMatrix H *ᵥ z)).re =
      ∑ i, ∑ k, (z i * (complexQuadMatrix H i k * z k)).re := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Complex.re_sum]
  rw [hR, e1, e2, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  subst hc hd
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  simp only [complexQuadMatrix, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem ComplexTaylorTwo.proof : ComplexTaylorTwo.Statement := by
  intro D ψ y₀ hψ
  refine ⟨complexLinearCoeffs (fderiv ℝ ψ y₀), complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀), ?_⟩
  refine (taylor_two_isLittleO hψ).congr_left fun z => ?_
  have h1 := re_complexLinearCoeffs_dot (fderiv ℝ ψ y₀) z
  have h2 := re_dot_complexQuadMatrix (fderiv ℝ (fderiv ℝ ψ) y₀) z
  have h3 := ReciprocityTheory.AnForm.M.re_star_dot_hessC ψ y₀ (star z)
  rw [star_star] at h3
  rw [Complex.add_re, h1, h2, h3]
  unfold levi
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace HilbertIncrement

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

theorem weight_intWeight (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (intWeight (ι := ι)) e =
      fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) := by
  funext k
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Nat.cast_sum, Nat.cast_mul, intWeight, unitDeg, blockWeight]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : k = v.1 <;> simp [h]

theorem isWeightedHomogeneous_intWeight_iff {f : MRing ι F} {a : K → ℕ} :
    IsWeightedHomogeneous (intWeight (ι := ι)) f (fun k => (a k : ℤ)) ↔
      IsWeightedHomogeneous (blockWeight ι) f a := by
  constructor
  · intro h e he
    funext k
    have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = (a k : ℤ) := by
      have := congrFun (h he) k
      rw [weight_intWeight] at this
      exact this
    exact_mod_cast e1
  · intro h e he
    rw [weight_intWeight, h he]

theorem ringPiece_natCast (a : K → ℕ) :
    ringPiece (F := F) (ι := ι) (fun k => (a k : ℤ)) =
      weightedHomogeneousSubmodule F (blockWeight ι) a := by
  ext f
  simp only [ringPiece, mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_intWeight_iff

theorem component_intWeight_mem {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J)
    {f : MRing ι F} (hf : f ∈ J) (m : K → ℤ) :
    weightedHomogeneousComponent (intWeight (ι := ι)) m f ∈ J := by
  classical
  by_cases hm : ∀ k, 0 ≤ m k
  · have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f =
        weightedHomogeneousComponent (blockWeight ι) (fun k => (m k).toNat) f := by
      ext e
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent, weight_intWeight]
      have hiff : ((fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ)) = m) ↔
          Finsupp.weight (blockWeight ι) e = fun k => (m k).toNat := by
        constructor
        · intro h
          funext k
          have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
          have := hm k
          show _ = (m k).toNat
          omega
        · intro h
          funext k
          have e1 : Finsupp.weight (blockWeight ι) e k = (m k).toNat := congrFun h k
          have := hm k
          show ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k
          omega
      simp only [hiff]
    rw [e]
    exact hJ f hf _
  · push Not at hm
    obtain ⟨k, hk⟩ := hm
    have e : weightedHomogeneousComponent (intWeight (ι := ι)) m f = 0 := by
      ext e
      rw [coeff_weightedHomogeneousComponent, weight_intWeight, coeff_zero, if_neg]
      intro h
      have e1 : ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) = m k := congrFun h k
      omega
    rw [e]
    exact J.zero_mem

theorem isMultiHomogIdeal_sup_X {q : Ideal (MRing ι F)} (hq : IsMultiHomogIdeal q)
    (v : Σ k, ι k) : IsMultiHomogIdeal (q ⊔ Ideal.span {(X v : MRing ι F)}) := by
  classical
  intro f hf n
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hX : IsMultiHomog (X v : MRing ι F) (blockWeight ι v) :=
    isWeightedHomogeneous_X F (blockWeight ι) v
  rw [map_add, GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide.component_mul_form hX t n]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hq p hp n)) ?_
  split_ifs
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩)
  · exact zero_mem _

def quotPiece (J : Ideal (MRing ι F)) (m : K → ℤ) : Submodule F (MRing ι F ⧸ J) :=
  (ringPiece m).map (Ideal.Quotient.mkₐ F J).toLinearMap

theorem quotPiece_natCast (J : Ideal (MRing ι F)) (a : K → ℕ) :
    quotPiece J (fun k => (a k : ℤ)) = gradedPiece J a := by
  rw [quotPiece, gradedPiece, ringPiece_natCast]

theorem isMultigrading_quotPiece [Fintype K] {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) :
    IsMultigrading ι (MRing ι F ⧸ J) (quotPiece J) where
  internal := by
    classical
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
      intro s v hv hsum m hm
      have hex : ∀ i ∈ s, ∃ y ∈ ringPiece (F := F) (ι := ι) i,
          (Ideal.Quotient.mkₐ F J).toLinearMap y = v i := fun i hi => Submodule.mem_map.mp (hv i hi)
      choose! x hx hxv using hex
      have hy : (∑ i ∈ s, x i) ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
        rw [← hsum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← hxv i hi]
        rfl
      have hc := component_intWeight_mem hJ hy m
      rw [map_sum] at hc
      have hcs : (∑ i ∈ s, weightedHomogeneousComponent (intWeight (ι := ι)) m (x i)) = x m := by
        rw [Finset.sum_eq_single m]
        · rw [weightedHomogeneousComponent_of_mem (hx m hm), if_pos rfl]
        · intro j hj hjm
          rw [weightedHomogeneousComponent_of_mem (hx j hj), if_neg (Ne.symm hjm)]
        · intro h
          exact absurd hm h
      rw [hcs] at hc
      rw [← hxv m hm]
      simpa [Ideal.Quotient.eq_zero_iff_mem] using hc
    · show (⨆ m, (ringPiece (F := F) (ι := ι) m).map (Ideal.Quotient.mkₐ F J).toLinearMap) = ⊤
      rw [← Submodule.map_iSup]
      show Submodule.map _ (⨆ i, weightedHomogeneousSubmodule F (intWeight (ι := ι)) i) = ⊤
      rw [(weightedDecomposition F (intWeight (ι := ι))).isInternal.submodule_iSup_eq_top,
        Submodule.map_top, LinearMap.range_eq_top]
      exact Ideal.Quotient.mkₐ_surjective F J
  smul_mem := by
    intro v m x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    refine Submodule.mem_map.mpr ⟨(X v : MRing ι F) • y, isMultigrading_ring.smul_mem v m y hy, ?_⟩
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, smul_eq_mul, map_mul]
    rfl

theorem proof (hrec : IntersectionRecursion.Statement.{u}) : HilbertIncrement.Statement.{u} := by
  intro d hmod F _ K _ _ ι _ q hq hdim b
  obtain ⟨i, hi⟩ := hq.relevant b
  have hJ : IsMultiHomogIdeal (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) :=
    isMultiHomogIdeal_sup_X hq.multiHomog ⟨b, i⟩
  obtain ⟨hstep, hsupp⟩ :=
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.HilbertIncrement.closed.{u} F K ι (d + 1) q b i hq
      hdim (by omega) hi
  obtain ⟨a₀, C, hbd⟩ := hmod F K ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}))
    (quotPiece _) (isMultigrading_quotPiece hJ) (fun W hW hann => by
      rw [Ideal.annihilator_quotient] at hann
      simpa using hsupp W hW hann)
  refine ⟨a₀, C, fun a ha => ?_⟩
  have h1 : hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) =
      (Module.finrank F (quotPiece (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})
        fun k => (a k : ℤ)) : ℤ) := by
    rw [show unitDeg b = Pi.single b 1 from rfl, hstep, hilbFn,
      if_pos (fun k => Nat.cast_nonneg _), quotPiece_natCast]
    have ha' : (fun k => ((a k : ℤ)).toNat) = a := funext fun k => by omega
    rw [ha']
  have h2 : intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) =
      topCycleNum F ι (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) d
        (fun _ => fun k => (a k : ℤ)) := by
    rw [hrec F K ι q d hq hdim b i hi]
    unfold topCycleNum
    refine finsum_congr fun W => ?_
    have hann : Module.annihilator (MRing ι F)
        (MRing ι F ⧸ (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)})) =
        q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} := Ideal.annihilator_quotient
    by_cases hc : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
    · rw [dif_pos hc, dif_pos (by rw [hann]; exact hc)]
      rfl
    · rw [dif_neg hc, dif_neg (by rw [hann]; exact hc)]
  rw [h1, h2]
  simpa using hbd a ha

end HilbertIncrement

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPieceIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

noncomputable section

theorem ptsIntegral_congr_integrand {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g g' : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ z ∈ mcPts P, g z = g' z) : ptsIntegral P φ g = ptsIntegral P φ g' := by
  unfold ptsIntegral ptsIntegralAt
  split_ifs with hΨ
  · have hd : ∀ y w, sheetDensity P hΨ.choose φ g y w = sheetDensity P hΨ.choose φ g' y w := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1]
      · rfl
    simp only [hd]
  · rfl

theorem PieceIntegral.proof (h : ClopenDegree.Statement) : PieceIntegral.Statement := by
  intro K _ _ ι _ P e L I hP hL hPI hopen
  set Z : Set ((Σ k, ι k) → ℂ) := {z | ∀ f ∈ I, eval z f = 0} with hZ
  set A := Z ∩ mcPts P with hA
  have h1 : ptsIntegral P (pot L) (Z.indicator fun _ => (1 : ℝ)) =
      ptsIntegral P (pot L) (A.indicator fun _ => (1 : ℝ)) := by
    refine ptsIntegral_congr_integrand P _ fun z hz => ?_
    by_cases hzZ : z ∈ Z
    · rw [Set.indicator_of_mem hzZ, Set.indicator_of_mem (show z ∈ A from ⟨hzZ, hz⟩)]
    · rw [Set.indicator_of_notMem hzZ, Set.indicator_of_notMem fun h' => hzZ h'.1]
  have hZc : IsClosed Z := by
    have hZi : Z = ⋂ f ∈ I, {z | eval z f = 0} := by
      ext z
      simp [hZ]
    rw [hZi]
    exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval f) continuous_const
  have hcl : IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) := by
    constructor
    · have hpre : (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) = (↑) ⁻¹' Z := by
        ext ⟨z, hz⟩
        simp [hA]
      rw [hpre]
      exact hZc.preimage continuous_subtype_val
    · rw [isOpen_iff_mem_nhds]
      rintro ⟨z, hz⟩ ⟨hzZ, -⟩
      rw [nhds_subtype]
      exact ((hopen z hz hzZ).comap Subtype.val).mono fun y hy => ⟨hy y.2, y.2⟩
  have hAeq : A = zeroLocus ℂ I ∩ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp only [hA, hZ, mcPts, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_zeroLocus_iff, aeval_eq_eval]
    constructor
    · rintro ⟨hz, hU, -⟩
      exact ⟨hz, hU⟩
    · rintro ⟨hz, hU⟩
      exact ⟨hz, hU, fun f hf => hz _ (hPI (Ideal.mem_map_of_mem _ hf))⟩
  rw [h1, h K ι P e L A hP hL Set.inter_subset_right hcl, intNum_radical_eq_offBlocks, hAeq]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ClopenComponents.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (A : Set ((Σ k, ι k) → ℂ)),
    IsArithVar P (e + 1) → A ⊆ mcPts P → IsClopen (((↑) : mcPts P → (Σ k, ι k) → ℂ) ⁻¹' A) →
    ∃ S : Finset (Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      (∀ W ∈ S, W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) ∧
      A = mcPts P ∩ ⋃ W ∈ S, zeroLocus ℂ W ∧
      vanishingIdeal ℂ A = ⨅ W ∈ S, W

section Inhabitants

open GroundTheory.Heights₂.Heights.Inter

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreDimGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegreDimGe.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ((e + 1 : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreHilb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegreHilb.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (n : ℤ),
    hilbFn (segrePrime F q) (fun _ : Unit => n) = hilbFn q (fun _ : K => n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegrePrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def SegrePrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] [Nonempty K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    IsMultiProjPrime (segrePrime F q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

