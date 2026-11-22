import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.FiniteIntegralClosureCharZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0044
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNormalLocusRep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace NormalLocusRep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_mul_zpow_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g d) : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ chartRingZ y c := by
  rw [NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  refine ⟨⟨_, aeval_mul_zpow_mem y c hg⟩, ⟨_, aeval_mul_zpow_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem charZero_of_isHorizontal (y : (Σ k, ι k) → Ω) (hH : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    show mConeMap y (C (n : ℤ)) = 0
    rw [mConeMap, aeval_C, MvPolynomial.algebraMap_apply]
    simp [hn]
  rw [hH, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem charZero_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : CharZero (chartRingZ y c) :=
  charZero_of_inj_zero fun n hn => by
    have : ((n : chartRingZ y c) : Ω) = 0 := by rw [hn]; rfl
    exact_mod_cast this

theorem finiteType_chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Algebra.FiniteType ℤ (chartRingZ y c) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

theorem exists_conductor [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ a ∈ chartRingZ y c, a ≠ 0 ∧ ∀ t ∈ integralClosure (chartRingZ y c) Ω, a * t ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have := charZero_chartRingZ y c
  have := finiteType_chartRingZ y c
  have : Module.Finite A (integralClosure A Ω) :=
    Model.finite_integralClosure_fractionRing_of_charZero A Ω
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule A (integralClosure A Ω)).FG)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (S.image ((↑) : integralClosure A Ω → Ω))
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h0)
  refine ⟨((b : A) : Ω), (b : A).2, hb0, fun t ht => ?_⟩
  have htop : (⟨t, ht⟩ : integralClosure A Ω) ∈ Submodule.span A (S : Set (integralClosure A Ω)) := by
    rw [hS]; trivial
  suffices key : ∀ x ∈ Submodule.span A (S : Set (integralClosure A Ω)), ((b : A) : Ω) * (x : Ω) ∈ A from
    key _ htop
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr⟩ := hb (x : Ω) (Finset.mem_image_of_mem _ hx)
    rw [show ((b : A) : Ω) * (x : Ω) = (b : A) • (x : Ω) by rw [Algebra.smul_def]; rfl, ← hr]
    exact r.2
  | zero => simp
  | add x z _ _ hx hz =>
    simp only [Subalgebra.coe_add, mul_add]
    exact add_mem hx hz
  | smul r x _ hx =>
    have : ((b : A) : Ω) * ((r • x : integralClosure A Ω) : Ω) = (r : Ω) * (((b : A) : Ω) * (x : Ω)) := by
      rw [Subalgebra.coe_smul, Algebra.smul_def]
      show _ * ((r : Ω) * _) = _
      ring
    rw [this]
    exact mul_mem r.2 hx

omit [Fintype K] in

theorem isMultiHomog_prod {J : Type} (s : Finset J) (H : J → MRing ι) (N : J → K → ℕ)
    (hH : ∀ j ∈ s, IsMultiHomog (H j) (N j)) : IsMultiHomog (∏ j ∈ s, H j) (∑ j ∈ s, N j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocalRep.isMultiHomog_C (ι := ι) 1
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact LocalRep.isMultiHomog_mul (hH j (Finset.mem_insert_self j s))
      (ih fun i hi => hH i (Finset.mem_insert_of_mem hi))

theorem notMem_mCoordIdeal (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hmem
  have h := (RingHom.mem_ker).mp hmem
  erw [ConeTrdeg.mConeMap_of_isMultiHomog y hf] at h
  exact mul_ne_zero (MvPolynomial.C_ne_zero.2 h0)
    (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h

end NormalLocusRep

open NormalLocusRep in

theorem NormalLocusRep.proof : NormalLocusRep.Statement := by
  intro K _ ι _ Ω _ y D hV hbir
  classical
  have := charZero_of_isHorizontal y hV.2.2.1

  have hchart : ∀ c : ∀ k, ι k, ∃ (N : K → ℕ) (H : MRing ι), IsMultiHomog H N ∧ aeval y H ≠ 0 ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ integralClosure (chartRingZ y c) Ω,
        (aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ))) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨a, ha, ha0, hcond⟩ := exists_conductor y hbir c hc
      obtain ⟨N, H, hH, he⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hc ha
      have hP : ∀ N' : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ N' k) ≠ 0 := fun N' =>
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
      have hHa : aeval y H * ∏ k, y ⟨k, c k⟩ ^ (-(N k : ℤ)) = a := by
        rw [he, mul_assoc, ← Finset.prod_mul_distrib]
        rw [Finset.prod_eq_one fun k _ => by
          rw [← zpow_natCast, ← zpow_add₀ (hc k), add_neg_cancel, zpow_zero], mul_one]
      refine ⟨N, H, hH, ?_, fun _ t ht => ?_⟩
      · rw [he]
        exact mul_ne_zero ha0 (hP N)
      · rw [hHa]
        exact hcond t ht
    · exact ⟨0, C 1, LocalRep.isMultiHomog_C 1, by simp, fun h => absurd h hc⟩
  choose N H hH hH0 hcond using hchart
  refine ⟨∑ c, N c, ∏ c, H c, isMultiHomog_prod _ H N fun c _ => hH c,
    notMem_mCoordIdeal y (isMultiHomog_prod _ H N fun c _ => hH c)
      (by rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun c _ => hH0 c), ?_⟩
  intro a τ s hs z hz hfz

  choose c hzc using hz.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hzc k
    have hmem : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      show mConeMap y (X ⟨k, c k⟩) = 0
      simp [mConeMap, h0]
    simpa using hz.2 _ hmem
  have hHz : eval z (map (Int.castRingHom ℂ) (H c)) ≠ 0 := by
    rw [map_prod, map_prod] at hfz
    exact (Finset.prod_ne_zero_iff.mp hfz) c (Finset.mem_univ c)
  have hx := hcond c hyc _ (hs c hyc)
  obtain ⟨M, G, hG, hGe⟩ := LocalRep.exists_form_of_mem_chartRingZ y c hyc hx
  refine ⟨M + (N c + fun k => ((τ : ℤ) * a k).toNat), N c + (M + fun k => (-((τ : ℤ) * a k)).toNat),
    G * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (N c + fun k => ((τ : ℤ) * a k).toNat) k,
    H c * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M + fun k => (-((τ : ℤ) * a k)).toNat) k,
    LocalRep.isMultiHomog_mul hG (LocalRep.isMultiHomog_chartMono c _),
    LocalRep.isMultiHomog_mul (hH c) (LocalRep.isMultiHomog_chartMono c _), fun k => ?_, ?_, ?_⟩
  · simp only [Pi.add_apply]
    push_cast
    omega
  ·
    have hz' : ∀ p q : K → ℤ, (∏ k, y ⟨k, c k⟩ ^ p k) * ∏ k, y ⟨k, c k⟩ ^ q k =
        ∏ k, y ⟨k, c k⟩ ^ (p k + q k) := fun p q => by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => (zpow_add₀ (hyc k) _ _).symm
    have hnat : ∀ p : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ p k) = ∏ k, y ⟨k, c k⟩ ^ (p k : ℤ) := fun p =>
      Finset.prod_congr rfl fun k _ => (zpow_natCast _ _).symm
    have key : (∏ k, y ⟨k, c k⟩ ^ (-(N c k : ℤ))) * (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k))) *
        (∏ k, y ⟨k, c k⟩ ^ M k) * (∏ k, y ⟨k, c k⟩ ^ (N c k + ((τ : ℤ) * a k).toNat)) =
        ∏ k, y ⟨k, c k⟩ ^ (M k + (-((τ : ℤ) * a k)).toNat) := by
      simp only [hnat]
      rw [hz', hz', hz']
      refine Finset.prod_congr rfl fun k _ => ?_
      congr 1
      push_cast
      omega
    simp only [map_mul, map_prod, map_pow, aeval_X, Pi.add_apply]
    rw [hGe]
    linear_combination (s * aeval y (H c)) * key
  · simp only [map_mul, map_prod, map_pow, map_X, eval_X]
    exact mul_ne_zero hHz (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hzc k))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Set MeasureTheory Manifold EmbeddingWeight

noncomputable section

namespace PiecesAdditiveAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_weight {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {J : Type} [Fintype J]
    {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    ∃ u : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
      (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) ∧
      ∀ z ∈ mcPts P, u z = (S i).indicator (fun _ => (1 : ℝ)) z := by
  classical
  let T : J → Set ((Σ k, ι k) → ℂ) := fun j => mcPts P ∩ S j ∩ {z | ∀ k, blockNormSq z k = 1}
  let C : J → Set ((Σ k, ι k × ι k) → ℂ) := fun j => projPt '' T j
  have hT : ∀ j, IsCompact (T j) := by
    intro j
    refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
    have : T j = ({z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} ∩ S j) ∩
        {z | ∀ k, blockNormSq z k = 1} := by
      ext z
      simp only [T, mcPts, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
        by_contra hcon
        push Not at hcon
        have := h3 k
        simp [blockNormSq, hcon] at this
    rw [this]
    exact ((isClosed_zeros P).inter (hS j)).inter isCompact_sphere.isClosed
  have hC : ∀ j, IsCompact (C j) := fun j =>
    (hT j).image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hmem : ∀ j, ∀ z ∈ mcPts P, z ∈ S j → projPt z ∈ C j := by
    intro j z hz hzj
    obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1
    exact ⟨_, ⟨⟨mcPts_smul hP c hc hz, hsm j c z hc hzj⟩, hc1⟩, projPt_smul c hc z⟩
  have hdisj : ∀ j j', j ≠ j' → Disjoint (C j) (C j') := by
    intro j j' hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨⟨hzP, hzs⟩, -⟩, rfl⟩ ⟨w, ⟨⟨hwP, hwt⟩, -⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (hsm j c z hc hzs) hwt)
  obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
    (isClosed_biUnion_finset fun j _ => (hC j).isClosed) (hC i).isClosed
    (Set.disjoint_iUnion₂_left.2 fun j hj => hdisj j i (Finset.ne_of_mem_erase hj))
  refine ⟨fun z => f (projPt z), ?_, fun c z hc => by simp only [projPt_smul c hc], ?_⟩
  · exact (contMDiff_iff_contDiff.mp f.contMDiff).comp_contDiffOn contDiffOn_projPt
  · intro z hz
    obtain ⟨j, hj, -⟩ := huniq z hz
    by_cases hji : j = i
    · subst hji
      rw [Set.indicator_of_mem hj]
      exact h1.self_of_nhdsSet _ (hmem j z hz hj)
    · have hzi : z ∉ S i := fun h => hji ((huniq z hz).unique hj h)
      rw [Set.indicator_of_notMem hzi]
      exact h0.self_of_nhdsSet _
        (Set.mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩, hmem j z hz hj⟩)

omit [∀ k, Fintype (ι k)] in

theorem sheetDensity_sum (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {J : Type} [Fintype J] (c : J → ℝ) (g : J → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ i, c i * g i z) y w = ∑ i, c i * sheetDensity P Ψ φ (g i) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp

theorem integrable_piece (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    {J : Type} [Fintype J] {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y,
      sheetDensity P Ψ (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w) := by
  obtain ⟨u, hus, hui, hu⟩ := exists_weight hP.2.1.2.1 hS hsm huniq i
  let B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := HermLine.ofWeight u hui
  have hB : IsSmoothHerm B := Real.contDiff_exp.comp_contDiffOn hus.neg
  have hlog : ∀ z, logNorm B 1 z = u z := by
    intro z
    simp [logNorm, B, HermLine.ofWeight]
  have hhom : IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hsec : IsSectionOn P B 1 := ⟨0, fun k => by simp [B, HermLine.ofWeight], hhom, hnot⟩
  refine (hInt K ι P e Ψ L B 1 hP hΨ hL hB hsec).congr (Eventually.of_forall fun y => ?_)
  refine finsum_mem_congr rfl fun w _ => ?_
  exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.sheetDensity_congr_mcPts P Ψ (fun _ _ _ => rfl)
    (fun z hz => (hlog z).trans (hu z hz)) y w

end PiecesAdditiveAlt

open PiecesAdditiveAlt in

theorem PiecesAdditive.proof (hInt : PtsIntegrableStatement) : PiecesAdditive.Statement := by
  intro K _ ι _ P e L J _ S c hP hL hS hsm huniq
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hlin : ∀ y, (∑ᶠ w ∈ fibre P hΨ.choose y, sheetDensity P hΨ.choose (pot L)
        (fun z => ∑ i, c i * (S i).indicator (fun _ => (1 : ℝ)) z) y w) =
        ∑ i, c i * ∑ᶠ w ∈ fibre P hΨ.choose y,
          sheetDensity P hΨ.choose (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w := by
      intro y
      have hfin := fibreFinite K ι P e _ hP hΨ.choose_spec y
      simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, sheetDensity_sum, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [hlin]
    rw [integral_finsetSum _ fun i _ =>
      (integrable_piece hInt hP hΨ.choose_spec hL hS hsm huniq i).const_mul (c i)]
    simp only [integral_const_mul]
  · simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric Real

noncomputable section

theorem integral_polydisc_gauss (D n : ℕ) (lam : Fin D → ℝ) (R : ℝ) (hn : 0 < n) (hR : 0 < R) :
    ∫ z in closedBall (0 : Fin D → ℂ) (R / Real.sqrt n),
        Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) =
      ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hρ : 0 < R / Real.sqrt n := div_pos hR (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hsq : (R / Real.sqrt n) ^ 2 = R ^ 2 / n := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hball : closedBall (0 : Fin D → ℂ) (R / Real.sqrt n) =
      Set.univ.pi fun _ => closedBall (0 : ℂ) (R / Real.sqrt n) := by
    rw [closedBall_pi _ hρ.le]
    rfl
  have hw : ∀ z : Fin D → ℂ, Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) =
      ∏ j, Real.exp (-((n : ℝ) * lam j) * ‖z j‖ ^ 2) := by
    intro z
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hfac : ∀ j, ∫ x in closedBall (0 : ℂ) (R / Real.sqrt n),
      Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2) = gaussDiscMass (lam j) R * (n : ℝ)⁻¹ := by
    intro j
    rw [integral_closedBall_gauss _ _ hρ.le, gaussDiscMass]
    by_cases hl : lam j = 0
    · rw [if_pos (by simp [hl]), if_pos hl, hsq]
      ring
    · have hnl : (n : ℝ) * lam j ≠ 0 := mul_ne_zero hn' hl
      rw [if_neg hnl, if_neg hl, hsq]
      have e : -((n : ℝ) * lam j) * (R ^ 2 / n) = -lam j * R ^ 2 := by
        field_simp
      rw [e]
      field_simp
  simp_rw [hw]
  rw [hball, volume_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod
    (fun (j : Fin D) (x : ℂ) => Real.exp (-((n : ℝ) * lam j) * ‖x‖ ^ 2))]
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow,
    mul_comm]

theorem PolydiscSubmean.proof : PolydiscSubmean.Statement := by
  intro D n lam R f hn hR _ hf
  set w : (Fin D → ℂ) → ℝ := fun z => Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2) with hwdef
  have hwc : Continuous w := by
    rw [hwdef]
    fun_prop
  have hw0 : ∀ z, 0 ≤ w z := fun z => (Real.exp_pos _).le
  have hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z := by
    intro u z
    simp only [hwdef, Pi.smul_apply, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
  have h := sq_norm_mul_setIntegral_le hf hwc hw0 hrot
  simp only [hwdef] at h
  rw [integral_polydisc_gauss D n lam R hn hR, ← mul_assoc] at h
  exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionSupBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

namespace ResolutionSupBound

theorem eval_smul_homog {ι : Type*} {f : MvPolynomial ι ℂ} {n : ℕ} (hf : f.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) f = c ^ n * eval z f := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : e.degree = n := by
    by_contra h
    exact (mem_support_iff.mp he) (hf.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : e.degree = ∑ i ∈ e.support, e i := rfl
  rw [← hdeg, hs]
  ring

theorem ptNorm_smul {ι : Type*} (m : ConeMetric ℂ ι) {n : ℕ} {f : MvPolynomial ι ℂ} (hf : f.IsHomogeneous n)
    {c : ℂ} (hc : c ≠ 0) (z : ι → ℂ) :
    ptNorm m (RingHom.id ℂ) n f (c • z) = ptNorm m (RingHom.id ℂ) n f z := by
  have hc' : (0 : ℝ) < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc) n
  simp only [ptNorm, MvPolynomial.map_id, eval_smul_homog hf, m.smul, norm_mul, norm_pow, mul_pow]
  exact mul_div_mul_left _ _ hc'.ne'

theorem proof (hI : ResolutionImageSup.Statement) (hND : NonvanishingDense.Statement) :
    ResolutionSupBound.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨C, hC⟩ := hI D Ω κ d
  refine ⟨C, fun n hn f hf z hz => ?_⟩
  set B := C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧ eval w (map (Int.castRingHom ℂ) g) ≠ 0}
  have hzm : z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := by
    refine ⟨fun _ => ?_, hz.2⟩
    by_contra h
    simp only [not_exists, not_not] at h
    exact hz.1 (funext fun q => h q.2)
  have hzS : z ∈ closure S := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hzm
  have key : ∀ w ∈ S, ptNorm d.m (RingHom.id ℂ) n f w ≤ B := by
    rintro w ⟨hw, hwg⟩
    obtain ⟨y, c, hc, hyc⟩ := d.R.surj w hw fun h => hwg (h.2 g hgJ)
    have hy : resPt d y = c () • w := by
      rw [resPt, hyc]
      rfl
    rw [← ptNorm_smul d.m hf (hc ()), ← hy]
    exact hC n hn f hf y
  have hρ : ContinuousAt d.m.ρ z :=
    (d.smooth.continuousOn).continuousAt (isOpen_ne.mem_nhds hz.1)
  have hcont : ContinuousAt (ptNorm d.m (RingHom.id ℂ) n f) z := by
    unfold ptNorm
    simp only [MvPolynomial.map_id]
    exact ((MvPolynomial.continuous_eval f).norm.continuousAt).div (hρ.pow n)
      (pow_pos (d.m.pos z hz.1) n).ne'
  have := mem_closure_iff_nhdsWithin_neBot.1 hzS
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall key)

end ResolutionSupBound

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCoordArithOfFnField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def CoordArithOfFnField.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (d : ℕ),
    Nonempty K' → (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y = blockFnField y' →
    IsArithVar (mCoordIdeal y) d → IsArithVar (mCoordIdeal y') d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

