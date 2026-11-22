import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Comparison
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenter

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.Height
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField
open scoped ContDiff

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace HermLine

def standardPow (m : ι → ℕ) : HermLine n where
  deg k := m k
  metric z := ∏ k, l2Norm (z k) ^ m k
  metric_pos z hz := Finset.prod_pos fun k _ ↦ pow_pos (vectorL2Norm_pos (hz k)) _
  metric_smul c z _ _ := by
    simp only [vectorL2Norm_const_mul, mul_pow, Finset.prod_mul_distrib, zpow_natCast]
  metric_smooth := contDiffOn_prod fun k _ ↦ (contDiffOn_l2Norm_block k).pow _

end HermLine

theorem height_mul (A B : HermLine n) {x : Cone n (AlgebraicClosure ℚ)} (hx : BlockNonzero x) :
    height (A.mul B) x = height A x + height B x := by
  have hA := finite_support_height A x hx
  have hB := finite_support_height B x hx
  have hfin : (∑ᶠ v : FinitePlace (coordField x),
      ∑ k, ((A.mul B).deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) =
      (∑ᶠ v : FinitePlace (coordField x),
        ∑ k, (A.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i))) +
      ∑ᶠ v : FinitePlace (coordField x),
        ∑ k, (B.deg k : ℝ) * Real.log (⨆ i, v (coordVec x k i)) := by
    rw [← finsum_add_distrib hA hB]
    refine finsum_congr fun v ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [HermLine.mul, Pi.add_apply, Int.cast_add]
    ring
  have hinf : (∑ σ : coordField x →+* ℂ,
      Real.log ((A.mul B).metric fun k i ↦ σ (coordVec x k i))) =
      (∑ σ : coordField x →+* ℂ, Real.log (A.metric fun k i ↦ σ (coordVec x k i))) +
      ∑ σ : coordField x →+* ℂ, Real.log (B.metric fun k i ↦ σ (coordVec x k i)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    exact Real.log_mul (A.metric_pos _ (blockNonzero_sigma hx σ)).ne'
      (B.metric_pos _ (blockNonzero_sigma hx σ)).ne'
  unfold height
  rw [hfin, hinf]
  ring

def HeightAsIntersection.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ),
    Geo.IsIntersectionFamily II → ∀ (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x →
    height A x = II (orbitIdeal x) 1 ![A.toGeo] / Geo.degC (ι := blockIdx n) (orbitIdeal x)

theorem HeightAsIntersection.proof (h₁ : OrbitCurve.Statement) (h₂ : OrbitDegree.Statement)
    (h₃ : HeightRecR.Statement) : HeightAsIntersection.Statement := by
  intro ι _ _ _ n II hII A x hx
  obtain ⟨-, hAdd, hR⟩ := hII
  have hW : Geo.IsArithVar (ι := blockIdx n) (orbitIdeal x) (0 + 1) := h₁ ι n x hx
  have hdeg : (0 : ℝ) < Geo.degC (ι := blockIdx n) (orbitIdeal x) := by
    exact_mod_cast h₂ ι n x hx
  obtain ⟨c, hc⟩ := exists_chart hx
  have hsnoc : ∀ B : Geo.HermLine (blockIdx n),
      (Fin.snoc (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) B : Fin 1 → _) = ![B] := by
    intro B
    funext i
    fin_cases i
    rfl
  have hL : ∀ j : Fin 0, Geo.IsSmoothHerm ((Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) j) :=
    fun j ↦ j.elim0
  have key : ∀ (B : HermLine n) (d : ι → ℕ), (∀ k, B.deg k = d k) →
      II (orbitIdeal x) 1 ![B.toGeo] = Geo.degC (ι := blockIdx n) (orbitIdeal x) * height B x := by
    intro B d hd
    have h := hR (orbitIdeal x) 0 Fin.elim0 B.toGeo (chartMonomial c d) d hW hL
      B.isSmoothHerm_toGeo hd ((geoMultiHomog_iff _ d).mpr (isWeightedHomogeneous_chartMonomial c d))
      (chartMonomial_notMem_orbitIdeal x c hc d)
    rw [hsnoc] at h
    exact h.trans (h₃ ι n II B x _ hx (isSectionOn_chartMonomial B x c hc d hd))
  let m : ι → ℕ := fun k ↦ (A.deg k).natAbs
  have hB := key (HermLine.standardPow m) m fun k ↦ rfl
  have hAB := key (A.mul (HermLine.standardPow m)) (fun k ↦ (A.deg k + m k).toNat) fun k ↦ by
    simp only [HermLine.mul, HermLine.standardPow, Pi.add_apply, m]
    omega
  have hadd := hAdd (orbitIdeal x) 0 Fin.elim0 A.toGeo (HermLine.standardPow m).toGeo hW hL
    A.isSmoothHerm_toGeo (HermLine.standardPow m).isSmoothHerm_toGeo
  rw [hsnoc, hsnoc, hsnoc, ← HermLine.toGeo_mul] at hadd
  have hadd' : II (orbitIdeal x) 1 ![(A.mul (HermLine.standardPow m)).toGeo] =
      II (orbitIdeal x) 1 ![A.toGeo] + II (orbitIdeal x) 1 ![(HermLine.standardPow m).toGeo] :=
    hadd
  rw [hAB, hB, height_mul A _ hx] at hadd'
  rw [eq_div_iff hdeg.ne']
  linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterDivSupp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial

def OrbitCenterDivSupp.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ),
    BlockNonzero x → Geo.IsMultiHomog (ι := blockIdx n) s a → s ∉ orbitIdeal x →
    ∀ v : FinitePlace (coordField x), s ∈ orbitCenter x v →
      orbitCenter x v ∈ Geo.divSupp (orbitIdeal x) s

theorem exists_finitePlace_two_lt_one (K : Type) [Field K] [NumberField K] :
    ∃ v : FinitePlace K, v 2 < 1 := by
  have : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K)
    (Ideal.span {(2 : ℤ)}) ⊥ (fun a ha ↦ by
      rw [Ideal.mem_comap, Ideal.mem_bot,
        map_eq_zero_iff _ (algebraMap ℤ (𝓞 K)).injective_int] at ha
      simp [ha])
  have h2 : (2 : 𝓞 K) ∈ Q := by
    have : (2 : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self 2
    simpa using this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at h2
    exact two_ne_zero h2
  refine ⟨FinitePlace.mk ⟨Q, hQ, hne⟩, ?_⟩
  rw [FinitePlace.mk_apply, show (2 : K) = algebraMap (𝓞 K) K 2 from (map_ofNat _ 2).symm]
  exact (FinitePlace.norm_lt_one_iff_mem (K := K)
    (v := (⟨Q, hQ, hne⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (2 : 𝓞 K)).mpr h2

example : ∃ v : FinitePlace (coordField samplePoint), BlockNonzero samplePoint ∧
    Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 1) 1) 1 ∧
    chartMonomial (fun _ ↦ 1) 1 ∉ orbitIdeal samplePoint ∧
    chartMonomial (fun _ ↦ 1) 1 ∈ orbitCenter samplePoint v := by
  obtain ⟨v, hv⟩ := exists_finitePlace_two_lt_one (coordField samplePoint)
  refine ⟨v, samplePoint_blockNonzero,
    (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _),
    chartMonomial_notMem_orbitIdeal _ _ (fun _ ↦ by simp [samplePoint]) 1, ?_⟩
  have hX : chartMonomial (n := fun _ : Unit ↦ 1) (fun _ ↦ 1) 1 = X ⟨(), 1⟩ := by
    simp [chartMonomial]
  rw [hX]
  refine X_mem_orbitCenter _ _ () 1 ?_
  have h1 : coordVec samplePoint () 1 = 2 :=
    Subtype.ext (by simp [coordVec, samplePoint]; rfl)
  have h0 : coordVec samplePoint () 0 = 1 := Subtype.ext (by simp [coordVec, samplePoint])
  rw [h1]
  calc v 2 < 1 := hv
    _ = v (coordVec samplePoint () 0) := by rw [h0, map_one]
    _ ≤ ⨆ j, v (coordVec samplePoint () j) :=
      le_ciSup (f := fun j ↦ v (coordVec samplePoint () j)) (Set.finite_range _).bddAbove 0

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterLe.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ),
    Geo.IsMultiHomog (ι := blockIdx n) F d →
      v (evalCone (coordVec x) F) ≤ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k

example : Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 0) 1) 1 :=
  (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterMemIff.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → ∀ (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ)
      (d : ι → ℕ), Geo.IsMultiHomog (ι := blockIdx n) F d →
      (F ∈ orbitCenter x v ↔ v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k)

example : BlockNonzero samplePoint ∧
    Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 0) 1) 1 :=
  ⟨samplePoint_blockNonzero, (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _)⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterPrime.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → ∀ v : FinitePlace (coordField x), (orbitCenter x v).IsPrime

example : BlockNonzero samplePoint := samplePoint_blockNonzero

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitCenterZero.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ v : FinitePlace (coordField x), orbitCenter x v ∉ Geo.divSupp (orbitIdeal x) s →
      finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) = 0

example : BlockNonzero samplePoint ∧
    Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
      (chartMonomial (fun _ ↦ 0) 1) :=
  ⟨samplePoint_blockNonzero,
    isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl)⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) (p : Coord n) :
    ratioField x :=
  ⟨x p.1 p.2 / x p.1 (c p.1), div_mem_ratioField x p.1 p.2 (c p.1)⟩

def chartRing (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    Subalgebra ℤ (ratioField x) :=
  Algebra.adjoin ℤ (Set.range (chartRatio x c))

def chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1)) :
    MvPolynomial (Coord n) ℤ →ₐ[ℤ] chartRing x c :=
  aeval fun p ↦ ⟨chartRatio x c p, Algebra.subset_adjoin (Set.mem_range_self p)⟩

def chartPoint (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (V : Ideal (MvPolynomial (Coord n) ℤ)) : Ideal (chartRing x c) :=
  Ideal.map (chartEval x c) V

def AbsCentredAt {L : Type*} [Field L] (O : Subalgebra ℤ L) (m : Ideal O) (φ : L → ℝ) : Prop :=
  (∀ u : O, φ u ≤ 1) ∧ ∀ u : O, φ u < 1 ↔ u ∈ m

def localQuotLength {O : Type*} [CommRing O] (m : Ideal O) [m.IsPrime] (f : O) : ℕ :=
  (Module.length (Localization.AtPrime m)
    (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f})).toNat

example : ((chartEval samplePoint (fun _ ↦ 0) (X ⟨(), 1⟩) : ratioField samplePoint) :
    AlgebraicClosure ℚ) = 2 := by
  simp [chartEval, chartRatio, samplePoint]

open Classical in

example {L : Type*} [Field L] (O : Subalgebra ℤ L) :
    AbsCentredAt O ⊥ fun t ↦ if t = 0 then 0 else 1 := by
  refine ⟨fun u ↦ by dsimp only; split_ifs <;> norm_num, fun u ↦ ?_⟩
  rw [Ideal.mem_bot]
  constructor
  · intro h
    dsimp only at h
    split_ifs at h with h0
    · exact Subtype.ext h0
    · exact absurd h (lt_irrefl 1)
  · rintro rfl
    simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegreeRatio
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitDegreeRatio.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (x : Cone n (AlgebraicClosure ℚ)), BlockNonzero x →
    Geo.degC (ι := blockIdx n) (orbitIdeal x) = Module.finrank ℚ (ratioField x)

example : BlockNonzero samplePoint := samplePoint_blockNonzero

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitLocalSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

def OrbitLocalSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s,
      (Module.finrank ℚ (coordField x) : ℝ) *
          ((Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
            ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V))) =
        (Module.finrank ℚ (ratioField x) : ℝ) *
          ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
            (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)))

example : BlockNonzero samplePoint ∧
    Geo.IsSectionOn (orbitIdeal samplePoint) (HermLine.standard _).toGeo
      (chartMonomial (fun _ ↦ 0) 1) :=
  ⟨samplePoint_blockNonzero,
    isSectionOn_chartMonomial _ _ _ (fun _ ↦ by simp [samplePoint]) 1 (fun _ ↦ rfl)⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

omit [DecidableEq ι] in

theorem mConeMap_of_isMultiHomog {Ω : Type*} [Field Ω] (y : Coord n → Ω)
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) :
    Geo.mConeMap (ι := blockIdx n) y s = C (eval₂ (Int.castRingHom Ω) y s) * ∏ k, X k ^ a k := by
  classical
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum, eval₂_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hmon : ∏ p ∈ m.support, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, X k ^ a k := by
    rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hs m hm k]
  rw [Geo.mConeMap, aeval_monomial, eval₂_monomial, Finsupp.prod, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, hmon, map_mul, map_prod, map_pow, eq_intCast,
    map_intCast]
  ring

theorem evalCone_coordVec_ne_zero (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (hW : s ∉ orbitIdeal x) :
    evalCone (coordVec x) s ≠ 0 := by
  intro h
  apply hW
  have e : eval₂ (Int.castRingHom (AlgebraicClosure ℚ)) (flatCone x) s =
      algebraMap (coordField x) (AlgebraicClosure ℚ) (evalCone (coordVec x) s) := by
    rw [← evalCone_map]
    rfl
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ s a hs, e, h,
    map_zero, map_zero, zero_mul]

theorem HeightRecR.proof (hV : OrbitDivVertical.Statement) (hF : OrbitFiniteSum.Statement)
    (hA : OrbitArchSum.Statement) : HeightRecR.Statement := by
  intro ι _ _ _ n I A x s hx hs
  obtain ⟨a, _, hsa, hsW⟩ := id hs
  have ht : evalCone (coordVec x) s ≠ 0 := evalCone_coordVec_ne_zero x s a hsa hsW
  have e1 : Geo.recR I (orbitIdeal x) (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) A.toGeo s =
      (∑ᶠ V ∈ Geo.divSupp (orbitIdeal x) s,
        (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V))) -
      Geo.arInt (orbitIdeal x) s A.toGeo (Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) := by
    unfold Geo.recR
    congr 1
    refine finsum_mem_congr rfl fun V hV' ↦ ?_
    rw [if_neg (hV ι n A x s hx hs V hV')]
    congr 4
    funext j
    exact j.elim0
  have hpos : ∀ σ : coordField x →+* ℂ, 0 < A.metric (fun k i ↦ σ (coordVec x k i)) :=
    fun σ ↦ A.metric_pos _ (blockNonzero_sigma hx σ)
  have e2 : ∀ σ : coordField x →+* ℂ,
      Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
          A.metric (fun k i ↦ σ (coordVec x k i))) =
        Real.log ‖σ (evalCone (coordVec x) s)‖ -
          Real.log (A.metric (fun k i ↦ σ (coordVec x k i))) := fun σ ↦ by
    rw [evalCone_map, Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr ht)) (hpos σ).ne']
  have hsupp1 : (Function.support fun v : FinitePlace (coordField x) ↦
      finiteTerm A v (coordVec x)).Finite := finite_support_height A x hx
  have hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦
      Real.log (v (evalCone (coordVec x) s))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  have hprod := sum_log_places_eq_zero ht
  rw [e1, hF ι n A x s hx hs, hA ι n A x s hx hs, finsum_sub_distrib hsupp1 hsupp2,
    Finset.sum_congr rfl fun σ _ ↦ e2 σ, Finset.sum_sub_distrib, height]
  simp only [finiteTerm]
  linear_combination (-((Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) /
    Module.finrank ℚ (coordField x))) * hprod

end

end GroundTheory.Heights₂.Heights
end

