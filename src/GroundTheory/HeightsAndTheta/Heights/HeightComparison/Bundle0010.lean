import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0005

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  refine isJacobsonRing_iff_prime_eq.mpr fun P hP ↦ ?_
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun a ha ↦ ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at ha
    have h1 := Int.isUnit_iff.mp (ha 1)
    have h2 := Int.isUnit_iff.mp (ha (-1))
    rw [Ideal.mem_bot]
    omega
  · have := hP.isMaximal h
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem natCard_eq_pow_length_of_finiteType (F : Type) [Field F] [Algebra.FiniteType ℤ F]
    (q : ℕ) [CharP F q] :
    q.Prime ∧ Nat.card F = q ^ (Module.length ℤ F).toNat := by
  have := int_isJacobsonRing
  have : Module.Finite ℤ F := finite_of_finite_type_of_isJacobsonRing ℤ F
  have hq : q ≠ 0 := by
    rintro rfl
    have : CharZero F := CharP.charP_to_charZero F
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (fun a b h ↦ by simpa using h) (Field.toIsField F))
  have hqp : q.Prime := (CharP.char_is_prime_or_zero F q).resolve_right hq
  have : Fact q.Prime := ⟨hqp⟩
  let : Algebra (ZMod q) F := ZMod.algebra F q
  have : Module.Finite (ZMod q) F := Module.Finite.of_restrictScalars_finite ℤ (ZMod q) F
  have : Finite F := Module.finite_of_finite (ZMod q)
  have : Fintype F := Fintype.ofFinite F
  refine ⟨hqp, ?_⟩
  rw [Module.length_eq_of_surjective (S := ℤ) (R := ZMod q) (M := F) (ZMod.intCast_surjective),
    Module.length_eq_finrank, ENat.toNat_natCast, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]

theorem OrbitChartResidue.proof (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement)
    (hD : OrbitChartDehom.Statement) : OrbitChartResidue.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have hrel : Geo.IsRelevant V := hV.2
  have hxc : ∀ c' : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → ∀ k, x k (c' k) ≠ 0 := by
    intro c' h k h0
    apply h k
    apply hPV
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h0]
  set i : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose
  have hi : ∀ k, (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) ∉ V := fun k ↦ (hrel k).choose_spec
  obtain ⟨eQ⟩ := hQ ι n x c (hxc c hc) V hPV
  obtain ⟨hchar, ⟨eD⟩⟩ := hD ι n A x s hx hs V hV i c hi hc
  set J := V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) - 1)
  let e : (chartRing x c ⧸ chartPoint x c V) ≃+* (MvPolynomial (Coord n) ℤ ⧸ J) := eQ.trans eD.symm
  have := hM ι n A x s hx hs V hV c hc
  have hfield : IsField (MvPolynomial (Coord n) ℤ ⧸ J) :=
    MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
      e.symm.toMulEquiv
  have : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield
  let : Field (MvPolynomial (Coord n) ℤ ⧸ J) := Ideal.Quotient.field J
  have hft : Algebra.FiniteType ℤ (MvPolynomial (Coord n) ℤ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ J)
      (Ideal.Quotient.mkₐ_surjective ℤ J)
  have : CharP (MvPolynomial (Coord n) ℤ ⧸ J) (Geo.charOf V) := by
    constructor
    intro a
    have hJC : ∀ b : ℤ, ((b : MvPolynomial (Coord n) ℤ ⧸ J) = 0 ↔ b ∈ V.comap (C : ℤ →+* _)) := by
      intro b
      rw [(map_intCast (Ideal.Quotient.mk J) b).symm.trans (congrArg _ (eq_intCast C b).symm),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hchar]
    rw [← Int.cast_natCast, hJC, Submodule.IsPrincipal.mem_iff_generator_dvd, ← Int.natAbs_dvd,
      Int.natCast_dvd_natCast]
    rfl
  obtain ⟨-, hcard⟩ := @natCard_eq_pow_length_of_finiteType (MvPolynomial (Coord n) ℤ ⧸ J) _
    (by convert hft using 1 <;> rfl) (Geo.charOf V) _
  have hgeo : Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 =
      ((Module.length ℤ (MvPolynomial (Coord n) ℤ ⧸ J)).toNat : ℤ) := by
    simp only [Geo.geoNum, dif_pos hrel]
    rfl
  rw [hgeo, Nat.card_congr e.toEquiv, hcard, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

theorem mem_closure_chartRatio (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) (z : ratioField x) :
    z ∈ Subfield.closure (Set.range (chartRatio x c)) := by
  set T := Subfield.closure (Set.range (chartRatio x c))
  let T' : Subfield (AlgebraicClosure ℚ) := T.map (ratioField x).val.toRingHom
  let E : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    T'.toIntermediateField fun q ↦ by
      rw [eq_ratCast]
      exact SubfieldClass.ratCast_mem T' q
  have hE : ratioField x ≤ E := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    refine ⟨chartRatio x c ⟨k, i⟩ / chartRatio x c ⟨k, j⟩,
      div_mem (Subfield.subset_closure (Set.mem_range_self _))
        (Subfield.subset_closure (Set.mem_range_self _)), ?_⟩
    simp [chartRatio, div_div_div_cancel_right₀ (hc k)]
  obtain ⟨t, ht, hzt⟩ := hE z.2
  have : t = z := Subtype.ext hzt
  exact this ▸ ht

theorem OrbitChartRing.proof : OrbitChartRing.Statement := by
  intro ι _ _ n x c hc
  refine ⟨(Subalgebra.fg_iff_finiteType _).mp
    ⟨(Set.finite_range (chartRatio x c)).toFinset, by simp [chartRing]⟩, ?_⟩
  refine (isLocalization_iff _ _).mpr ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} h ↦ ⟨1, ?_⟩⟩
  · refine isUnit_iff_ne_zero.mpr fun h ↦ nonZeroDivisors.coe_ne_zero y ?_
    exact Subtype.ext h
  · have hsub : Subring.closure (Set.range (chartRatio x c)) ≤ (chartRing x c).toSubring :=
      Subring.closure_le.mpr fun _ hp ↦ Algebra.subset_adjoin hp
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subfield.mem_closure_iff.mp (mem_closure_chartRatio x c hc z)
    by_cases hb0 : b = 0
    · refine ⟨(0, 1), ?_⟩
      rw [hb0, div_zero] at hab
      simp [← hab]
    · have hb' : (⟨b, hsub hb⟩ : chartRing x c) ≠ 0 := fun h ↦ hb0 (congrArg Subtype.val h)
      refine ⟨(⟨a, hsub ha⟩, ⟨⟨b, hsub hb⟩, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      change z * b = a
      rw [← hab, div_mul_cancel₀ _ hb0]
  · rw [Subtype.val_injective h]

example : Algebra.FiniteType ℤ (chartRing samplePoint (fun _ ↦ 0)) ∧
    IsFractionRing (chartRing samplePoint (fun _ ↦ 0)) (ratioField samplePoint) :=
  OrbitChartRing.proof Unit _ samplePoint _ fun _ ↦ by simp [samplePoint]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartTerm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval₂_mul_block_of_isMultiHomog {R : Type*} [CommRing R] (s : MvPolynomial (Coord n) ℤ)
    (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (g : ℤ →+* R) (y : Coord n → R)
    (t : ι → R) :
    eval₂ g (fun p ↦ y p * t p.1) s = eval₂ g y s * ∏ k, t k ^ a k := by
  classical
  simp only [eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [mul_assoc]
  congr 1
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  change ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
  rw [Finset.prod_pow_eq_pow_sum, hs m hm k]

omit [Fintype ι] in

theorem coe_chartEval (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℤ) :
    (((chartEval x c f : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by
  have h : (((ratioField x).val.restrictScalars ℤ).comp (chartRing x c).val).comp (chartEval x c) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) :=
    algHom_ext fun p ↦ by simp [chartEval, chartRatio]
  exact DFunLike.congr_fun h f

theorem evalCone_ne_zero_of_notMem_orbitIdeal (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hs : Geo.IsMultiHomog (ι := blockIdx n) s a)
    (hW : s ∉ orbitIdeal x) : evalCone x s ≠ 0 := by
  intro h0
  apply hW
  have hC : ∀ g : ℤ →+* MvPolynomial ι (AlgebraicClosure ℚ),
      eval₂ g (fun p ↦ C (flatCone x p)) s = C (evalCone x s) := fun g ↦ by
    rw [evalCone, eval₂_comp_left]
    congr 1
    exact RingHom.ext_int _ _
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_def,
    eval₂_mul_block_of_isMultiHomog s a hs _ (fun p ↦ C (flatCone x p)) X, hC, h0, map_zero,
    zero_mul]

omit [Fintype ι] in

theorem coe_evalCone_coordVec (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ) :
    ((evalCone (coordVec x) s : coordField x) : AlgebraicClosure ℚ) = evalCone x s := by
  have h := eval₂_comp_left (algebraMap (coordField x) (AlgebraicClosure ℚ)) (Int.castRingHom _)
    (fun v ↦ coordVec x v.1 v.2) s
  rw [RingHom.ext_int ((algebraMap (coordField x) (AlgebraicClosure ℚ)).comp (Int.castRingHom _))
    (Int.castRingHom _)] at h
  exact h

theorem OrbitChartTerm.proof : OrbitChartTerm.Statement := by
  intro ι _ _ n A x s hs c hxc
  obtain ⟨a, ha, hhom, hW⟩ := hs
  have hfac : evalCone x s =
      ((chartEval x c s : ratioField x) : AlgebraicClosure ℚ) * ∏ k, x k (c k) ^ a k := by
    rw [coe_chartEval, aeval_def, ← eval₂_mul_block_of_isMultiHomog s a hhom _
      (fun p ↦ x p.1 p.2 / x p.1 (c p.1)) (fun k ↦ x k (c k)), evalCone]
    congr 1
    funext p
    exact (div_mul_cancel₀ _ (hxc p.1)).symm
  have hx0 : evalCone x s ≠ 0 := evalCone_ne_zero_of_notMem_orbitIdeal x s a hhom hW
  have hf0 : chartEval x c s ≠ 0 := by
    intro h
    rw [h] at hfac
    simp at hfac
    exact hx0 hfac
  refine ⟨hf0, fun v hv ↦ ?_⟩
  have hsup : ∀ k, ⨆ i, v (coordVec x k i) = v (coordVec x k (c k)) := fun k ↦
    le_antisymm (not_lt.mp fun h ↦ hv k (X_mem_orbitCenter x v k (c k) h))
      (le_ciSup (f := fun i ↦ v (coordVec x k i)) (Finite.bddAbove_range _) (c k))
  have hK : evalCone (coordVec x) s =
      IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s) *
        ∏ k, coordVec x k (c k) ^ a k := by
    apply Subtype.ext
    rw [coe_evalCone_coordVec, hfac, MulMemClass.coe_mul, IntermediateField.coe_prod,
      IntermediateField.coe_inclusion]
    simp only [SubmonoidClass.coe_pow]
    rfl
  have hc0 : ∀ k, 0 < v (coordVec x k (c k)) := fun k ↦
    FinitePlace.pos_iff.mpr fun h ↦ hxc k (congrArg Subtype.val h)
  have hv0 : 0 < v (IntermediateField.inclusion (ratioField_le_coordField x) (chartEval x c s)) :=
    FinitePlace.pos_iff.mpr fun h ↦ hf0 (Subtype.ext
      ((IntermediateField.inclusion (ratioField_le_coordField x)).injective
        (h.trans (map_zero _).symm)))
  have ha' : ∀ k, (A.deg k : ℝ) = (a k : ℝ) := fun k ↦ by
    have h := ha k
    rw [HermLine.toGeo_a] at h
    exact_mod_cast h
  rw [hK, map_mul, map_prod, Real.log_mul hv0.ne' (Finset.prod_pos fun k _ ↦ (by
      rw [map_pow]; exact pow_pos (hc0 k) _)).ne',
    Real.log_prod fun k _ ↦ (by rw [map_pow]; exact (pow_pos (hc0 k) _).ne'), finiteTerm]
  simp only [map_pow, Real.log_pow, hsup, ha']
  ring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitLocalSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

theorem OrbitLocalSum.proof (hR : OrbitChartRing.Statement) (hM : OrbitChartMax.Statement)
    (hF : OrbitChartResidue.Statement) (hU : OrbitChartMult.Statement)
    (hP : LocalLengthPlaces.Statement) (hC : OrbitCenterChart.Statement)
    (hS : PlaceCentredSum.Statement) (hT : OrbitChartTerm.Statement) :
    OrbitLocalSum.Statement := by
  intro ι _ _ _ n A x s hx hs V hV
  obtain ⟨hVmin, hVrel⟩ := id hV
  choose c hc using hVrel
  have hWV : orbitIdeal x ≤ V := le_sup_left.trans hVmin.1.2
  have hxc : ∀ k, x k (c k) ≠ 0 := fun k h ↦ hc k (hWV (by
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h]))
  obtain ⟨hft, hfr⟩ := hR ι n x c hxc
  have := hM ι n A x s hx hs V hV c hc
  obtain ⟨hf0, hterm⟩ := hT ι n A x s hs c hxc
  let _ : Algebra (ratioField x) (coordField x) :=
    (IntermediateField.inclusion (ratioField_le_coordField x)).toRingHom.toAlgebra
  have hset : {v : FinitePlace (coordField x) | orbitCenter x v = V} =
      {v : FinitePlace (coordField x) | AbsCentredAt (chartRing x c) (chartPoint x c V)
        fun u ↦ v (algebraMap (ratioField x) (coordField x) u)} :=
    Set.ext fun v ↦ hC ι n A x s hx hs V hV c hc v
  have hsum : ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
        -Real.log (v (algebraMap (ratioField x) (coordField x) (chartEval x c s))) :=
    finsum_mem_congr rfl fun v hv ↦ hterm v fun k hk ↦ hc k (by
      rw [← (show orbitCenter x v = V from hv)]
      exact hk)
  have hdeg := Module.finrank_mul_finrank ℚ (ratioField x) (coordField x)
  rw [hsum, hset, hS (ratioField x) (coordField x) (chartRing x c) (chartPoint x c V),
    hU ι n A x s hx hs V hV c hc, hF ι n A x s hx hs V hV c hc,
    ← hP (ratioField x) (chartRing x c) hft hfr (chartPoint x c V) (chartEval x c s) hf0, ← hdeg]
  push_cast
  ring_nf
  rfl

end GroundTheory.Heights₂.Heights
end

