import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0089
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.ImportsBis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.LatticeWithoutBigness

noncomputable section

theorem Z2.proof (hMo : MoriwakiBigStatement) : SuccessiveMinimaUpperBound := by
  have hG : ArithmeticVolumeBig.Statement := ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hMo
  have hT : TopConstantTwist.Statement := TopConstantTwist.proof
  have hM : BirationalModelExists.Statement := BirationalModelExists.proof
  have hS : SmallSectionPointHeight.Statement := SmallSectionPointHeight.proof SectionOrderAtPoint.proof
  have hfin : CurvePointsFinite.Statement := CurvePointsFinite.proof
  intro K _ ι _ P P0 D A e' F II hII har hP0 hsemi hnef hconj hF hdense
  have hA : IsSmoothHerm A := hsemi.1
  have : Nonempty K := har.1

  have hdeg : ∀ W : Ideal (MRing ι), IsArithVar W 1 → (0 : ℝ) < degC W := by
    intro W hW
    have : Finite (projPts W) := hfin K ι W hW
    obtain ⟨z, hz⟩ := IndefiniteRowSideFullHecke.HeightsSet.CurveComplexPoint.full K ι W hW
    have : Nonempty (projPts W) := ⟨Quot.mk _ ⟨z, hz⟩⟩
    have : 0 < Nat.card (projPts W) := Nat.card_pos
    exact_mod_cast this

  have hmc : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ, II K ι W 1 ![A.tensor (constLine c)] =
      II K ι W 1 ![A] - ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι))
        (fun _ => c) := by
    intro W hW c
    have h := metricChange K ι (II K ι) (hII K ι) W 0 ![] A (fun _ => c) (fun _ _ _ => rfl) hW
      (fun j => j.elim0) hA contDiffOn_const
    have e1 : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
        (Fin.snoc (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) B : Fin (0 + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
          = ![B] := fun B => by
      funext i
      fin_cases i
      rfl
    rw [e1, e1] at h
    exact h
  have hlow : ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∀ c : ℝ,
      c * degC W ≤ ptsIntegral (e := 0) W (pot (![] : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)) (fun _ => c) := by
    intro W hW c
    exact PtsIntegralZeroLowerNE.proof K ι W _ (fun _ => c) c hW.2.1.2.1 (hfin K ι W hW)
      (fun _ _ _ _ => rfl) (fun _ _ => le_rfl)
  have h1P : (1 : MRing ι) ∉ P := fun h => har.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hfun : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (fun _ : Fin 1 => B) = ![B] := fun B => by
    funext i
    fin_cases i
    rfl
  rcases Nat.eq_zero_or_pos D with hD | hD
  ·
    subst hD
    obtain ⟨W, hWF, -⟩ := hdense 1 ⟨fun _ => 0, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one⟩ h1P
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have : P.IsPrime := har.2.1.1
    have hWP : P = W :=
      CurveIsOrbit.eq_of_le_of_ringKrullDim_eq (d := 1 + Fintype.card K) hPW har.2.2.2 hW.2.2.2
    rw [← hWP] at hle
    have htw : II K ι P 1 (fun _ => A.tensor (constLine e')) =
        II K ι P 1 (fun _ => A) - ((1 : ℕ) : ℝ) * e' * geomDeg P A 0 := hT K ι P 0 A e' II hII har hA
    rw [hfun, hfun] at htw
    have hm := hmc P har e'
    have hl := hlow P har e'
    show II K ι P 1 (fun _ => A) ≤ ((1 : ℕ) : ℝ) * e' * geomDeg P A 0
    rw [hfun]
    push_cast at htw ⊢
    linarith
  ·
    obtain ⟨Ω, _, y, hyP, hbir⟩ := hM K ι P (D + 1) har
    subst hyP
    by_contra hlt
    push Not at hlt
    obtain ⟨e'', hgt, htop⟩ := exists_gt_of_lt (N := ((D + 1 : ℕ) : ℝ)) (by positivity) hlt
    have htw := hT K ι (mCoordIdeal y) D A e'' II hII har hA
    have hvol := hG K ι Ω y D (A.tensor (constLine e'')) P0 II hD hII har hbir hP0
      (isSemipositiveRel_twist hsemi e'') (nefOnFibres_twist hnef e'') (isConjInvariantH_twist hconj e'')
    have hpos : 0 < arVolP (IsSmallH (mCoordIdeal y) y (A.tensor (constLine e'')))
        (chartLat y (A.tensor (constLine e'')).a) 1 D := by
      linarith
    obtain ⟨τ, hτ, s, hsL, hs0, hsm⟩ := exists_small_section_of_arithmeticVolume_pos hpos
    obtain ⟨f, hfh, hfP, hfW⟩ := hS K ι Ω y D (A.tensor (constLine e'')) τ s II hII har hbir
      (isSmoothHerm_twist hA e'') hτ (SmallSectionPointHeight.chartLat_le_chartLatNm _ _ _ hsL) hs0 hsm
    obtain ⟨W, hWF, hfW'⟩ := hdense f hfh hfP
    obtain ⟨hW, hPW, hle⟩ := hF W hWF
    have h0 := hfW W hW hPW hfW'
    have hm := hmc W hW e''
    have hl := hlow W hW e''
    have hd := hdeg W hW
    nlinarith [mul_pos (sub_pos.mpr hgt) hd]

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNef
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleFibreAlt

noncomputable section

namespace KleimanNef

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiProjPrime_map_red (p : ℕ) {V : Ideal (MRing ι)} (hV : IsMultiProjPrime V)
    (hp : ((p : ℕ) : MRing ι) ∈ V) : IsMultiProjPrime (V.map (red p)) := by
  have : V.IsPrime := hV.1
  refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) (ker_red_le p hp),
    isMultiHomogIdeal_map _ hV.2.1, fun k => ?_⟩
  obtain ⟨i, hi⟩ := hV.2.2 k
  refine ⟨i, fun h => hi ?_⟩
  have h' : red p (X ⟨k, i⟩ : MRing ι) ∈ V.map (red p) := by
    simpa only [red, map_X] using h
  exact (mem_map_red_iff p hp _).1 h'

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem charOf_mem (W : Ideal (MRing ι)) : ((charOf W : ℕ) : MRing ι) ∈ W := by
  have hg := Submodule.IsPrincipal.generator_mem (W.comap (C : ℤ →+* MRing ι))
  have hdvd : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) ∣
      ((charOf W : ℕ) : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have hmem : ((charOf W : ℕ) : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
    Ideal.mem_of_dvd _ hdvd hg
  rw [Ideal.mem_comap, map_natCast] at hmem
  exact hmem

end KleimanNef

open KleimanNef in

theorem KleimanNef.proof (hF : KH.KleimanNefFStatement) : KH.KleimanNefIntersectionNonneg := by
  classical
  intro K _ ι _ V n a hV hchar hdim hnef
  have : V.IsPrime := hV.1
  set p := charOf V with hpdef
  have : Fact p.Prime := ⟨HilbertSamuel.SemiampleNefAlt.charOf_prime hchar⟩
  have hpV : ((p : ℕ) : MRing ι) ∈ V := charOf_mem V
  let I : IFamily (ZMod p) ι := fun V _ L => NumbersDVR.intNum (ZMod p) V L
  have hI : IsFieldIntersection I := GeoNumTarget.isFieldIntersection_intNum p
  have hGeo := GroundTheory.Heights₂.Heights.geoNumStatement ι p I hI
  have hproj : IsProjVarF (V.map (red p)) n :=
    ⟨isMultiProjPrime_map_red p hV hpV, by rw [ringKrullDim_red p hpV, hdim]⟩
  have hnefF : ∀ j, KH.NefOnF I (V.map (red p)) (a j) := by
    intro j W' hW' hle
    set W := W'.comap (red p) with hWdef
    have hmap : W.map (red p) = W' := Ideal.map_comap_of_surjective _ (red_surjective p) W'
    have hVW : V ≤ W := Ideal.map_le_iff_le_comap.mp hle
    have hpW : ((p : ℕ) : MRing ι) ∈ W := hVW hpV
    have hWm : IsMultiProjPrime W := by
      obtain ⟨⟨hW'p, hW'h, hW'r⟩, -⟩ := hW'
      refine ⟨Ideal.comap_isPrime _ W', isMultiHomogIdeal_comap _ hW'h, fun k => ?_⟩
      obtain ⟨i, hi⟩ := hW'r k
      refine ⟨i, ?_⟩
      rw [hWdef, Ideal.mem_comap, map_X]
      exact hi
    have hdimW : ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← ringKrullDim_red p hpW, hmap, hW'.2]
    have hWp : IsProjVarF (W.map (red p)) 1 := by
      rw [hmap]
      exact hW'
    have h := hnef j W hWm hVW hdimW
    rw [hGeo W 1 _ hWm hpW hWp, hmap] at h
    convert h using 2
    funext i
    fin_cases i
    rfl
  have h := hF (ZMod p) K ι I (V.map (red p)) n a hI hproj hnefF
  rw [hGeo V n a hV hpV hproj]
  exact h

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
end

