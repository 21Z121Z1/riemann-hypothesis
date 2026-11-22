import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1229

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTauFixedUnitCentralizerIsNorm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

open GlobalTheory.LocNormTau in

theorem GlobalTheory.LocNormTau.exists_norm_of_tau_fixed_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G (β : G.C) = β →
    ∀ (Y : G.Cˣ) (s : ℚ), (Y : G.C) * β * sh G (Y : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (Y : G.C)).Separable → (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) →
      IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) → IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) →
      inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C) = m →
      ∃ v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = v * (inC G (w.1.adicCompletion ℚ) (β : G.C) * (starT G.star (w.1.adicCompletion ℚ) (v : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop * inC G (w.1.adicCompletion ℚ) ((β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G β hβ Y s hY hsep hdeg
  obtain ⟨f, hf0, hfc⟩ := exists_conj_neg G
  set e : G.C := algebraMap G.F G.C f with he_def
  set e' : G.C := algebraMap G.F G.C f⁻¹ with he'_def
  have hecomm : ∀ c : G.C, Commute e c := fun c => Algebra.commutes f c
  have he'comm : ∀ c : G.C, Commute e' c := fun c => Algebra.commutes f⁻¹ c
  have hee' : e * e' = 1 := by rw [he_def, he'_def, ← map_mul, mul_inv_cancel₀ hf0, map_one]
  have hsh_e : sh G e = -e := by
    simp only [sh, he_def, G.star_F, hfc, map_neg]
  have hsh_e' : sh G e' = -e' := by
    simp only [sh, he'_def, G.star_F, map_inv₀, hfc, inv_neg, map_neg]
  have hτe : (β : G.C) * sh G e * ((β⁻¹ : G.Cˣ) : G.C) = -e := by
    rw [hsh_e, mul_neg, neg_mul, (hecomm _).symm.eq, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨L, _, _, _, _, ι, hιinj, hιrange⟩ := GlobalTheory.FixedCentraliserReg.fixed_algebra_exists p G β Y hsep hdeg
  have hee : e * e ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(hecomm _).mul_left (hecomm _), ?_⟩
    rw [sh_mul, hsh_e, neg_mul_neg, ← ((hecomm (β : G.C)).mul_left (hecomm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  have hee'' : e' * e' ∈ Set.range ι := by
    refine (hιrange _).2 ⟨(he'comm _).mul_left (he'comm _), ?_⟩
    rw [sh_mul, hsh_e', neg_mul_neg, ← ((he'comm (β : G.C)).mul_left (he'comm _)).eq, mul_assoc, Units.mul_inv,
      mul_one]
  obtain ⟨d, hd⟩ := hee
  obtain ⟨di, hdi⟩ := hee''
  have hddi : d * di = 1 := hιinj (by
    rw [map_mul, hd, hdi, map_one, mul_assoc, ← mul_assoc e e', hee', one_mul, hee'])
  have hne2 : ∀ᶠ w : AwayP p in Filter.cofinite, w.1.asIdeal ≠ Ideal.span {2} := by
    rw [Filter.eventually_cofinite]
    refine Set.Subsingleton.finite ?_
    intro w₁ h₁ w₂ h₂
    simp only [Set.mem_setOf_eq, not_not] at h₁ h₂
    exact Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext (h₁.trans h₂.symm))
  filter_upwards [hne2, GlobalTheory.T.eventually_isIntegral_of_integralCoordsLocalTensor p G, GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι d), GlobalTheory.T.eventually_integralCoords_scalarTensorInclusion p G (ι di)] with w h2 hint hId hId'
  intro m hmY hmI hmI' hmτ
  set K := w.1.adicCompletion ℚ
  obtain ⟨hΦinj, hΦrange⟩ := GlobalTheory.FinClsLoc.baseChange_fixedCentraliser_alg p G β Y L ι hιinj hιrange K
  set Φ := Algebra.TensorProduct.map (AlgHom.id K K) ι with hΦ
  have hmτ' : tauR G β K (m : K ⊗[ℚ] G.C) = m := hmτ
  have hm'τ : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) = ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) := by
    have h1 : tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * (m : K ⊗[ℚ] G.C) = 1 := by
      rw [← hmτ', ← tauR_mul, Units.mul_inv, tauR_one]
    calc _ = tauR G β K ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C) * ((m : K ⊗[ℚ] G.C) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)) := by
          rw [Units.mul_inv, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  obtain ⟨y, hy⟩ := (hΦrange m).2 ⟨hmY, hmτ⟩
  obtain ⟨y', hy'⟩ := (hΦrange ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C)).2 ⟨hmY.units_inv_left, hm'τ⟩
  have hyy' : y * y' = 1 := hΦinj (by rw [map_mul, hy, hy', Units.mul_inv, map_one])
  set dK : K ⊗[ℚ] L := (1 : K) ⊗ₜ d
  set dK' : K ⊗[ℚ] L := (1 : K) ⊗ₜ di
  have hdd' : dK * dK' = 1 := by
    simp only [dK, dK', Algebra.TensorProduct.tmul_mul_tmul, one_mul, hddi]
    rfl
  have hΦd : Φ dK = inC G K (ι d) := by
    simp only [hΦ, dK, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have hΦd' : Φ dK' = inC G K (ι di) := by
    simp only [hΦ, dK', Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rfl
  have pull : ∀ z : K ⊗[ℚ] L, IntC G w (Φ z) →
      ∃ g : Polynomial K, g.Monic ∧ (∀ i, g.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval z g = 0 := by
    intro z hz
    obtain ⟨g, hg1, hg2, hg3⟩ := hint _ hz
    refine ⟨g, hg1, hg2, hΦinj ?_⟩
    rw [← Polynomial.aeval_algHom_apply, hg3, map_zero]
  obtain ⟨a', b', hab⟩ := GlobalTheory.OddLocalNormEtale.exists_eq_sq_sub_mul_sq L w.1 h2 y y' dK dK' hyy' hdd'
    (pull y (by rw [hy]; exact hmI)) (pull y' (by rw [hy']; exact hmI'))
    (pull dK (by rw [hΦd]; exact hId)) (pull dK' (by rw [hΦd']; exact hId'))
  set a := Φ a'
  set b := Φ b'
  set E := inC G K e
  have haY := ((hΦrange a).1 ⟨a', rfl⟩).1
  have haτ : tauR G β K a = a := ((hΦrange a).1 ⟨a', rfl⟩).2
  have hbY := ((hΦrange b).1 ⟨b', rfl⟩).1
  have hbτ : tauR G β K b = b := ((hΦrange b).1 ⟨b', rfl⟩).2
  have hE : ∀ x : K ⊗[ℚ] G.C, Commute E x := commute_inC_of_forall G K e hecomm
  have hτE : tauR G β K E = -E := by
    rw [tauR_inC, hτe, map_neg]
  have habc : a * b = b * a := by
    simp only [a, b, ← map_mul, mul_comm a' b']
  have hEE : Φ dK = E * E := by rw [hΦd, hd, map_mul]
  have hm : (m : K ⊗[ℚ] G.C) = a * a - E * E * (b * b) := by
    rw [← hy, hab, map_sub, map_mul, map_mul, map_mul, hEE]
  set vv : K ⊗[ℚ] G.C := a + b * E
  have hτv : tauR G β K vv = a - E * b := by
    rw [tauR_add, tauR_mul, haτ, hbτ, hτE, neg_mul, sub_eq_add_neg]
  obtain ⟨key1, key2⟩ := norm_aux a b E (hE a) (hE b) habc
  rw [← hm] at key1 key2
  have hmv : Commute (m : K ⊗[ℚ] G.C) vv := by
    show (m : K ⊗[ℚ] G.C) * vv = vv * m
    calc (m : K ⊗[ℚ] G.C) * vv = vv * (a - E * b) * vv := by rw [key1]
      _ = vv * m := by rw [mul_assoc, key2]
  refine ⟨⟨vv, (a - E * b) * ((m⁻¹ : (K ⊗[ℚ] G.C)ˣ) : K ⊗[ℚ] G.C), ?_, ?_⟩, ?_, ?_⟩
  · rw [← mul_assoc, key1, Units.mul_inv]
  · rw [mul_assoc, hmv.units_inv_left.eq, ← mul_assoc, key2, Units.mul_inv]
  · exact haY.add_left (hbY.mul_left (hE _))
  · change (m : K ⊗[ℚ] G.C) = vv * tauR G β K vv
    rw [hτv, key1]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleFiniteFreeNbhdStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_etale_finite_free_nbhd : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) [CharZero k], IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, IsAffineOpen U ∧ genericPoint X ∈ U ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ (π.app U).hom.Etale ∧ (π.app U).hom.Finite ∧ (letI := (π.app U).hom.toAlgebra; Module.Free Γ(X, U) Γ(Y, π ⁻¹ᵁ U) ∧ Module.finrank Γ(X, U) Γ(Y, π ⁻¹ᵁ U) = π.residueDegree (genericPoint Y)) := by
  first | exact @GlobalTheory.GenFinEtField.exists_affine_finite_etale_free | exact GlobalTheory.GenFinEtField.exists_affine_finite_etale_free | (intros; apply GlobalTheory.GenFinEtField.exists_affine_finite_etale_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivFractionFieldOfLocalRingOfVarietyPStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algEquiv_fractionField_of_localRingOfVarietyPoint : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ]
  (R : Subring K) (π : R →+* κ), IsLocModel (algebraMap ℂ K) R →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → Function.Injective π →
  ∃ e : K ≃ₐ[ℂ] κ, ∀ r : R, e r = π r := by
  first | exact @GlobalTheory.locModel_fracField_algEquiv | exact GlobalTheory.locModel_fracField_algEquiv | (intros; apply GlobalTheory.locModel_fracField_algEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionClearingRationalFunctionDenomiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleSection_clearing_rationalFunction_denominator : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (f : X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H 0 c ∧ g * f ∈ P.H 0 c := by
  first | exact @GlobalTheory.HSNef.DenOne.exists_den_one | exact GlobalTheory.HSNef.DenOne.exists_den_one | (intros; apply GlobalTheory.HSNef.DenOne.exists_den_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicMulIntegralGL
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

open ValuativeRel

theorem mem_integer_iff_mem_Ov {E : Type} [Field E] [NumberField E] (w : Pl E) (x : w.adicCompletion E) :
    x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Ov E w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _)
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one

theorem integralGL_le_KGL {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) :
    GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) n ≤ GlobalTheory.LFun.KGL w n := by
  intro g hg
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.GLnLocal.mem_integralGL_iff _ n).1 hg
  let A : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨g i j, (mem_integer_iff_mem_Ov w _).1 (h1 i j)⟩
  let B : Matrix (Fin n) (Fin n) (Ov E w) :=
    Matrix.of fun i j => ⟨(g⁻¹ : GL (Fin n) (w.adicCompletion E)) i j, (mem_integer_iff_mem_Ov w _).1 (h2 i j)⟩
  have hinj : Function.Injective (RingHom.mapMatrix (m := Fin n) (Ov E w).subtype) :=
    fun M N h => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  have hA : RingHom.mapMatrix (Ov E w).subtype A = (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hB : RingHom.mapMatrix (Ov E w).subtype B =
      ((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := rfl
  have hAB : A * B = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.mul_inv])
  have hBA : B * A = 1 := hinj (by rw [map_mul, map_one, hA, hB, Units.inv_mul])
  exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hA⟩

theorem exists_parabolic_mul_maximalCompact : ∀ (E : Type) [Field E] [NumberField E] (a n : ℕ) (w : Pl E) (g : GLw n w),
    ∃ p ∈ GlobalTheory.LeviDesc.parP a n w, ∃ k ∈ GlobalTheory.LFun.KGL w n, g = p * k := by
  intro E _ _ a n w g
  have hβ : Monotone fun i : Fin n => decide (a ≤ (i : ℕ)) := by
    intro i j hij
    by_cases h : a ≤ (i : ℕ)
    · have : a ≤ (j : ℕ) := h.trans (Fin.le_iff_val_le_val.1 hij)
      simp [h, this]
    · simp [h]
  obtain ⟨p, hp, k, hk, rfl⟩ :=
    GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL (w.adicCompletion E) n hβ g
  exact ⟨p, hp, k, integralGL_le_KGL w n hk, rfl⟩

end GlobalTheory.LeviDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeRigidifiedBundleTrivialLocuStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_rigidifiedBundle_trivialLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), TrivCond A N T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  first | exact @GlobalTheory.TrivLocusLocal.exists_closed_triv_local | exact GlobalTheory.TrivLocusLocal.exists_closed_triv_local | (intros; apply GlobalTheory.TrivLocusLocal.exists_closed_triv_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDominatingVarietyPointNoTrBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CommonPoint

theorem isFractionRing_of_isLocModel {K : Type} [Field K] [Algebra ℂ K] {R : Subring K}
    (h : IsLocModel (algebraMap ℂ K) R) : IsFractionRing R K :=
  IsFractionRing.of_field R K fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac f
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩

theorem exists_residue {K : Type} [Field K] [Algebra ℂ K] (R : Subring K)
    (h : IsLocModel (algebraMap ℂ K) R) (h' : RatRes (algebraMap ℂ K) R) :
    letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
    ∃ ε : R →ₐ[ℂ] ℂ, ∀ r : R, ε r = 0 ↔ NonUnit R (r : K) := by
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.T.exists_residue_to_complex_of_rationalResidue R h h'
  exact ⟨⟨ε, h1⟩, h2⟩

theorem pair_step : ∀ {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (R : Subring K) (S : Subring L),
  IsLocModel (algebraMap ℂ K) R → RatRes (algebraMap ℂ K) R →
  IsLocModel (algebraMap ℂ L) S → RatRes (algebraMap ℂ L) S →
  ∃ (M : Type) (_ : Field M) (_ : Algebra ℂ M) (ρ : K →ₐ[ℂ] M) (σ : L →ₐ[ℂ] M) (T : Subring M),
    IsLocModel (algebraMap ℂ M) T ∧ RatRes (algebraMap ℂ M) T ∧
    Dominates ρ.toRingHom T R ∧ Dominates σ.toRingHom T S := by
  intro K L _ _ _ _ R S hR hR' hS hS'
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R hR.const_mem).toAlgebra
  letI : Algebra ℂ S := ((algebraMap ℂ L).codRestrict S hS.const_mem).toAlgebra
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.EssFiniteType ℂ R := hR.essFiniteType
  haveI : Algebra.EssFiniteType ℂ S := hS.essFiniteType
  haveI := isFractionRing_of_isLocModel hR
  haveI := isFractionRing_of_isLocModel hS
  obtain ⟨εR, hεR⟩ := exists_residue R hR hR'
  obtain ⟨εS, hεS⟩ := exists_residue S hS hS'
  let iR : R →ₐ[ℂ] K := IsScalarTower.toAlgHom ℂ R K
  let iS : S →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ S L
  have hinj : Function.Injective (Algebra.TensorProduct.map iR iS) := by
    have e : (Algebra.TensorProduct.map iR iS).toLinearMap =
        (iR.toLinearMap.rTensor L).comp (iS.toLinearMap.lTensor R) := by
      ext x y; simp
    have h1 : Function.Injective (iS.toLinearMap.lTensor R) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    have h2 : Function.Injective (iR.toLinearMap.rTensor L) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    intro x y hxy
    have ex := LinearMap.congr_fun e x
    have ey := LinearMap.congr_fun e y
    exact h1 (h2 (ex.symm.trans (hxy.trans ey)))
  haveI : IsDomain (K ⊗[ℂ] L) := GlobalTheory.TensorFields.isDomain_tensor_complex K L
  haveI : IsDomain (R ⊗[ℂ] S) := hinj.isDomain _
  haveI : Algebra.EssFiniteType S (S ⊗[ℂ] R) := Algebra.EssFiniteType.baseChange ℂ R S
  haveI : Algebra.EssFiniteType ℂ (S ⊗[ℂ] R) := Algebra.EssFiniteType.comp ℂ S (S ⊗[ℂ] R)
  haveI : Algebra.EssFiniteType ℂ (R ⊗[ℂ] S) :=
    Algebra.EssFiniteType.of_surjective (Algebra.TensorProduct.comm ℂ S R).toAlgHom
      (Algebra.TensorProduct.comm ℂ S R).surjective
  let ε : R ⊗[ℂ] S →ₐ[ℂ] ℂ := Algebra.TensorProduct.lift εR εS fun _ _ => Commute.all _ _
  obtain ⟨T, hT, hT', hTa⟩ := GlobalTheory.T.exists_localModel_at_complexPoint (R ⊗[ℂ] S) ε
  let M := FractionRing (R ⊗[ℂ] S)
  let j : R ⊗[ℂ] S →ₐ[ℂ] M := IsScalarTower.toAlgHom ℂ _ M
  have hj : Function.Injective j := IsFractionRing.injective (R ⊗[ℂ] S) M
  have hl : Function.Injective (j.comp Algebra.TensorProduct.includeLeft) := by
    rw [AlgHom.coe_comp]
    exact hj.comp (Algebra.TensorProduct.includeLeft_injective (S := ℂ) (algebraMap ℂ S).injective)
  have hr : Function.Injective (j.comp Algebra.TensorProduct.includeRight) := by
    rw [AlgHom.coe_comp]
    exact hj.comp (Algebra.TensorProduct.includeRight_injective (algebraMap ℂ R).injective)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : K →ₐ[ℂ] M, ∀ r : R, ρ (r : K) = j (r ⊗ₜ 1) :=
    ⟨IsFractionRing.liftAlgHom hl, fun r => (IsFractionRing.liftAlgHom_apply hl _).trans
      (IsFractionRing.lift_algebraMap hl r)⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : L →ₐ[ℂ] M, ∀ s : S, σ (s : L) = j (1 ⊗ₜ s) :=
    ⟨IsFractionRing.liftAlgHom hr, fun s => (IsFractionRing.liftAlgHom_apply hr _).trans
      (IsFractionRing.lift_algebraMap hr s)⟩
  refine ⟨M, inferInstance, inferInstance, ρ, σ, T, hT, hT', fun f hf => ?_, fun f hf => ?_⟩
  · have e : ρ.toRingHom f = algebraMap _ M ((⟨f, hf⟩ : R) ⊗ₜ[ℂ] (1 : S)) := hρ ⟨f, hf⟩
    rw [e]
    refine ⟨(hTa _).1, fun hn => (hTa _).2 ?_⟩
    have h0 : εR ⟨f, hf⟩ = 0 := (hεR ⟨f, hf⟩).2 hn
    simp [ε, h0]
  · have e : σ.toRingHom f = algebraMap _ M ((1 : R) ⊗ₜ[ℂ] (⟨f, hf⟩ : S)) := hσ ⟨f, hf⟩
    rw [e]
    refine ⟨(hTa _).1, fun hn => (hTa _).2 ?_⟩
    have h0 : εS ⟨f, hf⟩ = 0 := (hεS ⟨f, hf⟩).2 hn
    simp [ε, h0]

theorem trBasis_of_isLocModel {κ : Type} [Field κ] [Algebra ℂ κ] {O : Subring κ}
    (h : IsLocModel (algebraMap ℂ κ) O) : ∃ (k : ℕ) (z : Fin k → κ), TrBasis (algebraMap ℂ κ) z := by
  letI : Algebra ℂ O := ((algebraMap ℂ κ).codRestrict O h.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ O := h.essFiniteType
  haveI : IsScalarTower ℂ O κ := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing O κ := IsFractionRing.of_field O κ (fun f => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac f
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩)
  haveI : Algebra.EssFiniteType O κ := Algebra.EssFiniteType.of_isLocalization κ (nonZeroDivisors O)
  haveI : Algebra.EssFiniteType ℂ κ := Algebra.EssFiniteType.comp ℂ O κ
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis ℂ κ
  refine ⟨s.card, fun i => (s.equivFin.symm i : κ), ?_⟩
  have e : (algebraMap ℂ κ).toAlgebra = (inferInstance : Algebra ℂ κ) :=
    Algebra.algebra_ext _ _ fun _ => rfl
  unfold TrBasis
  rw [e]
  exact hs.comp_equiv s.equivFin.symm

theorem exists_common_dominating_varietyPoint_noTrBasis {κ : Type} [Field κ] [Algebra ℂ κ] (c : ℕ) : ∀ (O : Fin c → Subring κ),
    (∀ i, IsLocModel (algebraMap ℂ κ) (O i) ∧ RatRes (algebraMap ℂ κ) (O i)) →
    ∃ (κ' : Type) (_ : Field κ') (_ : Algebra ℂ κ') (ρ : Fin c → (κ →ₐ[ℂ] κ')) (O' : Subring κ'),
      IsLocModel (algebraMap ℂ κ') O' ∧ RatRes (algebraMap ℂ κ') O' ∧
      ∀ i, Dominates (ρ i).toRingHom O' (O i) := by
  induction c with
  | zero =>
    intro O _
    exact ⟨ℂ, inferInstance, inferInstance, Fin.elim0, ⊤, isLocModel_self, ratRes_self,
      fun i => i.elim0⟩
  | succ c ih =>
    intro O hO
    obtain ⟨κ'', _, _, ρ'', O'', h1, h2, h3⟩ := ih (fun i => O (Fin.castSucc i)) (fun i => hO _)
    obtain ⟨M, _, _, ρ', σ, T, g1, g2, g3, g4⟩ :=
      pair_step O'' (O (Fin.last c)) h1 h2 (hO _).1 (hO _).2
    refine ⟨M, inferInstance, inferInstance, Fin.lastCases σ (fun j => ρ'.comp (ρ'' j)), T, g1, g2,
      fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using g4
    | cast j =>
      simp only [Fin.lastCases_castSucc]
      exact (h3 j).trans g3

theorem exists_common_field : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (c : ℕ) (O : Fin c → Subring κ),
  (∀ i, IsLocModel (algebraMap ℂ κ) (O i) ∧ RatRes (algebraMap ℂ κ) (O i)) → (∃ (k : ℕ) (z : Fin k → κ), TrBasis (algebraMap ℂ κ) z) →
  ∃ (κ' : Type) (_ : Field κ') (_ : Algebra ℂ κ') (ρ : Fin c → (κ →ₐ[ℂ] κ')) (O' : Subring κ'),
    IsLocModel (algebraMap ℂ κ') O' ∧ RatRes (algebraMap ℂ κ') O' ∧ (∀ i, Dominates (ρ i).toRingHom O' (O i)) ∧
    ∃ (k' : ℕ) (z' : Fin k' → κ'), TrBasis (algebraMap ℂ κ') z' := by
  intro κ _ _ c O hO _
  obtain ⟨κ', _, _, ρ, O', h1, h2, h3⟩ := exists_common_dominating_varietyPoint_noTrBasis c O hO
  exact ⟨κ', inferInstance, inferInstance, ρ, O', h1, h2, h3, trBasis_of_isLocModel h1⟩

end GlobalTheory.CommonPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactInvertibleKrylovMatrices
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem exists_isCompact_krylov_units : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w)), IsCompact Ω → (∀ y ∈ Ω, ∃ e, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y.val e).det) → ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = GlobalTheory.LeviDesc.Krylov.krylov y.val e := by
  intro E _ _ w r Ω hΩ hcov
  classical
  let kr : (Fin r → w.adicCompletion E) → GLw r w → Matrix (Fin r) (Fin r) (w.adicCompletion E) :=
    fun e y => GlobalTheory.LeviDesc.Krylov.krylov y.val e
  have hkc : ∀ e, Continuous (kr e) := by
    intro e
    have hv : Continuous fun y : GLw r w => (y.val : Matrix (Fin r) (Fin r) (w.adicCompletion E)) :=
      Units.continuous_val
    refine continuous_matrix fun i j => ?_
    simp only [kr, GlobalTheory.LeviDesc.Krylov.krylov_apply]
    exact (continuous_apply i).comp ((hv.pow (j : ℕ)).matrix_mulVec continuous_const)
  let U : (Fin r → w.adicCompletion E) → Set (GLw r w) := fun e => {y | (kr e y).det ≠ 0}
  have hU : ∀ e, IsOpen (U e) := fun e => isOpen_ne_fun ((hkc e).matrix_det) continuous_const
  have hsub : Ω ⊆ ⋃ e, U e := by
    intro y hy
    obtain ⟨e, he⟩ := hcov y hy
    exact Set.mem_iUnion.2 ⟨e, he.ne_zero⟩
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover U hU hsub
  obtain ⟨K, hKc, hKU, hΩK⟩ := hΩ.finite_compact_cover t U (fun e _ => hU e) ht
  have hunit : ∀ e, ∀ y : K e, IsUnit (kr e y.1) := fun e y =>
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hKU e y.2))
  let f : ∀ e, K e → GLw r w := fun e y => (hunit e y).unit
  have hf : ∀ e, Continuous (f e) := by
    intro e
    rw [Units.continuous_iff]
    constructor
    · exact (hkc e).comp continuous_subtype_val
    · have : (fun y : K e => ((f e y)⁻¹ : GLw r w).val) = fun y => (kr e y.1)⁻¹ := by
        funext y
        rw [Matrix.coe_units_inv]
        rfl
      rw [this]
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (((hkc e).comp continuous_subtype_val).matrix_det.inv₀ fun y => hKU e y.2).smul
        ((hkc e).comp continuous_subtype_val).matrix_adjugate
  refine ⟨⋃ e ∈ t, Set.range (f e), t.isCompact_biUnion fun e _ => ?_, ?_⟩
  · haveI := isCompact_iff_compactSpace.1 (hKc e)
    exact isCompact_range (hf e)
  · intro y hy
    rw [hΩK] at hy
    simp only [Set.mem_iUnion] at hy
    obtain ⟨e, he, hyK⟩ := hy
    exact ⟨e, f e ⟨y, hyK⟩, Set.mem_biUnion he ⟨⟨y, hyK⟩, rfl⟩, rfl⟩

end GlobalTheory.LeviDesc.Krylov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetTwistedCentralizerEllipticStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_set_twisted_centralizer_elliptic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ t ∈ twCent (MonoidHom.id (UL n w)) y, IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) → t ∈ Ω := by
  first | exact @GlobalTheory.CentCpt.main | exact GlobalTheory.CentCpt.main | (intros; apply GlobalTheory.CentCpt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjSameSeparableCharpolySplitPlaceStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_same_separable_charpoly_split_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∀ P ∈ Ell E n, ∀ w : Pl E, IsSplitAt w → ∀ γ γ' : UL n w, γ.1.val.charpoly = atPl w P → γ'.1.val.charpoly = atPl w P → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
  first | exact @GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt | exact GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt | (intros; apply GlobalTheory.BCT.SplitConj.exists_conj_of_isSplitAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

theorem exists_eq_flagPt_of_isLocalRing (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ Part a l) :
    ∃ g : ι → GL (Fin N) A, x = flagPt a l g := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.flag_point_in_some_cell ι κ N a l (x (IsLocalRing.closedPoint A))
  have := GlobalTheory.T.schubert_cell_open_immersion ι κ N a l w
  have hr : Set.range x ⊆ Set.range (cell a l w) := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map x.continuous).mem_open
      (cell a l w).isOpenEmbedding.isOpen_range hw
  have e := IsOpenImmersion.lift_fac (cell a l w) x hr
  refine ⟨fun τ => GeneralLinearGroup.map (Spec.preimage (IsOpenImmersion.lift (cell a l w) x hr)).hom
    (cellGL a l w τ), ?_⟩
  rw [← spMap_flagPt]
  exact e.symm.trans (congrArg (· ≫ cell a l w) (Spec.map_preimage _).symm)

end GlobalTheory.FlagZ
end

