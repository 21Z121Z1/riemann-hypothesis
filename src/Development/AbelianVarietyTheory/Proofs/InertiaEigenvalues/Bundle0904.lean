import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Formalism.SharpRestriction.LevelLetterCocycles.NEqRZeroMulXPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0897
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0890
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0898
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0054
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorPrimesLtSpecialPrimeThresholdEventually
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.LevelBelowStarBound.QdSmall

theorem qd_lt_lStar_at {D : D7} (L : SizeData₂ D) (P : ParameterChoice' D L)
    (hy : Real.exp 1 ≤ L.sc.x ^ (L.sc.eps / 3)) :
    (D.host.q : ℝ) < LevelStarExponents.lStar L ∧ (D.host.d : ℝ) < LevelStarExponents.lStar L ∧ ∀ p ∈ D.host.small, (p : ℝ) < LevelStarExponents.lStar L := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  set y := L.sc.x ^ (L.sc.eps / 3) with hydef
  have hL : L.sc.L = y ^ 3 := by
    unfold Scale.L
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  have he2 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero; linarith
  have hy2 : 2 < y := lt_of_lt_of_le he2 hy

  have hkey : L.sc.L / 72 < L.sc.L - y := by
    rw [hL]
    have hy0 : 0 ≤ y := by linarith
    have h4 : 4 ≤ y ^ 2 := by nlinarith
    have : 4 * y ≤ y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h4 hy0]
    nlinarith

  have hb' : Real.exp (L.sc.L - y) ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X' Scale.b
    rw [← hydef, Real.exp_sub, mul_div_assoc]
    have : 0 ≤ Real.exp L.sc.L / Real.exp y := by positivity
    nlinarith

  have hn1 : (1 : ℝ) ≤ D.R.n := Formalism.MainNotions.TwistedPlaces.n_ge_one D
  have ht1 : (1 : ℝ) ≤ D.R.t := Formalism.MainNotions.TwistedPlaces.t_ge_one D
  have hc := P.condE_le
  have hc0 : (0 : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by positivity
  have hc36 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ Real.exp (L.sc.L / 72) ^ 36 := by
    have h1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
    have h2 : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ (LevelStarExponents.condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) h1
    have h3 : L.sc.b ^ ((1 : ℝ) / 2) = Real.exp (L.sc.L / 72) ^ 36 := by
      unfold Scale.b
      rw [← Real.exp_mul, ← Real.exp_nat_mul]
      congr 1; push_cast; ring
    linarith
  have hcE : (LevelStarExponents.condE D : ℝ) ≤ Real.exp (L.sc.L / 72) :=
    (pow_le_pow_iff_left₀ hc0 (Real.exp_pos _).le (by norm_num)).1 hc36
  have hlt : (LevelStarExponents.condE D : ℝ) < L.sc.b' :=
    lt_of_le_of_lt hcE (lt_of_lt_of_le (Real.exp_lt_exp.2 hkey) hb')
  have hstar : L.sc.b' < LevelStarExponents.lStar L := Formalism.MainNotions.TwistedPlaces.lStar_gt L P

  obtain ⟨hq, hd⟩ := P.qd_pow
  have hxp : 0 < L.sc.x ^ (2 * L.Ct + 5) := Real.rpow_pos_of_pos hx0 _
  have hq0 : 1 ≤ D.host.q := by
    have : (0 : ℝ) < D.host.q := lt_trans hxp hq
    exact_mod_cast this
  have hd0 : 1 ≤ D.host.d := by
    have : (0 : ℝ) < D.host.d := lt_trans hxp hd
    exact_mod_cast this
  have hS0 : 1 ≤ D.host.QS := D.host.QS_pos
  have hcv : LevelStarExponents.condE D = D.host.QS * D.host.q * D.host.d := rfl
  have hqC : D.host.q ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.q = 1 * D.host.q * 1 := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hdC : D.host.d ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.d = 1 * 1 * D.host.d := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hSC : D.host.QS ≤ LevelStarExponents.condE D := by
    rw [hcv]
    calc D.host.QS = D.host.QS * 1 * 1 := by ring
      _ ≤ D.host.QS * D.host.q * D.host.d := by gcongr
  have hqC' : (D.host.q : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast hqC
  have hdC' : (D.host.d : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast hdC
  refine ⟨by linarith, by linarith, fun p hp => ?_⟩
  have hpC : (p : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast (Nat.le_of_mem_primeFactors hp).trans hSC
  linarith

theorem qd_lt_lStar : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (a : Fm.Ix x),
    ((Fm.D x a).host.q : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧ ((Fm.D x a).host.d : ℝ) < LevelStarExponents.lStar (Fm.L x a) ∧
      ∀ p ∈ (Fm.D x a).host.small, (p : ℝ) < LevelStarExponents.lStar (Fm.L x a) := by
  intro eps Fm
  refine ⟨Real.exp (3 / eps), fun x hx0 hx a => ?_⟩
  apply qd_lt_lStar_at (Fm.L x a) (Fm.params x hx a)
  have hX := Fm.L_x x a hx
  have hE := Fm.L_eps x a
  have hpos : 0 < eps := hE ▸ (Fm.L x a).sc.eps_pos
  rw [hX, hE]
  have h3 : 0 < eps / 3 := by positivity
  calc Real.exp 1 = Real.exp (3 / eps) ^ (eps / 3) := by
        rw [← Real.exp_mul]; congr 1; field_simp
    _ ≤ x ^ (eps / 3) := Real.rpow_le_rpow (Real.exp_pos _).le hx0 h3.le

end GlobalTheory.LevelBelowStarBound.QdSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundExtendedOfRationalBound
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

open scoped ENNReal

namespace GlobalTheory.Proof.congruenceBound_extended_of_rationalBound

open GlobalTheory.IndefiniteRowSideFullHecke

theorem congBound_of_rational : ∀ (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), π ∈ D.nd.Z i → (∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) → (Br.sFin D.loc D.nbr i (fun _ => ρ) π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i (fun _ => ρ) π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})) → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vCC D i π ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sPi D i π ρ + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.shaSum D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vClass D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.epsQ D i := by
  intro D i π ρ hπ hζ h
  classical
  obtain ⟨he0, het⟩ := GlobalTheory.Proof.QuotientLengthInfimum.ramLen_ne D i
  refine (GlobalTheory.Proof.QuotientLengthInfimum.conclusion_iff D i π ρ).2 ?_
  by_cases hs : Br.sFin D.loc D.nbr i (fun _ => ρ) π
  swap
  · have h1 : SelmerSumLargePrime.selLen D i ρ π = ⊤ := not_lt_top_iff.mp hs
    rw [h1]; simp
  by_cases hsh : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤
  swap
  · push Not at hsh
    obtain ⟨k, hk, hk'⟩ := hsh
    have h1 : SelmerSumLargePrime.shaSum D i = ⊤ := by
      unfold SelmerSumLargePrime.shaSum
      refine top_le_iff.mp (le_trans hk' ?_)
      exact Finset.single_le_sum (f := fun e : ℕ => Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ))
        (fun _ _ => zero_le) hk
    rw [h1, ENat.mul_top he0]; simp
  have hr := h hs hsh
  have hc : SelmerSumLargePrime.ccLen D i π ≠ ⊤ := by
    unfold SelmerSumLargePrime.ccLen
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.vcc_ne_top _ (D.nd.T_sep i) _ _ hπ
  have hs' : SelmerSumLargePrime.selLen D i ρ π ≠ ⊤ := hs.ne
  have hq : ∀ P ∈ D.nd.Q i,
      Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1}) ≠ ⊤ := by
    intro P hP
    have h0 : SelmerSumLargePrime.zetaP D i P - 1 ≠ 0 := by
      rw [← GlobalTheory.Proof.QuotientLengthInfimum.zetaP_eq, BaseSizes.zetaP_eq D i P hP]
      exact sub_ne_zero.mpr (hζ P hP)
    exact Module.length_ne_top_iff.2
      (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero h0))
  have hrow : ∀ k ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) k : ℚ) =
      ((Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ)).toNat : ℚ) := fun k hk =>
    D.nd.sha_eq _ k (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2 _
      (ENat.natCast_toNat (hsh k hk).ne).symm
  have hlq : ∀ P ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i P - 1}) =
      ((Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1})).toNat : ℚ) /
        ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := by
    intro P hP
    rw [← BaseSizes.zetaP_eq D i P hP, GlobalTheory.Proof.QuotientLengthInfimum.zetaP_eq]
    rfl
  have hv : D.nd.vcc i π = ((SelmerSumLargePrime.ccLen D i π).toNat : ℚ) / ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := rfl
  have hsp : Br.sPi D.loc D.nbr i (fun _ => ρ) π =
      ((SelmerSumLargePrime.selLen D i ρ π).toNat : ℚ) / ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := rfl
  rw [hv, hsp, Finset.sum_congr rfl hrow, Finset.sum_congr rfl hlq, ← Finset.sum_div] at hr
  have hE0 : (0 : ℚ) < ((SelmerSumLargePrime.ramLen D i).toNat : ℚ) := by
    have : (SelmerSumLargePrime.ramLen D i).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]; tauto
    exact_mod_cast Nat.pos_of_ne_zero this
  set E := (SelmerSumLargePrime.ramLen D i).toNat with hEdef
  set c := (SelmerSumLargePrime.ccLen D i π).toNat
  set s := (SelmerSumLargePrime.selLen D i ρ π).toNat
  set A := ∑ k ∈ Finset.Ioo 0 D.R.t, (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ)).toNat with hA
  set B := ∑ P ∈ D.nd.Q i,
    (Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {SelmerSumLargePrime.zetaP D i P - 1})).toNat with hB
  set v := padicValNat (D.nd.l i) (hE D.host)
  have key : (c : ℚ) ≤ s + E * A + E * v + D.R.t * B := by
    have h2 : ((s : ℚ) / E + (A : ℚ) + (v : ℚ) + (D.R.t : ℚ) * ((B : ℚ) / E)) * E =
        s + E * A + E * v + D.R.t * B := by
      field_simp
    rw [← h2, ← div_le_iff₀ hE0]
    push_cast [hA, hB]
    exact hr
  have knat : c ≤ s + E * A + E * v + D.R.t * B := by exact_mod_cast key
  have hsum : SelmerSumLargePrime.shaSum D i = (A : ℕ∞) := by
    unfold SelmerSumLargePrime.shaSum
    rw [hA, Nat.cast_sum]
    exact Finset.sum_congr rfl fun k hk => (ENat.natCast_toNat (hsh k hk).ne).symm
  have htw : SelmerSumLargePrime.twistLen D i = ((D.R.t * B : ℕ) : ℕ∞) := by
    unfold SelmerSumLargePrime.twistLen
    rw [hB, Nat.cast_mul, Nat.cast_sum]
    exact congrArg _ (Finset.sum_congr rfl fun P hP => (ENat.natCast_toNat (hq P hP)).symm)
  rw [hsum, htw, ← ENat.natCast_toNat hc, ← ENat.natCast_toNat hs', ← ENat.natCast_toNat het]
  exact_mod_cast knat

end GlobalTheory.Proof.congruenceBound_extended_of_rationalBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInvStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv : ∀ {R : Ranks} (Hs : Host R) (μ : HChar Hs.E), IsCSD Hs μ → ∀ (w w' : HeightOneSpectrum (𝓞 Hs.E)), IsConjPl Hs w w' → ∃ i : w.adicCompletion Hs.E ≃+* w'.adicCompletion Hs.E, Continuous i ∧ (∀ x, i (algebraMap Hs.E _ x) = algebraMap Hs.E _ (Hs.conj x)) ∧ ∀ x, μ.loc w' (Units.map i.toRingHom.toMonoidHom x) = (μ.loc w x)⁻¹ := by
  first | exact @GlobalTheory.ConjLocCsd.main | exact GlobalTheory.ConjLocCsd.main | (intros; apply GlobalTheory.ConjLocCsd.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesCompletionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_places_completion : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, Laws a ha ε (ParLaws.locRec hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, Laws a' ha' ε' (ParLaws.locRec hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  first | exact @GlobalTheory.LocLanglands.artin_transport | exact GlobalTheory.LocLanglands.artin_transport | (intros; apply GlobalTheory.LocLanglands.artin_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem wAll_holds : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WAll D HW F :=
  fun D HW F Cm =>
    GlobalTheory.T.wachHypothesis_crystallineLattices D HW F Cm (GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1 (GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).2 (GlobalTheory.crysOnCond_all D HW F)

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfHyp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Pointwise

namespace GlobalTheory.DepthZeroType

theorem isSplitPl_of_over (D : D7) (k : Fin 2) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hP := (GlobalTheory.Mem.Chr.splitsC_place (p := D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hw).2.2
  by_contra hn
  have hle : ∀ x ∈ w.asIdeal, D.host.conj • x ∈ w.asIdeal := by
    intro x hx
    by_contra hy
    refine hn ⟨x, hx, fun y e hy' => hy ?_⟩
    have : y = D.host.conj • x := Subtype.ext e
    rwa [← this]
  refine GlobalTheory.TypePlace.conj_ne_one D.host (hP _ ?_)
  have h1 : D.host.conj • w.asIdeal ≤ w.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    simpa using hle _ hy
  have hm : (D.host.conj • w.asIdeal).IsMaximal :=
    Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ (𝓞 D.host.E) D.host.conj) (hp := w.isMaximal)
  exact hm.eq_of_le w.isMaximal.ne_top h1

theorem mem_Ine_of_wild (D : D7) (w : PlE D.host) {σ} (hσ : σ ∈ wildSet D.nd (D.nd.plOm.1 w)) :
    σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := GlobalTheory.TameGenPowers.wild_mem_Ine hσ

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.DepthZeroWild → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → GlobalTheory.HubX.DepthZeroG D := by
  intro hp h1 h2 hL D P hR i w hwS hk Q σ hσ
  obtain ⟨S, hS, -, -⟩ := GlobalTheory.T.exists_true_reading_with_laws hp.fin hL D P hR
  have hw : IsSplitPl D.host w := hk.elim fun k h => isSplitPl_of_over D k w h
  have ht := (GlobalTheory.MuTameQS.main hL D P S hS i w hw (Or.inl hwS)).1
  obtain ⟨v, hv0, hv⟩ := (GlobalTheory.T.tame_block_type_at_split_place hL D P S hS i w hw hk ht).2 Q
  have hfix : v ∈ GlobalTheory.PRep.fixed ((S i w hw).rep Q).π
      (GlobalTheory.SplitWeil.KOne (w.adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
    intro h
    have := GlobalTheory.JacBlock.KOne_le_stab ht hv h.2
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact this
  rw [P.T.inePol w _ σ (mem_Ine_of_wild D w hσ), (S i w hw).locV Q, hS.rc]
  exact GlobalTheory.T.inertia_unipotent_depth_zero hp.bz h1 h2 hL D w _ _ ⟨v, hfix, hv0⟩ σ hσ

end GlobalTheory.DepthZeroType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Detects
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

namespace GlobalTheory.PointsDetectAlg

theorem core {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] (φ : c.F →+* ℂ_[p]) (hI : IntAll Xo c)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) {ι : Type} [Fintype ι] (g : ι → Rul Xo c) (hg : ∀ s, g s ∈ sec Xo c a n)
    (hli : LinearIndependent c.F g) (w : ι → ℂ_[p])
    (hw : ∀ z : PtC Xo c φ, ∑ s, w s * valC z.1 (g s) = 0) : w = 0 := by
  by_contra hw0
  let wP : ι → PAt φ := w
  have hrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, wP s * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    obtain ⟨z, u, hu, hz⟩ := GlobalTheory.T.exists_algebraicInteger_point_of_finiteExtension E H Dw l Xo c p φ hI L ((toCp φ).comp σ.toRingHom)
      (fun a => by simp [toCp_algebraMap]) y a n
    have h1 := hw z
    simp only [hz _ (hg _)] at h1
    have h2 : u * ∑ s, w s * toCp φ (σ (evR Xo c (g s) y)) = 0 := by
      rw [Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun s _ => ?_
      change u * (w s * toCp φ (σ _)) = w s * (u * toCp φ (σ _))
      ring
    exact (mul_eq_zero.1 h2).resolve_left hu
  let K := algebraicClosure c.F (PAt φ)
  let V : Set (ι → K) := {v | ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (_ : FiniteDimensional c.F L)
    (σ : L →ₐ[c.F] PAt φ) (y : FrPt Xo c L), ∀ s, (v s : PAt φ) = σ (evR Xo c (g s) y)}
  obtain ⟨d, hd0, hd⟩ := GlobalTheory.T.exists_linear_relation_descend_base_field K (PAt φ) ι V wP hw0 (by
    rintro v ⟨L, _, _, _, σ, y, hv⟩
    simpa only [IntermediateField.algebraMap_apply, hv] using hrel L σ y)

  have hdrel : ∀ (L : Type) [Field L] [Algebra c.F L] [FiniteDimensional c.F L] (σ : L →ₐ[c.F] PAt φ)
      (y : FrPt Xo c L), ∑ s, (d s : PAt φ) * σ (evR Xo c (g s) y) = 0 := by
    intro L _ _ _ σ y
    have hmem : (fun s => (⟨σ (evR Xo c (g s) y), mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := c.F) (evR Xo c (g s) y)).algHom σ)⟩ : K)) ∈ V :=
      ⟨L, inferInstance, inferInstance, inferInstance, σ, y, fun s => rfl⟩
    have := congrArg (fun x : K => (x : PAt φ)) (hd _ hmem)
    simpa using this

  let K0 := IntermediateField.adjoin c.F (Set.range fun s => (d s : PAt φ))
  have hfin : FiniteDimensional c.F K0 := IntermediateField.finiteDimensional_adjoin (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact (mem_algebraicClosure_iff.1 (d s).2).isIntegral)
  let bs := Module.finBasis c.F K0
  let m := Module.finrank c.F K0
  let e : Fin m → PAt φ := fun t => (bs t : PAt φ)
  have he : LinearIndependent c.F e :=
    bs.linearIndependent.map' K0.val.toLinearMap (LinearMap.ker_eq_bot.2 K0.val.injective)
  have hea : ∀ t, IsAlgebraic c.F (e t) := fun t =>
    (Algebra.IsAlgebraic.isAlgebraic (R := c.F) (bs t)).algHom K0.val
  have dmem : ∀ s, (d s : PAt φ) ∈ K0 := fun s => IntermediateField.subset_adjoin _ _ ⟨s, rfl⟩
  let q : ι → Fin m → c.F := fun s t => bs.repr ⟨d s, dmem s⟩ t
  have hq : ∀ s, (d s : PAt φ) = ∑ t, algebraMap c.F (PAt φ) (q s t) * e t := by
    intro s
    have h := congrArg (fun x : K0 => (x : PAt φ)) (bs.sum_repr ⟨d s, dmem s⟩)
    simp only [IntermediateField.coe_sum, Algebra.smul_def] at h
    exact h.symm
  let hh : Fin m → Rul Xo c := fun t => ∑ s, q s t • g s
  have hhsec : ∀ t, hh t ∈ sec Xo c a n := fun t => Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hg s)
  have hev : ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L) (t : Fin m),
      evR Xo c (hh t) y = ∑ s, algebraMap c.F L (q s t) * evR Xo c (g s) y := by
    intro L _ _ y t
    have := map_sum (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y)
      (fun s => q s t • g s) Finset.univ
    simp only [evalL, LinearMap.coe_mk, AddHom.coe_mk, evalAt_smul] at this
    exact this
  have hzero : ∀ t, hh t = 0 := by
    intro t
    refine GlobalTheory.T.weightSection_eq_zero_of_vanishing_finite_extensions E H Dw l Xo c a n (hh t) (hhsec t) fun L _ _ _ y => ?_
    have := GlobalTheory.T.eq_zero_of_sum_mul_embeddings_eq_zero' c.F (PAt φ) L m e he hea (fun t => evR Xo c (hh t) y) (fun σ => by
      rw [← hdrel L σ y]
      simp only [hev, map_sum, map_mul, AlgHom.commutes, hq, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring)
    exact congrFun this t
  have hq0 : ∀ s t, q s t = 0 := fun s t =>
    Fintype.linearIndependent_iff.1 hli (fun s => q s t) (hzero t) s
  apply hd0
  funext s
  apply Subtype.ext
  rw [hq s]
  simp [hq0]

end GlobalTheory.PointsDetectAlg

namespace GlobalTheory.PointsDetectAlg

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct

theorem detects : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), Detects YS fw iC b j := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j x hx
  let bV := Module.Basis.ofVectorSpace S.Ks (NX.FmK S ((j : ℕ) + 1))
  let B := Algebra.TensorProduct.basis (NX.KB S i b) bV
  let r := B.repr x
  let g : r.support → T0.R ((j : ℕ) + 1) := fun s => (cuspOf YS fw j (bV s) : T0.R ((j : ℕ) + 1))
  have hx' : x = ∑ s : r.support, r s • B s := by
    conv_lhs => rw [← B.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    exact (Finset.sum_coe_sort r.support (fun s => r s • B s)).symm
  have hval : ∀ z : Pts YS iC b ((j : ℕ) + 1), ∑ s : r.support, iC (r s) * valC z.1 (g s) = 0 := by
    intro z
    have h := hx z
    rw [hx'] at h
    have e : valAt YS fw j z.1 (∑ s : r.support, r s • B s) = ∑ s : r.support, valAt YS fw j z.1 (r s • B s) :=
      map_sum (valAt YS fw j z.1) (fun s : r.support => r s • B s) Finset.univ
    rw [← h]
    refine Eq.trans ?_ e.symm
    refine Finset.sum_congr rfl fun s _ => ?_
    refine Eq.trans ?_ (valAt_smul YS fw j z.1 (r s) (B s)).symm
    congr 1
    have hb : B s = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bV s : NX.KB S i b ⊗[S.Ks] _) :=
      Algebra.TensorProduct.basis_apply _ _
    refine Eq.trans ?_ (congrArg (valAt YS fw j z.1) hb).symm
    refine Eq.trans ?_ (valAt_tmul YS fw j z.1 1 (bV s)).symm
    exact (one_mul _).symm.trans (congrArg (· * _) (map_one iC).symm)
  have hli : LinearIndependent T0.Q.c.F g := by
    rw [Fintype.linearIndependent_iff]
    intro cf hcf s
    have h1 : ((cuspOf YS fw j (∑ t : r.support, (eKs YS).symm (cf t) • bV t) : Cu T0 κ j) : T0.R ((j : ℕ) + 1)) = 0 := by
      rw [← hcf, map_sum]
      simp only [cuspOf_smul, RingEquiv.apply_symm_apply]
      push_cast
      rfl
    have h2 : ∑ t : r.support, (eKs YS).symm (cf t) • bV t = 0 :=
      (cuspOf YS fw j).injective ((Subtype.ext h1).trans (map_zero _).symm)
    have h3 := Fintype.linearIndependent_iff.1 (bV.linearIndependent.comp _ Subtype.val_injective) _ h2 s
    simpa using h3
  have hI : IntAll (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := fw.laws.intAll _ ⟨Nat.le_add_left _ _, j.2⟩
  have hw := core (embC YS iC b) hI (wtA (κ j)) (κ j).n g (fun s => cuspOf_mem_sec YS fw j _) hli
    (fun s => iC (r s)) hval
  have hr : ∀ s : r.support, r s = 0 := fun s => (map_eq_zero iC).1 (congrFun hw s)
  rw [hx']
  exact (Finset.sum_eq_zero fun s _ => by rw [hr s]; exact zero_smul _ _).trans rfl

end GlobalTheory.PointsDetectAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameCharacterParahoricInvariantStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_character_parahoric_invariant : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] (r t : ℕ) (χ : Fˣ →* ℂˣ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) F) W) (z : MonoidAlgebra ℂ (GL (Fin r) (ZMod p))) (y : W) (ℓ : GL (Fin r) (ZMod p) → GL (Fin r) F), resCard F = p → IsSmooth π → π.IsIrreducible → IsTame χ → y ≠ 0 → IsBlockVec χ π y → (∀ g, IsLift g (ℓ g)) → (z.coeff.sum fun g c => c • π (emb₂ F (stdSum (rfl : r + t = r + t)) (ℓ g, 1)) y) = y → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi F (Two (Fin r) (Fin t))) Y), τ.IsIrreducible ∧ IsSubquotient τ (jac (two (stdSum (rfl : r + t = r + t))) π) ∧ ∃ w : Y, w ≠ 0 ∧ (∀ g ∈ KO F (Fin t), τ (Pi.mulSingle true g) w = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • w) ∧ TypeVec (n := Fin r) (τ.comp (MonoidHom.mulSingle (fun j => GL (Two (Fin r) (Fin t) j) F) false)) z w := by
  first | exact @GlobalTheory.JacTypeVec.exists_subquot_typeVec | exact GlobalTheory.JacTypeVec.exists_subquot_typeVec | (intros; apply GlobalTheory.JacTypeVec.exists_subquot_typeVec <;> assumption)
end

