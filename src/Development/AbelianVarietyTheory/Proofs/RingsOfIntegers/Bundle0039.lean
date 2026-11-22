import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0034
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0033
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GaugeThirdDifferenceSymmetryIntegralExponentials
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0017
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceHarmonic
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CdvrExtSt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PlaceExtField

theorem cdvrExtSt : PullbackSections.CDVRExtSt := by
  intro T hT K _ jK hfin
  letI := jK.toAlgebra
  obtain ⟨T', iT, e, ψ, _, he, hv, hψ, _, hres⟩ := exists_cdvr_finite_extension T K
  refine ⟨T', ψ.toRingHom, e, he, fun a _ => ?_, hres hT⟩

  have h : ψ.toRingHom (jK a) = iT a := hψ a
  rw [h, hv a]

end GlobalTheory.PlaceExtField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteBasisPowerSeriesSubstFiniteColengthStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∃ (r : ℕ) (b : Fin r → MvPowerSeries σ V), Module.finrank V (MvPowerSeries σ V ⧸ Ideal.span (Set.range φ)) = r ∧ ∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i := by
  first | exact @GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient | exact GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient | (intros; apply GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GaugeThirdDifferenceSymmetryIntegralExponentialsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauge_thirdDifference_symmetry_integral_exponentials : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → (∃ Θ : PS V 3 d, IsTheta B K h w0 Θ) ∧ ∃ jo : PS V 1 d, IsIota B K h w0 jo := by
  first | exact @GlobalTheory.PlaceInt.exists_isTheta_and_isIota | exact GlobalTheory.PlaceInt.exists_isTheta_and_isIota | (intros; apply GlobalTheory.PlaceInt.exists_isTheta_and_isIota <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueBoundOfColumnProductsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_bound_of_column_products : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ f : Fin n → PS T.Fr 1 (chD C.ch), (∀ b, IsIntPS T (f b)) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (∑ mo ∈ P.support, P.coeff mo * ∏ b, C.ch.B.nabVal T.Fr C.ch.h H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))) → ChBound C e ρ w n := by
  first | exact @GlobalTheory.PlaceInt.chBound_of_columns | exact GlobalTheory.PlaceInt.chBound_of_columns | (intros; apply GlobalTheory.PlaceInt.chBound_of_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem hv_pulls : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (a : 𝓞 E) (N k k' : ℕ), a * H.bar a = (N : 𝓞 E) → k' = k * N → ∀ (n : ℕ) (F : Fin n → SecN Xo y.x k) (F' : Fin n → SecN Xo y.x k'), (∀ b, Pulls Xo a (F b) (F' b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k' F' P = algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F P := by
  intro E _ _ _ H Dw l Xo c inst hstar nab hnab S _ _ y a N k k' haN hk n F F' hF w P hP
  have e : inst = H.starRing := GlobalTheory.PowGerm.starRing_ext_of_star _ _ (fun x => (hstar x).trans rfl)
  subst e

  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 c.F)) P.support
    (fun m => P.coeff m)
  have hb0 : algebraMap (𝓞 c.F) c.F b ≠ 0 := by
    intro h0
    exact nonZeroDivisors.ne_zero hbM ((IsFractionRing.injective (𝓞 c.F) c.F) (by rw [h0, map_zero]))

  have hsmul : ∀ (k0 : ℕ) (G : Fin n → SecN Xo y.x k0),
      hv Xo c nab y k0 G (algebraMap (𝓞 c.F) c.F b • P) =
        algebraMap c.F S (algebraMap (𝓞 c.F) c.F b) * hv Xo c nab y k0 G P := by
    intro k0 G
    unfold hv
    rw [MvPolynomial.support_smul_eq hb0, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [MvPolynomial.coeff_smul, smul_eq_mul, map_mul, _root_.mul_assoc]

  have hQ : algebraMap (𝓞 c.F) c.F b • P ∈ harmA c w n := by
    unfold HH HHa at hP
    obtain ⟨h1, h2, h3⟩ := hP
    refine ⟨⟨Submodule.smul_mem _ _ h1, fun σ i i' hi t => by rw [map_smul, h2 σ i i' hi t],
      fun m hm σ i => h3 m (MvPolynomial.support_smul hm) σ i⟩, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · obtain ⟨r, hr⟩ := hb m hm
      have hr' : algebraMap (𝓞 c.F) c.F r = algebraMap (𝓞 c.F) c.F b * P.coeff m := by
        rw [hr, Algebra.smul_def]
      rw [← hr']
      exact r.2
    · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
      exact Subring.zero_mem _
  have key : hv Xo c nab y k' F' (algebraMap (𝓞 c.F) c.F b • P) =
      algebraMap c.F S (nrm Dw c w a) * hv Xo c nab y k F (algebraMap (𝓞 c.F) c.F b • P) :=
    GlobalTheory.T.harmonic_value_normalised_pullback_chain_rule E H Dw l Xo c nab hnab S y a N k (k' : ℤ) (by rw [hstar]; exact haN)
      (by exact_mod_cast hk) n F F' (fun i => hF i) w _ hQ
  rw [hsmul, hsmul, _root_.mul_left_comm] at key
  exact mul_left_cancel₀ ((map_ne_zero _).mpr hb0) key
end GlobalTheory.PlaceInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueEqChartValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValue_eq_chart_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (S : Type) [Field S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (k n : ℕ) (F : Fin n → SecN Xo y.x k) (f : Fin n → PS S 1 C.d), (∀ b, IsGerm y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)) → ∀ (w : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HH c w n → hv Xo c nab y k F P = chartVal C k f P := by
  first | exact @GlobalTheory.PlaceInt.hv_eq_chartVal | exact GlobalTheory.PlaceInt.hv_eq_chartVal | (intros; apply GlobalTheory.PlaceInt.hv_eq_chartVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueIntegralOfUnitDiscriminant
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.ChartUnram

open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

theorem isRQ_or_rat (T : CDVR) : TB.IsRQ (R := T.V) T.Fr ∨ Nonempty (Algebra ℚ T.V) := by
  by_cases hN : ∃ N : ℕ, N ≠ 0 ∧ ¬ IsUnit (N : T.V)
  · left
    obtain ⟨N, hN0, hNu⟩ := hN
    refine ⟨IsFractionRing.injective T.V T.Fr, fun y => ?_⟩
    have hNV0 : (N : T.V) ≠ 0 := by exact_mod_cast hN0
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hNV0 hϖ
    have hϖN : ϖ ∣ (N : T.V) := by
      rcases m with _ | m
      · exact absurd (hm.isUnit_iff.2 (by simp)) hNu
      · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := T.V) y
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hs0 hϖ
    obtain ⟨c, hc⟩ : s ∣ (N : T.V) ^ n := hn.dvd.trans (pow_dvd_pow_of_dvd hϖN n)
    refine ⟨c * a, N ^ n, pow_pos (Nat.pos_of_ne_zero hN0) n, ?_⟩
    have hsK : algebraMap T.V T.Fr s ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective T.V T.Fr)]; exact hs0
    have hcast : ((N ^ n : ℕ) : T.Fr) = algebraMap T.V T.Fr ((N : T.V) ^ n) := by
      rw [map_pow, map_natCast]; push_cast; rfl
    rw [hcast, hc, map_mul, map_mul]
    field_simp
  · right
    push Not at hN
    have hu : ∀ z : nonZeroDivisors ℤ, IsUnit (Int.castRingHom T.V z) := by
      rintro ⟨z, hz⟩
      have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
      have h1 := hN z.natAbs (Int.natAbs_ne_zero.2 hz0)
      rcases Int.natAbs_eq z with h | h
      · show IsUnit ((z : ℤ) : T.V)
        rw [h, Int.cast_natCast]; exact h1
      · show IsUnit ((z : ℤ) : T.V)
        rw [h, Int.cast_neg, Int.cast_natCast]; exact h1.neg
    exact ⟨(IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) hu).toAlgebra⟩

section Abstract

variable {R k : Type} [CommRing R] [Field k] [Algebra ℚ k] [Algebra R k]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem value_mem_rat [Algebra ℚ R] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O]
    (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h) (w0 : O) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ)) (σ : T → O →+* k) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a))
    (u : (Σ τ : T, Fin (rr τ)) → Fin d → R)
    (hu : ∀ l a, (dAct k B a).mulVec (fun j => algebraMap R k (u l j)) = σ l.1 a • fun j => algebraMap R k (u l j))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T rr n) k)
    (hP : P ∈ HaO rr n k (algebraMap R k).range cc isX a)
    (f : Fin n → PS k 1 d) (hf : ∀ b, TB.IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ (algebraMap R k).range := by
  classical
  obtain ⟨h0, hh0⟩ := GlobalTheory.canonGauge_exists R d O R B
  obtain ⟨hc, hv⟩ := GlobalTheory.canonGauge_nabVal_baseChange R d O B R k (Algebra.ofId R k) h0 hh0
  have e := GlobalTheory.canonGauge_independence_harmonic R d O k B h _ hg hc T rr cc isX σ hcc hX hσ hsep
    (fun ℓ j => algebraMap R k (u ℓ j)) hu n (MvPolynomial.rename (CVA.lEq (T := T) (r := rr) (n := n)) P)
    (CVA.harm_rename (r := rr) (n := n) cc isX P hP.1.1) w0 m f
  rw [CVA.sum_rename, CVA.sum_rename] at e
  simp only [colM_lEq_colL] at e
  rw [e]
  refine Subring.sum_mem _ fun mo _ => Subring.mul_mem _ (hP.2 mo) (Subring.prod_mem _ fun b _ => ?_)
  choose g hg' using hf b
  have hfb : f b = MvPowerSeries.map (Algebra.ofId R k : R →+* k) (g : PS R 1 d) := by
    ext mm
    exact (hg' mm).symm
  have h1 := hv w0 m g _ u (MvPolynomial.monomial (colL rr n mo b) 1)
  rw [MvPolynomial.map_monomial, map_one, ← hfb] at h1
  exact ⟨_, h1.symm⟩

theorem value_mem_idem (hRQ : TB.IsRQ (R := R) k)
    (B : FB R d O) (h : PS k 2 d) (hg : B.IsCanonGauge k h) (w0 : O) (hw0 : w0 + star w0 = 1) (m : ℕ)
    {T : Type} [Fintype T] (rr : T → ℕ) (cc : T → T) (hcc : ∀ τ, cc (cc τ) = τ) (isX : T → Prop)
    (hX : ∀ τ, isX τ ∨ isX (cc τ)) (hX' : ∀ τ, ¬ (isX τ ∧ isX (cc τ)))
    (σ : T → O →+* k) (hσ : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (hsep : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a))
    (hidem : ∀ t : T, ∃ (n : ℕ) (b : Fin n → O) (c : Fin n → R), (∑ i, algebraMap R k (c i) * σ t (b i) = 1) ∧
      ∀ a : O, ∃ m : Fin n → Fin n → ℤ, (∀ i, a * b i = ∑ j, m i j • b j) ∧
        ∀ j, ∑ i, (m i j : k) * algebraMap R k (c i) = σ t a * algebraMap R k (c j))
    (u : (Σ τ : T, Fin (rr τ)) → Fin d → R)
    (hu : ∀ l a, (dAct k B a).mulVec (fun j => algebraMap R k (u l j)) = σ l.1 a • fun j => algebraMap R k (u l j))
    (n : ℕ) (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T rr n) k)
    (hP : P ∈ HaO rr n k (algebraMap R k).range cc isX a)
    (f : Fin n → PS k 1 d) (hf : ∀ b, TB.IntAA (R := R) k (f b)) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 m (f b) (fun ℓ j => algebraMap R k (u ℓ j))
      (MvPolynomial.monomial (colL rr n mo b) 1) ∈ (algebraMap R k).range := by
  classical
  obtain ⟨φ, hφ⟩ := EigA.eigLift_core hRQ B h hg (fun ℓ : (Σ τ : T, Fin (rr τ)) => ℓ.1) σ u hu hidem
  have heig0 : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ℓ'.1 ≠ cc ℓ.1 →
      ∑ i, (algebraMap R k (φ ℓ' i) - (TB.sg1 k h).mulVec (fun j => algebraMap R k (u ℓ' j)) i) *
        algebraMap R k (u ℓ i) = 0 := by
    intro ℓ ℓ' hne
    obtain ⟨x, hx⟩ := hsep ℓ.1 (cc ℓ'.1) fun e => hne (by rw [e, hcc])
    rw [hσ] at hx
    exact hφ ℓ ℓ' ⟨x, sub_ne_zero.1 hx.ne_zero⟩
  let c : T → T := fun τ => if isX τ then τ else cc τ
  let s : T → Bool := fun τ => decide (isX τ)
  have hcs : ∀ τ, c (cc τ) = c τ ∧ s (cc τ) ≠ s τ := by
    intro τ
    have hc : cc (cc τ) = τ := hcc τ
    by_cases h1 : isX τ
    · have h2 : ¬ isX (cc τ) := fun h2 => hX' τ ⟨h1, h2⟩
      constructor
      · simp only [c, h1, h2, if_true, if_false, hc]
      · simp [s, h1, h2]
    · have h2 : isX (cc τ) := (hX τ).resolve_left h1
      constructor
      · simp only [c, h1, h2, if_true, if_false]
      · simp [s, h1, h2]
  have hnot : ∀ ℓ ℓ' : (Σ τ : T, Fin (rr τ)), ¬ (c ℓ.1 = c ℓ'.1 ∧ s ℓ.1 ≠ s ℓ'.1) → ℓ'.1 ≠ cc ℓ.1 := by
    intro ℓ ℓ' hn he'
    apply hn
    rw [he']
    exact ⟨(hcs ℓ.1).1.symm, (hcs ℓ.1).2.symm⟩
  have key := chartValJ (R := R) (k := k) hRQ 1
    (Submodule.mem_one.2 ⟨1, map_one _⟩) B h hg w0 hw0 m rr cc hcc isX hX c s hcs u φ (fun _ _ => 0)
    (fun _ _ => Submodule.zero_mem _)
    (fun ℓ ℓ' hne => by simpa only [add_zero] using heig0 ℓ ℓ' hne)
    (fun ℓ ℓ' hn => by
      have h1 := hnot ℓ ℓ' hn
      have h2 : ℓ.1 ≠ cc ℓ'.1 := fun h2 => h1 (by rw [h2]; exact (hcc _).symm)
      simp only [TB.betaH]
      rw [Finset.sum_sub_distrib, heig0 ℓ ℓ' h1]
      have h3 := heig0 ℓ' ℓ h2
      simp only [mul_comm] at h3 ⊢
      rw [h3, sub_self])
    (fun ℓ ℓ' _ => by simp [TB.betaH]) (fun ℓ ℓ' _ => by simp [TB.betaH])
    n a P hP
    (∑ mo ∈ P.support, ∑ b, TB.pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL _ n mo b))
    (fun mo hmo => Finset.single_le_sum (f := fun mo => ∑ b, TB.pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1)
      (fun ℓ => s ℓ.1) (colL _ n mo b)) (fun _ _ => Nat.zero_le _) hmo) f hf
  rw [one_pow] at key
  exact Submodule.mem_one.1 key

end Abstract

end GlobalTheory.ChartUnram

open GlobalTheory.ChartUnram ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf in

theorem GlobalTheory.PlaceInt.chBound_zero_of_isUnit_discr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsUnit ((NumberField.discr E : ℤ) : T.V) → ∀ (e : ℕ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e 0 w n := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y C hdisc e w n
  refine GlobalTheory.PlaceInt.chBound_of_columns E H Dw l Xo c hstar T io y C e 0 w n fun k P hP f hf => ?_
  letI := io.toAlgebra
  obtain ⟨B, hBT, hB⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hg, -, heig, -⟩ := hB B hBT
  obtain ⟨gF, gA, -, -, -, -, gu⟩ := C.gen.1
  have hu : C.ch.uvec = fun ℓ i => algebraMap T.V T.Fr (C.uvecT ℓ i) := funext fun ℓ => funext fun i => gu ℓ i
  rw [hu] at heig
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [ChartBiext.toK_self, gF, hBT.1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [ChartBiext.toK_self, gA, hBT.2.1]
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => star_star τ
  have hσ : ∀ (τ : E →+* ℂ) (a : 𝓞 E), (io.comp (embK c (ComplexEmbedding.conjugate τ))) a =
      (io.comp (embK c τ)) (star a) := by
    intro τ a
    refine congrArg io (Subtype.ext ?_)
    change ((embK c _ a : c.F) : ℂ) = ((embK c _ _ : c.F) : ℂ)
    simp only [embK_coe]
    rw [ComplexEmbedding.conjugate_coe_eq, hstar, H.bar_eq, NumberField.IsCMField.complexEmbedding_complexConj]
  have hsep : ∀ τ τ' : E →+* ℂ, τ ≠ τ' → ∃ a, IsUnit ((io.comp (embK c τ)) a - (io.comp (embK c τ')) a) := by
    intro τ τ' hne
    by_contra hall
    push Not at hall
    apply hne
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => ?_
    have h0 := hall x
    rw [isUnit_iff_ne_zero, not_not, sub_eq_zero] at h0
    have h2 := congrArg (fun z : c.F => (z : ℂ)) (io.injective h0)
    simpa only [embK_coe] using h2
  have key : ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal T.Fr C.ch.h H.w0 k (f b)
      (fun ℓ j => algebraMap T.V T.Fr (C.uvecT ℓ j)) (MvPolynomial.monomial (colL Dw.mult n mo b) 1) ∈
        (algebraMap T.V T.Fr).range := by
    rcases isRQ_or_rat T with hRQ | ⟨⟨_⟩⟩
    · have hunit : IsUnit (((discr E).natAbs : ℕ) : T.V) := by
        rcases Int.natAbs_eq (discr E) with h | h
        · rwa [h, Int.cast_natCast] at hdisc
        · rw [h, Int.cast_neg, Int.cast_natCast] at hdisc
          simpa using hdisc.neg
      obtain ⟨v, hv⟩ : ∃ v : T.V, algebraMap T.V T.Fr v * (((discr E).natAbs : ℕ) : T.Fr) = 1 := by
        refine ⟨↑hunit.unit⁻¹, ?_⟩
        rw [← map_natCast (algebraMap T.V T.Fr), ← map_mul, hunit.val_inv_mul, map_one]
      have hint : ∀ τ : E →+* ℂ, ∀ x : 𝓞 E, ∃ v : T.V,
          algebraMap T.V T.Fr v = (io.comp (embF c τ)) (algebraMap (𝓞 E) E x) := by
        intro τ x
        obtain ⟨Q, hPm, hPe⟩ := RingOfIntegers.isIntegral_coe x
        refine IsIntegrallyClosed.isIntegral_iff.1 ⟨Q.map (Int.castRingHom T.V), hPm.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap T.V T.Fr).comp (Int.castRingHom T.V))
          ((io.comp (embF c τ)).comp (algebraMap ℤ E)), ← Polynomial.hom_eval₂]
        exact (congrArg _ hPe).trans (map_zero _)
      exact value_mem_idem hRQ B C.ch.h hg H.w0 (by rw [hstar]; exact CVA.cmHostUnit_add_conj_eq_one H) k Dw.mult _ hcc (InPsi H)
        (CVA.inPsi_or H) (CVA.not_inPsi_both H) (fun τ => io.comp (embK c τ)) hσ hsep
        (fun τ => EigA.idem_data (io.comp (embF c τ)) (hint τ) v hv) C.uvecT heig n _ P hP f hf
    · exact value_mem_rat B C.ch.h hg H.w0 k Dw.mult _ hcc (InPsi H)
        (CVA.inPsi_or H) (fun τ => io.comp (embK c τ)) hσ hsep C.uvecT heig n _ P hP f hf
  rw [neg_zero, EReal.coe_zero]
  refine nval_nonneg_of_int e ?_
  unfold FB.nabVal FB.hL at key ⊢
  rw [eF, eA] at key
  rw [hu]
  exact key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open Formalism.BasicNotions Formalism.MainNotions IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostField_galois_degree_discr_conj_moves_primes : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E), IsGalois ℚ D.host.E ∧ Module.finrank ℚ D.host.E = 4 * D.R.ord ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr D.host.E → p ∣ D.host.condN) ∧ ∀ p ∈ D.host.condN.primeFactors, p.Prime ∧ ∀ 𝔭 : Ideal (𝓞 D.host.E), 𝔭.IsPrime → (p : 𝓞 D.host.E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭 := by
  first | exact @GlobalTheory.PlaceInt.host_galois_discr_moves | exact GlobalTheory.PlaceInt.host_galois_discr_moves | (intros; apply GlobalTheory.PlaceInt.host_galois_discr_moves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralChart_formalBiextension_gauge_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∃ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B ∧ ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → B.IsCanonGauge T.Fr (gaugeOf C) ∧ MvPowerSeries.constantCoeff (gaugeOf C) = 0 ∧ (letI := io.toAlgebra; (∀ (ℓ : Lt1 Dw) (a : 𝓞 E), (dAct T.Fr B a).mulVec (C.ch.uvec ℓ) = io (embK c ℓ.1 a) • C.ch.uvec ℓ) ∧ ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ChBound C e ρ w n → ∀ (k : ℕ) (P : MvPolynomial (LtN Dw n) T.Fr), P ∈ FFV (Dw := Dw) T w n → ∀ g : PS T.V n (chD C.ch), ((-ρ : ℝ) : EReal) ≤ nval T.V e (nabValN B T.Fr (gaugeOf C) H.w0 k (FB.toK T.Fr g) (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P)) := by
  first | exact @GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound | exact GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound | (intros; apply GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InvariantsAndTraceFiniteFreeDomainEndomorphismsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariants_and_trace_finite_free_domain_endomorphisms : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (G : Finset (R →ₐ[A] R)), G.card = Module.finrank A R → (∀ x : R, (∀ g ∈ G, g x = x) → x ∈ (algebraMap A R).range) ∧ ∀ x : R, algebraMap A R (Algebra.trace A R x) = ∑ g ∈ G, g x := by
  first | exact @GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank | exact GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank | (intros; apply GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMulStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNormalisedPullbackSection_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (a b : 𝓞 E) (k k' k'' : ℕ) (F : SecN Xo x k) (F' : SecN Xo x k') (F'' : SecN Xo x k''), Pulls Xo a F F' → Pulls Xo b F' F'' → Pulls Xo (a * b) F F'' := by
  first | exact @GlobalTheory.PullComp.pulls_mul | exact GlobalTheory.PullComp.pulls_mul | (intros; apply GlobalTheory.PullComp.pulls_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecompositionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_group_primary_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x z → ∃ (J J' : Type) (_ : Fintype J) (_ : Fintype J') (a : J → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (a' : J' → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (σ : J × J' ≃ Fin (Λ.zCard N (Dw.p + Dw.q))), Function.Injective a ∧ (∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) ∧ (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ i b, a' i b ^ m = 1 ∧ a' i b ^ (N ^ 2) = 1) ∧ (∀ i i' b, z (σ (i, i')) b = a i b * a' i' b) ∧ Fintype.card J = ℓ ^ (Λ.zCard N (Dw.p + Dw.q)).factorization ℓ := by
  first | exact @GlobalTheory.isotropic_primary_decomposition | exact GlobalTheory.isotropic_primary_decomposition | (intros; apply GlobalTheory.isotropic_primary_decomposition <;> assumption)
end

