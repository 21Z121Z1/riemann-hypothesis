import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0111
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevMoveOfFrOver

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BaseChangeOfFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.LiesBaseChange

theorem isIntegral_of_scale (S : CDVR) {W L : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L]
    [Algebra W L] [IsFractionRing W L] (φ : S.Fr →+* L) (hφ : φ.Finite) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV W (φ z) = (r : ℤ) * vV S.V z) (w : W) :
    (φ.comp (algebraMap S.V S.Fr)).IsIntegralElem (algebraMap W L w) := by
  have hint : ∀ a : S.V, ∃ v : W, algebraMap W L v = φ (algebraMap S.V S.Fr a) := fun a =>
    (IntegralFrameAllCompare.mem_range_iff _).2 (by
      rw [hi]; exact mul_nonneg (by positivity) ((IntegralFrameAllCompare.mem_range_iff _).1 ⟨a, rfl⟩))
  choose g0 hg0 using hint
  have hinj := IsFractionRing.injective W L
  let g : S.V →+* W :=
    { toFun := g0
      map_one' := hinj (by simp [hg0])
      map_mul' := fun a b => hinj (by simp [hg0])
      map_zero' := hinj (by simp [hg0])
      map_add' := fun a b => hinj (by simp [hg0]) }
  have hg : ∀ a, algebraMap W L (g a) = φ (algebraMap S.V S.Fr a) := hg0
  letI : Algebra S.V W := g.toAlgebra
  letI : Algebra S.Fr L := φ.toAlgebra
  letI : Algebra S.V L := (φ.comp (algebraMap S.V S.Fr)).toAlgebra
  have t1 : IsScalarTower S.V W L := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have t2 : IsScalarTower S.V S.Fr L := IsScalarTower.of_algebraMap_eq fun a => rfl
  have : FiniteDimensional S.Fr L := hφ
  obtain ⟨-, hloc, -, -, hfr⟩ := integralClosure_finite_local_of_isAdicComplete S.V S.cpl L
  have : CharZero S.Fr := IsFractionRing.charZero_of_isFractionRing S.V
  have hded : IsDedekindDomain (integralClosure S.V L) := integralClosure.isDedekindDomain S.V S.Fr L
  have hval : ValuationRing (integralClosure S.V L) := by
    have := ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (integralClosure S.V L)).out 2 1).1 hded
    exact this
  have hBW : ∀ b : integralClosure S.V L, ∃ v : W, algebraMap W L v = b := fun b =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.tower_top (A := W) b.2)
  choose k0 hk0 using hBW
  let k : integralClosure S.V L →+* W :=
    { toFun := k0
      map_one' := hinj (by simp [hk0])
      map_mul' := fun a b => hinj (by simp [hk0])
      map_zero' := hinj (by simp [hk0])
      map_add' := fun a b => hinj (by simp [hk0]) }
  have hk : ∀ b, algebraMap W L (k b) = b := hk0
  have hmax : ((maximalIdeal W).comap k).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := S.V) _ ?_
    have hle : maximalIdeal S.V ≤ ((maximalIdeal W).comap k).comap (algebraMap S.V (integralClosure S.V L)) := by
      intro a ha
      by_cases h0 : a = 0
      · simp [h0]
      rw [Ideal.mem_comap, Ideal.mem_comap, mem_maximalIdeal]
      intro hu
      have h1 := IntegralFrameAllCompare.vV_of_isUnit (K := L) hu
      have h3 : (0 : ℤ) < r * vV S.V (algebraMap S.V S.Fr a) :=
        mul_pos (by exact_mod_cast hr) (IntegralFrameAllCompare.vV_pos h0 ha)
      rw [← hi] at h3
      rw [hk] at h1
      exact h3.ne' h1
    have hp : (((maximalIdeal W).comap k).comap (algebraMap S.V (integralClosure S.V L))).IsPrime :=
      inferInstance
    rw [← (maximalIdeal.isMaximal S.V).eq_of_le hp.ne_top hle]
    infer_instance
  have hm := eq_maximalIdeal hmax
  change IsIntegral S.V (algebraMap W L w)
  by_cases hw : w = 0
  · subst hw; rw [map_zero]; exact isIntegral_zero
  have hw' : algebraMap W L w ≠ 0 := (map_ne_zero_iff _ hinj).2 hw
  rcases ValuationRing.isInteger_or_isInteger (integralClosure S.V L) (algebraMap W L w) with ⟨b, hb⟩ | ⟨b, hb⟩
  · rw [← hb]; exact b.2
  · have hb' : (b : L) = (algebraMap W L w)⁻¹ := hb
    have hu : IsUnit b := by
      by_contra hn
      have : b ∈ (maximalIdeal W).comap k := by rw [hm]; exact hn
      refine this (IsUnit.of_mul_eq_one w (hinj ?_))
      rw [map_mul, hk, hb', map_one, inv_mul_cancel₀ hw']
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    have hc' : (b : L) * c = 1 := congrArg Subtype.val hc
    have : (c : L) = algebraMap W L w := by
      rw [hb', inv_mul_eq_one₀ hw'] at hc'
      exact hc'.symm
    rw [← this]; exact c.2

theorem exists_extension (S S' : CDVR) (φ : S.Fr →+* S'.Fr) (hφ : φ.Finite) {r : ℕ} (hr : 0 < r)
    (hi : ∀ z, vV S'.V (φ z) = (r : ℤ) * vV S.V z) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] (f : S.Fr →+* C) (h1 : ∀ a : S.V, ‖f (algebraMap S.V S.Fr a)‖ ≤ 1)
    (h2 : ∀ a ∈ maximalIdeal S.V, ‖f (algebraMap S.V S.Fr a)‖ < 1) :
    ∃ f' : S'.Fr →+* C, f'.comp φ = f ∧ (∀ a : S'.V, ‖f' (algebraMap S'.V S'.Fr a)‖ ≤ 1) ∧
      ∀ a ∈ maximalIdeal S'.V, ‖f' (algebraMap S'.V S'.Fr a)‖ < 1 := by
  obtain ⟨f', hf'⟩ : ∃ f' : S'.Fr →+* C, f'.comp φ = f := by
    letI : Algebra S.Fr S'.Fr := φ.toAlgebra
    letI : Algebra S.Fr C := f.toAlgebra
    have : FiniteDimensional S.Fr S'.Fr := hφ
    exact ⟨(IsAlgClosed.lift (R := S.Fr) (S := S'.Fr) (M := C)).toRingHom,
      RingHom.ext fun x => (IsAlgClosed.lift (R := S.Fr) (S := S'.Fr) (M := C)).commutes x⟩
  have hff : ∀ x, f' (φ x) = f x := fun x => congrArg (fun t : S.Fr →+* C => t x) hf'
  have hle : ∀ a : S'.V, ‖f' (algebraMap S'.V S'.Fr a)‖ ≤ 1 := fun a => by
    obtain ⟨p, hp, hpa⟩ := isIntegral_of_scale S φ hφ hr hi a
    let v : Valuation C NNReal := NormedField.valuation
    let g : S.V →+* v.integer := (f.comp (algebraMap S.V S.Fr)).codRestrict v.integer fun x => by
      change ‖f (algebraMap S.V S.Fr x)‖₊ ≤ 1
      exact_mod_cast h1 x
    have hI : IsIntegral v.integer (f' (algebraMap S'.V S'.Fr a)) := by
      refine ⟨p.map g, hp.map g, ?_⟩
      rw [Polynomial.eval₂_map]
      have := congrArg f' hpa
      rw [Polynomial.hom_eval₂, map_zero, ← RingHom.comp_assoc, hf'] at this
      exact this
    have : ‖f' (algebraMap S'.V S'.Fr a)‖₊ ≤ 1 := (Valuation.integer.integers v).mem_of_integral hI
    exact_mod_cast this
  refine ⟨f', hf', hle, fun a ha => ?_⟩
  by_cases h0 : a = 0
  · simp [h0]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible S.V
  have hπm : π ∈ maximalIdeal S.V := hπ.not_isUnit
  have hπ0 : φ (algebraMap S.V S.Fr π) ≠ 0 :=
    (map_ne_zero φ).2 ((map_ne_zero_iff _ (IsFractionRing.injective S.V S.Fr)).2 hπ.ne_zero)
  have ha0 : algebraMap S'.V S'.Fr a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective S'.V S'.Fr)).2 h0
  have hva := IntegralFrameAllCompare.vV_pos (K := S'.Fr) h0 ha
  have hn : 0 < vV S'.V (φ (algebraMap S.V S.Fr π)) := by
    rw [hi]; exact mul_pos (by exact_mod_cast hr) (IntegralFrameAllCompare.vV_pos hπ.ne_zero hπm)
  obtain ⟨n, hn'⟩ := Int.eq_ofNat_of_zero_le hn.le
  obtain ⟨b, hb⟩ := (IntegralFrameAllCompare.mem_range_iff (V := S'.V)
      ((algebraMap S'.V S'.Fr a) ^ (n : ℤ) * (φ (algebraMap S.V S.Fr π)) ^ (-1 : ℤ))).2 (by
    rw [vV_mul (zpow_ne_zero _ ha0) (zpow_ne_zero _ hπ0), IntegralFrameAllCompare.vV_zpow,
      IntegralFrameAllCompare.vV_zpow, hn']
    nlinarith)
  have he : (algebraMap S'.V S'.Fr a) ^ n = algebraMap S'.V S'.Fr b * φ (algebraMap S.V S.Fr π) := by
    rw [hb, zpow_neg_one, zpow_natCast, inv_mul_cancel_right₀ hπ0]
  have hlt : ‖f' (algebraMap S'.V S'.Fr a)‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, he, map_mul, norm_mul, hff]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hle b) (norm_nonneg _) (h2 π hπm)
  exact lt_of_pow_lt_pow_left₀ n zero_le_one (by rwa [one_pow])

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Formalism.L2.Pj.dualMap (g.comp f) = (Formalism.L2.Pj.dualMap g).comp (Formalism.L2.Pj.dualMap f) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

theorem dual_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) {X : Scheme.{0}}
    {u : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber A) ⟶ X} {u' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber B) ⟶ X}
    (h : u' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap f) ≫ u) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap (g.comp f)) ≫ u =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap g) ≫ u' := by
  rw [h, ← Category.assoc, dualMap_comp]
  congr 1
  exact Spec.map_comp (CommRingCat.ofHom (Formalism.L2.Pj.dualMap f)) (CommRingCat.ofHom (Formalism.L2.Pj.dualMap g))

theorem baseChange_of_finite_extension {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (la : HeightOneSpectrum (𝓞 c.F)) (Tw : PointsOfFlagModel.Tower (Formalism.MainNotions.WeightAlgebra.resCh la) Xo c) (S S' : CDVR)
    (io : c.F →+* S.Fr) (φ : S.Fr →+* S'.Fr) (y : IntFr Xo c S io) (y' : IntFr Xo c S' (φ.comp io))
    (hφ : φ.Finite) {r : ℕ} (hr0 : 0 < r) (hr : ∀ z, vV S'.V (φ z) = (r : ℤ) * vV S.V z)
    (mx : letI := io.toAlgebra; letI := (φ.comp io).toAlgebra
      y'.1.x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ ≫ y.1.x)
    (mu : letI := io.toAlgebra; letI := (φ.comp io).toAlgebra
      ∀ τ i, y'.1.u τ i = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (Formalism.L2.Pj.dualMap φ) ≫ y.1.u τ i)
    (z : PointsOfFlagModel.Pt Tw .yy) (hl : LiesOverBaseChange la Tw S io y z) : LiesOverBaseChange la Tw S' (φ.comp io) y' z := by
  obtain ⟨h0, f, hf, h1, h2, hx, hu⟩ := hl
  obtain ⟨f', hf', h1', h2'⟩ := exists_extension S S' φ hφ hr0 hr f h1 h2
  subst hf'
  have e1 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (f'.comp φ) =
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap f' ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ :=
    Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom f')
  refine ⟨h0, f', hf, h1', h2', ?_, fun τ i => (hu τ i).imp fun u' h => ⟨h.1, h.2.trans (dual_comp φ f' (mu τ i))⟩⟩
  exact hx.trans ((congrArg (· ≫ _) e1).trans ((Category.assoc _ _ _).trans
    (congrArg (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap f' ≫ ·) mx.symm)))

theorem lies_of_finite_extension : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (S S' : CDVR) (io : T.Q.c.F →+* S.Fr) (φ : S.Fr →+* S'.Fr) (y : IntFr (T.Q.Xo j) T.Q.c S io) (y' : IntFr (T.Q.Xo j) T.Q.c S' (φ.comp io)) (e e' : ℕ), φ.Finite → OverLa la S.V io e → OverLa la S'.V (φ.comp io) e' → (∀ a : S.V, ∃ b : S'.V, algebraMap S'.V S'.Fr b = φ (algebraMap S.V S.Fr a)) → (letI := io.toAlgebra; letI := (φ.comp io).toAlgebra; FrMap ({ φ with commutes' := fun _ => rfl } : S.Fr →ₐ[T.Q.c.F] S'.Fr) y.1 y'.1) → ∀ eta, T.G.lies j la S io y eta → T.G.lies j la S' (φ.comp io) y' eta := by
  intro D T _ j _ la S S' io φ y y' e e' hφ ho ho' hj hm eta hl hjm
  obtain ⟨z, hz, hl'⟩ := hl hjm
  obtain ⟨r, hr⟩ := IntegralFrameAllCompare.exists_scale (V := S.V) (W := S'.V) φ fun a => hj a
  have hee := IntegralFrameAllCompare.index_eq ho ho' hr
  have hr0 : 0 < r := Nat.pos_of_mul_pos_right (hee ▸ ho'.1)
  exact ⟨z, hz, baseChange_of_finite_extension la _ S S' io φ y y' hφ hr0 hr hm.1 hm.2.1 z hl'⟩

end GlobalTheory.LiesBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselGapExistsFunctionalStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_gap_exists_functional : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → SideG k r z π u μW μN μG νq → ∃ l, IsBeL R z π μW μN l := by
  first | exact @GlobalTheory.exists_normalised_bessel_map | exact GlobalTheory.exists_normalised_bessel_map | (intros; apply GlobalTheory.exists_normalised_bessel_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartFromPointDatumOfLawsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFromPointDatum_of_laws : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → LinkSt := by
  first | exact @GlobalTheory.ChartLink.link | exact GlobalTheory.ChartLink.link | (intros; apply GlobalTheory.ChartLink.link <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslateStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeries_shift_eq_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  first | exact @GlobalTheory.MomOne.Transfer.shift_eq_hat_translate | exact GlobalTheory.MomOne.Transfer.shift_eq_hat_translate | (intros; apply GlobalTheory.MomOne.Transfer.shift_eq_hat_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesTranslateNormLe
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TransNorm

variable {q : ℕ} [Fact q.Prime]

lemma bd_add {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) (hg : Bd B g) : Bd B (f + g) := by
  simpa using ((sup_norm_laws q).1 f g B B hf hg).1

lemma bd_mul_one {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) (hg : Bd 1 g) : Bd B (f * g) := by
  simpa using ((sup_norm_laws q).1 f g B 1 hf hg).2

lemma bd_C {a : ℂ_[q]} {B : ℝ} (ha : ‖a‖ ≤ B) : Bd B (C a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · simpa using (norm_nonneg a).trans ha

lemma bd_one : Bd 1 (1 : ℂ_[q]⟦X⟧) := by
  simpa using (bd_C (a := (1 : ℂ_[q])) (B := 1) (by simp))

lemma bd_X : Bd 1 (X : ℂ_[q]⟦X⟧) := by
  intro n
  rw [coeff_X]
  split_ifs <;> simp

lemma bd_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (n : ℕ) : Bd 1 (f ^ n) := by
  induction n with
  | zero => simpa using bd_one
  | succ n ih => rw [pow_succ]; exact bd_mul_one ih hf

lemma bd_sum {α : Type} (s : Finset α) (f : α → ℂ_[q]⟦X⟧) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, Bd B (f i)) : Bd B (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (Bd B) (fun _ _ => bd_add) ?_ hf
  intro n
  simpa using hB

lemma bd_prod {α : Type} (s : Finset α) (f : α → ℂ_[q]⟦X⟧)
    (hf : ∀ i ∈ s, Bd 1 (f i)) : Bd 1 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (Bd 1) (fun _ _ => bd_mul_one) bd_one hf

lemma bd_sub_C {f : ℂ_[q]⟦X⟧} {a : ℂ_[q]} (hf : Bd 1 f) (ha : ‖a‖ ≤ 1) : Bd 1 (f - C a) := by
  have := bd_add hf (bd_C (a := -a) (by simpa using ha))
  simpa [sub_eq_add_neg] using this

lemma bd_cancel {f g : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bdd f) (hg : Bd 1 g)
    (hg' : ∀ r : ℝ, r < 1 → ∃ n, r < ‖coeff n g‖) (h : Bd B (f * g)) : Bd B f := by
  intro i
  have key := (sup_norm_laws q).2.2.2.1 f g B hf ⟨1, hg⟩ h i
  by_contra hlt
  push Not at hlt
  have hB : 0 ≤ B := (norm_nonneg _).trans (h 0)
  have hpos : 0 < ‖coeff i f‖ := hB.trans_lt hlt
  obtain ⟨n, hn⟩ := hg' (B / ‖coeff i f‖) ((div_lt_one hpos).2 hlt)
  have := key n
  rw [div_lt_iff₀ hpos] at hn
  nlinarith

lemma bd_cancel_prod {α : Type} (s : Finset α) (g : α → ℂ_[q]⟦X⟧) {B : ℝ}
    (hg : ∀ i, Bd 1 (g i)) (hg' : ∀ i, ∀ r : ℝ, r < 1 → ∃ n, r < ‖coeff n (g i)‖)
    {f : ℂ_[q]⟦X⟧} (hf : Bdd f) (h : Bd B (f * ∏ i ∈ s, g i)) : Bd B f := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    apply ih
    rw [Finset.prod_insert ha, mul_comm (g a), ← mul_assoc] at h
    obtain ⟨C, hC⟩ := hf
    exact bd_cancel ⟨C, bd_mul_one hC (bd_prod s g fun i _ => hg i)⟩ (hg a) (hg' a) h

lemma analyticAt_eval (p : Polynomial ℂ) {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    AnalyticAt ℂ (fun z => p.eval (F z)) z := by
  simp only [Polynomial.eval_eq_sum_range]
  exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul (hF.pow i)

lemma hat_eval (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (hℓ : constantCoeff ℓ = 0) (p : Polynomial ℂ)
    {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    hat ι ℓ (fun z => p.eval (F z)) =
      p.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (ι : ℂ →+* ℂ_[q])) (hat ι ℓ F) := by
  obtain ⟨h1, h2, -⟩ := TaylorRead.hat_laws q ι ℓ hℓ
  induction p using Polynomial.induction_on with
  | C a => simpa using h2 a
  | add p r hp hr =>
    simp only [Polynomial.eval_add, Polynomial.eval₂_add]
    rw [(h1 _ _ (analyticAt_eval p hF) (analyticAt_eval r hF)).1, hp, hr]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc]
    simp only [Polynomial.eval_mul (q := Polynomial.X), Polynomial.eval_X, Polynomial.eval₂_mul_X]
    rw [(h1 _ _ (analyticAt_eval _ hF) hF).2.1, ih]

lemma bd_eval₂ (ι : ℂ ≃+* ℂ_[q]) (p : Polynomial ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ i ≤ p.natDegree, ‖ι (p.coeff i)‖ ≤ B) {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) :
    Bd B (p.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (ι : ℂ →+* ℂ_[q])) f) := by
  rw [Polynomial.eval₂_eq_sum_range]
  refine bd_sum _ _ hB fun i hi => bd_mul_one (bd_C ?_) (bd_pow hf i)
  exact hp i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

lemma norm_coeff_prod (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (a : Fin m → ℂ) (ha : ∀ i, ‖ι (a i)‖ ≤ 1) (n : ℕ) :
    ‖ι ((∏ i, (Polynomial.X - Polynomial.C (a i))).coeff n)‖ ≤ 1 := by
  have h : Bd 1 (∏ i, (X - C (ι (a i)) : ℂ_[q]⟦X⟧)) :=
    bd_prod _ _ fun i _ => bd_sub_C bd_X (ha i)
  have e : (∏ i, (X - C (ι (a i)) : ℂ_[q]⟦X⟧)) =
      Polynomial.coeToPowerSeries.ringHom
        ((∏ i, (Polynomial.X - Polynomial.C (a i))).map (ι : ℂ →+* ℂ_[q])) := by
    simp [Polynomial.map_prod, map_prod]
  have := h n
  rw [e] at this
  simpa only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe, Polynomial.coeff_map, RingHom.coe_coe] using this

lemma analyticAt_x_of_not_mem_lattice (M : Mdl q) {t : ℂ} (ht : t ∉ M.L.lattice) : AnalyticAt ℂ M.x t := by
  have := M.L.analyticOnNhd_weierstrassP t ht
  unfold Mdl.x
  fun_prop

lemma analyticAt_y (M : Mdl q) {t : ℂ} (ht : t ∉ M.L.lattice) : AnalyticAt ℂ M.y t := by
  have := M.L.analyticOnNhd_derivWeierstrassP t ht
  have := analyticAt_x_of_not_mem_lattice M ht
  unfold Mdl.y
  fun_prop

lemma analyticAt_shift {F : ℂ → ℂ} {t : ℂ} (hF : AnalyticAt ℂ F t) :
    AnalyticAt ℂ (fun z => F (z + t)) 0 :=
  AnalyticAt.comp_of_eq (g := F) (f := fun z => z + t) hF (by fun_prop) (by simp)

theorem translate_norm_le : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ) (t : ℂ) (B : ℝ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → AnalyticAt ℂ φ t → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → ¬ M.Small t → Bdd (hat M.ι ℓ (fun z => φ (z + t))) → Bd B (hat M.ι ℓ φ) → Bd B (hat M.ι ℓ (fun z => φ (z + t))) := by
  intro q _ M ℓ φ t B hc hE h0 ht hpole hts hbdd hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hℓ := hc.2.1
  obtain ⟨hl1, hl2, -⟩ := TaylorRead.hat_laws q M.ι ℓ hℓ
  obtain ⟨m, P, A, B', hP, hid⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hc.1 hE
  have hPx : ∀ i, ‖M.ι (M.x (P i))‖ ≤ 1 := fun i =>
    not_lt.1 fun h => hpole _ (hP i).2 (Or.inr h)
  obtain ⟨-, v, xs, ys, -, hxs, hys, -, hxs0, hys0, -, -, -, hread⟩ := GlobalTheory.T.integral_weierstrass_chart_xy_unit_series q M ℓ hc
  set D : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hD
  set k := max A.natDegree B'.natDegree with hk
  have e0 := hread φ A B' k h0 (le_max_left _ _) (le_max_right _ _) (fun _ => 1) analyticAt_const
    D D.natDegree le_rfl (by simpa only [one_mul] using hid 0)
  have hS : Bd B (∑ i ∈ Finset.range (k + 1),
      (C (M.ι (A.coeff i)) * X ^ (2 * (k - i) + 3) * xs ^ i +
        C (M.ι (B'.coeff i)) * X ^ (2 * (k - i)) * xs ^ i * ys)) := by
    refine (sup_norm_laws q).2.2.2.2.2 _ 1 (2 * D.natDegree) B bd_one (by simp) ?_
    rw [hl2, map_one, map_one, one_mul] at e0
    rw [mul_one, ← e0]
    refine bd_mul_one (bd_mul_one hB (bd_pow bd_X _)) (bd_sum _ _ zero_le_one fun i _ => ?_)
    exact bd_mul_one (bd_mul_one (bd_C (norm_coeff_prod M.ι _ hPx i)) (bd_pow bd_X _)) (bd_pow hxs _)
  have hco := Triang.coeff_norm_le q xs ys k (fun i => M.ι (A.coeff i)) (fun i => M.ι (B'.coeff i)) B
    hxs hys hxs0 hys0 hS
  obtain ⟨hxt, hyt, hbig⟩ := GlobalTheory.T.chart_hat_coeff_bounds q M ℓ t hc hts
  have htl : t ∉ M.L.lattice := fun h => hts (Or.inl h)
  have ax := analyticAt_shift (analyticAt_x_of_not_mem_lattice M htl)
  have ay := analyticAt_shift (analyticAt_y M htl)
  have aφ := analyticAt_shift ht
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), φ (z + t) * D.eval (M.x (z + t)) =
      A.eval (M.x (z + t)) + B'.eval (M.x (z + t)) * M.y (z + t) := by
    have tt : Filter.Tendsto (fun z : ℂ => z + t) (𝓝[≠] 0) (𝓝[≠] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Filter.Tendsto (fun z : ℂ => z + t) (𝓝 0) (𝓝 (0 + t)) :=
          (continuous_id.add continuous_const).tendsto 0
        rw [zero_add] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    exact tt.eventually (hid t)
  have e1 := (hl1 _ _ (aφ.mul (analyticAt_eval D ax))
    ((analyticAt_eval A ax).add ((analyticAt_eval B' ax).mul ay))).2.2.1 hev
  have e2 := (hl1 _ _ aφ (analyticAt_eval D ax)).2.1
  have e3 := (hl1 _ _ (analyticAt_eval A ax) ((analyticAt_eval B' ax).mul ay)).1
  have e4 := (hl1 _ _ (analyticAt_eval B' ax) ay).2.1
  have e5 : hat M.ι ℓ (fun z => φ (z + t)) * hat M.ι ℓ (fun z => D.eval (M.x (z + t))) =
      hat M.ι ℓ (fun z => A.eval (M.x (z + t))) +
        hat M.ι ℓ (fun z => B'.eval (M.x (z + t))) * hat M.ι ℓ (fun z => M.y (z + t)) := by
    rw [← e2, ← e4]
    exact e1.trans e3
  rw [hat_eval _ _ hℓ D ax, hat_eval _ _ hℓ A ax, hat_eval _ _ hℓ B' ax] at e5
  have e6 : D.eval₂ ((C : ℂ_[q] →+* ℂ_[q]⟦X⟧).comp (M.ι : ℂ →+* ℂ_[q]))
      (hat M.ι ℓ (fun z => M.x (z + t))) =
      ∏ i, (hat M.ι ℓ (fun z => M.x (z + t)) - C (M.ι (M.x (P i)))) := by
    rw [hD, Polynomial.eval₂_finsetProd]
    simp
  rw [e6] at e5
  refine bd_cancel_prod Finset.univ _ (fun i => bd_sub_C hxt (hPx i)) (fun i r hr => ?_) hbdd ?_
  · obtain ⟨n, hn, hn'⟩ := hbig r hr
    refine ⟨n, ?_⟩
    rwa [map_sub, coeff_C, if_neg hn.ne', sub_zero]
  · rw [e5]
    exact bd_add (bd_eval₂ _ _ hB0 (fun i hi => (hco i (hi.trans (le_max_left _ _))).1) hxt)
      (bd_mul_one (bd_eval₂ _ _ hB0 (fun i hi => (hco i (hi.trans (le_max_right _ _))).2) hxt) hyt)

end GlobalTheory.MomOne.TransNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsConjLevelMapByLevelMoves
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ConjLevelMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_inv {S : Scheme.{0}} {t : SAB H S} (e : S ≅ S) (n : SABMap t t e.hom) :
    ∃ n' : SABMap t t e.inv, n.φ ≫ n'.φ = 𝟙 _ := by
  obtain ⟨i, hi⟩ := ObjMaps.exists_sab_id t
  obtain ⟨i', hi'⟩ := LevelFibre.sab_cast e.inv_hom_id.symm i
  obtain ⟨n', hn'⟩ := ObjMaps.exists_sab_cancel n i'
  have h : n'.φ ≫ n.φ = 𝟙 _ := hn'.symm.trans (hi'.trans hi)
  have pn : IsPullback n.φ t.G.hom t.G.hom e.hom := n.cart.1
  have : IsIso n.φ := pn.isIso_fst_of_isIso
  refine ⟨n', ?_⟩
  rw [← cancel_mono n.φ, Category.assoc, h, Category.comp_id, Category.id_comp]

theorem conj_sec {S S₂ : Scheme.{0}} {t : SAB H S} {t₂ : SAB H S₂} {r r' : S₂ ⟶ S} {ρ : S ⟶ S} {ρ₂ : S₂ ≅ S₂}
    (m : SABMap t₂ t r) (m' : SABMap t₂ t r') (ν : SABMap t t ρ) (ν₂ : SABMap t₂ t₂ ρ₂.hom)
    (hr : ρ₂.hom ≫ r' = r ≫ ρ) (hφ : ν₂.φ ≫ m'.φ = m.φ ≫ ν.φ)
    {σ σ' : 𝟙_ (Over S₂) ⟶ t₂.G} {τ τ' : 𝟙_ (Over S) ⟶ t.G} (k : ℕ)
    (h₂ : σ'.left ≫ ν₂.φ = ρ₂.hom ≫ σ.left) (hm : (σ' ^ k).left ≫ m.φ = r ≫ τ'.left)
    (h : τ'.left ≫ ν.φ = ρ ≫ τ.left) : (σ ^ k).left ≫ m'.φ = r' ≫ τ.left := by
  have e := OverMove.pow_left_comp ν₂ h₂ k
  have a₁ : ρ₂.hom ≫ (σ ^ k).left ≫ m'.φ = ((σ' ^ k).left ≫ m.φ) ≫ ν.φ :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m'.φ) e.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg ((σ' ^ k).left ≫ ·) hφ).trans (Category.assoc _ _ _).symm)))
  have a₂ : (r ≫ τ'.left) ≫ ν.φ = ρ₂.hom ≫ r' ≫ τ.left :=
    (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ τ.left) hr.symm).trans (Category.assoc _ _ _))))
  exact (cancel_epi ρ₂.hom).1 (a₁.trans ((congrArg (· ≫ ν.φ) hm).trans a₂))

end ConjLevelMap

open ConjLevelMap in

theorem exists_conj_levelMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.EtaOK → ∀ (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ) (ρ₂ : d.Xo₂.X ≅ d.Xo₂.X) (ν₂ : SABMap d.Xo₂.univ.t d.Xo₂.univ.t ρ₂.hom) (gM gA gM₂ gA₂ : Dw.La →ₗ[𝓞 E] Dw.La), IsLevMove ρ ν gM gA → IsLevMove ρ₂.hom ν₂ gM₂ gA₂ → (∀ a, gM₂ a - gM a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ a, Dw.ModN l.A (gA₂ a - gA a)) → ∃ (r' : d.Xo₂.X ⟶ Xo.X) (m' : SABMap d.Xo₂.univ.t Xo.univ.t r'), ρ₂.hom ≫ r' = d.r ≫ ρ ∧ ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ ∧ DeltaDat.EtaOK { d with r := r', m := m' } := by
  intro E _ _ _ H Dw l Xo c n d hE ρ ν ρ₂ ν₂ gM gA gM₂ gA₂ h h₂ hM hA
  obtain ⟨i, hi⟩ := exists_inv ρ₂ ν₂
  obtain ⟨q, hq⟩ := ObjMaps.exists_sab_comp ν d.m
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_comp q i
  have hr : ρ₂.hom ≫ ρ₂.inv ≫ d.r ≫ ρ = d.r ≫ ρ := ρ₂.hom_inv_id_assoc _
  have hφ : ν₂.φ ≫ m'.φ = d.m.φ ≫ ν.φ := by
    rw [hm', hq, ← Category.assoc, hi, Category.id_comp]
  have eM : ∀ a, Xo.univ.eta (gM₂ a) = Xo.univ.eta (gM a) := fun a => by
    rw [← sub_add_cancel (gM₂ a) (gM a), Xo.univ.eta_add, Xo.univ.eta_ker _ (hM a), _root_.one_mul]
  have eA : ∀ a, Xo.univ.etaA (gA₂ a) = Xo.univ.etaA (gA a) := fun a => by
    obtain ⟨x, hx⟩ := hA a
    rw [← sub_add_cancel (gA₂ a) (gA a), Xo.univ.etaA_add, hx, Xo.univ.etaA_ker, _root_.one_mul]
  refine ⟨_, m', hr, hφ, fun a => ?_, fun a => ?_⟩
  · exact conj_sec d.m m' ν ν₂ hr hφ d.pd (h₂.2.1 a) (hE.1 (gM₂ a)) (by rw [eM]; exact h.2.1 a)
  · exact conj_sec d.m m' ν ν₂ hr hφ (d.l₂.A / l.A) (h₂.2.2 a) (hE.2 (gA₂ a)) (by rw [eA]; exact h.2.2 a)

end GlobalTheory
end

