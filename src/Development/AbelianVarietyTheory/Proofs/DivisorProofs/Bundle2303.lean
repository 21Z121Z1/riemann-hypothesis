import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0058
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortBoundOfTrivAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2255
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2253
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointGenericFibre
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem isTest_base_generic : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → ∀ yb : Sp 𝓞_ℂ_[p] ⟶ X, IsTest p Xw yb → ∃ φ : V →+* 𝓞_ℂ_[p], Function.Injective φ ∧ IsLocalHom φ ∧ yb ≫ s = Spec.map (CommRingCat.ofHom φ) ∧ ∃ y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s, y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb := by
  intro F _ _ V _ p _ hp X s Xw _ yb _

  obtain ⟨φ, hφ⟩ : ∃ φ : V →+* 𝓞_ℂ_[p], yb ≫ s = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage (yb ≫ s)).hom, (Spec.map_preimage (yb ≫ s)).symm⟩

  have hpV0 : ((p : V) : F) ≠ 0 := by
    push_cast; exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpV : (p : V) ∈ IsLocalRing.maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := (V.valuation_eq_one_iff (p : V)).1 hu
    have h2 := (V.mem_nonunits_iff).1 hp
    have : ((p : V) : F) = (p : F) := by push_cast; rfl
    rw [this] at h1
    exact (ne_of_lt h2) h1
  have hpV0' : (p : V) ≠ 0 := fun h => hpV0 (by rw [h]; rfl)
  have hφp : φ (p : V) = (p : 𝓞_ℂ_[p]) := map_natCast φ p
  have hpO : ¬ IsUnit (p : 𝓞_ℂ_[p]) := Formalism.BasicNotions.Loc.OC_l_not_unit p
  have hpO0 : (p : 𝓞_ℂ_[p]) ≠ 0 := by
    intro h
    have : ((p : 𝓞_ℂ_[p]) : ℂ_[p]) = 0 := by rw [h]; rfl
    push_cast at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)

  have hmax : ∀ P : Ideal V, P.IsPrime → P ≠ ⊥ → P = IsLocalRing.maximalIdeal V := fun P hP hne =>
    IsLocalRing.eq_maximalIdeal (hP.isMaximal hne)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    by_contra hne
    push_neg at hne
    obtain ⟨a, ha, ha0⟩ := hne
    have hker : RingHom.ker φ ≠ ⊥ := fun h => ha0 (by
      have : a ∈ RingHom.ker φ := ha
      rw [h] at this; exact this)
    have := hmax _ (RingHom.ker_isPrime φ) hker
    have hp' : (p : V) ∈ RingHom.ker φ := this ▸ hpV
    exact hpO0 (hφp ▸ hp')
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hP := hmax (Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p])) (Ideal.comap_isPrime _ _) (by
      intro h
      have : (p : V) ∈ Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]) := by
        rw [Ideal.mem_comap, hφp, IsLocalRing.mem_maximalIdeal]; exact hpO
      rw [h, Ideal.mem_bot] at this
      exact hpV0' this)
    have : a ∈ Ideal.comap φ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]) := by
      rw [hP, IsLocalRing.mem_maximalIdeal]; exact hna
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal] at this
    exact this ha
  refine ⟨φ, hinj, hloc, hφ, ?_⟩

  have hg : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) :=
    (FaithfulSMul.algebraMap_injective _ _).comp hinj
  obtain ⟨ψ, hψ⟩ : ∃ ψ : FractionRing V →+* ℂ_[p],
      ψ.comp (algebraMap V (FractionRing V)) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ :=
    ⟨IsFractionRing.lift (K := FractionRing V) hg,
      RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := FractionRing V) hg x⟩
  have w : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb) ≫ s =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
    rw [Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hψ]
  let y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s := pullback.lift _ _ w
  refine ⟨y, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι
  exact pullback.lift_fst _ _ w

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointLiftProper
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem field_pt_eq_bot {K : Type} [Field K] (z : Sp K) : z = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) :=
  by haveI := z.isPrime; exact PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

theorem isTest_lift (p : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (hπ : IsProper π) (Xw O : X.Opens)
    (hO : Xw ≤ O) (hiso : IsIso (π ∣_ O)) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (hyb : IsTest p Xw yb) :
    ∃ yb', IsTest p (π ⁻¹ᵁ Xw) yb' ∧ yb' ≫ π = yb := by
  obtain ⟨⟨T, kO, yT, hfin, hinj, hyT⟩, hrange⟩ := hyb
  have hgen : yT (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ Xw := by
    have h1 := hrange ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]), rfl⟩
    rw [bot_map (FaithfulSMul.algebraMap_injective 𝓞_ℂ_[p] ℂ_[p]), ← hyT, bot_map hinj] at h1
    exact h1
  set y : Sp T.Fr ⟶ X := spMap (algebraMap T.V T.Fr) ≫ yT with hy
  have hyO : Set.range y ⊆ (O : Set X) := by
    rintro _ ⟨z, rfl⟩
    rw [field_pt_eq_bot z, hy, bot_map (IsFractionRing.injective T.V T.Fr)]
    exact hO hgen
  have hr : Set.range y ⊆ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hyO
  let y₀ : Sp T.Fr ⟶ O := IsOpenImmersion.lift O.ι y hr
  let y' : Sp T.Fr ⟶ X' := y₀ ≫ inv (π ∣_ O) ≫ (π ⁻¹ᵁ O).ι
  have hy' : y' ≫ π = spMap (algebraMap T.V T.Fr) ≫ yT := by
    simp only [y', Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, y₀, IsOpenImmersion.lift_fac]
    exact hy
  haveI : ValuationRing T.V := inferInstance
  obtain ⟨yT', -, hyT'⟩ := valuative_lift_of_isProper π y' yT hy'
  refine ⟨spMap kO ≫ yT', ⟨⟨T, kO, yT', hfin, hinj, rfl⟩, ?_⟩, by rw [Category.assoc, hyT', hyT]⟩
  rintro _ ⟨z, rfl⟩
  show π _ ∈ Xw
  have := hrange ⟨z, rfl⟩
  rw [← hyT, ← hyT'] at this
  simp only [Scheme.Hom.comp_apply, Category.assoc] at this
  exact this

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThRuleLower
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.ThetaBound
open Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.RefSum.LowP

set_option maxHeartbeats 1000000 in

theorem thRule_lower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (p : ℕ), p.Prime → ¬ p ∣ l.M → ∀ (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P₁ ∈ harmA (Dw := Dw) c a n, ∀ A B : ℝ, PolyBetween Xo la P₁ A B → ∀ (x : Fin n → Dw.La) (f : Rul Xo c), IsThRule Xo c nab x P₁ f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → (A : EReal) ≤ nval T.V (vV T.V (p : T.Fr)).toNat (evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro nab hnab p hp hpM la a n P₁ hP₁ A B hPB x f hf T io e ho y hy
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨T', iT, r, y', C', ⟨hr, hiT, φ, hφ, hmap⟩, hfin, hgood, hrat⟩ :=
    Prep.exists_good_chart_allRat E H Dw l Xo c hnab.1 T io y hy (l.M ^ 2) (pow_pos hM0 2)
  have ho' := ho.bc iT hr hiT
  have hvp : 0 < vV T.V (p : T.Fr) := by
    have h1 := ho.2 (p : c.F)
    rw [map_natCast] at h1
    rw [h1]
    exact mul_pos (by exact_mod_cast ho.1) (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.vLa_pos la.1 p hp.ne_zero la.2)
  have hvp' : vV T'.V (p : T'.Fr) = (r : ℤ) * vV T.V (p : T.Fr) := by
    rw [← map_natCast iT p, hiT]
  obtain ⟨k₀, hk₀⟩ := Int.eq_ofNat_of_zero_le hvp.le
  have he' : (vV T'.V (p : T'.Fr)).toNat = r * (vV T.V (p : T.Fr)).toNat := by
    rw [hvp', hk₀, ← Nat.cast_mul, Int.toNat_natCast, Int.toNat_natCast]
  have hk0 : 0 < k₀ := by omega
  have he'pos : 0 < (vV T'.V (p : T'.Fr)).toNat := by
    rw [he', hk₀, Int.toNat_natCast]; exact Nat.mul_pos hr hk0
  have hu : IsUnit (l.M : T'.V) := by
    refine GlobalTheory.PlaceInt.ShortTriv.isUnit_of_coprime T' (ℓ := p)
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)) fun h => ?_
    have h2 := GlobalTheory.PlaceInt.ShortTriv.vV_natCast T' h
    rw [hvp', hk₀] at h2
    have : (0 : ℤ) < (r : ℤ) * (k₀ : ℤ) := by positivity
    omega
  rw [← nval_bc iT hr hiT ((vV T.V (p : T.Fr)).toNat), ← he']
  obtain ⟨n', j, -, -, a3⟩ := (GlobalTheory.TorsFac.factorisation E H Dw l Xo l.M p l.odd dvd_rfl hp).1 hpM
  letI := (iT.comp io).toAlgebra
  choose F hF using fun b : Fin n =>
    (RatData.exists_thetaVal_data E H Dw l Xo c T'.Fr y'.1).1 hrat (x b)
  have hev : iT (evI y f) = thExpr Xo c nab y'.1 P₁ F := by
    letI : Algebra T.Fr T'.Fr := iT.toAlgebra
    exact GlobalTheory.T.thetaRule_value_integral_framed_point_extension_field E H Dw l Xo c nab hnab T io y T'.Fr φ hφ y'.1 hmap a n x P₁ hP₁ F hF f hf
  have ht : ∀ b, ∃ t' : ptO Xo (xOf y') ⟶ Xo.univ.t.G, t' ^ (l.M ^ 2) = 1 ∧
      IsUUOver Xo.univ.t.G Xo.univ.t.PP l.M (sOf1 y') 1 t' (F b) := by
    intro b
    have h1 : levPt Xo y'.1.x (x b) ^ l.M = 1 := by
      obtain ⟨t', -, -, -, -, b1, b2, -⟩ := hF b
      rw [← b1, ← pow_mul, ← pow_two]
      exact (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1
    obtain ⟨t', -, b2, b3⟩ :=
      (uu_through_moves E H Dw l Xo T'.Fr (xOf y') l.M l.odd (sOf1 y')).2 _ _ (F b) h1 (hF b)
    exact ⟨t', (a3 _ t' (killed_pow Xo t' b2) ⟨2, b2⟩).1, b3⟩
  choose t' ht1 ht2 using ht
  have hρ : ∀ k, (A : EReal) ≤ nuLocOf C' (vV T'.V (p : T'.Fr)).toNat k (MvPolynomial.map (iT.comp io) P₁) :=
    fun k => (hPB T' (iT.comp io) (r * e) ho' y' hfin C' k).1
  have hb := GlobalTheory.T.harmonic_value_ge_local_depth_prime_to_p E H Dw l Xo c T' (iT.comp io) y' C' hgood nab hnab _ A a n he'pos P₁ hP₁ hρ l.M l.odd hu
    t' F (fun b => ⟨ht1 b, ht2 b⟩)
  have hh := (hv_linear E H Dw l Xo c hnab.1 nab hnab T'.Fr y'.1 n P₁).2.2 l.M F
  rw [← hh] at hb
  rw [hev, thExpr, map_inv₀, map_pow, map_natCast, GlobalTheory.PlaceInt.TermBound.nval_inv_pow_mul T' _ _ _ hu]
  exact hb

end GlobalTheory.RefSum.LowP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_blockPeriodMatrix_fourierJacobiExpansion : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → ∀ Z, (Summable fun χ => ‖d.fj σ S χ Z‖) ∧ ∑' χ, d.fj σ S χ Z = thetaChar (d.full σ S) (d.aF σ) (d.bF σ) Z := by
  first | exact @GlobalTheory.MBLow.Cl.fj_expansion | exact GlobalTheory.MBLow.Cl.fj_expansion | (intros; apply GlobalTheory.MBLow.Cl.fj_expansion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → Differentiable ℂ (thetaChar τ a b) ∧ (∃ z, thetaChar τ a b z ≠ 0) ∧ ∀ M N z, thetaChar τ a b (z + perV τ M N) = autV τ a b M N z * thetaChar τ a b z := by
  first | exact @GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy | exact GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy | (intros; apply GlobalTheory.MBLow.Cl.thetaChar_entire_ne_zero_automorphy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariantStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_archimedean_invariant : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ g ∈ UAt σ X (evI F), ∀ (h : UA σ W.J) (Φ : (Fin n × Fin d → AF F) → ℂ),
      Φ ∈ schA F (Fin n × Fin d) → ∀ y, M.I om (om (g, h) Φ) y = M.I om Φ (y * h) := by
  first | exact @GlobalTheory.ThetaRightTranslate.thetaIntegral_translate | exact GlobalTheory.ThetaRightTranslate.thetaIntegral_translate | (intros; apply GlobalTheory.ThetaRightTranslate.thetaIntegral_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleLieBasisChangeUnitFactorStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_lieBasisChange_unit_factor : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (R K : Type) [CommRing R] [Field K] [CharZero K] (f : R →+* K) (x : KeyIn K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (φ : x.P.A.left ⟶ G.left), IsGrpPullback x.P.A G (spMap f) φ → ∀ (y y' : Fin x.P.g → (epsR R ⟶ G)) (v' : Fin x.P.g → (epsR K ⟶ x.P.A)), IsLieBasis y → IsLieBasis y' → (∀ i, IsVecOver f φ (y i) (x.v i)) → (∀ i, IsVecOver f φ (y' i) (v' i)) → ∃ (hv : IsLieBasis v') (u : Rˣ), (κ K ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv⟩ : K) = f u * κ K x := by
  first | exact @GlobalTheory.MBLow.key_basis_change | exact GlobalTheory.MBLow.key_basis_change | (intros; apply GlobalTheory.MBLow.key_basis_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_scale_section_pow_eight : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (C : Type) [Field C] [CharZero C] (x : KeyIn C) (a : C), a ≠ 0 → ∃ (th' : x.P.L.Sec) (h' : _), a ^ 8 * (κ C ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ : C) = κ C x ∧ ∀ (g : ℕ) (hg : x.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp C) ⟶ x.P.A)) (ϑ : I → C) (J : I → Fin g → C), ThJet x hg m pt ϑ J → ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ hg m pt (fun i => a * ϑ i) (fun i j => a * J i j) := by
  first | exact @GlobalTheory.MBLow.ScaleJet.scale_key | exact GlobalTheory.MBLow.ScaleJet.scale_key | (intros; apply GlobalTheory.MBLow.ScaleJet.scale_key <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValueClassicalNormalFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_value_classicalNormalForm : ∀ κ : Rule, Homog (fun _ => 1) κ → ThetaOne κ → ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) → Mx.det ≠ 0 ∧ (κ ℂ x : ℂ) * c ^ 8 = Mx.det ^ 4 := by
  first | exact @GlobalTheory.MBLow.Cl.key_value_of_nf | exact GlobalTheory.MBLow.Cl.key_value_of_nf | (intros; apply GlobalTheory.MBLow.Cl.key_value_of_nf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChange
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

namespace GlobalTheory.ModelChg

theorem det_ne_zero_of_hasSig {n r s : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (h : HasSig A r s) : A.det ≠ 0 := by
  obtain ⟨hrs, P, hP⟩ := h
  have hu : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) (0 : Matrix (Fin r) (Fin s) ℂ)
      (0 : Matrix (Fin s) (Fin r) ℂ) (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hu
  have h2 : (Pᵀ * A * P.map star).rank ≤ A.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hP, h1] at h2
  simp at h2
  have h3 : A.rank = n := le_antisymm (by simpa using A.rank_le_card_width) (by omega)
  have h4 : LinearMap.range A.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact h3)
  have h5 : Function.Surjective A.mulVec := LinearMap.range_eq_top.mp h4
  exact (Matrix.isUnit_iff_isUnit_det A |>.mp (Matrix.mulVec_surjective_iff_isUnit.mp h5)).ne_zero

theorem det_ne_zero_of_sig {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (B : Base F E) {n r s : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ w, HasSig (c • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h1 := det_ne_zero_of_hasSig (h w)
  rw [Matrix.det_smul] at h1
  intro h0
  apply h1
  rw [show (J.map (B.emb w).1).det = (B.emb w).1 J.det from ((B.emb w).1.map_det J).symm, h0, map_zero, mul_zero]

theorem modelChange (hK : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.ModelChange := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ om₁ hP₁
  obtain ⟨a, ha, hco⟩ := GlobalTheory.T.good_models_differ_by_symplectic_matrix F E σ B.ψ n d X W M M₁ hP.good hP₁.good
  obtain ⟨e, c, hc, hev, hbij, hθ⟩ :=
    GlobalTheory.T.symplectic_change_of_good_models_intertwines hK F E σ B n d X W M M₁ r s r' s' hP.base hP.herm hP.skew hP.good hP₁.good a ha hco
  obtain ⟨om₂, hW₂, hint⟩ := GlobalTheory.T.eigen_intertwiner_preserves_schwartz_space hK F E σ B n d X W M χX χW om r s r' s' hP M₁ hP₁.good e hev hbij
  have hX : X.J.det ≠ 0 :=
    det_ne_zero_of_sig B X.J 1 one_ne_zero (fun w => by simpa using hP.herm.sig w)
  have hWd : W.J.det ≠ 0 := det_ne_zero_of_sig B W.J Complex.I Complex.I_ne_zero hP.skew.sig
  have huniq := GlobalTheory.T.adelicWeilRep_schrodingerModel_unique F E σ hP.base.cm n d X W M₁ B.ψ χX χW hP.base.std hP.herm.herm hX
    hP.skew.skew hWd om₂ om₁ hW₂ hP₁.weil
  refine ⟨e, c, hc, hev, hbij, fun Φ hΦ => ⟨hθ Φ hΦ, fun x => ?_⟩⟩
  rw [hint x Φ hΦ, huniq x (e Φ) (hbij.mapsTo hΦ)]

end GlobalTheory.ModelChg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionInverseImageBaseProductFunctionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSection_inverseImage_baseProduct_function : ∀ (g : ℕ) (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (W : Fin g → Fin g → ℂ), NF x hg u τ a b c W → (∃ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th) ∧ (∀ th, IsPolAVSectionInverseImage x.P (baseOver (Sp ℂ)) x.th th → FnT u 1 th fun z => c * thetaChar τ a b z) ∧ ∀ (k : ℕ) (t t' : LB.Sec (LPow x.P.A x.P.L (k : ℤ) (baseOver (Sp ℂ)))) f, FnT u k t f → FnT u k t' f → ∀ j, t.f j = t'.f j := by
  first | exact @GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique | exact GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique | (intros; apply GlobalTheory.MBLow.Cl.thetaSection_fnT_thetaChar_and_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormOrderRationalPullbackOfEssentiallyEtale
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem isFreeGen_formMap_of_formallyEtale {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    {α : k →+* A} {β : k →+* B} {D : ℕ} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β)
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem formOrd_ratPull (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ)
    (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p]
    (hn : topologicalKrullDim W = n) (E : DivOver p) (E' : DivOver (f ≫ p))
    (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring)
    (hρ : ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale)
    (hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g)
    (η : RatForms p n) (hη : η ≠ 0) :
    E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  set φ := functionFieldMap f with hφ
  set ρ := φ.restrict E.ring E'.ring h with hρdef
  obtain ⟨ω, hω, g, hη', hg⟩ := E.isFormOrd_formOrd hn hη
  have hc : ρ.comp E.const = E'.const := by
    ext a
    exact RingHom.congr_fun (functionFieldMap_comp_constFn p f) a
  have hω' : IsFreeGen E'.ring (TopForm.formMap n ρ hc ω) := isFreeGen_formMap_of_formallyEtale hρ hc hω
  have e : φ.comp E.ring.subtype = E'.ring.subtype.comp ρ := by
    ext x
    rfl
  have hτ : (E'.ring.subtype.comp ρ).comp E.const = Cartier.constFn (f ≫ p) := by
    rw [RingHom.comp_assoc, hc]
    rfl
  have key : ratPull p f n (E.toRat n ω) = E'.toRat n (TopForm.formMap n ρ hc ω) := by
    have k1 := TopForm.formMap_formMap (D := n) E.ring.subtype φ _ e rfl
      (functionFieldMap_comp_constFn p f) hτ ω
    have k2 := TopForm.formMap_formMap (D := n) ρ E'.ring.subtype _ rfl hc rfl hτ ω
    exact k1.trans k2.symm
  have hpull : ratPull p f n η = φ (g : W.functionField) • E'.toRat n (TopForm.formMap n ρ hc ω) := by
    rw [hη', map_smulₛₗ, key]
  have hne : ratPull p f n η ≠ 0 := by
    rw [hpull]
    intro h0
    have hinj := (E'.isFreeGen_toRat hω').1
    have : φ (g : W.functionField) = 0 := hinj (by simpa using h0)
    exact (g.map φ.toMonoidHom).ne_zero this
  rw [← hg]
  refine DivOver.IsFormOrd.formOrd_eq hne ⟨_, hω', Units.map φ.toMonoidHom g, hpull, hord g⟩

end GlobalTheory.EtaleKlt
end
end

