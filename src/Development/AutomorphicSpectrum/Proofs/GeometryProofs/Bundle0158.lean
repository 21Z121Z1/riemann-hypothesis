import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuesOfFrame
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0155
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0101
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0149
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0087
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0098
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
import Development.WeilBound.CoreStatements.HodgeTatePoints.CiEigVal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstants
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetraction
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartIntegralPointAltBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_part_integral_point_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (P : AbPart 𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (lab : CMType H ⊕ CMType H) (m : ℕ) (s : Fin m → 𝔐.Li), 𝔐.IsLinPtOf z P MV A → (𝔐.dR lab).IsFrameAt s ⟨centre (spMap (algebraMap (𝓞 L) L) ≫ z), 𝔐.all _⟩ → ∃ sL : Fin m → V, IsValues 𝔐 z P MV s sL ∧ LinearIndependent L sL ∧ Submodule.span L (Set.range sL) = eigSp A.ρ (A.σ lab) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FrameVal.values_of_frame | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FrameVal.values_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.FrameVal.values_of_frame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVarStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_coords_arith_var : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))), (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ ∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) β) = 0 → z ∈ mcPts J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncRes.exists_snc_model | exact GlobalTheory.CompanionTheory.Ar.SncRes.exists_snc_model | (intros; apply GlobalTheory.CompanionTheory.Ar.SncRes.exists_snc_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqBtOrderTopStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_eq_btOrder_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top | exact GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top | (intros; apply GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.btOrder_isHopfOrder_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian | exact GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian | (intros; apply GlobalTheory.CompanionTheory.Relay.btOrder_isHopfOrder_noetherian <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_ideal_localization_map : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R),
    (∀ g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c, θ g = 0) →
    ∀ (F : MvPolynomial (Σ k, J k) ℚ), IsUnit (θ (map (algebraMap ℚ ℂ) F)) →
    ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) F : Ω)⁻¹
        (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) →
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
      (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart | exact GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartHom.exists_hom_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedGroupSmoothRelDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.CompanionTheory.Ggeo

theorem exists_smoothOfRelativeDimension_of_geometricallyConnected :
    ∀ (X : Scheme.{0}) [ConnectedSpace X] (G : Over X) [GrpObj G], Smooth G.hom →
      GeometricallyConnected G.hom → ∃ g : ℕ, SmoothOfRelativeDimension g G.hom := by
  intro X _ G _ hs hc
  haveI : Smooth G.hom := hs
  obtain ⟨d, W, hxW, hW⟩ : ∃ (d : G.left → ℕ) (W : G.left → G.left.Opens), (∀ x, x ∈ W x) ∧
      ∀ x, SmoothOfRelativeDimension (d x) ((W x).ι ≫ G.hom) := by
    choose d W hxW hW using fun x => ReciprocityTheory.ChartRestriction.G.H1.exists_dim G.hom x
    exact ⟨d, W, hxW, hW⟩
  have hres : ∀ (x : G.left) (V : G.left.Opens), V ≤ W x →
      SmoothOfRelativeDimension (d x) (V.ι ≫ G.hom) := by
    intro x V hV
    have h := HasRingHomProperty.comp_of_isOpenImmersion (@SmoothOfRelativeDimension (d x))
      (G.left.homOfLE hV) ((W x).ι ≫ G.hom) (hW x)
    rwa [← Category.assoc, Scheme.homOfLE_ι] at h
  have hd : IsLocallyConstant d := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨W x, (W x).isOpen, hxW x, fun y hy => ?_⟩
    have h1 := hres x (W x ⊓ W y) inf_le_left
    have h2 := hres y (W x ⊓ W y) inf_le_right
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h2 h1 ⟨y, hy, hxW y⟩
  let e : X ⟶ G.left := (η[G]).left
  have hcomp : e ≫ G.hom = 𝟙 X := Over.w (η[G])
  have he : ∀ s : X, G.hom (e s) = s := by
    intro s
    have h := congrArg (fun g : X ⟶ X => g s) hcomp
    simpa using h
  have hfib : ∀ s : X, _root_.IsPreconnected (G.hom ⁻¹' {s}) := by
    intro s
    rw [← Scheme.Hom.range_fiberι]
    exact isPreconnected_range (Scheme.Hom.continuous _)
  obtain ⟨s₀⟩ : Nonempty X := inferInstance
  have hconst : ∀ x, d x = d (e s₀) := by
    intro x
    have h1 : d x = d (e (G.hom x)) :=
      hd.apply_eq_of_isPreconnected (hfib (G.hom x)) rfl (he (G.hom x))
    have h2 : d (e (G.hom x)) = d (e s₀) :=
      (hd.comp_continuous (Scheme.Hom.continuous e)).apply_eq_of_isPreconnected
        isPreconnected_univ trivial trivial
    exact h1.trans h2
  refine ⟨d (e s₀), ?_⟩
  haveI : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (d (e s₀))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (d (e s₀))) W
    (eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩)
    (fun x => by rw [← hconst x]; exact hW x)

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeModel

section Normal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem exists_div_of_tie {κ : Type} {x : κ → Ω} (ht : CoordTie ℤ ξ x) {c : κ} {q : Cpt ξ} (hc : InChart ξ x c q)
    (a : Ω) : ∃ u ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ v ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), v ≠ 0 ∧ a = u / v := by
  have hg : InChart ξ x c (TieArith.genCpt ξ) :=
    ⟨hc.1, fun c' => (RegAtMono.regAt_mono X Ω ξ q (TieArith.genCpt ξ) q.2).1 (hc.2 c')⟩
  obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ ht c (TieArith.genCpt ξ) hg a).1
    (TieArith.mem_regAt_genCpt ξ ht.gen a)
  exact ⟨s * a, hsa, s, hs, hu.1, by field_simp [hu.1]⟩

variable [CharZero Ω]

theorem exists_trdeg_eq {κ : Type} [Finite κ] {x : κ → Ω} (ht : CoordTie ℤ ξ x) :
    ∃ d : ℕ, Algebra.trdeg ℤ Ω = d := by
  obtain ⟨c, hc⟩ := ht.cover (TieArith.genCpt ξ)
  set s : Set Ω := Set.range fun j => x j / x c with hs
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℤ s) Ω := by
    refine ⟨fun a => ?_⟩
    obtain ⟨u, hu, v, hv, hv0, rfl⟩ := exists_div_of_tie ht hc a
    have h1 : IsAlgebraic (Algebra.adjoin ℤ s) u := isAlgebraic_algebraMap (⟨u, hu⟩ : Algebra.adjoin ℤ s)
    have h2 : IsAlgebraic (Algebra.adjoin ℤ s) v := isAlgebraic_algebraMap (⟨v, hv⟩ : Algebra.adjoin ℤ s)
    rw [div_eq_mul_inv]
    exact h1.mul h2.inv
  obtain ⟨t, hts, hb⟩ := exists_isTranscendenceBasis_subset (R := ℤ) s
  have hfin : t.Finite := (Set.finite_range _).subset hts
  haveI := hfin.to_subtype
  haveI := Fintype.ofFinite t
  exact ⟨Fintype.card t, by rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype]⟩

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem mem_regAt_of_isIntegral (ht : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hs : SmoothGenericFibreM y) (q : Cpt ξ) (hq : q ∈ genFib ξ) (a : Ω)
    (ha : IsIntegral (regAt ξ q) a) : a ∈ regAt ξ q := by
  classical
  obtain ⟨c, hc⟩ := ht.cover q
  have hne : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hc.1) k (Finset.mem_univ k)
  set A : Subalgebra ℚ Ω := Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) with hA
  haveI : Algebra.Smooth ℚ A := hs c hne
  let R : Subalgebra ℚ Ω :=
    { (regAt ξ q) with
      algebraMap_mem' := fun r => by
        have e : algebraMap ℚ Ω r = (r.num : Ω) * ((r.den : ℕ) : Ω)⁻¹ := by
          rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
        rw [e]
        exact mul_mem (intCast_mem _ _) (hq r.den r.den_pos).2.2 }
  have hAR : ∀ b ∈ A, b ∈ regAt ξ q := by
    have : A ≤ R := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨⟨k, j⟩, rfl⟩
      exact Lat.block_ratio_mem hc k j
    exact fun b hb => this hb
  have hBA : ∀ b ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩), b ∈ A := by
    intro b hb
    have : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ A.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨j, rfl⟩
      show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ A
      rw [← Finset.prod_div_distrib]
      exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
    exact this hb
  have hfr : ∀ r ∈ regAt ξ q, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ regAt ξ q ∧ r = u / v := by
    intro r hr
    obtain ⟨s, hsB, hsu, hsr⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ ht c q hc r).1 hr
    refine ⟨s * r, hBA _ hsr, s, hBA _ hsB, hsu.1, hsu.2.2, ?_⟩
    field_simp [hsu.1]
  obtain ⟨v, hvA, hv0, hvR, hint⟩ :=
    GlobalTheory.CompanionTheory.Ggeo.ClearDenominators.exists_mul_isIntegral A (regAt ξ q) hAR hfr a ha
  haveI : IsFractionRing A Ω := IsFractionRing.of_field A Ω fun z => by
    obtain ⟨u, hu, w, hw, -, rfl⟩ := exists_div_of_tie ht hc z
    exact ⟨⟨u, hBA u hu⟩, ⟨w, hBA w hw⟩, rfl⟩
  haveI : IsIntegrallyClosed A := by
    have h1 : IsIntegrallyClosed (A ⧸ (⊥ : Ideal A)) :=
      GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth ℚ A ⊥ (by
        rw [IsDomain.minimalPrimes_eq_singleton_bot]; rfl)
    exact IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot A)
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have e : a = b * v⁻¹ := by
    have : (b : Ω) = v * a := hb
    rw [this]; field_simp [hv0]
  rw [e]
  exact mul_mem (hAR _ b.2) hvR

end Normal

section Blocks

variable {K : Type} {κ : Type} (J : K → Type)

def joinEquiv : ((k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k) ≃ ((k : K) → J k) × κ where
  toFun c := (fun k => c (.inl k), c (.inr ()))
  invFun t := fun k => match k with
    | .inl k => t.1 k
    | .inr () => t.2
  left_inv c := by funext k; rcases k with k | _ <;> rfl
  right_inv t := rfl

variable {J} [Fintype K] {Ω : Type} [Field Ω]

theorem segre_joinVec (x : (Σ k, J k) → Ω) (v : (Σ _ : Unit, κ) → Ω)
    (c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k) :
    ∏ k, Cmp.joinVec x v ⟨k, c k⟩ = (∏ k, x ⟨k, (joinEquiv J c).1 k⟩) * v ⟨(), (joinEquiv J c).2⟩ := by
  rw [Fintype.prod_sum_type]
  simp only [Finset.univ_unique, Finset.prod_singleton]
  rfl

theorem tie_joinVec {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type} [CommRing o] [Algebra o Ω]
    (x : (Σ k, J k) → Ω) (v : (Σ _ : Unit, κ) → Ω)
    (h : CoordTie o ξ (fun q : ((k : K) → J k) × κ => (∏ k, x ⟨k, q.1 k⟩) * v ⟨(), q.2⟩)) :
    CoordTie o ξ (fun c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k => ∏ k, Cmp.joinVec x v ⟨k, c k⟩) := by
  have e : (fun c : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => κ) k => ∏ k, Cmp.joinVec x v ⟨k, c k⟩) =
      fun c => (fun q : ((k : K) → J k) × κ => (∏ k, x ⟨k, q.1 k⟩) * v ⟨(), q.2⟩) (joinEquiv J c) :=
    funext fun c => segre_joinVec x v c
  rw [e]
  exact ExtraBlocks.coordTie_equiv (joinEquiv J) h

end Blocks

end GlobalTheory.CompanionTheory.Ar.ChangeModel

namespace GlobalTheory.CompanionTheory.Ar.ChangeModel

theorem dominates_comp {X₁ X₂ X₃ : Scheme.{0}} {Ω₁ Ω₂ Ω₃ : Type} [Field Ω₁] [Field Ω₂] [Field Ω₃]
    {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂} {ξ₃ : Spec (CommRingCat.of Ω₃) ⟶ X₃}
    {f : X₂ ⟶ X₁} {g : X₃ ⟶ X₂} {i : Ω₁ →+* Ω₂} {j : Ω₂ →+* Ω₃}
    (hf : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ f i) (hg : GlobalTheory.CompanionTheory.Ar.Dominates ξ₃ ξ₂ g j) :
    GlobalTheory.CompanionTheory.Ar.Dominates ξ₃ ξ₁ (g ≫ f) (j.comp i) := by
  unfold GlobalTheory.CompanionTheory.Ar.Dominates at *
  rw [← Category.assoc, hg, Category.assoc, hf, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem closure_eq_top_of_basis {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω)
    (hfin : letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) :
    ∃ (n : ℕ) (w : Option (Fin n) → Ω), w none ≠ 0 ∧
      Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ := by
  letI := i.toAlgebra
  haveI := hfin
  let b := Module.finBasis Ω₁ Ω
  refine ⟨_, fun l => l.elim 1 b, one_ne_zero, ?_⟩
  rw [eq_top_iff]
  intro a _
  rw [← b.sum_repr a]
  refine sum_mem fun j _ => ?_
  rw [Algebra.smul_def]
  refine mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨some j, none, ?_⟩))
  simp

theorem exists_normal_model : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] [CharZero Ω] (i : Ω₁ →+* Ω) (y : (Σ k, J k) → Ω₁) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω₁) ⟶ X), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (M : PModel ℤ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩)) (h : M.X ⟶ X), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ h i ∧ Flat.NormalCpt M.ξ ∧ SmoothGenericFibreM y' := by
  intro hRes K _ J _ Ω₁ Ω _ _ _ i y X ξ hfin hall htie
  classical

  let M₀ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) :=
    { X := X, ξ := ξ, s := specZIsTerminal.from X, hover := specZIsTerminal.hom_ext _ _, all := hall, tie := htie }

  obtain ⟨n, w, hw0, hclo⟩ := closure_eq_top_of_basis i hfin
  obtain ⟨M₁, f₁, hf₁⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω₁ _ _ M₀ Ω i (Option (Fin n)) w (fun a => by simp) ⟨none, hw0⟩ hclo
  let y₁ : (Σ k, Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k) → Ω :=
    Cmp.joinVec (fun p => i (y p)) (fun p : Σ _ : Unit, Option (Fin n) => w p.2)
  have ht₁ : CoordTie ℤ M₁.ξ (fun c' : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k =>
      ∏ k, y₁ ⟨k, c' k⟩) := by
    refine tie_joinVec _ _ ?_
    have e : (fun q : ((k : K) → J k) × Option (Fin n) => (∏ k, i (y ⟨k, q.1 k⟩)) * w q.2) =
        joinCo i (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) w := by
      funext q
      simp [joinCo, map_prod]
    show CoordTie ℤ M₁.ξ (fun q : ((k : K) → J k) × Option (Fin n) => (∏ k, i (y ⟨k, q.1 k⟩)) * w q.2)
    rw [e]
    exact M₁.tie

  obtain ⟨d, hd⟩ := exists_trdeg_eq ht₁
  obtain ⟨-, hAr⟩ := GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar M₁.X Ω M₁.ξ (K ⊕ Unit) _ y₁ d ht₁ hd
  obtain ⟨m, y₂, Jb, ⟨l₀, hl₀⟩, -, -, -, hsnc, -⟩ := SncRes.exists_snc_model hRes (K ⊕ Unit) _ Ω y₁ d 1 0 hAr
    (by intro a ha k; simp [MvPolynomial.support_one] at ha; simp [ha])
    (by
      intro h
      have : mConeMap y₁ 1 = 0 := h
      simp at this)

  let M₁' : PModel ℤ (fun c' : (k : K ⊕ Unit) → Cmp.joinIdx J (fun _ : Unit => Option (Fin n)) k => ∏ k, y₁ ⟨k, c' k⟩) :=
    { X := M₁.X, ξ := M₁.ξ, s := M₁.s, hover := M₁.hover, all := M₁.all, tie := ht₁ }
  have hclo₂ : Subfield.closure (Set.range (RingHom.id Ω) ∪ {a | ∃ l l', a = y₂ ⟨(), l⟩ / y₂ ⟨(), l'⟩}) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  obtain ⟨M₂, f₂, hf₂⟩ := GlobalTheory.T.exists_join_model_dominates ℤ Ω _ _ M₁' Ω (RingHom.id Ω) (Fin m) (fun l => y₂ ⟨(), l⟩)
    (fun a => rfl) ⟨l₀, hl₀⟩ hclo₂
  let z := Cmp.joinVec y₁ y₂
  have ht₂ : CoordTie ℤ M₂.ξ (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k =>
      ∏ k, z ⟨k, c' k⟩) := tie_joinVec _ _ M₂.tie
  have hsm : SmoothGenericFibreM z := GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel _ _ Ω z d Jb hsnc
  let M₂' : PModel ℤ (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k => ∏ k, z ⟨k, c' k⟩) :=
    { X := M₂.X, ξ := M₂.ξ, s := M₂.s, hover := M₂.hover, all := M₂.all, tie := ht₂ }

  obtain ⟨κ₃, _, y₃, M₃, f₃, hf₃, hN, -, hNorm⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω _ _ M₂' Ω
  have hf₃' : GlobalTheory.CompanionTheory.Ar.Dominates M₃.ξ M₂.ξ f₃ (RingHom.id Ω) := hf₃
  have hchart : ∀ p : Cpt M₃.ξ, ∃ c₀, InChart M₃.ξ
      (fun c' : (k : (K ⊕ Unit) ⊕ Unit) → Cmp.joinIdx (Cmp.joinIdx J (fun _ : Unit => Option (Fin n))) (fun _ : Unit => Fin m) k => ∏ k, z ⟨k, c' k⟩) c₀ p := by
    intro p
    obtain ⟨h, hreg, -⟩ := RegAtDom.regAt_dominates M₂.X Ω M₂.ξ M₃.X Ω M₃.ξ f₃ _ hf₃' p
    obtain ⟨c, hc⟩ := ht₂.cover ⟨f₃ p.1, h⟩
    exact ⟨c, hc.1, fun c' => hreg _ (hc.2 c')⟩

  obtain ⟨K', _, J', _, y', bk, bx, -, hinj, heq, ht', -⟩ := ExtraBlocks.exists_blocks_of_lines ℤ Ω _ y₃ M₃ _ _ z Empty
    (fun a => a.elim) hchart (fun a => a.elim)
  have hsm' : SmoothGenericFibreM y' :=
    GlobalTheory.T.smoothGenericFibre_of_dominates Ω _ _ z K' J' y' M₂.X M₃.X M₂.ξ M₃.ξ f₃ M₂.all M₃.all ht₂ ht' hf₃' hsm fun q hq =>
      GlobalTheory.T.normal_iso_of_integrally_closed M₂.X Ω M₂.ξ M₃.X M₃.ξ f₃ q (hNorm q) (mem_regAt_of_isIntegral ht₂ hsm q hq)
  refine ⟨K', inferInstance, J', inferInstance, y', fun k => bk (.inl (.inl k)), fun k => bx (.inl (.inl k)),
    { X := M₃.X, ξ := M₃.ξ, s := M₃.s, hover := M₃.hover, all := M₃.all, tie := ht' },
    f₃ ≫ f₂ ≫ f₁, fun a b e => ?_, fun k a => heq (.inl (.inl k)) a, ?_, hN, hsm'⟩
  · simpa using hinj e
  · have h1 := dominates_comp (dominates_comp hf₁ hf₂) hf₃'
    exact h1

end GlobalTheory.CompanionTheory.Ar.ChangeModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieEigenDecomposition
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.EigVal

theorem values_eigen_sheaves : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) :=
  @PositivityTheory.HtPt.Ci.eig_val

end GlobalTheory.CompanionTheory.Ar.EigVal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationVanishingConstantsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_vanishing_constants : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (g : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (φ : R →+* ℂ), Smooth G.hom → ∀ (V : G.left.Opens), IsAffineOpen V → ⊤ ≤ (1 : Over.mk (spMap φ) ⟶ G).left ⁻¹ᵁ V →
  ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V r) = 0) →
    (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f * D f' + valAt' (1 : Over.mk (spMap φ) ⟶ G).left V f' * D f) →
    ∃! c : Fin g → ℂ, ∀ f, D f = ∑ a, c a * TrivSqZeroExt.snd (valR (spMap (dualMap φ) ≫ (M.pt (Pi.single a 1)).left) V f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis | exact GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.lie_der_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EffectiveScaledWeightOfRetractionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effective_scaled_weight_of_retraction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (G : RefGeo Y) (A : G.An) (ν : RootIx D → ℤ) (k q' : ℕ) (s : G.Ω), (∃ inv : A.Sys.X → A.Re.R.X, ReciprocityTheory.AnForm.M.HoloMap A.Sys.A A.Re.R.A inv ∧ ∀ x, inv (A.Re.π x) = x) → SplitComps Y → 0 < k → 0 < q' → s ≠ 0 → G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s → ∃ (Fx : FixedData Y A.Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx), genPt Fx.ξf = genPt G.𝔐.ξ₀ ∧ Fx.kA = k ∧ Fx.q' = q' ∧ (∀ r, Fx.n r = (k * q' : ℕ) * ν r) ∧ o.Fl.deg = 1 ∧ o.Re.J = ⊤ ∧ Ht.AmpleQ R.y R.A.a ∧ Cmp.IsEmbedded o.Re.R.A R.P o.Re.R.U o.Re.R.lift ∧ Function.Bijective o.Re.π ∧ (∀ x : A.Sys.X, ∃ (U : Set A.Sys.X) (lam : A.Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, A.Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (A.Sys.A.chart j).source → (fderiv ℂ (fun z i => lam ((A.Sys.A.chart j).symm z) i / lam ((A.Sys.A.chart j).symm z) p) (A.Sys.A.chart j x)).ker = ⊥) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot | exact GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot | (intros; apply GlobalTheory.CompanionTheory.Ar.RefRoot.refRoot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCharacterSectionStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (χ : T →* Rˣ), ∃ s : Γ(Γ.G.left, ⊤), Γ.HasValues s (fun t => ((χ t : Rˣ) : R)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_character_section | exact GlobalTheory.CompanionTheory.Relay.exists_character_section | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_character_section <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteNormalModelOfResidueFiniteStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_normal_model_of_residue_finite : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℤ), IsProjOver s → ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X), (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom.Finite → ∃ (n : ℕ) (x : Fin n → Ω) (M : PModel ℤ x) (π : M.X ⟶ X), Flat.NormalCpt M.ξ ∧ IsFinite π ∧ M.ξ ≫ π = ξ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite | exact GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite <;> assumption)
end

