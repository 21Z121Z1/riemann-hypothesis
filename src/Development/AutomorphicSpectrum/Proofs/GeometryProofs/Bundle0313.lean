import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0039
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0312
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0308
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0311
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0206
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEffectiveWeightSection
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0310
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0285
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0300
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0280
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0275
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0202
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0153
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0276
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0277
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0271
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0309

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseSettingOfGoodTower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TopBase

theorem genPt_eq_of_factor {X : Scheme.{0}} {Ω Ω₁ Ω₂ : Type} [Field Ω] [Field Ω₁] [Field Ω₂]
    {a : Spec (CommRingCat.of Ω) ⟶ X} {ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X} {ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X}
    {g₁ : Ω₁ →+* Ω} {g₂ : Ω₂ →+* Ω}
    (h₁ : a = Spec.map (CommRingCat.ofHom g₁) ≫ ξ₁) (h₂ : a = Spec.map (CommRingCat.ofHom g₂) ≫ ξ₂) :
    genPt ξ₁ = genPt ξ₂ := by
  have e₁ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₁ = a w := by
    intro w
    rw [h₁, Scheme.Hom.comp_apply]
    exact congrArg ξ₁ (Subsingleton.elim (α := PrimeSpectrum Ω₁) _ _)
  have e₂ : ∀ w : Spec (CommRingCat.of Ω), genPt ξ₂ = a w := by
    intro w
    rw [h₂, Scheme.Hom.comp_apply]
    exact congrArg ξ₂ (Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _)
  exact (e₁ (IsLocalRing.closedPoint Ω)).trans (e₂ (IsLocalRing.closedPoint Ω)).symm

theorem base_setting_of_good_origin : ∀ Ch Cu : ℝ, NineGeoU Ch Cu → Out.WeilSt → PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → T.bad.card ≤ 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 → ∀ B : ℕ, 4 * Fintype.card (CMType H) * (D.p + D.q) ^ 2 ≤ B → ∀ a, T.HasBaseDegreeSettingStrict II Ch Cu (hostRd E) (hostLval H) B a := by
  intro Ch Cu hNine hWeil hAgr hProp hCmp hGiven hPts E _ _ _ _ H D Xo l c Y _ T o II hGlob hExtra hFull hp hq hqp
    hbad B hB a
  obtain ⟨-, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  haveI := hne
  have hf : 1 ≤ Fintype.card (CMType H) := Fintype.card_pos_iff.mpr hne
  have hN2 : 2 ≤ D.p + D.q := by omega
  have hsq : 4 ≤ (D.p + D.q) ^ 2 := by nlinarith
  have hB16 : 16 * Fintype.card (CMType H) ≤ B := by nlinarith
  have hB2 : 2 ≤ B := by omega
  have hB4 : 4 * Fintype.card (CMType H) + 2 ≤ B := by omega
  have hgen : genPt (o.Or B a).𝔐.ξ₀ = genPt (o.Fx a).ξf :=
    genPt_eq_of_factor (o.Or B a).𝔐.fn_over (o.Or B a).g_over
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Finset ℕ, ∀ r, r ∈ S₁ ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad :=
    ⟨(Finset.range (B + 1)).filter (fun r => r.Prime ∧ r ∉ T.bad), by
      intro r
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h1, h3⟩⟩
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp => ((o.bad_iff p).1 hp).1
  have hS₁P : ∀ p ∈ S₁, p.Prime := fun p hp => ((hS₁ p).1 hp).1
  have hdisj : Disjoint S₁ T.bad := Finset.disjoint_left.2 fun p hp hp' => ((hS₁ p).1 hp).2.2 hp'
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ T.bad := fun p hp hd =>
    (o.bad_iff p).2 ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩
  obtain ⟨K, _, J, _, Ω, _, _, W, _, _, Dc, Hd, Or, hgen', hS, hj, hbg, -, hHT⟩ :=
    GlobalTheory.T.full_intersection_generic_bound hGiven hWeil E H D Xo l c Y II hFull hGlob hp hq _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ T.bad S₁
      false hbadP hS₁P hdisj hdisc
  simp only [Bool.false_eq_true, if_false] at hj hbg
  have hsm : Or.sm = Sum.inr := by
    rcases Or.side with ⟨-, h, -⟩ | ⟨h, -, -⟩
    · exact h
    · exact absurd (congrFun (hbg.symm.trans h) hne.some) Sum.inl_ne_inr
  have hGood : Or.Good :=
    ⟨fun p hp => hHT p (Finset.mem_union_left _ hp),
      fun p hp => hHT p (Finset.mem_union_right _ (by rw [← hS]; exact hp))⟩
  have hSc : ∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B ∧ r ∉ T.bad := by
    intro r; rw [hS]; exact hS₁ r
  have hN : Dc.N = D.p + D.q := Or.N_eq
  have hAdm : admitted Xo l c Y Or B := by
    refine ⟨hGlob, hGood, o.bad_iff, ?_, ?_, hSc, ?_⟩
    · show T.bad.card ≤ 4 * Fintype.card (CMType H) * Dc.N ^ 2
      rw [hN]; exact hbad
    · exact hB4
    · show Dc.N - Dc.j ≤ Dc.j
      rw [hN, hj]; omega
  obtain ⟨U, M, S, S', hcw, hU0, hUt, hSt, hS't, hconj⟩ :=
    GlobalTheory.T.cusp_weight_regularisations_tied hGiven E H D Xo l c Y II K J Ω W Dc Hd T.bad Or
  obtain ⟨hpos, hht, hmean⟩ := hNine E H D Xo l c Y II K J Ω W Dc Hd T.bad Or B U M S' hFull hAdm hcw hS't
  obtain ⟨X, hXH, hXU, hXrd, hXL, hX1, hX2, hX3, hX4, hX5⟩ :=
    GlobalTheory.T.corrected_weight_regularization K J II (CMType H) Ω W Dc Hd M U S S' (hostRd E) (hostLval H) Ch Cu hSt hS't hU0 hUt hpos hconj
      hht hmean
  subst hXH
  obtain ⟨hdeg, hlim, hPP⟩ := GlobalTheory.T.good_origin_intersection_tower hAgr hProp hCmp hGiven hPts E H D Xo l c Y T o II hGlob hExtra hFull hp hq
    B B a K J Ω W Dc ℤ (Fin 2 → ℤ) X Or hB2 le_rfl hqp hbg hsm hGood (hgen'.trans hgen) hSc
  obtain ⟨-, -, hSemi, -, hResK, -, -, hGaga, -, hInputs, -, hAn, -, -⟩ := hGiven
  have hStk : Top.StokesAt X B :=
    GlobalTheory.T.intersection_final_estimate hInputs hAn hResK hGaga hSemi E H D Xo l c Y II K J Ω W Dc X.H T.bad Or B U hFull hAdm hcw ℤ
      (Fin 2 → ℤ) X rfl hXU hX1 B hB4 hlim
  exact ⟨K, inferInstance, J, inferInstance, Ω, inferInstance, inferInstance, W, inferInstance, inferInstance, Dc, ℤ,
    Fin 2 → ℤ, inferInstance, inferInstance, inferInstance, X, hN, hj.trans o.j_eq.symm, hXrd, hXL, hX1, hX2, hX3, hX4,
    hX5, hdeg, hlim, hStk, hPP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.TopBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEffectiveWeightSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_effective_weight_section : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (G : RefGeo Y), Nonempty G.An → ∀ ν : RootIx D → ℤ, (∀ τ (i k : Fin (D.p + D.q)), i < k → ν (τ, k) < ν (τ, i)) → ∃ (k q' : ℕ) (s : G.Ω), 0 < k ∧ 0 < q' ∧ s ≠ 0 ∧ G.IsEff (fun r => (k * q' : ℕ) * ν r) q' s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff | exact GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff | (intros; apply GlobalTheory.CompanionTheory.Ar.ExRefEff.exists_eff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
section
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem thmFlatA_of_resK_gaga_partI :
    Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA :=
  fun hR hG hP =>
    GlobalTheory.T.flat_theorem_of_parts hP (GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG) (GlobalTheory.T.flat_first_from_resolution_and_gaga hR hG) GlobalTheory.T.finite_constant_holds

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNorm
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.FinGood

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem finGood : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → U ∈ irreducibleComponents (Xo.XF c) → Z.IsGeom → FlatOnModel Z τ φ → l.GoodAt p → ∃ t : ℝ, HasFinNorm U τ φ p κ t := by
  intro hRes hGaga E _ _ _ H D l Xo c O _ β Y U Z τ φ p κ hβ hpq hrt hU hZ hφ hgood
  obtain ⟨O', _, _, _, β', Y', hβ', hκ, hsplit, hN3⟩ := GlobalTheory.T.good_reduction_dvr_model_exists E H D l Xo c p κ hpq hgood
  obtain ⟨-, hne, hgeom⟩ := GlobalTheory.T.irreducible_component_clopen E H D l Xo c U hU
  obtain ⟨Z'⟩ := hne O' β' Y' hβ'
  have hZ' : Z'.IsGeom := hgeom O β Y O' β' Y' Z Z' hβ hβ' hZ
  obtain ⟨φ', hline', hflat', -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hRes hGaga E H D l Xo c O' β' Y' U Z' τ hβ' hpq hrt hZ'
  obtain ⟨t', ht'⟩ := GlobalTheory.T.finite_constant_all_holds E H D l Xo c O' β' Y' U Z' τ p κ φ' hrt hβ'.1 hκ hsplit hN3 hZ' hflat' hline'
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.frame_function_two_models_relay hRes hGaga E H D l Xo c O β Y O' β' Y' U Z Z' τ φ φ' hβ hβ' hpq hrt hZ hZ' hφ hflat'
  refine ⟨t' - Real.log ‖κ x‖, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Fl.HasFinNorm
  intro V K _ _ _ _ _ _ j β₁ y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht' V K j β₁ y v w T tK m m' hj hjβ hfr hv hw
  have hjx : j (β₁ x) = κ x := by rw [← hjβ]; rfl
  have hφne : j (φ K y v w) ≠ 0 := (map_ne_zero j).mpr (hφ.1.ne K β₁ y v w hfr)
  have hxne : j (β₁ x) ≠ 0 := (map_ne_zero j).mpr ((map_ne_zero β₁).mpr hx0)
  rw [hx K β₁ y v w hfr, map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hxne) (norm_ne_zero_iff.mpr hφne), hjx] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Br.FinGood
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionDegreeLower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.intersection_degree_lower : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B₁ : ℕ) (U : ((Σ k, J k) → ℂ) → ℝ) (M : XModel Dc) (S' : BoundedRegularisationSetting M Dc.Xo Hd.aMu (corrW Hd U)), IsFullIntersectionSystem II → admitted Xo l c Y Or B₁ → S'.IsTied → PosU S' := by
  intro hG hW E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or B₁ U M S' hII hA hT
  exact GlobalTheory.T.posU_of_full_intersection_system hG.2.2.2.2.2.2.2.2.2.1 K J II _ Ω W Dc Hd M _ S' hII hT fun B hB =>
    GlobalTheory.T.intersection_degree_upper hG hW E H D Xo l c Y II K J Ω W Dc Hd S₀ Or B₁ B hA hB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterFrameBound
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem degree_of_flatOnModel : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [NumberField c.F] (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → IsClopen U → Z.IsGeom → FlatOnModel Z τ φ → (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) → N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hres hgaga E _ _ _ H D l Xo c O _ β Y _ U Z τ φ N _ χ hχ hO hpq hτ hcl hZ hflat hinf hfin
  obtain ⟨g, ty, FU, i, hty, hin⟩ := GlobalTheory.T.family_uniformization_type_relay E H D l Xo c U hpq hcl ⟨_, Z.genPt_mem⟩
  have hA := GlobalTheory.T.flat_first_from_resolution_and_gaga hres hgaga E H D l Xo c O β Y U Z τ φ hO hpq hτ hZ hflat.isLineFn hflat
  exact GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames GlobalTheory.T.FlatDegree_holds E H D l Xo c g ty FU i U τ φ N χ hχ hty hτ
    (hA.2 g ty FU i hty hin) hinf hfin

end GlobalTheory.CompanionTheory.Ar.Br
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLineLargeDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem slopeBound_and_lemmaS_of_siegel :
    LineOfLargeDegree.Statement → SlopeBoundSt ∧ Prov.LemmaS := fun hS =>
  GlobalTheory.T.slope_bound_of_large_degree_line hS (GlobalTheory.T.key_degree_of_bad_reduction GlobalTheory.T.key_bad_reduction_holds)

end GlobalTheory.CompanionTheory.Ar.Sl
end

