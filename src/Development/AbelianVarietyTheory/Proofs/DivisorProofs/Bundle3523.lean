import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3500
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3495
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0662
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3501
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3502

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankOneChangeImprovesImageRealPrime
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem mem_of_smul_mem_sup {O X : Type} [CommRing O] [AddCommGroup X] [Module O X] {I : Ideal O} (hI : I.IsMaximal)
    {N : Submodule O X} (hN : I • (⊤ : Submodule O X) ≤ N) {a : O} (ha : a ∉ I) {u : X} (hu : a • u ∈ N) : u ∈ N := by
  obtain ⟨c, i, hi, hc⟩ := hI.exists_inv ha
  have : c • (a • u) + i • u = u := by rw [smul_smul, ← add_smul, hc, one_smul]
  rw [← this]
  exact add_mem (N.smul_mem c hu) (hN (Submodule.smul_mem_smul hi trivial))

theorem map_range_rank_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (Z' : Submodule (𝓞 E) D.La)
    (ℓ : Z' →ₗ[𝓞 E] 𝓞 E) (u : D.La) :
    (LinearMap.range (Z'.subtype + ℓ.smulRight u)).map y = LinearMap.range (y ∘ₗ Z'.subtype + ℓ.smulRight (y u)) := by
  rw [← LinearMap.range_comp]
  congr 1
  ext x
  simp

end GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_improves_of_real {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭) :
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  have hm : (0 : D.La) ∈ perp D Z ⊓ perp D Z' := zero_mem _
  obtain ⟨ζ, hζZ, hζ, hζs, hopp⟩ := h.exists_rank_one hm θ (fun t => by simp [hθ])
  have hN : 𝔭 • (⊤ : Submodule (𝓞 E) X) ≤ img D y Z' 𝔭 := le_sup_right

  set P1 : (Z' →ₗ[𝓞 E] 𝓞 E) → Prop := fun ℓ => ℓ v ∈ 𝔭 with hP1
  set P2 : (Z' →ₗ[𝓞 E] 𝓞 E) → Prop := fun ℓ => y (ζ ℓ) ∈ img D y Z' 𝔭 with hP2
  have P1sub : ∀ a b, P1 (a + b) → P1 b → P1 a := fun a b hab hb' => by
    have := sub_mem hab hb'
    simpa [hP1] using this
  have P2sub : ∀ a b, P2 (a + b) → P2 b → P2 a := fun a b hab hb' => by
    have := sub_mem hab hb'
    simpa [hP2, map_add] using this

  obtain ⟨x, ⟨z, hz, rfl⟩, hx⟩ := Set.not_subset.1 hZ
  have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ 𝔭.zero_mem)
  obtain ⟨ℓ₂, hℓ₂⟩ := GlobalTheory.T.exists_linearForm_factor_through_traceGenerator D Z' θ s hs0 hgen z
  have hζ₂ : ζ ℓ₂ = H.bar s • z := by
    obtain ⟨c, -, hu⟩ := h.symm.2.2.1 (θ.comp ℓ₂.toAddMonoidHom)
    have e1 := hu ⟨ζ ℓ₂, hζZ ℓ₂⟩ fun a => by simpa using hζ ℓ₂ a
    have e2 := hu ⟨H.bar s • z, Z.smul_mem _ hz⟩ fun a => by simpa using (hℓ₂ a).symm
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hℓ₂P : ¬ P2 ℓ₂ := fun hP => by
    simp only [hP2, hζ₂, map_smul] at hP
    exact hx (mem_of_smul_mem_sup h𝔭 hN hs' hP)

  obtain ⟨ℓ₁, h1, h2⟩ : ∃ ℓ₁, ¬ P1 ℓ₁ ∧ ¬ P2 ℓ₁ := by
    by_cases ha : P2 ℓ₀
    · by_cases hb1 : P1 ℓ₂
      · refine ⟨ℓ₀ + ℓ₂, fun hp => hℓ₀ (P1sub _ _ hp hb1), fun hp => hℓ₂P ?_⟩
        rw [add_comm] at hp
        exact P2sub _ _ hp ha
      · exact ⟨ℓ₂, hb1, hℓ₂P⟩
    · exact ⟨ℓ₀, hℓ₀, ha⟩
  have he𝔭 : e ∉ 𝔭 := fun hm' => h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := sub_mem hm' he1
    simpa using this))
  have hbe : H.bar e ∉ 𝔭 := fun hm' => he𝔭 (by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hm'
    rw [hb] at this
    simpa [bar_bar] using this)
  set ℓ := e • ℓ₁ with hℓ
  refine ⟨LinearMap.range (Z'.subtype + ℓ.smulRight (0 + ζ ℓ)), hopp ℓ, fun 𝔮 h𝔮 hn𝔮 => ?_, fun hle => ?_⟩
  · have hZ'm : Z'.map y = LinearMap.range (y ∘ₗ Z'.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    show Z'.map y ⊔ _ ≤ _ ⊔ _
    rw [map_range_rank_one, hZ'm]
    by_cases hq : 𝔮 = 𝔭
    · subst hq
      refine (range_le_of_ker _ ℓ _ 𝔮 h𝔮 (v := v) (by simpa using hv) ?_).2
      show e * ℓ₁ v ∉ 𝔮
      exact fun hm' => h1 ((h𝔮.isPrime.mem_or_mem hm').resolve_left he𝔭)
    · exact range_le_of_mem _ ℓ _ 𝔮 fun x => by
        show e * ℓ₁ x ∈ 𝔮
        exact Ideal.mul_mem_right _ _ (he 𝔮 h𝔮 hn𝔮 hq)
  · have hZ'm : Z'.map y = LinearMap.range (y ∘ₗ Z'.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hmem := (range_le_of_ker (y ∘ₗ Z'.subtype) ℓ (y (0 + ζ ℓ)) 𝔭 h𝔭 (v := v) (by simpa using hv)
      (show e * ℓ₁ v ∉ 𝔭 from fun hm' => h1 ((h𝔭.isPrime.mem_or_mem hm').resolve_left he𝔭))).1
    have hin : y (ζ ℓ) ∈ img D y Z' 𝔭 := by
      apply hle
      show _ ∈ _ ⊔ _
      rw [map_range_rank_one]
      simpa using hmem
    rw [hℓ, hζs, map_smul] at hin
    exact h2 (mem_of_smul_mem_sup h𝔭 hN hbe hin)

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaleIsPullDegGeneratingEverywhereStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescale_isPullDeg_generating_everywhere : ∀ {W V : Type} [CommRing W] [IsDomain W] [CommRing V] [IsDomain V] (θ₀ : W →+* V) (D₀ : DegPre W) (Q : DegPre V) (e : Q.X ≃+ D₀.X) (β : Q.P.A.left ⟶ D₀.P.A.left), (∀ y, PsiUnitOn D₀ y Set.univ) → IsGrpPullback Q.P.A D₀.P.A (spMap θ₀) β → LBIso Q.P.L (D₀.P.L.pull β) → (∀ y, (Q.c y).left ≫ β = spMap θ₀ ≫ (D₀.c (e y)).left) → ∃ (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg θ₀ D₀ (GlobalTheory.PolDeg.rescale Q g)), (∀ y, hD.xe y = e y) ∧ hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ₀) = β ∧ hD.W = ⊤ := by
  first | exact @GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | exact GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top | (intros; apply GlobalTheory.PreLiftData.exists_rescale_isPullDeg_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivPowerSeriesPrescribedParametersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_powerSeries_prescribed_parameters : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → Nonempty (ℚ →+* R) → ∀ (m : ℕ) (t : Fin m → R), (∀ i, t i ∈ maximalIdeal R) → (∀ a : Fin m → R, ∑ i, a i * t i ∈ maximalIdeal R ^ 2 → ∀ i, a i ∈ maximalIdeal R) → ∃ (k : Type) (_ : Field k) (e : ℕ) (σ : R ≃+* ChartRing k m e), ∀ i, σ (t i) = bdParam k m e i := by
  first | exact @GlobalTheory.CohenChart.exists_ringEquiv_chartRing | exact GlobalTheory.CohenChart.exists_ringEquiv_chartRing | (intros; apply GlobalTheory.CohenChart.exists_ringEquiv_chartRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (π : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f π → (∀ a, (t'.act.act a).left ≫ π = π ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull π) → ∃ m : SABMap t' t f, m.φ = π := by
  first | exact @GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper | exact GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper | (intros; apply GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentOfToricChartsCorrectedSe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartDesc

theorem exists_semiAbelian_of_charts : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hP hpre tF mF
  have hNoeth : AlgebraicGeometry.IsNoetherian S := GlobalTheory.isNoetherian_of_isProjOver hP.2.2.2.2.1.2.1
  have hNorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).1 hP.2.2.2.2.1.1.1
  have hdom : IsDominant j := ⟨hP.2.2.2.2.1.2.2.2.1⟩
  have hAab : IsAbelianScheme tF.G :=
    ⟨tF.comm, tF.semi.smooth, MorphismProperty.of_isPullback (P := @IsProper) mF.cart.1 Xo.univ.proper, tF.semi.geomConnected⟩
  have hLB : tF.PP.L.IsLB := tF.PP.isLB
  have hAmp : RelAmple tF.G tF.PP.L := GlobalTheory.T.relAmple_rigidifiedBundle_pullback_universalTriple Xo c tF mF
  have hkc : ∀ (k : Type) [Field k], IsAdicComplete (maximalIdeal k) k := fun k _ => by
    rw [maximalIdeal_eq_bot]; infer_instance

  have bdChart : ∀ (x : S) (k : Type) [Field k] (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e))
      (ξ : Sp (ChartRing k m e) ⟶ S), C.y ≫ j = jK _ ≫ ξ → ξ (closedPoint _) = x →
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
      ∃ Ch : GlobalTheory.Desc.Chart j tF.G x, ∀ (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ π : Ch.G.left ⟶ G.left,
        IsGrpPullback Ch.G G Ch.ξ π → (x ∈ abLocus G ↔ closedPoint (ChartRing k m e) ∈ abLocus C.t.G) := by
    intro x k _ m e C ξ hy hcl het
    haveI : CharZero (ChartRing k m e) := charZero_of_injective_ringHom C.b.injective
    haveI := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
    haveI := hkc k
    obtain ⟨α, hα⟩ := GlobalTheory.T.genericFibre_isGrpPullback_of_universalTriple Xo c (ChartRing k m e) C.y C.t tF C.gen mF
    refine ⟨{ R := ChartRing k m e
              complete := GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
              charZero := inferInstance
              ξ := ξ
              centre := hcl
              etc := het
              unr := GlobalTheory.GenFan.formallyUnramified_residue_comp_of_isEtaleCompletion k m e _ het
              G := C.t.G
              semi := C.t.semi
              y := C.y
              hy := hy
              α := α
              gen := hα }, ?_⟩
    intro G _ hG π hπ
    rw [← hcl]
    exact abLocus_pullback abLocusOne hG hπ.1 (closedPoint _)
  have hch : ∀ x : S, Nonempty (GlobalTheory.Desc.Chart j tF.G x) := by
    intro x
    by_cases hx : x ∈ Set.range j
    · exact GlobalTheory.T.nonempty_semiAbelianCompletionChart_of_openPart Xo c j tF.G tF.semi x hx
    · obtain ⟨k, _, m, e, C, ξ, a, htaut, hy, hcl, het, -⟩ := hpre x hx
      obtain ⟨Ch, -⟩ := bdChart x k m e C ξ hy hcl het
      exact ⟨Ch⟩
  obtain ⟨G, _, e, hG, hpb, hmap⟩ := GlobalTheory.T.semiAbelian_descent_from_complete_regular_charts (Xo.XF c) S hNorm j hdom tF.G hAab tF.PP.L hLB hAmp hch
  haveI : IsCommMonObj G := hG.comm
  refine ⟨G, inferInstance, hG.comm, e, hG, hpb, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      by_contra hxj
      obtain ⟨k, _, m, e', C, ξ, a, htaut, hy, hcl, het, -, hset, -⟩ := hpre x hxj
      obtain ⟨Ch, hCh⟩ := bdChart x k m e' C ξ hy hcl het
      obtain ⟨π', hπ', -⟩ := hmap x Ch
      have hcp := (hCh G hG π' hπ').1 hx
      have hprod : ∏ i, C.s i ∈ (closedPoint (ChartRing k m e')).asIdeal := by
        by_contra hn
        exact hxj (hcl ▸ (hset _).2 hn)
      have hm : 1 ≤ C.m := by
        rcases Nat.eq_zero_or_pos C.m with h0 | h0
        · exfalso
          haveI : IsEmpty (Fin C.m) := by rw [h0]; infer_instance
          rw [Finset.univ_eq_empty, Finset.prod_empty] at hprod
          exact (maximalIdeal (ChartRing k m e')).ne_top_iff_one.1 (maximalIdeal.isMaximal _).ne_top hprod
        · exact h0
      exact GlobalTheory.T.closedPoint_notMem_abelianLocus_tautologicalBoundaryChart Xo c φ k m e' C htaut hm hcp
    · rintro ⟨x', rfl⟩
      rw [abLocus_pullback abLocusOne hG hpb.1 x']
      intro K _ _ t _
      haveI := hAab.proper
      infer_instance
  · intro k _ m n C hC ξ hξ tK a b
    haveI := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin n)
    haveI := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (ChartRing k m n)).2
    exact GlobalTheory.T.exists_grpPullback_map_semiAbelian_normalDomain (ChartRing k m n) j tF.G G e hG hpb C.t.G C.t.semi ξ C.y hξ tK.G a.φ b.φ a.cart b.cart

theorem exists_semiAbelian_of_charts_sepB : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hnsi Z zs i OZ N d J S π j _ BD hP _ hpre tF mF
  exact exists_semiAbelian_of_charts Xo c φ hpq hfan hnsi zs i OZ N d J π j BD hP hpre tF mF

end GlobalTheory.UChartDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothModelNearClosedFibreEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u ∧ l ≫ E.f = pullback.fst _ _ ≫ fU := by
  intro R _ _ _ hR M G' _ _ hG E
  have hRn : IsNoetherianRing R := hR.1
  have hRi : IsIntegrallyClosed R := hR.2.2.1
  obtain ⟨hΓ, hsurj⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  obtain ⟨P', b, X, a, hPn, hbs, hbl, hap, -, hab, hcomm, hX, hlift⟩ := GlobalTheory.T.closedFibre_projectiveEmbedding_factors_proper R hR M G' hG E
  have hsq : a ≫ b ≫ PSpace.str R E.N = (X.ι ≫ E.H.ι ≫ G'.hom) ≫ M.π := by
    rw [← Category.assoc, hcomm, Category.assoc, E.f_over]; simp only [Category.assoc]
  have hpt : ∀ w : X.toScheme, (b ≫ PSpace.str R E.N) (a w) = M.π (G'.hom (E.H.ι (X.ι w))) := by
    intro w
    have := congrArg (fun f => f w) hsq
    simpa [Scheme.Hom.comp_apply] using this
  have key : ∀ c : {x : P' // IsClosed ({x} : Set P') ∧ (b ≫ PSpace.str R E.N) x = closedPoint R},
      ∃ V : P'.Opens, c.1 ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧
        IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
    rintro ⟨x, hx1, hx2⟩
    refine GlobalTheory.T.exists_smooth_open_nbhd_isPullback_at_closedPoint R hR M G' hG E P' b X a hbs hbl hap hab hcomm hΓ hsurj x hx1 hx2 ?_ (hlift x hx1 hx2)
    intro Ω _ p p' hr he hs
    have hc : ∀ t, M.π (G'.hom (E.H.ι ((p ≫ X.ι) t))) = closedPoint R := by
      intro t
      have ht : (p ≫ a) t = x := by
        have : (p ≫ a) t ∈ Set.range (p ≫ a) := ⟨t, rfl⟩
        rw [hr] at this; exact this
      have := hpt (p t)
      rw [Scheme.Hom.comp_apply] at ht
      rw [ht, hx2] at this
      rw [Scheme.Hom.comp_apply]; exact this.symm
    have hf : (p ≫ X.ι) ≫ E.f = (p' ≫ X.ι) ≫ E.f := by
      rw [Category.assoc, Category.assoc, ← hcomm, ← Category.assoc, he, Category.assoc]
    have := GlobalTheory.T.eq_of_fieldPoints_closedFibre_same_projective_image R M G' E Ω (p ≫ X.ι) (p' ≫ X.ι) hc (by simpa only [Category.assoc] using hs) hf
    exact (cancel_mono X.ι).1 this
  choose V hxV hVs hVp using key
  set U : P'.Opens := ⨆ c, V c with hUdef
  have hUp : IsPullback (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (U.ι ≫ b ≫ PSpace.str R E.N) M.π :=
    GlobalTheory.T.isPullback_restrict_iSup_of_forall_restrict _ _ _ _ a _ _ _ hsq _ V hVp
  have hUs : Smooth (U.ι ≫ b ≫ PSpace.str R E.N) := GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth _ _ _ _ V hVs
  have hlft : LocallyOfFiniteType (b ≫ PSpace.str R E.N) := by
    have : IsProper (PSpace.str R E.N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N
    infer_instance
  have hU0 : ∀ y : P', (b ≫ PSpace.str R E.N) y = closedPoint R → y ∈ U := by
    refine GlobalTheory.T.mem_of_closedPoints_closedFibre_mem' R P' (b ≫ PSpace.str R E.N) hlft U ?_
    intro y hy1 hy2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy1, hy2⟩, hxV _⟩
  have hsep : IsSeparated (U.ι ≫ b ≫ PSpace.str R E.N) := by
    have : IsProper (PSpace.str R E.N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N
    infer_instance
  have hqc : QuasiCompact (U.ι ≫ b ≫ PSpace.str R E.N) := by
    haveI := hPn
    have : CompactSpace U := isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set P'))
    exact (quasiCompact_iff_compactSpace _).2 this
  let e := hUp.isoPullback
  refine ⟨Near.mk (Over.mk (U.ι ≫ b ≫ PSpace.str R E.N)) hUs hsep hqc
      (e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι) inferInstance ?_ ?_,
    U.ι ≫ b, e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι, ?_, ?_⟩
  · have := hUp.isoPullback_inv_snd
    exact this
  · intro g hg
    obtain ⟨z, rfl⟩ : g ∈ Set.range E.H.ι := by rw [Scheme.Opens.range_ι]; exact E.H_all g hg
    obtain ⟨w, rfl⟩ : z ∈ Set.range X.ι := by rw [Scheme.Opens.range_ι]; exact hX z hg
    have hw : a w ∈ U := hU0 _ (by rw [hpt]; exact hg)
    obtain ⟨w', rfl⟩ : w ∈ Set.range (a ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hw
    refine ⟨e.hom w', ?_⟩
    rw [← Scheme.Hom.comp_apply e.hom, Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.comp_apply]
  · simp only [Category.assoc]
  · show e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.f = pullback.fst (U.ι ≫ b ≫ PSpace.str R E.N) M.π ≫ U.ι ≫ b
    rw [← hcomm, ← Category.assoc ((a ⁻¹ᵁ U).ι), ← morphismRestrict_ι,
      ← Category.assoc e.inv]
    simp only [Category.assoc]
    rw [← Category.assoc e.inv (a ∣_ U), hUp.isoPullback_inv_fst]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerInvariantLifts
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.InvLiftSymm

theorem exists_symm_invLift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ → (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) → (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∀ C : Matrix (Fin n) (Fin n) R, (∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (C a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f) → ∃ Θ : Matrix (Fin n) (Fin n) R, Θᵀ = Θ ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, ∑ b, constFn Y.H.hom W (Θ a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hinv D J V j d hcov hle hlift hwt C hrel
  obtain ⟨g, w, e, P, Qm, he, hPQ, hfac⟩ := GlobalTheory.T.exists_basis_pullback_matrix_invariantFields_raynaud R Dd O oa Y n v dd hinv
  have hKS := GlobalTheory.T.kodairaSpencer_descent_of_torus_invariant_lifts R Dd O oa Y n v dd hinv g w e P he hfac D J V j d hcov hle hlift hwt C hrel
  have hM : (P * C * Pᵀ)ᵀ = P * C * Pᵀ := GlobalTheory.T.kodairaSpencer_relation_matrix_symmetric_local_domain R Dd.toPre.P g w e he D _ hKS
  have hM' : P * (Cᵀ * Pᵀ) = P * (C * Pᵀ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at hM
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hM, Matrix.mul_assoc]
  have hQP : Qmᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  set Θ : Matrix (Fin n) (Fin n) R := C * Pᵀ * Qmᵀ + Qm * P * Cᵀ - Qm * (P * C * Pᵀ) * Qmᵀ with hΘ
  have hΘP : Θ * Pᵀ = C * Pᵀ := by
    rw [hΘ, Matrix.sub_mul, Matrix.add_mul]
    simp only [Matrix.mul_assoc, hQP, Matrix.mul_one]
    rw [hM']
    simp only [← Matrix.mul_assoc]
    abel
  refine ⟨Θ, ?_, ?_⟩
  · rw [hΘ]
    simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, hM]
    simp only [Matrix.mul_assoc]
    abel
  · intro i i' W hW f
    rw [hrel i i' W hW f]
    let cf : R →+* Γ(Y.H.left, W) :=
      (Y.H.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    have hcf : ∀ r, constFn Y.H.hom W r = cf r := fun _ => rfl
    have hW' : W ≤ Y.q.left ⁻¹ᵁ (Dd.toPre.P.L.U (j i) ⊓ Dd.toPre.P.L.U (j i')) :=
      fun x hx => ⟨hle i (hW hx).1, hle i' (hW hx).2⟩
    set X : Fin g → Γ(Y.H.left, W) := fun c =>
      pbT Y.q.left (e c _ (Dd.toPre.P.L.g (j i) (j i')).val) W * pbT Y.q.left (Dd.toPre.P.L.g (j i) (j i'))⁻¹.val W
    have hdlg : ∀ b, dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W = ∑ c, cf (P c b) * X c := by
      intro b
      rw [dlg, hfac b _ W hW', Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hcf, _root_.mul_assoc]
    have key : ∀ (A : Matrix (Fin n) (Fin n) R) (a : Fin n),
        ∑ b, cf (A a b) * dlg Y.H Y.q.left Dd.toPre.P.L (dd b) (j i) (j i') W = ∑ c, cf ((A * Pᵀ) a c) * X c := by
      intro A a
      simp only [hdlg, Finset.mul_sum, Matrix.mul_apply, Matrix.transpose_apply, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul, _root_.mul_assoc]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hcf, ← Finset.sum_mul]
    rw [key Θ a, key C a, hΘP]

end GlobalTheory.InvLiftSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (b : o →+* W) (D : DegPre W), D.TauBimult → (∀ y, PsiUnitOn D y Set.univ) → ∀ n : ℕ, ∃ (T : TautBase o W) (ib : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n (mulDeg D n) ib β ββ w := by
  first | exact @GlobalTheory.TInjBase.main | exact GlobalTheory.TInjBase.main | (intros; apply GlobalTheory.TInjBase.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSetupRegularOverModuliPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSetup_regular_over_moduliPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x : Xo.XF c), ∃ (X' : USetup C) (w : X'.M.Z), X'.π w = C.i x ∧ X'.S.R ≤ X'.M.O w := by
  first | exact @GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at | exact GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at | (intros; apply GlobalTheory.UPoinc.SetupAt.exists_uSetup_regular_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFrameIsValueAtThetaConstantStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionFrame_isValueAt_thetaConstant : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m : ℕ), Odd m → ∀ (T : Over S) (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (y : T ⟶ P.A) (c : Γ(T.left, ⊤)), GlobalTheory.Ex.OneGen.ThG P.A P.L rig m th y c → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (y ^ m).left) (fun _ => 1)), IsTorsFrame P rig m (y ^ m) τ ∧ IsValueAt P.A P.L ((1 : ℕ) : ℤ) th (y ^ m) (powFrame P.A P.L (y ^ m) τ ((1 : ℕ) : ℤ)) c := by
  first | exact @GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt | exact GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt | (intros; apply GlobalTheory.Ex.OneGen.ThG.exists_isTorsFrame_isValueAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLatticeMapAtClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_lattice_map_at_closedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsGrpPullback G out.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ T.P.D.toPre.X), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (g' r ^ 2) (h T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  first | exact @GlobalTheory.UPoinc.TraitAtClosed.exists_trait_lattice_map | exact GlobalTheory.UPoinc.TraitAtClosed.exists_trait_lattice_map | (intros; apply GlobalTheory.UPoinc.TraitAtClosed.exists_trait_lattice_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitCoordsBalancedSymmetricRootsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_coords_balancedSymmetric_roots : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ n : ℕ, IsUnit (n : V) → ∀ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms H.bar X)) (t : Fin m → V), (∀ i, t i ≠ 0) → ∀ q : X → X → (FractionRing V)ˣ, (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ (x : 𝓞 E) a b, q (x • a) b = q a (H.bar x • b)) → (∀ y, ∃ u : Vˣ, (q y (H.w0 • y) : FractionRing V) = algebraMap V _ u * ∏ i, algebraMap V (FractionRing V) (t i) ^ ((n : ℤ) * (ε (.inl i) : LinearMap.BilinForm ℤ X) y (H.w0 • y))) → ∃ s : Fin m ⊕ Fin N → V, (∀ i, Associated (s (.inl i)) (t i)) ∧ (∀ j, IsUnit (s (.inr j))) ∧ ∀ a b, (q a b : FractionRing V) = ∏ k, algebraMap V (FractionRing V) (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ X) a b) := by
  first | exact @GlobalTheory.UnitForm.exists_unit_coords | exact GlobalTheory.UnitForm.exists_unit_coords | (intros; apply GlobalTheory.UnitForm.exists_unit_coords <;> assumption)
end

