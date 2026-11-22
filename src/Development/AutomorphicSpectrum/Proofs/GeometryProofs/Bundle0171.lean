import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0023
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0136
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0128
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0047
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0060
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0081
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangents
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0055
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0088
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticProvisionHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem prov_an : Prov.An :=
  ⟨GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds, GlobalTheory.T.convergence_statement_holds, GlobalTheory.T.signed_convergence_statement_holds, GlobalTheory.T.convergence_rate_statement_holds, GlobalTheory.T.uniform_integrability_statement_holds,
    GlobalTheory.T.pullback_statement_holds, GlobalTheory.T.global_regularization_statement_holds⟩

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem btEmb_localData (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)))
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (R' : Type) [CommRing R'] [IsDomain R'] [HenselianLocalRing R'] [Algebra R R']
    [IsIntegrallyClosed R'] (hflat : Module.Flat R R') :
    ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of (Γ'.btOrder ⊤)))
      (ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤) (U : Γ'.G.left.Opens),
      (∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t)) ∧
      IsPullback (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧
      IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) ∧
      IsOpenImmersion (U.ι ≫ j') ∧ Γ'.TranslatesCover (Γ'.btOrder ⊤) j' U ∧
      ∀ x : Γ'.G.left, Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) (j' x) =
        IsLocalRing.closedPoint R' → x ∈ U := by
  have hA := GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ
  have hinj : Function.Injective (algebraMap R R') := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hreg : IsSMulRegular R' r :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R') (mem_nonZeroDivisors_of_ne_zero hr0)
    have : r • (1 : R') = r • (0 : R') := by
      simp [Algebra.smul_def, hr]
    exact one_ne_zero (hreg this)
  obtain ⟨Γ', F, hbc⟩ := GlobalTheory.T.exists_base_change_group R T Γ R' (algebraMap R R') hinj
  haveI := Γ'.quasiFinite
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.finPres
  obtain ⟨U, hUfin, hUcl⟩ := GlobalTheory.T.henselian_quasi_finite_finite_part R' Γ'.G.left Γ'.G.hom
  have hU : Γ'.IsFinOpenSub U := GlobalTheory.T.isFinOpenSub_of_finite R' T Γ' U hUfin hUcl
  obtain ⟨j', hj'⟩ := (GlobalTheory.T.existsUnique_btOrder_embedding R' T Γ').exists
  have hbt := GlobalTheory.T.btOrder_flat_base_change R T Γ R' Γ' F hbc hflat
  have hfull : ∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
    obtain ⟨d, hd, hf⟩ := hA.full
    exact ⟨d, fun h => hd (hinj (by simpa using h)), hf⟩
  have hext := (GlobalTheory.T.hopf_order_scalar_extension R T R' (Γ.btOrder ⊤) hA hfull).2
  have hext' : ∃ e : R' ⊗[R] (Γ.btOrder ⊤) ≃ₐ[R'] Γ'.btOrder ⊤,
      ∀ (a : Γ.btOrder ⊤) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
    rw [hbt]; exact hext
  obtain ⟨e, he⟩ := hext'
  let iL : R' →+* R' ⊗[R] (Γ.btOrder ⊤) := Algebra.TensorProduct.includeLeftRingHom
  let iR : (Γ.btOrder ⊤) →+* R' ⊗[R] (Γ.btOrder ⊤) :=
    (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := Γ.btOrder ⊤)).toRingHom
  let ψ : Γ.btOrder ⊤ →+* Γ'.btOrder ⊤ := (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤).comp iR
  have hψ : ∀ (a : Γ.btOrder ⊤) (t : T), (ψ a).1 t = algebraMap R R' (a.1 t) := fun a t => he a t
  have sq : IsPullback (Spec.map (CommRingCat.ofHom iL)) (Spec.map (CommRingCat.ofHom iR))
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' (Γ.btOrder ⊤))
  let eH : CommRingCat.of (R' ⊗[R] (Γ.btOrder ⊤)) ⟶ CommRingCat.of (Γ'.btOrder ⊤) :=
    CommRingCat.ofHom (e : R' ⊗[R] (Γ.btOrder ⊤) →+* Γ'.btOrder ⊤)
  haveI : IsIso eH := (e.toRingEquiv.toCommRingCatIso).isIso_hom
  have hb : Spec.map (CommRingCat.ofHom ψ) = Spec.map eH ≫ Spec.map (CommRingCat.ofHom iR) := by
    rw [← Spec.map_comp]; rfl
  have hq : Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))) =
      Spec.map eH ≫ Spec.map (CommRingCat.ofHom iL) := by
    rw [← Spec.map_comp]
    congr 2
    ext r t
    exact congrArg (fun y : Γ'.btOrder ⊤ => y.1 t) (e.commutes r).symm
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom ψ))
      (Spec.map (CommRingCat.ofHom (algebraMap R' (Γ'.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    refine IsPullback.of_iso sq.flip (asIso (Spec.map eH)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hb]
    · simp [hq]
    · simp
    · simp
  have hw : F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) :=
    GlobalTheory.T.embedding_base_change_compat R T Γ R' Γ' F hbc _ _ ψ hψ j j' hj hj'
  have hsq2 : IsPullback F j' j (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_bot ?_ hw hsq
    rw [hj'.isOver, hj.isOver]
    exact hbc.cart
  obtain ⟨ho, hTC⟩ := GlobalTheory.T.btOrder_embedding_open_cover R' T Γ' U hU j' hj'
  refine ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, ho, hTC, fun x hx => hUcl x ?_⟩
  rw [← hj'.isOver]
  simpa using hx

theorem btEmb_specMap_asIdeal {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (x : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom φ) x).asIdeal = Ideal.comap φ x.asIdeal := rfl

theorem isOpenImmersion_emb_and_translatesCover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  intro R _ _ _ _ T _ _ Γ j hj
  have hA := GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ
  refine ⟨?_, ?_⟩
  · haveI := hA.finite
    haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    haveI : LocallyOfFinitePresentation (j ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) := by
      rw [hj.isOver]; exact Γ.finPres
    haveI := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j
      (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
    refine GlobalTheory.T.flat_local_extension_exists R Γ.G.left _ j (Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤)))) ?_
    intro P _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := GlobalTheory.T.exists_henselian_flat_over_prime R P
    obtain ⟨Γ', F, j', ψ, U, -, hsq, hsq2, ho, -, hcl⟩ := btEmb_localData R T Γ j hj R' hflat
    exact ⟨R', inferInstance, inferInstance, inferInstance, Γ'.G.left, _, j', _, F, _, U, hflat, hcomap, hsq, hsq2, ho, hcl⟩
  · intro P
    let p : Ideal R := P.asIdeal.comap (algebraMap R (Γ.btOrder ⊤))
    haveI : p.IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨R', _, _, _, _, hic, hflat, hcomap⟩ := GlobalTheory.T.exists_henselian_flat_over_prime R p
    obtain ⟨Γ', F, j', ψ, U, hψ, hsq, hsq2, -, hTC, -⟩ := btEmb_localData R T Γ j hj R' hflat
    obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Spec.map (CommRingCat.ofHom (algebraMap R (Γ.btOrder ⊤))))
      (g := Spec.map (CommRingCat.ofHom (algebraMap R R'))) P (IsLocalRing.closedPoint R')
      (PrimeSpectrum.ext hcomap.symm)
    let Q := hsq.isoPullback.inv z
    have hQ : Spec.map (CommRingCat.ofHom ψ) Q = P := by
      rw [← hz1]
      change (hsq.isoPullback.inv ≫ Spec.map (CommRingCat.ofHom ψ)) z = _
      rw [hsq.isoPullback_inv_fst]
    obtain ⟨t, g', -, H⟩ := hTC Q
    refine ⟨t, F g', trivial, fun f f' hff => ?_⟩
    have h1 := H (ψ f) (ψ f') (fun h => by rw [hψ, hψ, hff])
    have hg : (j (F g')).asIdeal = Ideal.comap ψ (j' g').asIdeal := by
      rw [← btEmb_specMap_asIdeal]
      change ((F ≫ j) g').asIdeal = ((j' ≫ Spec.map (CommRingCat.ofHom ψ)) g').asIdeal
      rw [hsq2.w]
    rw [hg, ← hQ, btEmb_specMap_asIdeal]
    exact h1

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentComplexPointTangentsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_complex_point_tangents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (n : ℕ) (v : Fin n → Z.V) (y : Sp ℂ ⟶ Y.X) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre y) (w : Fin n → (epsAt y ⟶ Y.t.G)), Function.Injective β → (∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → y ≫ Y.s = spMap (σ.comp β) → (Z.eig τ).IsFrameAt v ⟨centre y, h⟩ → (∀ i, Z.M.ValAt y (v i) (w i)) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value | exact GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFrames.EigValue.isEigFrame_value <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberSectionDerivation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HtPull

theorem secVal_congr {B : Type} [CommRing B] {Z : Scheme.{0}} {x x' : Spec (CommRingCat.of B) ⟶ Z} (e : x = x')
    (W : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ W) (h' : ⊤ ≤ x' ⁻¹ᵁ W) (s : Γ(Z, W)) : secVal x W h s = secVal x' W h' s := by
  subst e
  rfl

theorem epsMul_snd {C : Type} [CommRing C] (c : C) (a : DualNumber C) :
    (GlobalTheory.CompanionTheory.Ar.epsMul c a).snd = c * a.snd := by
  simp [GlobalTheory.CompanionTheory.Ar.epsMul]

theorem one_left_eps {S : Scheme.{0}} (G : Over S) [GrpObj G] {C : Type} [CommRing C] (y : Sp C ⟶ S) :
    (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left = spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def]
  simp

theorem pt_zero {S : Scheme.{0}} {G : Over S} [GrpObj G] {C : Type} [CommRing C] {y : Sp C ⟶ S} {L : Type}
    [AddCommGroup L] [Module C L] (M : LieModel G y L) : M.pt 0 = 1 := by
  have := M.add 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem one_snd {S : Scheme.{0}} (G : Over S) [GrpObj G] {C : Type} [CommRing C] (y : Sp C ⟶ S) (W : G.left.Opens)
    (h0 : ⊤ ≤ (1 : Over.mk y ⟶ G).left ⁻¹ᵁ W) (h1 : ⊤ ≤ (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left ⁻¹ᵁ W) (s : Γ(G.left, W)) :
    (secVal (B := DualNumber C) (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left W h1 s).snd = 0 := by
  have e := one_left_eps G y
  have h2 : ⊤ ≤ (spMap (algebraMap C (DualNumber C)) ≫ (1 : Over.mk y ⟶ G).left) ⁻¹ᵁ W := e ▸ h1
  rw [secVal_congr e W h1 h2 s, secring C (DualNumber C) _ G.left _ W h0 h2 s]
  exact TrivSqZeroExt.snd_inl _ _

theorem exists_linear_snd : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S) (L : Type) [AddCommGroup L] [Module C L] (M : LieModel G y L) (W : G.left.Opens) (h : ∀ l, ⊤ ≤ (M.pt l).left ⁻¹ᵁ W) (s : Γ(G.left, W)), ∃ D : L →ₗ[C] C, ∀ l, D l = (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd := by
  intro S G _ C _ y L _ _ M W h s
  have p0 := pt_zero M
  have h1 : ⊤ ≤ (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left ⁻¹ᵁ W := p0 ▸ h 0
  have h0 : ⊤ ≤ (1 : Over.mk y ⟶ G).left ⁻¹ᵁ W := by
    intro z _
    have t : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ (M.pt 0).left = (1 : Over.mk y ⟶ G).left := M.tan 0
    show (1 : Over.mk y ⟶ G).left z ∈ W
    rw [← t]
    exact h 0 (show spMap (TrivSqZeroExt.fstHom C C C).toRingHom z ∈ (⊤ : Scheme.Opens _) from trivial)
  refine ⟨{ toFun := fun l => (secVal (B := DualNumber C) (M.pt l).left W (h l) s).snd, map_add' := ?_, map_smul' := ?_ },
    fun l => rfl⟩
  · intro l l'
    have e : (M.pt (l + l')).left = (M.pt l * M.pt l').left := by rw [M.add]
    have hvw : ⊤ ≤ (M.pt l * M.pt l').left ⁻¹ᵁ W := e ▸ h (l + l')
    have key := GlobalTheory.T.tangent_section_additive S G C y (M.pt l) (M.pt l') (M.tan l) (M.tan l') W (h l) (h l') hvw h1 s
    have key' := congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom.hom t) key
    simp only [map_add] at key'
    have key'' : secVal (B := DualNumber C) (M.pt l * M.pt l').left W hvw s +
        secVal (B := DualNumber C) (1 : GlobalTheory.CompanionTheory.Ar.epsAt y ⟶ G).left W h1 s =
        secVal (B := DualNumber C) (M.pt l).left W (h l) s + secVal (B := DualNumber C) (M.pt l').left W (h l') s := key'
    have key3 := congrArg TrivSqZeroExt.snd key''
    rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_add, one_snd G y W h0 h1 s, add_zero] at key3
    show (secVal (B := DualNumber C) (M.pt (l + l')).left W (h (l + l')) s).snd = _
    rw [secVal_congr e W (h (l + l')) hvw s]
    exact key3
  · intro c l
    have e := M.smul c l
    have h2 : ⊤ ≤ (spMap (GlobalTheory.CompanionTheory.Ar.epsMul c) ≫ (M.pt l).left) ⁻¹ᵁ W := e ▸ h (c • l)
    show (secVal (B := DualNumber C) (M.pt (c • l)).left W (h (c • l)) s).snd = c • _
    rw [secVal_congr e W (h (c • l)) h2 s, secring _ _ _ G.left _ W (h l) h2 s, epsMul_snd]
    rfl

end GlobalTheory.CompanionTheory.Ar.HtPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.EigBase

section Linear

variable {O F F' V T : Type} [CommRing O] [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]
  [AddCommGroup T] [Module F' T] [Module F T] [IsScalarTower F F' T]

theorem mem_eigSp {R E : Type} [CommRing R] [AddCommGroup E] [Module R E] (ρ : O →+* Module.End R E) (σ : O →+* R)
    (u : E) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem linearIndependent_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) : LinearIndependent F' fun i => j (u i) := by
  have hs : LinearIndepOn F id (Set.range u) := hu.linearIndepOn_id
  let b := Module.Basis.extend hs
  let g : Fin n → (hs.extend (Set.subset_univ _)) := fun i => ⟨u i, hs.subset_extend _ ⟨i, rfl⟩⟩
  have hg : Function.Injective g := fun a c e => hu.injective (congrArg Subtype.val e)
  have e : (fun i => j (u i)) = (hj.basis b) ∘ g := by
    funext i
    simp [IsBaseChange.basis_apply, b, g]
  rw [e]
  exact (hj.basis b).linearIndependent.comp g hg

theorem equiv_baseChange {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) (a : O) (y : F' ⊗[F] V) :
    hj.equiv (LinearMap.baseChange F' (ρ a - σ a • LinearMap.id) y) =
      ρ' a (hj.equiv y) - algebraMap F F' (σ a) • hj.equiv y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c w =>
    rw [LinearMap.baseChange_tmul, hj.equiv_tmul, hj.equiv_tmul, map_smul, hact, smul_comm (algebraMap F F' (σ a)) c,
      ← smul_sub]
    congr 1
    simp [algebraMap_smul]
  | add y z hy hz =>
    simp only [map_add, hy, hz, smul_add]
    abel

theorem exists_sum_of_mem_eigSp {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {t : T}
    (ht : t ∈ eigSp ρ' ((algebraMap F F').comp σ)) :
    ∃ (J : Type) (B : J → F') (b : J →₀ V), (∀ k, b k ∈ eigSp ρ σ) ∧ t = b.sum fun k w => B k • j w := by
  classical
  let B := Module.Basis.ofVectorSpace F F'
  obtain ⟨b, hb⟩ := TensorProduct.eq_repr_basis_left B (hj.equiv.symm t)
  refine ⟨_, B, b, fun k => (mem_eigSp ρ σ _).2 fun a => ?_, ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : V →ₗ[F] V, A = ρ a - σ a • LinearMap.id := ⟨_, rfl⟩
    have h0 : LinearMap.baseChange F' A (hj.equiv.symm t) = 0 := by
      apply hj.equiv.injective
      rw [hA, equiv_baseChange hj σ hact, LinearEquiv.apply_symm_apply, map_zero]
      exact sub_eq_zero.2 ((mem_eigSp ρ' _ t).1 ht a)
    rw [← hb, map_finsuppSum] at h0
    simp only [LinearMap.baseChange_tmul] at h0
    have h1 : (b.mapRange A (map_zero A)).sum (fun i n => B i ⊗ₜ[F] n) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      exact h0
    have h2 := TensorProduct.sum_tmul_basis_left_eq_zero B _ h1
    have h3 := DFunLike.congr_fun h2 k
    simpa [hA, sub_eq_zero] using h3
  · rw [← hj.equiv.apply_symm_apply t, ← hb, map_finsuppSum]
    simp [hj.equiv_tmul]

theorem frame_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) (hs : Submodule.span F (Set.range u) = eigSp ρ σ) :
    LinearIndependent F' (fun i => j (u i)) ∧
      Submodule.span F' (Set.range fun i => j (u i)) = eigSp ρ' ((algebraMap F F').comp σ) := by
  refine ⟨linearIndependent_base hj hu, le_antisymm (Submodule.span_le.2 ?_) fun t ht => ?_⟩
  · rintro _ ⟨i, rfl⟩
    have hi : u i ∈ eigSp ρ σ := hs ▸ Submodule.subset_span ⟨i, rfl⟩
    refine (mem_eigSp ρ' _ _).2 fun a => ?_
    rw [hact, (mem_eigSp ρ σ _).1 hi a, map_smul]
    simp [algebraMap_smul]
  · obtain ⟨J, B, b, hb, rfl⟩ := exists_sum_of_mem_eigSp hj σ hact ht
    have key : ∀ w ∈ Submodule.span F (Set.range u),
        j w ∈ Submodule.span F' (Set.range fun i => j (u i)) := fun w hw => by
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add w z _ _ hw hz =>
        rw [map_add]
        exact Submodule.add_mem _ hw hz
      | smul c w _ hw =>
        rw [map_smul, ← algebraMap_smul F' c]
        exact Submodule.smul_mem _ _ hw
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (key _ (hs ▸ hb k))

end Linear

theorem eigFrame_base {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {F F' : Type} [Field F]
    [Field F'] [Algebra F F'] (x : Sp F ⟶ S) {P : Type} [CommRing P] (act : OAct P G) (σ : P →+* F) {n : ℕ}
    (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt (spMap (algebraMap F F') ≫ x) ⟶ G))
    (hv : ∀ i, (v' i).left = spMap (dualMap (algebraMap F F')) ≫ (v i).left) (h : IsEigFrame act x σ v) :
    IsEigFrame act (spMap (algebraMap F F') ≫ x) ((algebraMap F F').comp σ) v' := by
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨T, _, _, _, _, M', j, hl, hj⟩ := GlobalTheory.T.exists_lie_model_base_change S G F F' x V M
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G F x V M P act.act act.hom act.one act.mul act.add
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act S G F' _ T M' P act.act act.hom act.one act.mul act.add
  have hl' : ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap F F')) ≫ (M.pt e).left := fun e => by
    have := hl e
    simpa [LieModel.Lifts] using this
  have hact : ∀ a e, ρ' a (j e) = j (ρ a e) := fun a e => M'.inj (Over.OverMorphism.ext (by
    rw [hρ' a (j e), Over.comp_left, hl', hl', hρ a e, Over.comp_left, Category.assoc]))
  choose u hu using fun i => M.onto (v i) (h.1 i).1
  obtain rfl : (fun k => M.pt (u k)) = v := funext hu
  obtain ⟨-, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S F G x V M
  obtain ⟨hli, hsp⟩ := ((hf P act ρ σ hρ).2 n u).1 h
  have hvv : v' = fun k => M'.pt (j (u k)) := funext fun k => Over.OverMorphism.ext (by rw [hv k, hl'])
  rw [hvv]
  exact (((GlobalTheory.T.lie_model_eigenvectors_action S F' G _ T M').2 P act ρ' _ hρ').2 n _).2 (frame_base hj σ hact hli hsp)

theorem isEigFrame_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) [Smooth G.hom] (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsEigFrame act x σ v → IsEigFrame act x' (f.comp σ) v' := by
  intro S G _ _ F _ x _ P _ act σ F' _ f x' hx n v v' hv h
  letI := f.toAlgebra
  subst hx
  exact eigFrame_base x act σ v v' hv h

end GlobalTheory.CompanionTheory.Ar.EigBase
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EventuallyOneTmulAdicIntegralCoords
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

def lieModelOfEquiv {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {F F' : Type} [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
    (M : LieModel G x F) (e : F' ≃ₗ[R] F) : LieModel G x F' where
  pt v := M.pt (e v)
  tan v := M.tan _
  inj := M.inj.comp e.injective
  onto v hv := by
    obtain ⟨w, h⟩ := M.onto v hv
    exact ⟨e.symm w, by simpa using h⟩
  add v w := by rw [map_add, M.add]
  smul c v := by rw [map_smul, M.smul]

theorem exists_bdryChart_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (y : Sp ℂ ⟶ Xo.X) (n a : ℕ), a ≤ n → y ≫ Xo.s = spMap σ →
    ∃ C : BdryChart Xo σ n a, ∀ z, C.pt z ≫ C.k = y := by
  intro E _ _ _ H D l Xo σ y n a ha hy
  obtain ⟨t, ⟨m⟩⟩ := exists_sab y Xo.univ.t
  obtain ⟨i, -⟩ := ObjMaps.exists_sab_id t
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum ℂ))
  obtain ⟨F, _, _, ⟨M⟩⟩ := lieModel_exists _ t.G ℂ (𝟙 _)
  obtain ⟨b⟩ := GlobalTheory.T.lie_model_free_of_smooth _ t.G g hg ℂ (𝟙 _) F M
  refine ⟨{ a_le := ha, R := ℂ, t := t, g := g, dim := hg, M := lieModelOfEquiv M b.equivFun.symm,
            ψ := fun _ => RingHom.id ℂ, hol := ⟨Metric.isOpen_ball, fun r => differentiableOn_const _⟩,
            V := Sp ℂ, j := 𝟙 _, j_open := inferInstance, k := y, tV := t, m₁ := i, m₂ := m,
            pt := fun _ => 𝟙 _, pt_eq := fun z _ => ⟨by simp [spMap], by simpa using hy⟩ }, fun z => Category.id_comp _⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreePullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_power_free_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (z : X₂), FibPF t₂ z ↔ FibPF t (f z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff | exact GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusTorsionGeneratorRelationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_torsion_generator_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (x : Sp k ⟶ X0) (p : ℕ) (y : Tm x p ⟶ t.G), y ^ p = 1 → ∀ (κ : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G ^ p, snd t.G t.G]) (cφG t ![fst t.G t.G, snd t.G t.G])) (Sum.elim (cε 2) fun I => -((p : ℤ) * cε 2 I)))), κ.IsGen → ∀ (τ : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![y.left, (1 : Tm x p ⟶ t.G).left] ![1, -1])), τ.IsGen → ∃ C : LB.Gen (LB.LinComb t.PP.L (K := Fin 2) ![pa t.G x y, pb t.G x p] ![(p : ℤ), -(p : ℤ)]), C.IsGen ∧ ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Ym t.G x p) (z : Z') (J : (Z' ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val C r z J = (val κ (r ≫ (lift (fst (Tm x p) t.G ≫ y) (snd (Tm x p) t.G)).left) z J)⁻¹ * val τ (r ≫ (fst (Tm x p) t.G).left) z J ^ p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold | exact GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.exists_gen_pfold <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentBaseChangeCompatStatement
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_base_change_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω) (W : Subring Ω) (φ : W →+* ℂ) (z₁ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ 𝔐₀.X), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → (∀ a : W, φ a ≠ 0 → IsUnit a) → (∀ (a : Ω) (r : ℂ), ValAt 𝔐.ξ z₁ a r → ∃ h : a ∈ W, φ ⟨a, h⟩ = r) → (∀ (a : Ω₀) (r : ℂ), ValAt 𝔐₀.ξ z₂ a r → ∃ h : i a ∈ W, φ ⟨_, h⟩ = r) → ∃ (σ₁ : 𝔐.X.presheaf.stalk (centre z₁) →+* W) (σ₂ : 𝔐₀.X.presheaf.stalk (centre z₂) →+* W), (∀ s, (σ₁ s : Ω) = genMap 𝔐.ξ ⟨centre z₁, 𝔐.all _⟩ s) ∧ (∀ s, (σ₂ s : Ω) = i (genMap 𝔐₀.ξ ⟨centre z₂, 𝔐₀.all _⟩ s)) ∧ (∀ s, φ (σ₁ s) = (Scheme.stalkClosedPointTo z₁).hom s) ∧ (∀ s, φ (σ₂ s) = (Scheme.stalkClosedPointTo z₂).hom s) ∧ spMap σ₁ ≫ 𝔐.X.fromSpecStalk (centre z₁) ≫ 𝔐.f = spMap σ₂ ≫ 𝔐₀.X.fromSpecStalk (centre z₂) ≫ 𝔐₀.f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.exists_common_point | exact GlobalTheory.CompanionTheory.Ar.OrArch.exists_common_point | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.exists_common_point <;> assumption)
end

