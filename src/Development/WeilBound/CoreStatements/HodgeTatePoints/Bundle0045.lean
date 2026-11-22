import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0047
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoPiece
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnWLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
import Development.WeilBound.CoreStatements.HodgeTatePoints.A36
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0099
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0020
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfFlat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0044
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0035
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.ROmVia

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.A53
section
namespace PositivityTheory.HtPt.Ktw

theorem a52 :
    GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutOneGenerator.proof
    GroundTheory.Heights₂.Heights.Kleiman.GlobalFunctionsIntegral.proof

theorem a53 :
    GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutNonempty.proof a52

theorem a54 :
    GroundTheory.Heights₂.Heights.Kleiman.CutComponent.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.CutComponent.proof
    GroundTheory.Heights₂.Heights.Kleiman.CutZeroNotLe.proof a53
    GroundTheory.Heights₂.Heights.Kleiman.CutDimLower.proof

theorem a55 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleProductPos.proof hR
    GroundTheory.Heights₂.Heights.Kleiman.PointDegreePos.proof a54
    GroundTheory.Heights₂.Heights.Kleiman.CutMultPos.proof

theorem a56 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.ClaimSeq.proof
    GroundTheory.Heights₂.Heights.Kleiman.ZeroIdealChart.proof

theorem a57 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Filt.proof
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.Exists.proof

theorem a58 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Reduce.proof a57
    GroundTheory.Heights₂.Heights.Kleiman.QuotTrans.proof
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Piece.proof

theorem a59 :
    GroundTheory.Heights₂.Heights.Kleiman.ClaimVanish.Statement.{0, 0} :=
  PositivityTheory.HtPt.KtwS.ClaimVanish.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof a56

theorem a60 :
    GroundTheory.Heights₂.Heights.Kleiman.StepTwo.Statement.{0, 0, 0} :=
  PositivityTheory.HtPt.KtwS.StepTwo.assembled a58 a4
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof
    GroundTheory.Heights₂.Heights.Kleiman.TwistSplit.proof

theorem a61 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Lift.proof a56 a59 a60

theorem a62 :
    GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen.proof a4
    GroundTheory.Heights₂.Heights.Kleiman.RestrictGenerated.proof

theorem a63 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

theorem a72 (hR : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.VeryAmpleNefPlusAmple.assembled a39 a43 a48 a51 hR (a55 hR) a61 a62
    GroundTheory.Heights₂.Heights.Kleiman.PointGenerated.proof

end PositivityTheory.HtPt.Ktw
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopf
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Htat.HopfOrderTop

private theorem btOrder_top_isHopfOrder' (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group)
    (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R' : Type) [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R']
    [HenselianLocalRing R'] (T : Type) [CommGroup T] [Finite T] (Γ' : QFGroup R' T) :
    IsHopfOrder (Γ'.btOrder ⊤) := by
  haveI := Γ'.separated
  haveI := Γ'.quasiCompact
  haveI := Γ'.quasiFinite
  haveI := Γ'.finPres
  have hU : Γ'.IsFinOpenSub (GlobalTheory.finitePart Γ'.G.hom) := by
    apply QFGroup.isFinOpenSub_of_closedFibre
    · exact GlobalTheory.isFinite_finitePart (R := CommRingCat.of R') Γ'.G.hom
    · intro x hx
      exact GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R') _ x hx
  rw [← PositivityTheory.HtPt.Htat.HopfOrderEqTop.btOrder_eq_top hHenselian hBaseChange hRegular R' T Γ' _ hU]
  exact PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub R' T Γ' _ hU

private theorem exists_smul_mem_of_extOrder {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {T : Type} [CommGroup T] [Finite T] (A : Subalgebra R (T → R))
    (hA : ∀ g : T → K, g ∈ extOrder (algebraMap R K) A) :
    ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A := by
  classical
  have key : ∀ x ∈ extOrder (algebraMap R K) A, ∃ s : R, s ≠ 0 ∧ ∃ a ∈ A,
      algebraMap R K s • x = fun t => algebraMap R K (a t) := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨1, one_ne_zero, a, ha, by simp⟩
    | algebraMap k =>
      obtain ⟨⟨n, ⟨s, hs⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
      refine ⟨s, nonZeroDivisors.ne_zero hs, algebraMap R (T → R) n, Subalgebra.algebraMap_mem A n, ?_⟩
      funext t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [mul_comm]
      exact hk
    | add x y _ _ hx hy =>
      obtain ⟨s1, hs1, a1, ha1, e1⟩ := hx
      obtain ⟨s2, hs2, a2, ha2, e2⟩ := hy
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, s2 • a1 + s1 • a2, A.add_mem (A.smul_mem ha1 _) (A.smul_mem ha2 _), ?_⟩
      funext t
      have h1 := congrFun e1 t
      have h2 := congrFun e2 t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, map_mul, map_add] at h1 h2 ⊢
      linear_combination (algebraMap R K s2) * h1 + (algebraMap R K s1) * h2
    | mul x y _ _ hx hy =>
      obtain ⟨s1, hs1, a1, ha1, e1⟩ := hx
      obtain ⟨s2, hs2, a2, ha2, e2⟩ := hy
      refine ⟨s1 * s2, mul_ne_zero hs1 hs2, a1 * a2, A.mul_mem ha1 ha2, ?_⟩
      funext t
      have h1 := congrFun e1 t
      have h2 := congrFun e2 t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul] at h1 h2 ⊢
      linear_combination (algebraMap R K s2 * y t) * h1 + (algebraMap R K (a1 t)) * h2
  choose s hs a ha e using fun t : T =>
    key _ (hA (fun u => algebraMap R K ((Pi.single t (1 : R) : T → R) u)))
  haveI := Fintype.ofFinite T
  have hδ : ∀ t, s t • (Pi.single t (1 : R) : T → R) = a t := by
    intro t
    funext u
    apply IsFractionRing.injective R K
    have := congrFun (e t) u
    simpa [Algebra.smul_def] using this
  refine ⟨∏ t, s t, Finset.prod_ne_zero_iff.mpr fun t _ => hs t, fun f => ?_⟩
  have hmem : (∏ t, s t) • f = ∑ t, (f t * ∏ t' ∈ Finset.univ.erase t, s t') • a t := by
    funext u
    simp only [← hδ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_prod_erase _ s (Finset.mem_univ u)]
    ring
  rw [hmem]
  exact A.sum_mem fun t _ => A.smul_mem (ha t) _

theorem btOrder_top_isHopfOrder (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) : IsHopfOrder (Γ.btOrder ⊤) := by
  classical
  refine PositivityTheory.HtPt.Htat.HopfOrderFlatLocal.isHopfOrder_of_flat_local R T _ ?_ ?_
  · obtain ⟨ΓK, F, hbc⟩ := hBaseChange R T Γ (FractionRing R) (algebraMap R (FractionRing R))
      (IsFractionRing.injective R _)
    have hK := btOrder_top_isHopfOrder' hHenselian hBaseChange hRegular (FractionRing R) T ΓK
    rw [PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange R T Γ _ ΓK F hbc inferInstance] at hK
    obtain ⟨d', hd', hd'm⟩ := hK.full
    refine exists_smul_mem_of_extOrder (K := FractionRing R) _ fun g => ?_
    have := hd'm (d'⁻¹ • g)
    rwa [smul_smul, mul_inv_cancel₀ hd', one_smul] at this
  · intro P hP
    haveI := hP.isPrime
    obtain ⟨R', iR, iD, iH, iA, hic, hfl, hcomap⟩ := hHenselian R P
    have hinj : Function.Injective (algebraMap R R') := PositivityTheory.HtPt.Htat.ValuationInjectivePi.flat_inj
    obtain ⟨Γ', F, hbc⟩ := hBaseChange R T Γ R' (algebraMap R R') hinj
    refine ⟨R', iR, iD, inferInstance, iA, hfl, hcomap, ?_⟩
    rw [← PositivityTheory.HtPt.Htat.ValuationInjectivePi.btOrder_flat_baseChange R T Γ R' Γ' F hbc hfl]
    exact btOrder_top_isHopfOrder' hHenselian hBaseChange hRegular R' T Γ'

end PositivityTheory.HtPt.Htat.HopfOrderTop

theorem PositivityTheory.HtPt.Htat.bt_hopf_of (hHenselian : type_of% @GlobalTheory.T.exists_henselian_flat_over_prime) (hBaseChange : type_of% @GlobalTheory.T.exists_base_change_group) (hRegular : type_of% @GlobalTheory.T.regular_at_base_change) : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), IsHopfOrder (Γ.btOrder ⊤) :=
  @PositivityTheory.HtPt.Htat.HopfOrderTop.btOrder_top_isHopfOrder hHenselian hBaseChange hRegular
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MgTate
section
noncomputable section

namespace PositivityTheory.HtPt.Mg

section Pairing

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

private theorem surjective_appTop_of_iso' {X Y : Scheme.{0}} (f : X ≅ Y) : Function.Surjective f.hom.appTop.hom := by
  have h : f.inv.appTop ≫ f.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  intro x
  refine ⟨f.inv.appTop.hom x, ?_⟩
  have hx := congrArg (fun g => g.hom x) h
  simpa using hx

theorem surj_fst_of_proper (hA : IsSemiAbelian A) (T : Over S) (hT : IsProper (pullback.snd A.hom T.hom)) :
    Function.Surjective (fst T A).left.appTop.hom := by
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.geomConnected
  haveI hAb : IsAbelianScheme ((Over.pullback T.hom).obj A) :=
    ⟨inferInstance, (inferInstance : Smooth (pullback.snd A.hom T.hom)), hT,
      (inferInstance : GeometricallyConnected (pullback.snd A.hom T.hom))⟩
  have hb := (GlobalTheory.ExpansionTotal.globalFns T.left ((Over.pullback T.hom).obj A) hAb).2
  have e : (fst T A).left = (pullbackSymmetry T.hom A.hom).hom ≫ pullback.snd A.hom T.hom := by
    simp
  rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  exact Function.Surjective.comp (surjective_appTop_of_iso' _) hb

omit [GrpObj A] in
theorem proper_of_hom {T T' : Over S} (h : T' ⟶ T) (hT : IsProper (pullback.snd A.hom T.hom)) :
    IsProper (pullback.snd A.hom T'.hom) := by
  have e : h.left ≫ T.hom = T'.hom := Over.w h
  have q : pullback.snd A.hom (h.left ≫ T.hom) =
      (pullbackLeftPullbackSndIso A.hom T.hom h.left).inv ≫ pullback.snd (pullback.snd A.hom T.hom) h.left := by
    rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
  have hp : IsProper (pullback.snd A.hom (h.left ≫ T.hom)) := by
    rw [q]
    infer_instance
  rwa [e] at hp

theorem tval_div' (hL : L.IsLB) {T : Over S} (hT : Function.Surjective (fst T A).left.appTop.hom)
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (x : T ⟶ A) (z : Z) (J)
    (hJ : Good L z J) :
    tval θ r z J * (tval θ' r z J)⁻¹ =
      tval θ (r ≫ (translT A x).left) z J * (tval θ' (r ≫ (translT A x).left) z J)⁻¹ := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  exact val_div_eq hL (fst T A).left hT hu hu' r _ (by rw [Category.assoc, translT_fst]) z J hJ

private theorem mul_eq_mul_mul_of_ratio_eq {G : Type*} [CommGroup G] {a a' b b' c c' d d' u : G}
    (h1 : a' * a⁻¹ = b' * b⁻¹) (h2 : c' * c⁻¹ = d' * d⁻¹) (h0 : a * d = c * b * u) :
    a' * d' = c' * b' * u := by
  have hb : b' = a' * a⁻¹ * b := by rw [h1]; group
  have hd : d' = c' * c⁻¹ * d := by rw [h2]; group
  have hd0 : d = a⁻¹ * (c * b * u) := by rw [← h0]; group
  rw [hb, hd, hd0]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commIsOf_change' (hL : L.IsLB) {T : Over S} (hT : Function.Surjective (fst T A).left.appTop.hom)
    {θx θy θx' θy' : ThetaGrp A L k T} {c : Γ(T.left, ⊤)ˣ} (hx : θx'.pt = θx.pt) (hy : θy'.pt = θy.pt)
    (H : CommIsOf A L k θx θy c) : CommIsOf A L k θx' θy' c := by
  rw [commIsOf_iff hL] at H ⊢
  intro Z r z J hJ
  have h1 := tval_div' hL hT θx' θx hx r θy.pt z J hJ
  have h2 := tval_div' hL hT θy' θy hy r θx.pt z J hJ
  have h0 := H Z r z J hJ
  rw [hx, hy]
  exact mul_eq_mul_mul_of_ratio_eq h1 h2 h0

theorem weilIs_pull_of_proper (hA : IsSemiAbelian A) (hL : L.IsLB) {T T' : Over S}
    (hT : IsProper (pullback.snd A.hom T'.hom)) (h : T' ⟶ T)
    {x y : T ⟶ A} {c : Γ(T.left, ⊤)ˣ} (H : WeilIs A L k x y c) :
    WeilIs A L k (h ≫ x) (h ≫ y) (Units.map h.left.appTop.hom.toMonoidHom c) := by
  intro p
  obtain ⟨V, hpV, ⟨θx0, θy0, hx0, hy0⟩, hall⟩ := H (h.left p)
  let V' : T'.left.Opens := h.left ⁻¹ᵁ V
  let g : overRes V' ⟶ overRes V := Over.homMk (h.left ∣_ V) (by
    simp only [overRes, Over.mk_hom]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w h])
  have key : g ≫ overResι V = overResι V' ≫ h := by
    ext
    simp [g, overResι, morphismRestrict_ι, V']
  have hsurj : Function.Surjective (fst (overRes V') A).left.appTop.hom :=
    surj_fst_of_proper hA _ (proper_of_hom (overResι V') hT)
  have hc : unitRes V' (Units.map h.left.appTop.hom.toMonoidHom c) =
      Units.map g.left.appTop.hom.toMonoidHom (unitRes V c) := by
    have hl := congrArg Over.Hom.left key
    simp only [Over.comp_left, overResι, Over.homMk_left] at hl
    ext
    simp only [unitRes, Units.coe_map, MonoidHom.coe_coe]
    have hv := congrArg (fun f => f.appTop.hom (c : Γ(T.left, ⊤))) hl
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hv
    exact hv.symm
  obtain ⟨θx', θy', hx', hy', hcc⟩ := exists_commIsOf_pull hL g (hall θx0 θy0 hx0 hy0)
  refine ⟨V', hpV, ⟨θx', θy', ?_, ?_⟩, ?_⟩
  · rw [hx', hx0, ← Category.assoc, key, Category.assoc]
  · rw [hy', hy0, ← Category.assoc, key, Category.assoc]
  · intro θx θy hx hy
    rw [hc]
    refine commIsOf_change' hL hsurj ?_ ?_ hcc
    · rw [hx, hx', hx0, ← Category.assoc, ← key, Category.assoc]
    · rw [hy, hy', hy0, ← Category.assoc, ← key, Category.assoc]

end Pairing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem exists_section_of_finite {Z : Scheme.{0}} {k K : Type} [Field k] [IsAlgClosed k] [Field K] (i : k →+* K)
    (f : Z ⟶ Sp k) [LocallyOfFiniteType f] (hf : Finite {p : Sp k ⟶ Z // p ≫ f = 𝟙 _}) (w : Sp K ⟶ Z)
    (hw : w ≫ f = spMap i) : ∃ p : Sp k ⟶ Z, p ≫ f = 𝟙 _ ∧ w = spMap i ≫ p := by
  haveI : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace f
  haveI : Finite (closedPoints Z) := Finite.of_equiv _ (pointEquivClosedPoint f)
  have hz : IsClosed ({w (IsLocalRing.closedPoint K)} : Set Z) := by
    set z := w (IsLocalRing.closedPoint K)
    have h1 := JacobsonSpace.closure_inter_closedPoints_eq_closure
      (isClosed_closure (s := ({z} : Set Z))).isLocallyClosed
    have hfin : (closure ({z} : Set Z) ∩ closedPoints Z).Finite :=
      (Set.toFinite (closedPoints Z)).subset Set.inter_subset_right
    have hcl : IsClosed (closure ({z} : Set Z) ∩ closedPoints Z) := by
      rw [← Set.biUnion_of_singleton (closure ({z} : Set Z) ∩ closedPoints Z)]
      exact hfin.isClosed_biUnion (fun c hc => hc.2)
    rw [hcl.closure_eq] at h1
    have hm : z ∈ closure ({z} : Set Z) ∩ closedPoints Z := by
      rw [h1]
      first
        | exact subset_closure (Set.mem_singleton z)
        | exact subset_closure (subset_closure (Set.mem_singleton z))
    exact hm.2
  refine ⟨pointOfClosedPoint f _ hz, pointOfClosedPoint_comp f _ hz, ?_⟩
  have hdesc := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Z w
  set φ := Z.descResidueField (Scheme.stalkClosedPointTo w)
  have hφ : Spec.map φ = spMap i ≫ Spec.map (residueFieldIsoBase f _ hz).hom := by
    have e1 : w ≫ f = Spec.map φ ≫ Spec.map (residueFieldIsoBase f _ hz).inv := by
      rw [SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hdesc]
    rw [← hw, e1, Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.comp_id]
  rw [pointOfClosedPoint, ← Category.assoc, ← hφ, hdesc]

theorem torsion_desc {X : Scheme.{0}} (G : Over X) [GrpObj G] [LocallyOfFiniteType G.hom] {k K : Type} [Field k]
    [IsAlgClosed k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) (n : ℕ) (hf : Finite {g : Over.mk x ⟶ G // g ^ n = 1})
    (g : Over.mk (spMap i ≫ x) ⟶ G) (hg : g ^ n = 1) : ∃ y : Over.mk x ⟶ G, y ^ n = 1 ∧ extPt i x ≫ y = g := by
  let Kn : Over X := pullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)
  let π : Kn ⟶ G := pullback.fst _ _
  have hπ0 : π ≫ (𝟙 G) ^ n = 1 := by
    rw [pullback.condition, comp_one]
  have hπ : ∀ {Y : Over X} (q : Y ⟶ Kn), (q ≫ π) ^ n = 1 := by
    intro Y q
    rw [← Category.comp_id (q ≫ π), ← comp_pow, Category.assoc, hπ0, comp_one]
  have hmk : ∀ {Y : Over X} (a : Y ⟶ G), a ^ n = 1 → a ≫ (𝟙 G) ^ n = toUnit Y ≫ (1 : 𝟙_ (Over X) ⟶ G) := by
    intro Y a ha
    rw [comp_pow, Category.comp_id, ha, comp_one]
  have hfac : ∀ {Y : Over X} (a : Y ⟶ G) (ha : a ^ n = 1) (q : Y ⟶ Kn), q ≫ π = a →
      q = pullback.lift a (toUnit Y) (hmk a ha) := by
    intro Y a ha q hq
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact hq
    · exact Subsingleton.elim _ _
  haveI h1lft : LocallyOfFiniteType (1 : 𝟙_ (Over X) ⟶ G).left := by
    have hc : (1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom = 𝟙 _ := Over.w _
    haveI : LocallyOfFiniteType ((1 : 𝟙_ (Over X) ⟶ G).left ≫ G.hom) := by
      rw [hc]
      infer_instance
    exact locallyOfFiniteType_of_comp _ G.hom
  haveI hπlft : LocallyOfFiniteType π.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      ((IsPullback.of_hasPullback ((𝟙 G) ^ n) (1 : 𝟙_ (Over X) ⟶ G)).map (Over.forget X)).flip h1lft
  haveI : LocallyOfFiniteType Kn.hom := by
    rw [← Over.w π]
    infer_instance
  let fZ : pullback Kn.hom x ⟶ Sp k := pullback.snd Kn.hom x
  have hq : ∀ p : Sp k ⟶ pullback Kn.hom x, p ≫ fZ = 𝟙 _ →
      (p ≫ pullback.fst Kn.hom x) ≫ Kn.hom = (Over.mk x).hom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (p ≫ fZ) ≫ x = x
    rw [hp, Category.id_comp]
  have hfin : Finite {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _} := by
    refine Finite.of_surjective (fun a : {a : Over.mk x ⟶ G // a ^ n = 1} =>
      (⟨pullback.lift (pullback.lift a.1 (toUnit _) (hmk a.1 a.2)).left (𝟙 _)
        (by rw [Over.w, Category.id_comp]; rfl), pullback.lift_snd _ _ _⟩ :
        {p : Sp k ⟶ pullback Kn.hom x // p ≫ fZ = 𝟙 _})) ?_
    rintro ⟨p, hp⟩
    let q : Over.mk x ⟶ Kn := Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)
    refine ⟨⟨q ≫ π, hπ q⟩, ?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← hfac (q ≫ π) (hπ q) q rfl]
      rfl
    · rw [pullback.lift_snd]
      exact hp.symm
  let w : Sp K ⟶ pullback Kn.hom x := pullback.lift (pullback.lift g (toUnit _) (hmk g hg)).left (spMap i)
    (by rw [Over.w]; rfl)
  obtain ⟨p, hp, hwp⟩ := exists_section_of_finite i fZ hfin w (pullback.lift_snd _ _ _)
  let q : Over.mk x ⟶ Kn := Over.homMk (p ≫ pullback.fst Kn.hom x) (hq p hp)
  refine ⟨q ≫ π, hπ q, ?_⟩
  ext
  have e1 : w ≫ pullback.fst Kn.hom x = (pullback.lift g (toUnit _) (hmk g hg)).left := pullback.lift_fst _ _ _
  have e2 := congrArg Over.Hom.left (pullback.lift_fst g (toUnit _) (hmk g hg))
  rw [Over.comp_left] at e2
  rw [← e2, ← e1, hwp]
  simp [q, extPt, π]

theorem unitOn_map {k K : Type} [Field k] [Field K] (i : k →+* K) (c : kˣ) :
    Units.map (spMap i).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map i.toMonoidHom c) := by
  apply Units.ext
  have := congrArg (fun q => q.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))
  exact this.symm

end PositivityTheory.HtPt.Mg
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RomNonunit
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rom

theorem a_nonunit_of (h : type_of% @GlobalTheory.T.fundamental_ideal_frobenius_powers) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ τ : MulChar F R, IsFund p τ → ∀ c' c : R, idealX AA.carrier K t τ = Ideal.span {c'} → idealX AA.carrier K t (τ ^ p) = Ideal.span {c} → v (algebraMap R C c') ^ p < v (algebraMap R C c) → c ∈ idealD p AA.carrier K t (τ ^ p) :=
  PositivityTheory.HtPt.Rd.a_nonunit_rom_of (@r_om_of h)

end PositivityTheory.HtPt.Rom
end

