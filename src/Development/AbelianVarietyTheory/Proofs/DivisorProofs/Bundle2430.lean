import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Torsor
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapAllTuplesCoeffFieldOfClauses
section
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.TwistField

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem oneMapOverL_of_clauses (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ) (i : Fin D.R.m)
    (hC : GlobalTheory.Hk3.Core R F) (h1 : R.tup_mu_off) (h2 : R.tup_mu_used) (hW : Nonempty (FWTie T R κ v₀)) (hpb : T.pb = R.C.P.pb)
    (hO : OMPins T R κ v₀ O i) (hph : PhaseTie T R κ v₀ O ph i) (hio : IoExt R) (h0 : OneMapRow0 T R κ v₀ O i)
    (hex : PinsOverL T R κ v₀ i) (hsp : LiftsSpan R i (v₀ i (sg0 D A))) : OneMapOverL T R κ v₀ (ph i) i := by
  have hrow := hph h0
  obtain ⟨w⟩ := id hW
  have hT := w.laws
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := (O i).hV
  have hn : (κ i).n = (Vc D i).rank :=
    (w.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, hlam, hU⟩ := GlobalTheory.T.adelicLift_eq_factor_mul_geometricClassSum D G Pl0 T0 A T R F κ v₀ hC h1 h2 hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hF₀, hP₀⟩ := hex
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := GlobalTheory.LiftSpanClauses.exists_retie_core O₀ hC
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hF₁ : O₁.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange := e₁ ▸ hF₀
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := hF₁.ge
  obtain ⟨c0, hr, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  have hid := hU _ _ (O i) hO.1.ge hP rfl hc c0 hx
  have hid₁ := hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁
  have hE₁ := GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ O₁ hle₁ hP₁
  have n0 := ne_zero_of_root hr
  have n1 := ne_zero_of_root hr₁
  by_cases hz : ∀ y, liftQ R i (v₀ i (sg0 D A)) A.μ0 y = 0
  · exact ⟨O₁, hF₁, hP₁, oneMapOf_of_ptIdent hT hV hn hP hrow hle₁ hP₁ hlev₁ hE₁ hsp hlam n0 n1 hid hid₁ (Or.inr hz)⟩
  · obtain ⟨y, hy⟩ := not_forall.1 hz
    have hu := const_ratio_mem hT hV hn hO.1 hP hrow hle₁ hP₁ hlev₁ hE₁ hlam n1 hid hid₁ hy
    have e : ((⟨c0 / c1, hu⟩ : O₁.c'.F) : ℂ) * c1 = c0 := div_mul_cancel₀ _ n1
    have hx₂ := xiConst_scaleXi O₁ ⟨c0 / c1, hu⟩ hx₁
    have hP₂ := pins_scaleXi O₁ ⟨c0 / c1, hu⟩ (fun h => div_ne_zero n0 n1 (congrArg Subtype.val h)) hx₁ (e.symm ▸ hr) hP₁
    rw [e] at hx₂
    exact ⟨scaleXi O₁ ⟨c0 / c1, hu⟩, hF₁, hP₂, oneMapOf_of_ptIdent (O' := scaleXi O₁ ⟨c0 / c1, hu⟩) hT hV hn hP hrow hle₁ hP₂ hlev₁
      (GlobalTheory.LiftSpanClauses.clsEx_of_core D G Pl0 T0 A T R κ v₀ hC.lev hC.fam hW hpb i _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂) hsp hlam n0 n0 hid
      (hU _ _ (scaleXi O₁ ⟨c0 / c1, hu⟩) hle₁ hP₂ hlev₁ hc₁ c0 hx₂) (Or.inl rfl)⟩

end GlobalTheory.TwistField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenImmersionClassifyingFamilyChartStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openImmersion_classifying_family_chart : ∀ (S : Scheme.{0}) (A B S' U : Over S) [GrpObj A] (b : B ⟶ S') (P : LB (A ⊗ B).left) (M : LB (A ⊗ U).left), Rep A b P → Fam A M → ∀ φ : U ⊗ S' ⟶ B, φ ≫ b = snd U S' → Same A M P (fst U S') φ → IsOpenImmersion φ.left → ∀ (T : Over S) (_ : T ⟶ S') (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  first | exact @GlobalTheory.RepChart.repChart | exact GlobalTheory.RepChart.repChart | (intros; apply GlobalTheory.RepChart.repChart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdinaryPointInvariantUnderObjectMap
section
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace ObjMapPts

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S₂ : Scheme.{0}} {s₁ : S ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o : Obj b N s₁} {o₂ : Obj b N s₂} {f : S ⟶ S₂}

def push (m : ObjMap o o₂ f) {k : Type} [CommRing k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ o.A) : Over.mk (x ≫ f) ⟶ o₂.A :=
  Over.homMk (g.left ≫ m.φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [m.cart.1.w, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w g))

@[simp] theorem push_left (m : ObjMap o o₂ f) {k : Type} [CommRing k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ o.A) :
    (push m x g).left = g.left ≫ m.φ := rfl

end ObjMapPts

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointCompleteFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_complete_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
    (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ (σ : E →+* ℂ) (x : LieG P.Gt) (u : Sp (DualNumber ℂ_[p]) ⟶ Xo.univ.t.G.left),
      LieTie P (ψ ≫ ν.φ) x u → IsEigAt c σ u → AvDefs.IsEig P.Gt P.oGt (embInt c P.integers σ) x := by
  first | exact @GlobalTheory.FlatModel.pt_isEig_of_lieTie | exact GlobalTheory.FlatModel.pt_isEig_of_lieTie | (intros; apply GlobalTheory.FlatModel.pt_isEig_of_lieTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointFrameMapStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_frame_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype)
    (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p)
    (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y yb yy P π ψ →
    ∀ u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left, IsTanAtG Y.t yb u → ∃ x : LieG P.Gt, ITie P π x u := by
  first | exact @GlobalTheory.FlatModel.exists_iTie | exact GlobalTheory.FlatModel.exists_iTie | (intros; apply GlobalTheory.FlatModel.exists_iTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointModelAbelianMap
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem spMap_epsMul_algebraMap {R : Type} [CommRing R] (s : R) :
    spMap (epsMul s) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  rw [spMap, spMap, ← Spec.map_comp]
  congr 1
  ext x
  · simp [epsMul]
  · simp [epsMul, TrivSqZeroExt.map]

theorem tanEig_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]]
    (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (y : FrPt Xo c ℂ_[p]), GlobalTheory.AllWt.ptF y = yy ≫ r →
    ∀ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left, w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy →
    spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left →
    ∀ σ : E →+* ℂ, (∀ a : 𝓞 E, (w ≫ Y.m.φ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w ≫ Y.m.φ) →
    IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν p _ _ yy y hy w hw h1 σ he
  have hx : yy ≫ r ≫ pullback.fst _ _ = y.x := by
    have h0 : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
    rw [hy, Category.assoc] at h0
    exact h0
  have hsq : ν.φ ≫ Xo.univ.t.G.hom = Y.oF.t.G.hom ≫ r ≫ pullback.fst _ _ := ν.cart.1.w
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hsq, ← Category.assoc, hw, Category.assoc, hx]
  · let T : Over (Xo'.XF c') := Over.mk yy
    have hu : ((1 : T ⟶ Y.oF.t.G).left ≫ ν.φ) ≫ Xo.univ.t.G.hom = T.hom ≫ (r ≫ pullback.fst _ _) := by
      rw [Category.assoc, hsq, ← Category.assoc, Over.w]
    let x₀ : Over.mk (T.hom ≫ (r ≫ pullback.fst _ _)) ⟶ Xo.univ.t.G := Over.homMk ((1 : T ⟶ Y.oF.t.G).left ≫ ν.φ) hu
    have hm := ν.cart.2 T 1 1 x₀ x₀ rfl rfl
    have hxx : x₀ * x₀ = x₀ * 1 := by
      rw [_root_.mul_one]
      ext1
      rw [hm, _root_.mul_one]
      rfl
    have h11 : x₀ = 1 := mul_left_cancel hxx
    have key : ∀ (m m' : Sp ℂ_[p] ⟶ Xo.X), m = m' →
        (1 : Over.mk m ⟶ Xo.univ.t.G).left = (1 : Over.mk m' ⟶ Xo.univ.t.G).left := by
      rintro _ _ rfl; rfl
    rw [← Category.assoc, h1]
    have : x₀.left = (1 : Over.mk (T.hom ≫ (r ≫ pullback.fst _ _)) ⟶ Xo.univ.t.G).left := by rw [h11]
    exact this.trans (key _ _ hx)
  · intro a
    have hA : w ≫ (Y.oF.t.act.act a).left =
        spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w := by
      apply Y.m.cart.1.hom_ext
      · rw [Category.assoc, Y.m.act a, ← Category.assoc, he a, Category.assoc]
      · rw [Category.assoc, Over.w, hw, Category.assoc, hw, ← Category.assoc, spMap_epsMul_algebraMap]
    rw [Category.assoc, ← ν.act a, ← Category.assoc, hA, Category.assoc]

end GlobalTheory.FlatModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartOffClosedPartFromBase
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem isLocalization_away_of_absorb {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) {f : R} (hf : f ∈ c) :
    IsLocalization.Away f (Localization.Away (algebraMap R R' f)) := by
  have hmap : ∀ a : R, algebraMap R (Localization.Away (algebraMap R R' f)) a =
      algebraMap R' (Localization.Away (algebraMap R R' f)) (algebraMap R R' a) := fun a =>
    IsScalarTower.algebraMap_apply R R' _ a
  refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [hmap, map_pow, map_pow]
    exact IsUnit.pow n (IsLocalization.Away.algebraMap_isUnit (algebraMap R R' f))
  · intro z
    obtain ⟨⟨r', ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R R' f)) z
    obtain ⟨y, -, hy⟩ := hc f hf r'
    refine ⟨⟨y, ⟨f ^ (n + 1), n + 1, rfl⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [hmap, hmap, hy, map_pow, map_pow, pow_succ, map_mul, ← hz, map_pow]
    ring
  · intro a b h
    rw [hmap, hmap] at h
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R R' f)) h
    refine ⟨⟨f ^ k, k, rfl⟩, hinj ?_⟩
    simp only [map_mul, map_pow] at hk ⊢
    exact hk

theorem pinched_off : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → ∀ x : B', (b' ≫ spMap (algebraMap R R')) x ∉ Set.range (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  intro R _ R' _ _ hinj c hc g B' C Y b' e i q hsm x hx
  obtain ⟨f, hfc, hfx⟩ : ∃ f ∈ c, f ∉ ((b' ≫ spMap (algebraMap R R')) x).asIdeal := by
    by_contra hno
    push_neg at hno
    apply hx
    have hr : Set.range (spMap (Ideal.Quotient.mk c)) =
        PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk c)) :=
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
    rw [hr, Ideal.mk_ker]
    exact hno
  haveI : IsLocalization.Away f (Localization.Away (algebraMap R R' f)) :=
    isLocalization_away_of_absorb hinj c hc hfc
  let l' : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R' := spMap (algebraMap R' _)
  let h : Sp (Localization.Away (algebraMap R R' f)) ⟶ Sp R := spMap (algebraMap R _)
  haveI : IsOpenImmersion l' := IsOpenImmersion.of_isLocalization (algebraMap R R' f)
  haveI : IsOpenImmersion h := IsOpenImmersion.of_isLocalization f
  have hcomp : l' ≫ spMap (algebraMap R R') = h := by
    simp only [l', h, spMap, ← Spec.map_comp]
    congr 1
  have hrange : Set.range h = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range _ f
  have hrange' : Set.range l' =
      (PrimeSpectrum.basicOpen (algebraMap R R' f) : Set (PrimeSpectrum R')) :=
    PrimeSpectrum.localization_away_comap_range _ _
  let j : pullback b' l' ⟶ B' := pullback.fst b' l'
  let u : pullback b' l' ⟶ Sp R := pullback.snd b' l' ≫ h
  have hju : j ≫ b' ≫ spMap (algebraMap R R') = u := by
    simp only [j, u, ← hcomp]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hsmu : SmoothOfRelativeDimension g u := by
    haveI : SmoothOfRelativeDimension g (pullback.snd b' l') :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback b' l') hsm
    haveI : SmoothOfRelativeDimension 0 h := inferInstance
    have := smoothOfRelativeDimension_comp g 0 (pullback.snd b' l') h
    simpa using this
  have hD : ∀ t : ↥(pullback b' l'), f ∉ (u t).asIdeal := fun t => by
    have : u t ∈ Set.range h := ⟨pullback.snd b' l' t, rfl⟩
    rw [hrange] at this
    exact this
  have hEmpty : ∀ (T : Scheme.{0}) (a : T ⟶ pullback b' l') (a' : T ⟶ Sp (R ⧸ c)),
      a ≫ u = a' ≫ spMap (Ideal.Quotient.mk c) → IsEmpty T := by
    intro T a a' w
    refine ⟨fun t => hD (a t) ?_⟩
    have e1 : u (a t) = spMap (Ideal.Quotient.mk c) (a' t) := by
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    rw [e1]
    show Ideal.Quotient.mk c f ∈ (a' t).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hfc]
    exact Ideal.zero_mem _
  have w1 : 𝟙 (pullback b' l') ≫ u = (j ≫ b') ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, Category.assoc, hju]
  have w2 : Scheme.emptyTo (pullback b' l') ≫ u = (Scheme.emptyTo C ≫ e) ≫ spMap (Ideal.Quotient.mk c) :=
    Scheme.empty_ext _ _
  refine ⟨pullback b' l', pullback b' l', ∅, u, 𝟙 _, j, Scheme.emptyTo _, Scheme.emptyTo C, hsmu,
    ⟨⟨w1⟩, ⟨PullbackCone.IsLimit.mk w1 (fun s => s.fst) (fun s => Category.comp_id _) (fun s => ?_)
      (fun s m h1 _ => by simpa using h1)⟩⟩, inferInstance, ?_,
    ⟨⟨w2⟩, ⟨PullbackCone.IsLimit.mk w2
      (fun s => haveI := hEmpty _ _ _ s.condition; isInitialOfIsEmpty.to _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)
      (fun s m _ _ => by haveI := hEmpty _ _ _ s.condition; exact isInitialOfIsEmpty.hom_ext _ _)⟩⟩, ?_⟩
  · have hr : Set.range s.snd ⊆ Set.range l' := by
      rintro _ ⟨t, rfl⟩
      rw [hrange']
      have e1 : spMap (algebraMap R R') (s.snd t) = u (s.fst t) := by
        rw [← Scheme.Hom.comp_apply, ← s.condition, Scheme.Hom.comp_apply]
      have := hD (s.fst t)
      rw [← e1] at this
      exact this
    have hl : IsOpenImmersion.lift l' s.snd hr ≫ l' = s.snd := IsOpenImmersion.lift_fac l' s.snd hr
    have hl2 : IsOpenImmersion.lift l' s.snd hr = s.fst ≫ pullback.snd b' l' := by
      rw [← cancel_mono h, ← hcomp, ← Category.assoc, hl, ← s.condition]
      show s.fst ≫ (pullback.snd b' l' ≫ h) = _
      rw [← hcomp]
      simp only [Category.assoc]
    show s.fst ≫ j ≫ b' = s.snd
    rw [← hl, hl2]
    exact congrArg (s.fst ≫ ·) pullback.condition
  · rw [IsOpenImmersion.range_pullbackFst l' b']
    show b' x ∈ Set.range l'
    rw [hrange']
    exact hfx
  · intro T a a' _
    haveI : IsEmpty T := ⟨fun t => isEmptyElim (a' t)⟩
    exact ⟨isInitialOfIsEmpty.to Y, isInitialOfIsEmpty.hom_ext _ _, isInitialOfIsEmpty.hom_ext _ _⟩

end GlobalTheory.Pinch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsAffineOfSpectra
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch.Aff

theorem pinched_of_iso (g : ℕ) {S S' Z B' C Y B₂ C₂ Y₂ : Scheme.{0}} {s' : S' ⟶ S} {z : Z ⟶ S}
    {b' : B' ⟶ S'} {e : C ⟶ Z} {i : Y ⟶ B'} {q : Y ⟶ C}
    {b₂ : B₂ ⟶ S'} {e₂ : C₂ ⟶ Z} {i₂ : Y₂ ⟶ B₂} {q₂ : Y₂ ⟶ C₂}
    (eB : B' ≅ B₂) (eC : C ≅ C₂) (eY : Y ≅ Y₂)
    (hb : b' = eB.hom ≫ b₂) (he : e = eC.hom ≫ e₂) (hi : i ≫ eB.hom = eY.hom ≫ i₂)
    (hq : q ≫ eC.hom = eY.hom ≫ q₂) (x : B') (h : Pinched g s' z b₂ e₂ i₂ q₂ (eB.hom x)) :
    Pinched g s' z b' e i q x := by
  obtain ⟨U, U', V, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := h
  refine ⟨U, U', V, u, p, j ≫ eB.inv, n, k ≫ eC.inv, hu, ?_, inferInstance, ?_, ?_, ?_⟩
  · simpa [hb] using hp
  · obtain ⟨t, ht⟩ := hx
    refine ⟨t, ?_⟩
    simp [ht]
  · simpa [he] using hn
  · intro T a a' h
    obtain ⟨y, hy1, hy2⟩ := hl T a a' h
    refine ⟨y ≫ eY.inv, ?_, ?_⟩
    · have : eY.inv ≫ i = i₂ ≫ eB.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hi]; simp
      rw [Category.assoc, this, ← Category.assoc, hy1, Category.assoc]
    · have : eY.inv ≫ q = q₂ ≫ eC.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, ← hq]; simp
      rw [Category.assoc, this, ← Category.assoc, hy2, Category.assoc]

theorem isPushout_of_isPullback_Spec {A B C D : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D}
    {k : C ⟶ D} (H : IsPullback (Spec.map h) (Spec.map k) (Spec.map f) (Spec.map g)) :
    IsPushout f g h k := by
  have w : k.op ≫ g.op = h.op ≫ f.op := by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp, Quiver.Hom.unop_op]
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact H.w.symm
  exact (IsPullback.of_map Scheme.Spec w H.flip).unop

end GlobalTheory.Pinch.Aff

namespace GlobalTheory.Pinch.Aff

theorem pinched_affine_of_spec : (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y)) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), IsAffine B' → IsAffine C → Smooth b' → e.appTop.hom.IsStandardSmoothOfRelativeDimension g → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ y : Y, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q (i y) := by
  intro H R _ _ R' _ _ _ hinj c hc g B' C Y b' e i q hB hC hsm hss h1 h2 y
  haveI : IsAffine Y := IsAffine.of_isPullback h1
  haveI := hsm
  set φc : CommRingCat.of R' ⟶ Γ(B', ⊤) := Spec.preimage (B'.isoSpec.inv ≫ b') with hφc
  set δc : CommRingCat.of (R ⧸ c) ⟶ Γ(C, ⊤) := Spec.preimage (C.isoSpec.inv ≫ e) with hδc
  set πc : Γ(B', ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom) with hπc
  set ψc : Γ(C, ⊤) ⟶ Γ(Y, ⊤) := Spec.preimage (Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom) with hψc
  have eφ : spMap φc.hom = B'.isoSpec.inv ≫ b' := by simp [spMap, φc]
  have eδ : spMap δc.hom = C.isoSpec.inv ≫ e := by simp [spMap, δc]
  have eπ : spMap πc.hom = Y.isoSpec.inv ≫ i ≫ B'.isoSpec.hom := by simp [spMap, πc]
  have eψ : spMap ψc.hom = Y.isoSpec.inv ≫ q ≫ C.isoSpec.hom := by simp [spMap, ψc]
  have hφs : φc.hom.Smooth := by
    rw [← HasRingHomProperty.Spec_iff (P := @Smooth), hφc, Spec.map_preimage]
    infer_instance
  have hδ : δc = (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).inv ≫ e.appTop := by
    apply Spec.map_injective
    rw [hδc, Spec.map_preimage, Spec.map_comp, Iso.inv_comp_eq, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hδs : δc.hom.IsStandardSmoothOfRelativeDimension g := by
    rw [hδ, CommRingCat.hom_comp]
    exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso.cancel_left_isIso _ _).mpr hss
  have hp1 : IsPushout (CommRingCat.ofHom (φc.hom.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c))
      (CommRingCat.ofHom πc.hom) (CommRingCat.ofHom (ψc.hom.comp δc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap πc.hom) (spMap ψc.hom ≫ spMap δc.hom) (spMap φc.hom ≫ spMap (algebraMap R R'))
      (spMap (Ideal.Quotient.mk c))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h1 Y.isoSpec B'.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hp2 : IsPushout (CommRingCat.ofHom (δc.hom.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom ψc.hom) (CommRingCat.ofHom (πc.hom.comp φc.hom)) := by
    apply isPushout_of_isPullback_Spec
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    change IsPullback (spMap ψc.hom) (spMap πc.hom ≫ spMap φc.hom) (spMap δc.hom ≫ spMap (Ideal.Quotient.mk c))
      (spMap (algebraMap R R'))
    rw [eφ, eδ, eπ, eψ]
    refine IsPullback.of_iso h2 Y.isoSpec C.isoSpec (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have hP := H R R' hinj c hc g Γ(B', ⊤) Γ(C, ⊤) Γ(Y, ⊤) φc.hom δc.hom πc.hom ψc.hom hφs hδs hp1 hp2
    (Y.isoSpec.hom y)
  have hpt : spMap πc.hom (Y.isoSpec.hom y) = B'.isoSpec.hom (i y) := by
    rw [eπ]; simp
  rw [hpt] at hP
  refine pinched_of_iso g B'.isoSpec C.isoSpec Y.isoSpec ?_ ?_ ?_ ?_ (i y) hP
  · rw [eφ]; simp
  · rw [eδ]; simp
  · rw [eπ]; simp
  · rw [eψ]; simp

end GlobalTheory.Pinch.Aff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerOfInducedBundleGenerated
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo

set_option autoImplicit false

namespace GlobalTheory.TrueGeo.InducedGen

theorem exists_isGenerated_pow : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A.Induced M L q cf → Y.ample A.D → ∃ m : ℕ, 1 ≤ m ∧ GlobalTheory.IsGenerated ((L.pow m).B.pull M.j) := by
  intro F _ _ C Y A M L q cf hI hA
  obtain ⟨_, r, hr, _, _⟩ := hI
  have hq : Y.ample ((q : ℕ) • A.D) := Var.ample_nsmul F Y A.D q q.pos hA
  have hiso : LBIso (L.B.pull M.j) (toLB ((q : ℕ) • A.D)) := hr.lbIso (presents_toLB _)
  have hamp : IsAmpleLB (L.B.pull M.j) := IsAmpleLB.of_lbIso hq hr.isLB hiso
  obtain ⟨n, hn, hg⟩ := hamp.exists_isGenerated_pow
  refine ⟨n, hn, ?_⟩
  exact hg.of_lbIso (LB.isLB_pull (isLB_lbPow L.isLB n) M.j)
    (LBIso.symm (lbIso_lbPow_pull L.isLB M.j n))

end GlobalTheory.TrueGeo.InducedGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_statement_holds : ProjSt := by
  first | exact @GlobalTheory.FlatModel.Proj.projSt | exact GlobalTheory.FlatModel.Proj.projSt | (intros; apply GlobalTheory.FlatModel.Proj.projSt <;> assumption)
end

