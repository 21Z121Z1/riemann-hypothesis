import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnOfFixedOverUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapsAgreeRootOfUnityEnlarged
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrderThree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0005
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalAtPrimesUnitaryCongruentOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0175
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0546
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacter

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjEqAddKummerTorusTorsionPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KummerConj

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion GlobalTheory.BXOf

attribute [local instance] gtGroup

theorem valuation_val_eq {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (O : ValuationSubring F) (φ : R →+* O)
    (hφ : ∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r))
    {X : Scheme.{0}} {L : LB X} (J₀ : X → L.ι) (h₀ : ∀ x, x ∈ L.U (J₀ x)) {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L (closedPoint F) J) (eJ : ∀ ψ : Sp O ⟶ X, J (spMap O.subtype ≫ ψ) = J₀ (ψ (closedPoint O)))
    {K : Type} [Fintype K] {φs : K → ((TK R).left ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φs ε))
    (ht : t.IsGen) (p : K → (Spec (CommRingCat.of R) ⟶ X)) (hp : ∀ k, φs k = jK R ≫ p k) (j : K → L.ι)
    (hj : ∀ k, ⊤ ≤ p k ⁻¹ᵁ L.U (j k)) (h : ⊤ ≤ (LB.LinComb L φs ε).U j) :
    O.valuation (sig F (val t (jFK (R := R) F) (closedPoint F) J) : F) =
      O.valuation (algebraMap (FractionRing R) F (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h)) := by
  have hs : spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R := by
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ
  have hr : ∀ k, jFK (R := R) F ≫ φs k = spMap O.subtype ≫ (spMap φ ≫ p k) := fun k => by
    rw [hp k, ← Category.assoc, ← Category.assoc, hs]
  obtain ⟨w, hw⟩ : ∃ w : ((Sp F).presheaf.stalk (closedPoint F))ˣ →* O.ValueGroupˣ,
      ∀ u, (w u : O.ValueGroup) = O.valuation (sig F u : F) :=
    ⟨(Units.map O.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hunit : ∀ (ψ : Sp O ⟶ X) (U : X.Opens) (hU : ψ (closedPoint O) ∈ U) (a : Γ(X, U)ˣ),
      w (gm (spMap O.subtype ≫ ψ) (closedPoint F) U a) = 1 := fun ψ U hU a => by
    refine Units.ext ((hw _).trans ?_)
    rw [← sig_nat O.subtype ψ hU a]
    exact O.valuation_unit _
  have hz : jFK (R := R) F (closedPoint F) ∈ LB.wchart L φs j := h trivial
  have g := gen_trans ht (jFK (R := R) F) (closedPoint F) (hJ.mem φs (jFK (R := R) F)) hz
  have htr : w (trF φs ε (jFK (R := R) F) (closedPoint F) (fun k => J (jFK (R := R) F ≫ φs k)) j) = 1 := by
    show w (∏ k, gm (jFK (R := R) F ≫ φs k) (closedPoint F) (L.U (J (jFK (R := R) F ≫ φs k)) ⊓ L.U (j k))
      (L.g (J (jFK (R := R) F ≫ φs k)) (j k)) ^ ε k) = 1
    rw [map_prod]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [map_zpow]
    refine (congrArg (· ^ ε k) ?_).trans (one_zpow _)
    rw [hr k]
    apply hunit
    exact ⟨by rw [eJ]; exact h₀ _, hj k (show spMap φ (closedPoint O) ∈ ⊤ from trivial)⟩
  have hgv : (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R)) ((LB.LinComb L φs ε).U j)
      (t.s j)).val = ((Spec (CommRingCat.of (FractionRing R))).presheaf.germ ⊤ (closedPoint (FractionRing R))
        trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv.hom
          (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h).val) := by
    refine (gm_val (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R)) _ (h trivial) (t.s j)).trans ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal, Units.coe_map, MonoidHom.coe_coe, res, RingHom.toMonoidHom_eq_coe]
    rw [Iso.hom_inv_id_apply]
    exact (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of (FractionRing R))).presheaf (homOfLE h)
      (closedPoint (FractionRing R)) trivial _).symm
  have hsg : sig (FractionRing R) (gm (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (closedPoint (FractionRing R))
      (LB.wchart L φs j) (t.s j)) = GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.genVal t j h := by
    refine Units.ext ((congrArg (stalkClosedPointIso (CommRingCat.of (FractionRing R))).hom.hom hgv).trans ?_)
    rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, Iso.inv_hom_id_apply]
  have n := sig_nat (algebraMap (FractionRing R) F) (𝟙 (Spec (CommRingCat.of (FractionRing R)))) (h trivial) (t.s j)
  rw [Category.comp_id] at n
  have n2 := (congrArg (Units.map (algebraMap (FractionRing R) F).toMonoidHom) hsg).symm.trans n
  have e : w (val t (jFK (R := R) F) (closedPoint F) J) =
      w (gm (jFK (R := R) F) (closedPoint F) ((LB.LinComb L φs ε).U j) (t.s j)) := by
    refine (congrArg w g).trans ?_
    rw [map_mul, htr, _root_.one_mul]
    rfl
  rw [← hw, e, hw]
  exact congrArg (fun u : Fˣ => O.valuation (u : F)) n2.symm

theorem conj_eq_add_tor : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ) (σ : F →ₐ[FractionRing R] F) (p p' : QkPt D F k), QkExt σ.toRingHom p p' →
    spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left →
    ∃ (τ : Multiplicative D.X →* Fˣ) (q : QkPt D F k), τ ^ k = 1 ∧ q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkAdd p q p' ∧
      ∀ (χ : D.X) (x : (FractionRing R)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D p.y χ x →
        ∃ s : F, s ≠ 0 ∧ O.valuation s ^ k = O.valuation (algebraMap (FractionRing R) F x) ∧
          σ s = (τ (Multiplicative.ofAdd χ) : F) * s := by
  intro R _ _ D hB F _ _ O φ hφ k σ p p' hext hfix
  have hσ' : σ.toRingHom.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F :=
    RingHom.ext fun a => σ.commutes a
  obtain rfl : p' = qkExt hB σ.toRingHom hσ' p := (qkExt_iff hB _ hσ' _ _).1 hext
  have hb : extMap σ.toRingHom hσ' ≫ p.g.b = p.g.b := Over.OverMorphism.ext hfix
  set d : GtPtF D F := gtExt D σ.toRingHom hσ' p.g - p.g with hd
  have hdb : d.b = 1 := by
    rw [hd, sub_eq_add_neg, add_b, neg_b, gtExt_b, hb, mul_inv_cancel]
  have hgd : gtExt D σ.toRingHom hσ' p.g = p.g + d := by rw [hd, add_sub_cancel]
  obtain ⟨τ, hτ⟩ := exists_torusPt_eq hdb
  have hkd : k • d = 0 := by
    rw [hd, nsmul_sub, ← map_nsmul, qk_nsmul hB, gtExt_iota, sub_self]
  have hτk : τ ^ k = 1 := by
    have e : torusPt D F (Additive.ofMul (τ ^ k)) = torusPt D F (Additive.ofMul 1) := by
      rw [ofMul_pow, map_nsmul, ← hτ, hkd, ofMul_one, map_zero]
    exact Additive.ofMul.injective (torusPt_injective e)
  let q : QkPt D F k := qkMk hB 0 d (by rw [hkd, map_zero])
  refine ⟨τ, q, hτk, rfl, (GlobalTheory.UT.isTor_iff _ _).2 ((isTorusPtF_iff_eq d τ).2 hτ), ?_, fun χ x hx => ?_⟩
  · refine (qkAdd_iff hB _ _ _).2 ?_
    have e : qkAdd hB p q = qkExt hB σ.toRingHom hσ' p := qk_ext (add_zero _) hgd.symm
    rw [e]
    exact qk_equiv_refl hB _

  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  choose J₀ h₀ using fun x : D.P.A.left => exists_chart D.P.isLB x
  obtain ⟨J, hJ, eJ⟩ := exists_good_ext D.P.isLB O.subtype Subtype.val_injective J₀ h₀
  let z : (TF (R := R) F).left := closedPoint F
  have hJ' : Good D.P.L z J := hJ
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨w, hw⟩ : ∃ w : ((TF (R := R) F).left.presheaf.stalk z)ˣ →* O.ValueGroupˣ,
      ∀ u, (w u : O.ValueGroup) = O.valuation (sig F u : F) :=
    ⟨(Units.map O.valuation.toMonoidWithZeroHom.toMonoidHom).comp (sig F), fun _ => rfl⟩
  have hint : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (ψ : K → (Y ⟶ D.P.A.left)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb D.P.L ψ ε)) (r : (Over.mk (spMap φ)).left ⟶ Y), w (val t (ρ.left ≫ r) z J) = 1 := by
    intro Y K _ ψ ε t r
    obtain ⟨u, hu⟩ := val_integral O.subtype h₀ eJ t r
    exact Units.ext ((hw _).trans ((congrArg O.valuation hu).trans (O.valuation_unit u)))
  obtain ⟨b, hb'⟩ := exists_extend O φ ρ rfl p.g.b
  have e₁ := w_nsmul ρ hJ' w hint p.g b hb' χ k
  rw [qk_nsmul hB, iota_val hB _ _ hJ'] at e₁
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ'
  refine ⟨(sig F (charVal p.g χ z J) : F), Units.ne_zero _, ?_, ?_⟩
  · have e₂ := congrArg Units.val e₁
    rw [Units.val_pow_eq_pow_val, hw, hw] at e₂
    rw [← e₂]
    obtain ⟨j, h, i1, i2, i3, i4, rfl⟩ := hx
    have er : (𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F = jFK (R := R) F := by simp
    show O.valuation (sig F (val (D.tau p.y χ) ((𝟙 (TF (R := R) F) :).left ≫ jFK (R := R) F) z J) : F) = _
    rw [er]
    refine valuation_val_eq O φ hφ J₀ h₀ hJ eJ (D.tau p.y χ) (tau_isGen D _ _)
      (Sum.elim (Sum.elim (Sum.elim (fun _ => (D.c (p.y + χ)).left) (fun _ => (D.c p.y).left))
        (fun _ => (D.c χ).left)) (fun _ => (η[D.P.A] : _ ⟶ _).left)) ?_ j ?_ h
    · rintro (((_ | _) | _) | _)
      · rfl
      · rfl
      · rfl
      · show (toUnit (TK R)).left ≫ eSec D.P.A = jK R ≫ (η[D.P.A] : _ ⟶ _).left
        have e : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
        rw [e]
        rfl
    · rintro (((_ | _) | _) | _)
      exacts [i1, i2, i3, i4]
  · have key : σ (sig F (charVal p.g χ z J) : F) =
        (sig F (charVal (gtExt D σ.toRingHom hσ' p.g) χ z J) : F) := by
      have e := gtExt_val σ.toRingHom hσ' p.g χ hJ'
      have hφ' : ∀ i, (extMap σ.toRingHom hσ').left ≫ DegPre.gtφ D F p.g.b χ i =
          𝟙 _ ≫ DegPre.gtφ D F p.g.b χ i := by
        intro i
        rw [Category.id_comp]
        fin_cases i
        · show (extMap σ.toRingHom hσ' ≫ (cP D _ χ * p.g.b)).left = (cP D _ χ * p.g.b).left
          rw [MonObj.comp_mul, comp_cP, hb]
        · show (extMap σ.toRingHom hσ' ≫ cP D _ χ).left = (cP D _ χ).left
          rw [comp_cP]
        · show (extMap σ.toRingHom hσ' ≫ p.g.b).left = p.g.b.left
          rw [hb]
        · show (extMap σ.toRingHom hσ' ≫ (1 : TF (R := R) F ⟶ D.P.A)).left = (1 : TF (R := R) F ⟶ D.P.A).left
          rw [MonObj.comp_one]
      replace e := e.trans (val_of (p.g.s χ) _ _ J _ (fun i => congrArg J (hφ' i)))
      have n := sig_nat σ.toRingHom (𝟙 (Spec (CommRingCat.of F))) (hJ'.mem (DegPre.gtφ D F p.g.b χ) (𝟙 _))
        ((p.g.s χ).s fun i => J (𝟙 _ ≫ DegPre.gtφ D F p.g.b χ i))
      rw [Category.comp_id] at n
      exact (congrArg Units.val n).trans (congrArg (fun u => (sig F u : F)) e.symm)
    have hs : sig F (charVal d χ z J) = τ (Multiplicative.ofAdd χ) := by
      rw [hτ, torusPt_val τ χ hJ']
      refine Units.ext ?_
      show (stalkClosedPointIso (CommRingCat.of F)).hom.hom (((Sp F).presheaf.germ ⊤ (closedPoint F) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (τ (Multiplicative.ofAdd χ) : F))) = _
      rw [← CommRingCat.comp_apply, germ_stalkClosedPointIso_hom, Iso.inv_hom_id_apply]
    have e := add_val p.g d χ hJ'
    rw [hdb, C.face₃, _root_.mul_one] at e
    rw [key, hgd, e, map_mul, Units.val_mul, hs, mul_comm]

end GlobalTheory.KummerConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapsAgreeRootOfUnityEnlargedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientMaps_agree_rootOfUnity_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x ≠ 0 →
    ∃ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL)
      (u : (w.st Z).toD7.what₂.LL) (u' : (w'.st Z').toD7.what₂.LL) (n n' : ℕ), n ≠ 0 ∧ u ^ n = 1 ∧ n' ≠ 0 ∧ u' ^ n' = 1 ∧
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) ∧ c0L i v ≠ 0 ∧
      HEq ((w'.st Z').toD7.what₂.embLL u' • c0L'' i' v') ((w.st Z).toD7.what₂.embLL u • c0L i v) := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftUnit.exists_agree_root | exact GlobalTheory.Mem.R3.Rw.LiftUnit.exists_agree_root | (intros; apply GlobalTheory.Mem.R3.Rw.LiftUnit.exists_agree_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGIs
section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl.TrueLocal

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob GlobalTheory.Mem.TruePeriods GlobalTheory.Mem.PeriodTie

theorem omTied_retie_of_cube {D : D7} (hF : FieldOK D.host D.what₂.embLL D.embE) (h3 : ∀ z : ℂ, z ^ 3 = 1 → z ∈ coefM D) {δ : ℂ}
    (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (retie D) δ := by
  obtain ⟨δ', h', m2, m3⟩ := exists_delta_data D hF
  have h0 := delta_ne_zero h'
  have hu0 : δ / δ' ≠ 0 := div_ne_zero (delta_ne_zero h) h0
  have hu : (δ / δ') ^ 12 = 1 := by
    unfold IsDiscriminantTwelfthRootOfIdealLattice at h h'
    rw [div_pow, h, ← h', div_self (pow_ne_zero _ h0)]
  have hmap : lamOf D D.host.ccK δ = (lamOf D D.host.ccK δ').map (AddMonoidHom.mulLeft (δ / δ')) := by
    rw [lamOf_eq_map, lamOf_eq_map, AddSubgroup.map_map]
    congr 1
    ext; simp [← mul_assoc, div_mul_cancel₀ _ h0]
  generalize δ / δ' = u at hu0 hu hmap
  refine (ties_of_data hF h ?_ ?_).1
  · have e : g2 (lamOf D D.host.ccK δ) = (u ^ 4)⁻¹ * g2 (lamOf D D.host.ccK δ') := by
      unfold g2
      rw [hmap, Model.eisG_map _ _ hu0]; ring
    rw [e]
    exact mul_mem (inv_mem (h3 _ (by rw [← pow_mul, hu]))) m2
  · have e : g3 (lamOf D D.host.ccK δ) = (u ^ 6)⁻¹ * g3 (lamOf D D.host.ccK δ') := by
      unfold g3
      rw [hmap, Model.eisG_map _ _ hu0]; ring
    rw [e]
    refine mul_mem (inv_mem ?_) m3
    rcases sq_eq_one_iff.1 (show (u ^ 6) ^ 2 = 1 by rw [← pow_mul, hu]) with e | e <;> rw [e]
    · exact one_mem _
    · exact neg_mem (one_mem _)

open GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC in
set_option maxHeartbeats 1000000 in
theorem omTied_withTrue {B : Base} {C : Cols B} (hF : FieldOK B.host B.embLL B.embE) (hc : B.host.ccK = ⊤) {δ : ℂ}
    (h : Th.IsDiscriminantTwelfthRootOfIdealLattice B.host ⊤ δ) (Z : Later B C) (hZ : Z.G.gx = Per.trueGx B.host B.embLL B.embE (Equiv.refl _)) :
    Formalism.L2.GlobalTheoryTheory.OmegaCompatible (recOf Z) δ := by
  have h1 : IsDiscriminantTwelfthRootOfIdealLattice (recOf Z) (recOf Z).host.ccK δ := by
    have : (recOf Z).host.ccK = ⊤ := hc
    rw [this]; exact h
  have h2 := omTied_retie_of_cube (D := recOf Z) hF (fun z hz => B.fixedField_le_coefficientField (B.KsC_le_LL0C (B.rootsField_le_KsC
    ((le_sup_right.trans le_sup_left : Fld.cycField (3 ^ 4) ≤ Fld.rootsField B.toPre)
      (Fld.mem_cycField (by norm_num) (by rw [show 3 ^ 4 = 3 * 27 by norm_num, pow_mul, hz, one_pow])))))) h1
  obtain ⟨W, V, S, N, G⟩ := Z
  obtain ⟨M, i, e, a, b, c⟩ := h2
  refine ⟨M, i, e, a, b, fun τ => ?_⟩
  obtain ⟨d, hd, hs⟩ := c τ
  refine ⟨d, hd, fun s => ?_⟩
  have : (recOf (⟨W, V, S, N, G⟩ : Later B C)).gx = G.gx := rfl
  rw [this, show G.gx = _ from hZ]
  exact hs s

section Stages

open Formalism.MainNotions.G Formalism.L2.G IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.ConcreteRecord GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B}

set_option maxHeartbeats 4000000 in

theorem isLocalFamily_stages (sc : Scale) (Z Z' : Later B C) (L0 : LevelData (recOf Z)) (T : ∀ u, Forms0 (recOf Z) u) (g)
    (h : IsLocalFamily sc (recOf Z) L0 T g) : IsLocalFamily sc (recOf Z') L0 (fun u => forms0Re Z' (T u)) g := by
  run_tac do
    let m ← Lean.Elab.Tactic.getMainGoal
    m.withContext do m.assign (← Lean.Meta.getFVarFromUserName `h)

end Stages

section Main

open Formalism.MainNotions.G Formalism.L2.G IsDedekindDomain Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.ConcreteRecord GlobalTheory.Mem.Top.ColOwe GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
open Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top.GroupRetwisting

attribute [local instance] Formalism.BasicNotions.factResChar Formalism.BasicNotions.Host.cmStar

theorem companion_of_colsHermS {D : D7} (H : Formalism.L2.Herm.ColsHermS D) : Companion D H.base.lev0 := fun u =>
  have hi : IsIntegral ℤ (D.host.conj ((H.atT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  ⟨Ideal.span {(⟨_, hi⟩ : 𝓞 D.host.E)}, (H.baseL u ⟨_, hi⟩ rfl).1⟩

theorem exists_gTiedS_heq {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (H0 : Formalism.L2.Herm.Herm0 D) (h : H0.lev0 = H.lev0) :
    ∃ g : Formalism.L2.Herm.SymmetricGroupCompatibility D H, HEq g H0.g := by
  obtain ⟨l, g⟩ := H0
  dsimp only at h
  subst h
  exact ⟨g, HEq.rfl⟩

theorem herm0_eq_to0 {D : D7} (X : Formalism.L2.Herm.FullTiedS D) (H0 : Formalism.L2.Herm.Herm0 D) (h : X.base.lev0 = H0.lev0)
    (hg : HEq X.g H0.g) : H0 = X.to0 := by
  obtain ⟨l, g⟩ := H0
  dsimp only at h hg
  subst h
  obtain rfl := eq_of_heq hg
  rfl

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem columnLocalData_of_levelZero_concreteData (w : ColW B f T) (Z : w.Lt) (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C)
    (hL : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)) (hV : Formalism.L2.Herm.VolumeCompatible (w.D Z)) (hO : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D Z) w.I.J.δ)
    (Gt : GatTies (w.D Z)) (c : LatCmp (w.D Z)) (G : GroupCompatibilityAll (w.D Z) Gt c) (hR : IsRecG K.s (w.D Z) Gt c G.herm G.forms)
    (hl : G.herm.lev0 = C.herm.base.lev0) (hf : G.forms = fun u => (C.forms u).to0)
    (hpl : ∀ u v hg (a : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' a)) (x : 𝓞 (w.D Z).host.F),
      x ∈ ((G.herm.g u v hg).pl a).1.asIdeal ↔ (0 : WithTop ℤ) < (w.D Z).what₂.places.val v
        (tauLL (w.D Z) (Gt.gat_pos u v hg ⟨a, s⟩) (algebraMap (w.D Z).host.F (w.D Z).host.E (x : (w.D Z).host.F)))) :
    Nonempty (ColumnDataSplitPrimes K w Z) := by
  obtain ⟨g, hg⟩ := exists_gTiedS_heq C.herm.base G.herm hl
  obtain ⟨Fu, h1, h2⟩ := GlobalTheory.T.exists_fullHermitianColumns_trueColumns w.I w.ok w.pins w.l Z C g hC hV
  have e : Fu.1.base.lev0 = G.herm.lev0 :=
    (congrArg (fun H : Formalism.L2.Herm.ColsHermS (w.D Z) => H.base.lev0) Fu.2).trans hl.symm
  exact ⟨⟨⟨C, hC, hL, Fu, h2, Gt, c, G, herm0_eq_to0 Fu.1 G.herm e (h1.trans hg), hf,
    gPlTiedS_of G.herm hpl _ _ e (h1.trans hg)⟩, hR, hO⟩⟩

set_option maxHeartbeats 8000000 in

theorem nonempty_columnLocalData_of_standardConcreteFamily (w : ColW B f T) (Z : w.Lt) (C : ColsTiedSym (w.D Z)) (hC : TC.StdC w.I w.l Z C)
    (hL : ∀ u, TC.StdLvC w.I w.l Z u (C.forms u)) (g) (hd)
    (h : IsLocalFamily K.s (w.D Z) C.herm.base.lev0 (fun u => (C.forms u).to0) g)
    (hV : Formalism.L2.Herm.VolumeCompatible (w.D { Z with G := { Z.G with gat := g, gat_d := hd } }))
    (hO : Formalism.L2.GlobalTheoryTheory.OmegaCompatible (w.D { Z with G := { Z.G with gat := g, gat_d := hd } }) w.I.J.δ) :
    Nonempty (ColumnDataSplitPrimes K w { Z with G := { Z.G with gat := g, gat_d := hd } }) := by
  obtain ⟨Gt, c, G, hR, hl, hf, hpl⟩ := isRecG_of_isLocalFamily C.joint0
    (fun u => GlobalTheory.T.exists_psi0_eq_embLL w.I w.ok w.pins w.l Z (C.forms u).gl (hC u).gl) hd h
  exact columnLocalData_of_levelZero_concreteData w _ (colsRe _ C) (stdC_colsRe w.I w.l _ C hC) (fun u => stdLvC_colsRe w.I w.l _ C u (hL u)) hV hO Gt c G hR
    (funext hl) (funext fun u => (hf u).trans ((forms0Re_setGat g hd _).symm.trans (columnFormsAlongLaterStages_stageZero_eq _ C u).symm)) hpl

set_option maxHeartbeats 8000000 in

theorem exists_trueVolume_stage_of_any_column_choice (p : WP) : StepW p fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := by
  refine StepW.of_all fun K B f T w hO _ _ => ?_
  obtain ⟨Z₀⟩ := TrueColsTest.later w.l (JetEx.hasLetters_of_over hO)
  obtain ⟨C, hC, hL⟩ := GlobalTheory.T.exists_standardColumnComparisons_trueColumns w.I w.ok w.pins w.l Z₀
  obtain ⟨g, hd, h⟩ := exists_isLocalFamily K.s (D := w.D Z₀) (fun u => (C.forms u).to0) C.herm.std (companion_of_colsHermS C.herm)
    C.joint0 fun u => GlobalTheory.T.exists_psi0_eq_embLL w.I w.ok w.pins w.l Z₀ (C.forms u).gl (hC u).gl
  refine ⟨{ Z₀.G.withTrue with gat := g, gat_d := hd }, (LayerTwoModel.gIs2_iff w _).2 fun W V S N => ?_⟩
  have hV : Formalism.L2.Theta.VolTieG (w.D ⟨W, V, S, N, { Z₀.G.withTrue with gat := g, gat_d := hd }⟩) :=
    GlobalTheory.T.volumesAgreeAdelic_of_trueVolume _ fun _ => rfl
  refine ⟨hV, nonempty_columnLocalData_of_standardConcreteFamily w ⟨W, V, S, N, Z₀.G.withTrue⟩ (colsRe _ C) (stdC_colsRe w.I w.l _ C hC)
    (fun u => stdLvC_colsRe w.I w.l _ C u (hL u)) g hd ?_ hV.hermVolTied
    (omTied_withTrue w.fld w.px.ccK_top w.ok.amb_ok.delta _ rfl)⟩
  have h' := isLocalFamily_stages K.s Z₀ ⟨W, V, S, N, Z₀.G.withTrue⟩ _ _ g h
  exact (congrArg (fun F => IsLocalFamily K.s (recOf ⟨W, V, S, N, Z₀.G.withTrue⟩) C.herm.base.lev0 F g)
    (funext (columnFormsAlongLaterStages_stageZero_eq ⟨W, V, S, N, Z₀.G.withTrue⟩ C))).mpr h'

theorem exists_trueVolumeStage_columnChoiceStep : StepW Pinned fun K B f T w => ∃ G : GJStage B w.C, GIs2 K w G := exists_trueVolume_stage_of_any_column_choice Pinned

end Main

end GlobalTheory.Mem.Top.Bl.TrueLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalAtPrimesUnitaryCongruentOneStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalAtPrimes_unitary_congruentOne : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 E))}, (∀ P ∈ Q, conjPrime₂ P ∉ Q) →
    ∀ (m : ℕ), 0 < m → (∀ P ∈ Q, ((m : ℕ) : 𝓞 E) ∈ P.asIdeal) → ∀ (z : GL (Fin n) (AfE F E)), z ∈ UAd hc n →
    z ∈ St (1 : GL (Fin n) (AfE F E)) →
    ∃ g : GL (Fin n) (AfE F E), g ∈ UAd hc n ∧ g ∈ RatAt Q ∧ GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g) ∧
      GlobalTheory.Mem.ColAd.CongOne ((m : ℕ) : 𝓞 E) (z⁻¹ * g)⁻¹ := by
  first | exact @GlobalTheory.SeeSaw.TwLev.GlueApprox.exists_ratAt_congOne | exact GlobalTheory.SeeSaw.TwLev.GlueApprox.exists_ratAt_congOne | (intros; apply GlobalTheory.SeeSaw.TwLev.GlueApprox.exists_ratAt_congOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsT
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.St

set_option maxHeartbeats 4000000 in

theorem exists_rowsT : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w) (x : St P), (∀ j v, 1 ≤ j → j ≤ B.R.m → x.o.η j v = P.q.eta j v) → ∃ t : RowsT K w x.o.Z P.Wt x.s.p0, Nonempty (RXs t) ∧ t.hX = P.hX ∧ HEq t.r.z x.m.z ∧ HEq t.r.Y x.r.Y ∧ HEq t.r.Z.jW x.r.Z.jW := by
  refine StepW.of_all fun K B f T w hK hF hw P x hη => ?_
  have hex : P.Wt = x.m.z.W1 (F0K K.s (w.D x.o.Z)) := by
    have h1 := x.m.W1 (F0K K.s (w.D x.o.Z))
    refine Eq.trans ?_ h1.symm
    refine P.exact.trans ?_
    rw [GlobalTheory.T.F0K_eq_of_kapDef K B f T w P.Z₀ x.o.Z P.kap (P.q.kap x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G)]
  let t : RowsT K w x.o.Z P.Wt x.s.p0 :=
    { hX := P.hX
      r := x.rowsAre hη
      exAt := x.m.exAt
      inGeo := x.m.inGeo
      grpAt := x.fits.grpAt
      grp := x.fits.grp
      mu :=
        { inj := w.ok.xi_inj
          range := w.xi_range
          mu0 := w.l.xi0
          star := by
            show w.I.xi w.I.muStar = f.del
            rw [w.ok.xi_star, w.C_eq]
          star' := by
            show w.I.xi w.I.muStar' = f.del'
            rw [w.ok.xi_star', w.C_eq]
          tw := P.q.mu.tw
          on := P.q.mu.on
          off := P.q.mu.off
          sub := P.sub
          supp := P.supp }
      exact := hex
      untw := GlobalTheory.T.index_zero_off_twistedPlaces K B f T w hK hF hw P x hη hex
      emt0 := GlobalTheory.T.periodForms_referenceTuple_isometry_column_pairing K B f T w hK hF hw P x hη
      emt := GlobalTheory.T.periodForms_isometry_columnPairing_at_state K B f T w hK hF hw P x hη
      etaF := x.etaF
      rowInt := GlobalTheory.T.periodRowLatticesIntegral_provisionalRows K B f T w P x.o
      idx := fun Y _ => (P.q.num x.o.η x.o.hη x.o.V x.o.S x.o.N x.o.G).idx Y }
  exact ⟨t, GlobalTheory.T.provisionalRows_furtherCompatibilities_at_state K B f T w hK hF hw P x hη t rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

end GlobalTheory.Mem.R3.Rw.St

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacterStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTuple_reading_level_character : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}, I.ReadsP a S.Lb S.U S.chi y lat st → ∀ (_c : (I.stX a).Cl) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ),
    (∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL)) →
    RdLevOn (E := B.fields.E) B.sp.cm (RatAt (I.Q a)) S.U S.chi (rowTyG I.Ch I.Ps) B.embLL (I.Q a)
      (fun _ => blockTri (blk2 B.R.r)) (fun P => (ξ P.1).comp (blkDet (blk2 B.R.r) 1)) := by
  first | exact @GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | exact GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | (intros; apply GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw <;> assumption)
end

