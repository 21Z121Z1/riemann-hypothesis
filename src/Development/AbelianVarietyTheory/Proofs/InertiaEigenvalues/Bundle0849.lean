import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockFirstActionMatrixUnitEq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Sl2NonnegWeightOfHighestWeightVector
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0046
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0844
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0444
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeSameMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwInputs.Move.Forms

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def fiOfEq (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) : NX.FormsIso (X.R.FW a) (X.R.FW b) :=
  hab ▸
    { eK := RingEquiv.refl _
      eK_LL := fun _ => rfl
      e := LinearEquiv.refl _ _
      eG := MulEquiv.refl _
      eW := fun _ => LinearIsometryEquiv.refl _ _
      wk := fun _ => Iff.rfl
      mkK := fun _ => Iff.rfl
      rho := fun _ _ => rfl
      chi := fun _ => rfl
      j := fun _ _ => rfl }

theorem fiOfEq_eG (X : RealSide D) {a b : Fin D.R.m} (hab : a = b) (g : X.Γ) : (fiOfEq X hab).eG g = g := by
  subst hab; rfl

variable (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
  (YS : NX.NExpRealS X.R X.cG S)

theorem fiOfEq_forms (j : Fin D.R.m) {a b : Fin D'.R.m} (ha : (j : ℕ) = a) (hb : (j : ℕ) = b) (hab : a = b) (x : (X.R.FW j).WK) :
    (fiOfEq X' hab).e ((m.forms j a ha).φ x) = (m.forms j b hb).φ x := by
  subst hab; rfl

include h in
theorem lt_m {n : ℕ} (h2 : n + 1 ≤ D'.R.m) : n < D.R.m := by
  have h3 : D.R.m = D'.R.m := by rw [h.gal.R]
  omega

abbrev dat : NX.RatDat D'.ntw :=
  NX.ratDatR X'.R X'.cG (m.kKsOf (e := e) YS (NX.idxOf D 0)) (m.kKsOf_spec h YS _)

abbrev back (i' : D'.ntw.Tw) : D.ntw.Tw := cast h.Tw_eq.symm i'

theorem back_heq (i' : D'.ntw.Tw) : HEq (back h i') i' := cast_heq _ _

def eFm (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) : 1 ≤ j → j ≤ D'.R.m →
    (D'.nexp.Fm i' j b ≃ₗ[FractionRing (D'.ntw.O i')] NX.Fm (dat h m YS) i' j b) :=
  match j with
  | 0 => fun h1 _ => absurd h1 (by decide)
  | n + 1 => fun _ h2 => m.eFOf h YS _ _ (back_heq h i') ⟨n, lt_m h h2⟩ b

def ks (j : Fin D.R.m) : KsIso ι (show S.Ks ≃+* (dat h m YS).Ks from (YS.fi j).eK.trans m.eK)
    (show S.G ≃* (dat h m YS).G from (YS.fi j).eG.trans m.γ) (S.A ((j : ℕ) + 1)) ((dat h m YS).A ((j : ℕ) + 1)) := m.ksOf h YS j

theorem eFm_cast {i : D.ntw.Tw} {i' : D'.ntw.Tw} (hi : HEq i i') (j : Fin D.R.m) (b : Bool) (h1 h2)
    (x : D.nexp.Fm i ((j : ℕ) + 1) b) :
    eFm h m YS i' ((j : ℕ) + 1) b h1 h2 (h.fmCast hi _ b x) =
      fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j) (YS.eF i _ b (Nat.le_add_left _ _) j.2 x) := by
  obtain rfl : i = back h i' := eq_of_heq (hi.trans (back_heq h i').symm)
  exact h.eFMove_fmCast hi (S' := dat h m YS) (ks h m YS j) _ x

theorem sup_move (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (x : D'.nexp.Fm i' j b) :
    x ∈ D'.nexp.Bsup i' j b ↔ eFm h m YS i' j b h1 h2 x ∈ NX.Bsup (dat h m YS) i' j b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  rw [eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2 x, fmOf_mem_Bsup, ← hsup]
  exact ((record_heq h.gal h.set h.frm h.Bsup h.delta hi).1 _ b _ _ (h.fmCast_heq hi _ b x).symm).1.symm

theorem rho_move (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) : NX.RhoStab (dat h m YS) j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (KsIso.rhoStab_iff (S' := dat h m YS) (ks h m YS ⟨n, lt_m h h2⟩)).1 (YS.rho _ h1 (lt_m h h2))

theorem chi_move (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) : NX.ChiInLL0 (dat h m YS) j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact KsIso.chiInLL0 (S' := dat h m YS) (ks h m YS ⟨n, lt_m h h2⟩) h.LL0 (YS.chi _ h1 (lt_m h h2))

theorem act_move (i' : D'.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D'.R.m) (g : G0g D'.nd) (x : D'.nexp.Fm i' j b) :
    eFm h m YS i' j b h1 h2 (D'.nexp.actG i' j b g x) =
      NX.actG (dat h m YS) i' j b (rho_move h m YS j h1 h2) (chi_move h m YS j h1 h2) g (eFm h m YS i' j b h1 h2 x) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have hi := back_heq h i'
  obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
  obtain ⟨g, rfl⟩ := h.grpEquiv.surjective g
  have e1 : D'.nexp.actG i' (n + 1) b (h.grpEquiv g) (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.actG _ (n + 1) b g x) :=
    eq_of_heq ((((record_heq h.gal h.set h.frm h.Bsup h.delta hi).1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.1 _ _
      (h.grpEquiv_heq g).symm).symm.trans (h.fmCast_heq hi _ b _).symm)
  rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, YS.act]
  refine fmOf_actG (S' := dat h m YS) _ _ _ _ _ _ _ _ ?_ _
  refine (dat h m YS).eG.symm_apply_eq.2 ?_
  refine Eq.symm ((m.cG_eG h _).trans (congrArg h.grpEquiv ?_))
  exact (YS.geq _ _).trans (S.eG.apply_symm_apply g)

def tie (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) : NX.NExpRealS X'.R X'.cG (dat h m YS) where
  fi j := fiOfEq X' (NX.idxOf_succ D' j)
  geq j g := congrArg (fun g => X'.cG (X'.R.eG g)) (fiOfEq_eG X' _ g)
  rho := rho_move h m YS
  chi := chi_move h m YS
  eF := eFm h m YS
  bsup i j b h1 h2 := ⟨1, one_ne_zero, fun x hx => by rw [one_smul]; exact (sup_move h m YS hsup i j b h1 h2 x).1 hx,
    fun x hx => by rw [one_smul]; exact (sup_move h m YS hsup i j b h1 h2 x).2 hx⟩
  act := act_move h m YS

theorem read_move (j : Fin D.R.m) (y : (S.A ((j : ℕ) + 1)).WK) :
    SameMap (evidence X j ((YS.fi j).e y))
      (evidence X' (h.cm j) ((fiOfEq X' (NX.idxOf_succ D' (h.cm j))).e ((ks h m YS j).φ y).1)) := by
  have e1 := fiOfEq_forms m j (a := NX.idxOf D' ((j : ℕ) + 1)) (b := h.cm j)
    (congrArg Fin.val (NX.idxOf_succ D' (h.cm j))).symm rfl (NX.idxOf_succ D' (h.cm j)) ((KsIso.ofFormsIso (YS.fi j)).φ y)
  exact (congrArg (fun z => SameMap (evidence X j ((YS.fi j).e y)) (evidence X' (h.cm j) z)) e1).mpr
    (m.read j (h.cm j) rfl ((KsIso.ofFormsIso (YS.fi j)).φ y))

theorem rdRel_move (hsup) (ρ : Setup D.ntw) (ρ' : Setup D'.ntw) (hs : SameSetup ρ ρ') (hρ : ρ.Good) (hρ' : ρ'.Good) (c : ℂ) :
    RdRel h (fun i j b => realRd YS X.geo.v₀ hρ i j b c) (fun i j b => realRd (tie h m YS hsup) X'.geo.v₀ hρ' i j b c) := by
  intro i i' hi j b f
  have hG := (hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl).1
  refine Function.hfunext hG.symm fun g' g hg => heq_of_eq ?_
  change c⁻¹ * evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b
      (eFm h m YS i' ((j : ℕ) + 1) b (Nat.le_add_left _ _) (h.cm j).2 (h.fmCast hi _ b f)) g' =
    c⁻¹ * evK YS X.geo.v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f) g
  have key : ∀ z : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b (fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j) z) g' =
        evK YS X.geo.v₀ hρ i j b z g := fun z => by
    induction z using TensorProduct.induction_on with
    | zero =>
      exact (congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
        (fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j)).map_zero).trans
          ((congrFun (map_zero _) _).trans (congrFun (evK YS X.geo.v₀ hρ i j b).map_zero g).symm)
    | add x y hx hy =>
      refine (congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
        ((fmOf (S' := dat h m YS) (h.scal hi b) (ks h m YS j)).map_add x y)).trans ?_
      refine (congrFun ((evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b).map_add _ _) g').trans ?_
      rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
    | tmul a y =>
      exact congrArg₂ (· * ·)
        ((record_heq h.gal h.set h.frm h.Bsup h.delta hi).2.1 _ _ hs.e b _ _ (h.frac_heq hi a).symm).symm
        (read_move h m YS j y _ _ (m.v₀ j (h.cm j) rfl) _ _ hg.symm).symm
  exact congrArg (c⁻¹ * ·) ((congrArg (fun z => evK (tie h m YS hsup) X'.geo.v₀ hρ' i' (h.cm j) b z g')
    (eFm_cast h m YS hi j b _ _ f)).trans (key _))

variable {YS} (H : NX.NExpRealH X.R X.cG S YS)

omit H in
include h m in

theorem hecke_sameMap (j : Fin D.R.m) {R : Finset (GA D (Wc D j))} {R' : Finset (GA D' (Wc D' (h.cm j)))}
    (hF : ∀ F F', HEq F F' → HEq (Mult.heckeLin (Wc D j) R F) (Mult.heckeLin (Wc D' (h.cm j)) R' F'))
    {T₁ T₂ : Mult.MMap (model X j)} {T₁' T₂' : Mult.MMap (model X' (h.cm j))} (h1 : SameMap T₁ T₁') (h2 : SameMap T₂ T₂') {c : ℂ}
    (h3 : T₁ = c • Mult.heckeOn (model X j) R T₂) : T₁' = c • Mult.heckeOn (model X' (h.cm j)) R' T₂' := by
  obtain ⟨hG, hW, -⟩ := hecke_geo h.gal.R h.gal.host h.sp j (h.cm j) rfl
  refine MultilinearMap.ext fun v' => funext fun g' => ?_
  obtain ⟨v, hv⟩ := exists_sameVec h.gal.R h.gal.host h.Tau h.eTau hW (m.MW j (h.cm j) rfl) v'
  obtain ⟨g, hg⟩ : ∃ g : GA D (Wc D j), HEq g g' := ⟨cast hG.symm g', cast_heq _ _⟩
  have e1 := hF (T₂ v) (T₂' v') (Function.hfunext hG fun a a' haa => heq_of_eq (h2 v v' hv a a' haa))
  have e2 : ∀ {A B : Type} {f : A → ℂ} {f' : B → ℂ} {a : A} {b : B}, A = B → HEq f f' → HEq a b → f a = f' b := by
    intro A B f f' a b h1 h2 h3
    subst h1; subst h2; subst h3; rfl
  rw [← h1 v v' hv g g' hg, h3]
  exact congrArg (c * ·) (e2 hG e1 hg)

def rdL (X : RealSide D) (j : Fin D.R.m) : (Fin (X.R.nW j) → D.what₂.LL) →ₛₗ[sg0 D X.A3.A] Mult.MMap (model X j) :=
  (X.R.HW j (sg0 D X.A3.A)).e.comp ((X.R.FW j).j (sg0 D X.A3.A))

def hecke (hsup) (hL : ∀ j, ℕ → PlE D'.host → Module.End D'.what₂.LL ((dat h m YS).WL j))
    (hs : ∀ j, NX.HeckeStabR (dat h m YS) j (hL j))
    (hc : ∀ (j : Fin D.R.m) (k : ℕ) (P : PlE D.host) (P' : PlE D'.host), HEq P P' → ∀ y : (S.A ((j : ℕ) + 1)).WK,
      ((ks h m YS j).φ ⟨H.hL _ k P y, H.hs _ (Nat.le_add_left _ _) j.2 k P _ y.2⟩ : (dat h m YS).WL ((j : ℕ) + 1)) =
        hL ((j : ℕ) + 1) k P' ((ks h m YS j).φ y)) : NX.NExpRealH X'.R X'.cG (dat h m YS) (tie h m YS hsup) where
  hL := hL
  hs j _ _ := hs j
  cHk i' b k P' := fracEquiv (h.oEquiv (back_heq h i')) (H.cHk _ b k (cast (place_geo h.gal.R h.gal.host).1.symm P'))
  cHk_zero i' b P' := by rw [H.cHk_zero, map_one]
  cHk_unit i' b P' := (H.cHk_unit _ b _).map _
  cHk_pow i' b k P' := by rw [H.cHk_pow, map_pow]
  hkEq i' j b h1 h2 k P' x p1 p2 p3 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
    have hi := back_heq h i'
    have hP : HEq (cast (place_geo h.gal.R h.gal.host).1.symm P') P' := cast_heq _ _
    generalize cast (place_geo h.gal.R h.gal.host).1.symm P' = P at hP ⊢
    obtain ⟨x, rfl⟩ := (h.fmCast hi _ b).surjective x
    obtain ⟨r1, -, r3⟩ := record_heq h.gal h.set h.frm h.Bsup h.delta hi
    have e1 : D'.nexp.hkF i' (n + 1) b k P' (h.fmCast hi _ b x) = h.fmCast hi _ b (D.nexp.hkF _ (n + 1) b k P x) :=
      eq_of_heq (((r1 _ b _ _ (h.fmCast_heq hi _ b x).symm).2.2 k _ _ hP).symm.trans (h.fmCast_heq hi _ b _).symm)
    change eFm h m YS i' (n + 1) b h1 h2 _ = _ • NX.hkFR (dat h m YS) i' (n + 1) b (hL (n + 1)) (hs (n + 1)) k P'
      (eFm h m YS i' (n + 1) b h1 h2 _)
    rw [e1, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2, eFm_cast h m YS hi ⟨n, lt_m h h2⟩ b h1 h2,
      H.hkEq _ _ b _ _ k P x (fun hh => p1 ((r3 P P' hP).1.1 hh)) (((place_geo h.gal.R h.gal.host).2 P P' hP).1.2 p2)
        (by rw [h.gal.R]; exact p3), fmOf_smul]
    exact congrArg _ (fmOf_restrict (S' := dat h m YS) (h.scal hi b) (ks h m YS ⟨n, lt_m h h2⟩) _ _ _ (hs (n + 1) k P')
      (hc ⟨n, lt_m h h2⟩ k P P' hP) _)

end GlobalTheory.TwInputs.Move.Forms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JointHarmonicHighestWeightMultiplicityOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HarmLine

theorem loc_jointTop : ∀ {σ : Type} [DecidableEq σ] {k l N : ℕ} (z : Fin k × Fin N → σ) (y : Fin l × Fin N → σ) (κ : Fin N → ℂ) (α : Fin k → ℂ) (β : Fin l → ℂ) (G P : MvPolynomial σ ℂ), G ≠ 0 → (∀ v ∈ G.vars, (∀ u, z u ≠ v) ∧ ∀ u, y u ≠ v) → GlobalTheory.CompactHarm.JointTop z y κ α β (G * P) → GlobalTheory.CompactHarm.JointTop z y κ α β P := by
  intro σ _ k l N z y κ α β G P hG hGv hJ
  have hd : ∀ u, u ∉ G.vars → ∀ Q : MvPolynomial σ ℂ,
      MvPolynomial.pderiv u (G * Q) = G * MvPolynomial.pderiv u Q := by
    intro u hu Q
    rw [Derivation.leibniz, MvPolynomial.pderiv_eq_zero_of_notMem_vars hu, smul_zero, add_zero, smul_eq_mul]
  have hz : ∀ c Q, MvPolynomial.pderiv (z c) (G * Q) = G * MvPolynomial.pderiv (z c) Q :=
    fun c Q => hd _ (fun h => (hGv _ h).1 c rfl) Q
  have hy : ∀ c Q, MvPolynomial.pderiv (y c) (G * Q) = G * MvPolynomial.pderiv (y c) Q :=
    fun c Q => hd _ (fun h => (hGv _ h).2 c rfl) Q
  have hmix : ∀ i j, GlobalTheory.Capelli.mixedOp ℂ z y i j (G * P) = G * GlobalTheory.Capelli.mixedOp ℂ z y i j P := by
    intro i j
    rw [GlobalTheory.Capelli.mixedOp_apply, GlobalTheory.Capelli.mixedOp_apply, mul_sub, Finset.mul_sum, Finset.mul_sum]
    simp only [hz, hy]
    exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => by ring) (Finset.sum_congr rfl fun _ _ => by ring)
  have hrz : ∀ c c', GlobalTheory.Capelli.rowOp ℂ z c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ z c c' P := by
    intro c c'
    simp only [GlobalTheory.Capelli.rowOp_apply, hz, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hry : ∀ c c', GlobalTheory.Capelli.rowOp ℂ y c c' (G * P) = G * GlobalTheory.Capelli.rowOp ℂ y c c' P := by
    intro c c'
    simp only [GlobalTheory.Capelli.rowOp_apply, hy, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hJ
  refine ⟨fun i j hij => ?_, fun i => ?_, fun c c' h => ?_, fun c => ?_, fun d d' h => ?_, fun d => ?_,
    fun c d => ?_⟩
  · have := h1 i j hij
    rw [hmix] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h2 i
    rw [hmix, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h3 c c' h
    rw [hrz] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h4 c
    rw [hrz, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h5 d d' h
    rw [hry] at this
    exact (mul_eq_zero.1 this).resolve_left hG
  · have := h6 d
    rw [hry, ← mul_smul_comm] at this
    exact mul_left_cancel₀ hG this
  · have := h7 c d
    simp only [hy, hz, ← Finset.mul_sum] at this
    exact (mul_eq_zero.1 this).resolve_left hG

theorem joint_line : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (lam : D.what₂.Tau → Fin n → ℂ) (P P' : PolF D m n), P ≠ 0 → GlobalTheory.LowestKType.IsHarm w P → GlobalTheory.LowestKType.IsHarm w P' → GlobalTheory.LowestKType.IsNHw w lam P → GlobalTheory.LowestKType.IsNHw w lam P' → GlobalTheory.LowestKType.IsKHw w P → GlobalTheory.LowestKType.IsKHw w P' → ∃ c : ℂ, P' = c • P := by
  intro D n m w lam P P' hP0 hH hH' hN hN' hK hK'
  classical
  set κ : D.what₂.Tau → Fin n → ℂ := fun τ a => lam τ a - (m : ℂ) / 2 + ((m - w.p τ : ℕ) : ℂ) with hκ
  have hJ := GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P hH hN hK
  have hJ' := GlobalTheory.T.jointHighestWeightHarmonic_of_fock_lowestKType D n m w lam P' hH' hN' hK'
  have hU : ∀ τ : D.what₂.Tau, ∃ Q₀ : MvPolynomial (Fin m × Fin n) ℂ, ∀ α β f,
      GlobalTheory.CompactHarm.JointTop (GlobalTheory.HarmLine.zR m n (w.p τ)) (GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β f →
        ∃ r : ℂ, f = r • Q₀ := fun τ =>
    GlobalTheory.T.jointHighestWeightHarmonic_multiplicity_one_covering _ _ (GlobalTheory.HarmLine.zR_inj m n (w.p τ)) (GlobalTheory.HarmLine.yR_inj m n (w.p τ))
      (GlobalTheory.HarmLine.zR_ne_yR m n (w.p τ)) (GlobalTheory.HarmLine.zR_yR_cover m n (w.p τ)) (κ τ)
  choose Q₀ hQ₀ using hU
  let Q : D.what₂.Tau → PolF D m n := fun τ => MvPolynomial.rename (Prod.mk τ) (Q₀ τ)
  have hfac : ∀ (τ : D.what₂.Tau) (P : PolF D m n) α β,
      GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ))
        (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P →
      ∃ R : PolF D m n, P = Q τ * R ∧ ∀ v ∈ R.vars, v.1 ≠ τ := by
    intro τ P α β h
    obtain ⟨s, f, g, hPs, hf, hg⟩ := GlobalTheory.T.isJointHighestWeightHarmonic_slice_outer_variables (Prod.mk τ) (fun a b h => (Prod.mk.inj h).2) _ _ _ _ _ P h
    choose! r hr using fun i (hi : i ∈ s) => hQ₀ τ α β (f i) (hf i hi)
    refine ⟨∑ i ∈ s, r i • g i, ?_, ?_⟩
    · rw [hPs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hr i hi, map_smul, smul_mul_assoc, mul_smul_comm]
    · intro v hv hvτ
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_sum_subset _ _ hv)
      have hvi' : v ∈ (g i).vars := by
        rw [MvPolynomial.smul_eq_C_mul] at hvi
        have := MvPolynomial.vars_mul (MvPolynomial.C (r i)) (g i) hvi
        simpa using this
      exact hg i hi v hvi' ⟨v.2, by rw [← hvτ]⟩
  have hQne : ∀ τ, Q τ ≠ 0 := by
    intro τ h0
    obtain ⟨α, β, hτ⟩ := hJ τ
    obtain ⟨R, hR, -⟩ := hfac τ P α β hτ
    exact hP0 (by rw [hR, h0, zero_mul])
  have hE : ∀ s : Finset D.what₂.Tau, ∀ P : PolF D m n,
      (∀ τ ∈ s, ∃ α β, GlobalTheory.CompactHarm.JointTop (Prod.mk τ ∘ GlobalTheory.HarmLine.zR m n (w.p τ))
        (Prod.mk τ ∘ GlobalTheory.HarmLine.yR m n (w.p τ)) (κ τ) α β P) →
      ∃ R : PolF D m n, P = (∏ τ ∈ s, Q τ) * R ∧ ∀ v ∈ R.vars, v.1 ∉ s := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro P _; exact ⟨P, by simp, by simp⟩
    | insert τ₀ s hτ₀ ih =>
      intro P hPs
      obtain ⟨R, hPR, hRv⟩ := ih P (fun τ hτ => hPs τ (Finset.mem_insert_of_mem hτ))
      obtain ⟨α, β, hJ0⟩ := hPs τ₀ (Finset.mem_insert_self _ _)
      have hG0 : (∏ τ ∈ s, Q τ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => hQne τ
      have hGv : ∀ v ∈ (∏ τ ∈ s, Q τ).vars, v.1 ∈ s := by
        intro v hv
        obtain ⟨τ, hτ, hv'⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hv)
        have := MvPolynomial.vars_rename (Prod.mk τ) (Q₀ τ) hv'
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 this
        exact hτ
      have hJR := loc_jointTop _ _ _ α β _ R hG0 (fun v hv =>
        ⟨fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this),
         fun u h => hτ₀ (by have := hGv v hv; rw [← h] at this; simpa using this)⟩) (hPR ▸ hJ0)
      obtain ⟨R', hRR', hR'v⟩ := hfac τ₀ R α β hJR
      refine ⟨R', by rw [hPR, hRR', Finset.prod_insert hτ₀]; ring, ?_⟩
      intro v hv
      rw [Finset.mem_insert, not_or]
      refine ⟨fun h => hR'v v hv h, hRv v ?_⟩
      have hR'0 : R' ≠ 0 := by rintro rfl; simp at hv
      rw [hRR', MvPolynomial.mem_vars_iff_degreeOf_ne_zero, MvPolynomial.degreeOf_mul_eq (hQne τ₀) hR'0]
      rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hv
      omega
  obtain ⟨R, hR, hRv⟩ := hE Finset.univ P (fun τ _ => hJ τ)
  obtain ⟨R', hR', hR'v⟩ := hE Finset.univ P' (fun τ _ => hJ' τ)
  have hc : ∀ R : PolF D m n, (∀ v ∈ R.vars, v.1 ∉ (Finset.univ : Finset D.what₂.Tau)) →
      R = MvPolynomial.C (R.coeff 0) := fun R h =>
    MvPolynomial.vars_eq_empty_iff_eq_C.1
      (Finset.eq_empty_of_forall_notMem fun v hv => h v hv (Finset.mem_univ _))
  rw [hc R hRv] at hR
  rw [hc R' hR'v] at hR'
  have hc0 : R.coeff 0 ≠ 0 := by
    intro h0; apply hP0; rw [hR, h0]; simp
  refine ⟨R'.coeff 0 / R.coeff 0, ?_⟩
  rw [hR', hR, MvPolynomial.smul_eq_C_mul, ← mul_assoc, mul_comm (MvPolynomial.C _) (∏ τ, Q τ), mul_assoc,
    ← MvPolynomial.C_mul, div_mul_cancel₀ _ hc0]

end GlobalTheory.HarmLine

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremEHypothesesAdmitted
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.AdmThmE

theorem admitted_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.admitted D HW F Cm 10 := by
  intro hBK hTD hEC D HW F Cm
  obtain ⟨hU, hE⟩ := GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm
  obtain ⟨pL, pW, _, _, pWR, pH, pTr, _⟩ := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨_, hSatE, _, _, _, _, hKillE, _, hF1E, _, hF2E, hTools, hBC⟩ := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  obtain ⟨p1, _, _, _, _, _, _, p8, p9, _, _, a, _⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hX := GlobalTheory.HerrExtUnit.main D HW F
  exact ⟨hU, pL, pW, pWR, pH, pTr, hTools, hSatE, hF1E, hF2E, hKillE, GlobalTheory.T.h1fGeneratorBoundAll_loc D, hBC,
    GlobalTheory.HodgeCrysSeq.hodge_crystalline_sequences D, hE,
    Formalism.MainNotions.UnusedSlot35.extension_clause D HW F ⟨p1, p8, hX⟩,
    Formalism.MainNotions.UnusedSlot35.extension_invariant_clause D HW F ⟨p1, p8, p9, a, hX⟩⟩

end GlobalTheory.AdmThmE
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfRaisingOperatorsJointHarmonicsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_raisingOperators_jointHarmonics : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), ∀ N : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ N) → (∀ ψ ∈ N, ∀ (τ : D.what₂.Tau) (i l : Fin m), (i : ℕ) < w.p τ → w.p τ ≤ (l : ℕ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ N) → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ N := by
  first | exact @GlobalTheory.RaiseGen.mem_of_raise | exact GlobalTheory.RaiseGen.mem_of_raise | (intros; apply GlobalTheory.RaiseGen.mem_of_raise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealComponentEqConjInverseRationalMatrix
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.ArchRatComp

theorem compAt_mt_eq_map_inv : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (γ a : GA D V) (γ' : GL (Fin V.rank) D.host.E),
    γ ∈ GQ V → GlobalTheory.Member.IsRat V γ γ' → a ∈ GinfC V → γ * a ∈ GfC V → ∀ τ : D.what₂.Tau, ∃ σ : D.host.E →+* ℂ,
      Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) = ((γ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map σ := by
  intro D θ _ V γ a γ' _ hrat _ hfc τ
  refine ⟨(θ τ).comp ((infPart D).comp (incA D)), ?_⟩
  have h1 : infHom V (γ * a) = 1 := hfc
  have h2 : infHom V a = (infHom V γ)⁻¹ := by
    rw [map_mul] at h1; exact eq_inv_of_mul_eq_one_right h1
  have h3 : infHom V γ = Formalism.UG.bc ((infPart D).comp (incA D)) γ' := by
    show (Formalism.UG.bc _) (matHom V γ) = _
    rw [hrat]
    ext i j
    rfl
  have h4 : Formalism.IndefR.Datum.compAt θ τ (Formalism.L2.Theta.mt V a) = ((infHom V a).val).map (θ τ) := rfl
  rw [h4, h2, h3, ← map_inv]
  ext i j
  rfl

end GlobalTheory.ArchRatComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TermInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TermInvProof

theorem termInv : ∀ D : D7, TermInv D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y s I hI hY n hn f₁ f₂ hf₁ hf₂
  obtain ⟨ν, 𝓨, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne (D := D) (m := s) (n := V.rank)
  exact GlobalTheory.T.doubledLagrangian_term_depends_only_on_isotropic_means D ψ hS.weil.std V W μ 𝓕 hS.covol Y (fr Y) (hS.frame Y) s I hI hY ν 𝓨 hν _ _ f₂
    (hS.weil.om_pres _ f₁ hf₁) hf₁ hf₂
    (fun x hx => GlobalTheory.T.thetaFun_isotropic_mean_unipotent_invariant D ψ V W χV χW om hS.weil s I hI ν 𝓨 hν n hn f₁ hf₁ x hx)

end GlobalTheory.TermInvProof

end
end

