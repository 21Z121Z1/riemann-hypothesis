import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringRationalOfLocalTraces
section
section
open NumberField
namespace GlobalTheory.CovTop
open GlobalTheory.BigTop Formalism.IndefR.FWT
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem covering_rational_of_local_traces : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → Rat := by
  intro _
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ =>
    ⟨0, le_rfl, ⟨0, fun x hx _ ι p hp i => ratAt_of_rows p i hp.1 hp.2⟩⟩⟩⟩
end GlobalTheory.CovTop
end

section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_rationality_criterion : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovTop.Rat := by
  first | exact @_root_.GlobalTheory.CovTop.covering_rational_of_local_traces | exact _root_.GlobalTheory.CovTop.covering_rational_of_local_traces | (intros; apply _root_.GlobalTheory.CovTop.covering_rational_of_local_traces <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DeformationRetractsOfKodairaSpencerZero
section
section
set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
end GlobalTheory.DeRham
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
variable {C : Over (Sp (DualNumber R))} [GrpObj C] {φ : C.left ⟶ A.left} {j : A.left ⟶ C.left}
end GlobalTheory.DeRham
namespace GlobalTheory.DeRham
open GlobalTheory.Cris GlobalTheory.Published GlobalTheory.Published.AbelianDeRham TensorProduct
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
end GlobalTheory.DeRham
namespace GlobalTheory.FlagTan
theorem exists_retraction_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' →
      ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left)
        (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i),
        IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
        (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) →
        ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  intro Pr GD E _ _ _ H Dw l Xo c K _ _ y x' _ _ A _ A' _ π π' i h _ hπ' _ hKS
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  exact GlobalTheory.DeRham.exists_retraction_of_isKSValue_one Pr.p5 GD h hA' gA' hKS
end GlobalTheory.FlagTan
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deformation_retracts_of_kodaira_spencer_zero : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) → ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  first | exact @_root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero | exact _root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero | (intros; apply _root_.GlobalTheory.FlagTan.exists_retraction_of_kodaira_spencer_zero <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsUnramifiedCurveOverField
section
section
set_option autoImplicit false
namespace GlobalTheory.RefSum.UnramCurveField
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.FieldSize.RayExistCurve
open scoped IntermediateField
end
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
theorem exists_unramified_curve_over_field : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ), 3 ≤ n → q.Prime → ¬ q ∣ 2 * n * H.d → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n :=
  fun h E _ _ _ H n q hn hq hnd => exists_field_of_rayField h.p8 E H n q hn hq
    (fun e => hnd ((e.mul_left 2).mul_right _)) (fun e => hnd (e.mul_left _))
end GlobalTheory.RefSum.UnramCurveField
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_curve_field_existence : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ), 3 ≤ n → q.Prime → ¬ q ∣ 2 * n * H.d → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n := by
  first | exact @_root_.GlobalTheory.RefSum.UnramCurveField.exists_unramified_curve_over_field | exact _root_.GlobalTheory.RefSum.UnramCurveField.exists_unramified_curve_over_field | (intros; apply _root_.GlobalTheory.RefSum.UnramCurveField.exists_unramified_curve_over_field <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeneratedWeightsMulStableAndBounded
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem generated_weights_mul_stable_and_bounded : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (P : WtPar (T.Q.Dw j)) (R : Choice TF.X Z Y.U P) (ω : CanId R.toModif) (h : Ready R ω (xiR D) (fun _ => D.sp.W j) Y.dict) (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂) (th : R.L.Sec) (k : Consts), BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ k.beta → (h.data f₁ f₂ th k).MulStable ∧ (h.data f₁ f₂ th k).MulBound fun _ => k.beta := by
  intro hPr D T j Y e o hG hE Z TF P R ω h f₁ f₂ th k hB
  have tr : ∀ (a b : AllWt.Weight (T.Q.Dw j)) (_ : a = b) (g : Cusp Z Y.U a), ∃ g' : Cusp Z Y.U b, g'.1 = g.1 ∧
      (g ∈ latOn Y.U Z (wtOf _ a 0) → g' ∈ latOn Y.U Z (wtOf _ b 0)) := by
    rintro a b rfl g
    exact ⟨g, rfl, id⟩
  have key : ∀ (i : ℕ) (hi : i < P.T) (w' : Cusp Z Y.U P.u₁) (f' : Cusp Z Y.U (P.wt i)),
      ∃ g' : Cusp Z Y.U (P.wt (i + 1)), g'.1 = w'.1 * f'.1 ∧
        (w' ∈ latOn Y.U Z (wtOf _ P.u₁ 0) → f' ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) →
          g' ∈ latOn Y.U Z (wtOf _ (P.wt (i + 1)) 0)) ∧
        ((h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' : (h.data f₁ f₂ th k).V (i + 1)) :
            (h.data f₁ f₂ th k).Sec (i + 1)) =
          (h.data f₁ f₂ th k).mulW i (f₁.b.equivFun w') (h.equivV f₁ f₂ th k hi.le f') := by
    intro i hi w' f'
    have hx := _root_.GlobalTheory.T.cuspidal_sections_mul_mem D T j Y e o hG hE Z P.u₁ (P.wt i) w' f' hPr
    obtain ⟨g, hg, hgl⟩ := hx
    have hy := tr _ _ (P.u₁_add_wt i) g
    obtain ⟨g', hg', hgl'⟩ := hy
    refine ⟨g', hg'.trans hg, fun a b => hgl' (hgl a b), ?_⟩
    exact (h.coe_equivV f₁ f₂ th k _ g').trans ((h.mulW_adjSec f₁ f₂ th k i w' f' g' (hg'.trans hg)).symm.trans
      (congrArg _ (h.coe_equivV f₁ f₂ th k hi.le f').symm))
  refine ⟨?_, ?_⟩
  · intro i hi w hw f hf
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', -, hl, he⟩ := hk
    have hw' : f₁.b.equivFun.symm w ∈ latOn Y.U Z (wtOf _ P.u₁ 0) :=
      (h.mem_lattice f₁ f₂ th k _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).lattice) (f₁.b.equivFun.apply_symm_apply w)) hw)
    have hf' : (h.equivV f₁ f₂ th k hi.le).symm f ∈ latOn Y.U Z (wtOf _ (P.wt i) 0) :=
      (h.equivV_mem f₁ f₂ th k hi.le _).1
        (Eq.mpr (congrArg (· ∈ (h.data f₁ f₂ th k).M i) (LinearEquiv.apply_symm_apply _ f)) hf)
    refine ⟨h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g', (h.equivV_mem f₁ f₂ th k _ g').2 (hl hw' hf'), ?_⟩
    exact he.trans (congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
      (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f)))
  · intro i hi σ w hw f hf g hg
    have pe : ∀ (a b : AllWt.Weight (T.Q.Dw j)), a = b → ∀ σ x,
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ x =
          petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ x := by
      rintro a b rfl σ x
      rfl
    have hk := key i hi (f₁.b.equivFun.symm w) ((h.equivV f₁ f₂ th k hi.le).symm f)
    obtain ⟨g', hgp, -, he⟩ := hk
    have hgg : g = h.equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) g' :=
      Subtype.ext (hg.trans ((congrArg₂ (fun a b => (h.data f₁ f₂ th k).mulW i a b) (f₁.b.equivFun.apply_symm_apply w)
        (congrArg Subtype.val (LinearEquiv.apply_symm_apply _ f))).symm.trans he.symm))
    have hb := GlobalTheory.T.petersson_norm_mul_le_sqrt_bergman_mul_component D T j Y e o hG hE Z P.u₁ (P.wt i) (f₁.b.equivFun.symm w)
      ((h.equivV f₁ f₂ th k hi.le).symm f) k.beta (zero_le_one.trans k.one_le_beta) hB σ
    have e0 : petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ g'.1 =
        petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.u₁ + P.wt i) 0) σ
          ((f₁.b.equivFun.symm w).1 * ((h.equivV f₁ f₂ th k hi.le).symm f).1) :=
      (congrArg (petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (P.wt (i + 1)) 0) σ) hgp).trans
        (pe _ _ (P.u₁_add_wt i).symm σ _)
    have e1 := h.nrm_equivV f₁ f₂ th k (Nat.succ_le_of_lt hi) σ g'
    have e2 := h.normAt_eq f₁ f₂ th k σ (f₁.b.equivFun.symm w)
    have e3 := h.nrm_equivV f₁ f₂ th k hi.le σ ((h.equivV f₁ f₂ th k hi.le).symm f)
    have e2' := (congrArg ((h.data f₁ f₂ th k).normAt σ) (f₁.b.equivFun.apply_symm_apply w).symm).trans e2
    have e3' := (congrArg (((h.data f₁ f₂ th k).nm i).nrm σ) (LinearEquiv.apply_symm_apply _ f).symm).trans e3
    calc _ = _ := congrArg (((h.data f₁ f₂ th k).nm (i + 1)).nrm σ) hgg
      _ = _ := e1
      _ = _ := e0
      _ ≤ _ := hb
      _ = _ := congrArg₂ (fun a b => Real.sqrt k.beta * a * b) e2'.symm e3'.symm
end GlobalTheory.HSApp
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.LocalShareNumberBound
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.LocShareNum
open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW host_facts sum_wtOf eUk_coeff_one_re_pos eJk_coeff_one_re_pos wtOf_eq_zero_of_not_label rangeW_of_sizes)
local instance {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
local instance {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
end GlobalTheory.CovTop.LocShareNum
namespace GlobalTheory.CovTop.LocShareNum
open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW rangeW_of_sizes)
theorem local_share_count_le_exp : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → Lifts fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  intro _hP hG
  refine ⟨1 / 52, by norm_num, fun eps he he1 => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, le_rfl, ?_⟩⟩⟩
  have hez : 0 < Fm.ez := div_pos he (lt_of_lt_of_le one_pos Fm.toFamCore.one_le_J)
  have hez1 : Fm.ez ≤ 1 := le_trans (div_le_self he.le Fm.toFamCore.one_le_J) (by linarith)
  obtain ⟨a, ha⟩ := wg_sum_le Fm.ez hez hez1
  refine ⟨max (max a (Fm.x1 + 1)) (max 4 ((3 / 2 : ℝ) ^ (1 / Fm.ez))), fun x hx hle ι p hp _ => ?_⟩
  have hx4 : 4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have hxa : a ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have hx1 : (3 / 2 : ℝ) ^ (1 / Fm.ez) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
  have hxe : 3 / 2 ≤ x ^ Fm.ez := by
    have hpos : 0 ≤ (3 / 2 : ℝ) ^ (1 / Fm.ez) := by positivity
    calc (3 / 2 : ℝ) = ((3 / 2 : ℝ) ^ (1 / Fm.ez)) ^ Fm.ez := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hez.ne', Real.rpow_one]
      _ ≤ x ^ Fm.ez := Real.rpow_le_rpow hpos hx1 hez.le
  have hS := sizesRec_at_point Fm hx hx4 ι (le_refl (6 : ℝ))
  have hR := rangeW_of_sizes hS hxe
  have hL := GlobalTheory.GLq.lemmaL_series_weights_of_greenCuspidalParametrisation hG _ hp.2.2
  dsimp only
  rw [Fm.L_x x ι hx, Fm.toFamCore.L_ez x ι]
  have hψ := stdAddChar_ne_one (Fm.D x ι)
  refine ⟨fun k => @ZMod.stdAddChar _ ⟨((Fm.D x ι).host.g_prime k).ne_zero⟩, hψ, fun S hS' => ?_⟩
  have h0 := locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 0 (S 0) (hS' 0)
  have h1 := locShare_eUk_le_Wg hL (tieAdmG_rec _) hR _ hψ 1 (S 1) (hS' 1)
  have h2 := ha x hxa _ hS
  linarith
end GlobalTheory.CovTop.LocShareNum
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_share_number_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GreenCuspidal → Lifts fun Fm x _ ι _ _ _ _ => ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod ((Fm.D x ι).host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧ ∀ S : ∀ k : Fin 2, Finset (Formalism.MainNotions.ArithmeticCylinders.Tup (Fm.D x ι) k), (∀ k, ∀ t ∈ S k, ¬ Formalism.MainNotions.ArithmeticCylinders.goodAt (Fm.D x ι) k t) → Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 0 (S 0) + Formalism.MainNotions.ArithmeticCylinders.locShare (Fm.D x ι) (fun k _ => Formalism.MainNotions.ArithmeticCylinders.eUk (Fm.D x ι) k (ψ₀ k)) 1 (S 1) ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := by
  first | exact @_root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp | exact _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp | (intros; apply _root_.GlobalTheory.CovTop.LocShareNum.local_share_count_le_exp <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwoDefBoundSubUnitErrorLeMuCore
section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CoreDesc
theorem isDefined_of_not_functionField_algClosed : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → ¬ FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  intro _
  refine ⟨0, 0, le_rfl, ?_⟩
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A hR _ _ _ _ hF
  exact (hF (fnAlgClosed_core p hR _ ⟨Nat.succ_pos _, i.isLt⟩)).elim
end GlobalTheory.CoreDesc
end

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_defBound_sub_unitError_le_muCore : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ M : ℝ, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → ¬ FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → 2 * defBound (dat p i) (wtA (p.κ i)) (p.κ i).n (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) - C₀ * unitE p ≤ muCore p i := by
  first | exact @_root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed | exact _root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed | (intros; apply _root_.GlobalTheory.CoreDesc.isDefined_of_not_functionField_algClosed <;> assumption)
end
end

