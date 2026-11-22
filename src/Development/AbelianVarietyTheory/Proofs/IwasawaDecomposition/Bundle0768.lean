import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0702
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0718
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0744
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0741
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0740
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0747
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.LevExt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gridCharacter_eq_reference_at_base_tuple {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) (j : ℕ) : L.mu t j = L.mu0 j := by
  have hx := h.xi t
  rw [h.xi_base] at hx
  have e : L.xi t = 1 := MonoidHom.ext (GlobalTheory.ChrEqUnique.eq_one_of_chrEq hx)
  show L.mu0 j * L.xi t = L.mu0 j
  rw [e, mul_one]

theorem Q_eq_empty {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) : L.Q t = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h1 := (h.Q_ram t PP).2 (Or.inl hPP)
  rw [h.xi_base] at h1
  exact h1 fun _ _ => rfl

theorem isRes_unique' {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

section Gen

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

theorem idc_heq (hP : B'.toPre = B.toPre) {c : (AE a.D)ˣ →* Circle} {c' : (AE a'.D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ) (h : ChrEq c χ)
    (h' : ChrEq c' χ') : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  have e : @Eq ((AE a.D)ˣ →* Circle) ((by with_unfolding_all exact (c' :))) c := GlobalTheory.ChrEqUnique.idc_unique a.D _ c χ ((by with_unfolding_all exact (h' :))) h
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

theorem res_heq (hP : B'.toPre = B.toPre) {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) {c : (kP PP)ˣ →* ℂˣ} {c' : (kP PP')ˣ →* ℂˣ}
    (h : IsRes χ PP c⁻¹) (h' : IsRes χ' PP' c'⁻¹) : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  have e : ((by with_unfolding_all exact (c' :)) : (kP PP)ˣ →* ℂˣ)⁻¹ = c⁻¹ := isRes_unique' (D := a.D) ((by with_unfolding_all exact (h' :))) h
  have e' : @Eq ((kP PP)ˣ →* ℂˣ) ((by with_unfolding_all exact (c' :))) c := inv_inj.1 e
  exact (by with_unfolding_all exact ((heq_of_eq e') :))

theorem hermitianCodeCharFrame_referenceCharacter_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) {i : Fin a.D.R.m}
    {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') : HEq ((Top.Fr.at a'.st f').mu0 i') ((Top.Fr.at a.st f).mu0 i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((Fin.ext h : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i') :))
  clear h
  subst e
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).mu0 i)) :))

theorem frat_eta_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) :
    HEq (Top.Fr.at a'.st f').eta (Top.Fr.at a.st f).eta := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl (Top.Fr.at a.st f).eta) :))

theorem mem_vGs (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) (h : PP ∈ (B.primes px).vGs) : PP' ∈ (B'.primes px').vGs := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  exact (by with_unfolding_all exact (h :))

end Gen

end GlobalTheory.Mem.R3.Rw.LevExt

open GlobalTheory.Mem.R3.Rw.LevExt in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hL'
  have hP : B'.toPre = B.toPre := hE.1
  have hC : z.R.toLevCh.C = Top.Fr.at (w.st Z) f := z.lev.C.trans (by rw [w.C_eq])
  have hC' : R'.toLevCh.C = Top.Fr.at (w'.st Z') f' := hL'.C.trans (by rw [w'.C_eq])
  have hmu0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (R'.toLevCh.C.mu0 i') (z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := Z) (a' := Z') hP hf h
  have heta : HEq R'.toLevCh.C.eta z.R.toLevCh.C.eta := by
    rw [hC, hC']
    exact frat_eta_heq (a := Z) (a' := Z') hP hf
  have hs := z.lev.is
  have hs' := hL'.is
  refine ⟨fun i i' h => ⟨?_, fun PP' PP hPP hm => ?_⟩, ?_, Q_eq_empty hs', Q_eq_empty hs⟩
  · rw [gridCharacter_eq_reference_at_base_tuple hs', gridCharacter_eq_reference_at_base_tuple hs]
    exact idc_heq (a := Z) (a' := Z') hP (hmu0 i i' h) (hs.mu0 i) (hs'.mu0 i')
  · have hm0 : PP ∈ (B.primes w.px).vGs := by
      have e := z.lev.Pg
      rw [← e]
      exact hm
    have hm' : PP' ∈ R'.toLevCh.Pg := by
      rw [hL'.Pg]
      exact mem_vGs (a := Z) (a' := Z') hP hpx hPP hm0
    exact res_heq (a := Z) (a' := Z') hP (hmu0 i i' h) hPP (hs.chi i PP hm) (hs'.chi i' PP' hm')
  · exact idc_heq (a := Z) (a' := Z') hP heta hs.eta hs'.eta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormLvlOp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenTranslate

section Act
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem extV_act (hr : R.grp_red_L) (hj : R.models_jV) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (g : G)
    (κ : GA D (Vc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (u : (A.fam.L i t).S.Forms)
    (h : GA D (Vc D i)) :
    R.extV i t (R.jV i t ((A.fam.L i t).r g u)) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t (R.jV i t u) (h * κ) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g u
  have hq : (finHom (Vc D i)).rangeRestrict κ ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    have h1 := hκ.2.1
    exact ⟨h1, trivial⟩
  let q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) q (R.eG g) := hκ.2.2
  have e := hT.2 q hl ((finHom (Vc D i)).rangeRestrict h)
  have hk : (R.cV i).ρ κ⁻¹ = 1 := (hc i).1 _ (inv_mem hκ.1)
  have hρ : (R.cV i).ρ (h * κ)⁻¹ = (R.cV i).ρ h⁻¹ := by
    rw [mul_inv_rev, MonoidHom.map_mul, hk, one_mul]
  have hrr : (finHom (Vc D i)).rangeRestrict (h * κ) = (finHom (Vc D i)).rangeRestrict h * (q : Bridge.Gf (Vc D i)) := map_mul _ _ _
  show (R.cV i).ρ h⁻¹ ((R.HV i t).e (R.jV i t ((A.fam.L i t).r g u)) ((finHom (Vc D i)).rangeRestrict h)) =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e (R.jV i t u) ((finHom (Vc D i)).rangeRestrict (h * κ)))
  have hch : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn (R.βV i) (flagL (R.datVt i t))) (finE_eq (Vc D i) κ)).trans
      (GlobalTheory.LiftEquivariance.ch_eq q).symm)
  refine (congrArg ((R.cV i).ρ h⁻¹) e).trans ?_
  refine (LinearMap.map_smul _ _ _).trans ?_
  exact congrArg₂ (fun (a : ℂ) w => a • w) ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hch.symm))
    (congrArg₂ (fun (f : Module.End ℂ (R.cV i).W) w => f w) hρ.symm (congrArg ((R.HV i t).e (R.jV i t u)) hrr.symm))
end Act

section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem liftForm_lvlOp (hOk : A3.A.fam.Ok 1) (i : Fin D.R.m) (t : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) :
    liftForm A3.A F.P0 F.ψ0 i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x) =
      ∑ g, a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hOk.conj (A3.A.fam.L i t).S ((hOk.lifts i t).hpos _) (A3.A.fam.L i t).r (hOk.lifts i t).act
    _ _ a ha x

theorem read_rat (hB : R.BaseW F) (hOk : A3.A.fam.Ok 1) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (hC : CenRead Y cG) (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i))
    (hκ : ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g))
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (hza : ∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g))
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) (h : GA D (Vc D i)) :
    (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)))).1 h =
      ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
        (Y.IL.jMt (Y.tup t) ht i (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))).1 (h * κ g) := by
  have e1 := congrArg (fun y => (Y.IL.jMt (Y.tup t) ht i y).1 h) (hC i t z a hza x)
  refine e1.trans ?_
  refine (congrFun (Y.mtRead i t ht _) h).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun g _ =>
    congrArg (fun w => ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • w) (congrFun (Y.mtRead i t ht x) (h * κ g)).symm)
  have e2 := liftForm_lvlOp (F := F) hOk i t a ha x
  refine (congrArg (fun v => R.extV i t (R.jV i t v) h) e2).trans ?_
  have e3 := map_sum (R.jV i t) (fun g => a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)) Finset.univ
  have e4 := map_sum (R.extV i t) (fun g => (R.jV i t) (a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))) Finset.univ
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e3).trans e4)).trans ?_
  refine (Finset.sum_apply h _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (R.jV i t) (a.coeff g) ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))
  have e6 := LinearMap.map_smul (R.extV i t) (D.what₂.embLL (a.coeff g)) (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e5).trans e6)).trans ?_
  refine (Pi.smul_apply (D.what₂.embLL (a.coeff g)) (R.extV i t (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))) h).trans ?_
  have e7 := extV_act hB.grp.red_L hB.models.jV hB.models.cV i t g (κ g) (hκ g) (liftForm A3.A F.P0 F.ψ0 i t x) h
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) e7).trans ?_
  refine (smul_smul _ _ _).trans ?_
  exact congrArg (fun c : ℂ => (c * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
    R.extV i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) (h * κ g)) (hza g)

end Read

theorem sum_reindex {G H W : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup W] [Module ℂ W] (e : G ≃* H)
    (c : H → ℂ) (ch : G → ℂ) (w : G → W) :
    ∑ g, (c (e g) * ch g) • w g = ∑ g₀, c g₀ • (ch (e.symm g₀) • w (e.symm g₀)) :=
  Fintype.sum_equiv e.toEquiv _ _ fun g => by simp [smul_smul]

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.BaseW F → A3.A.fam.Ok 1 → CenRead Y cG → ∀ (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i)), (∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)) → ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (y : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)) (h : GA D (Vc D i)), (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z y)).1 h = ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • (Y.IL.jMt (Y.tup t) ht i y).1 (h * κ g) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y cG hB hOk hC i t ht κ hκ z y h
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G (R.eG.trans cG).toEquiv
  let ad : GA D (Vc D i) → D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W := fun h' =>
    { toFun := fun y' => (Y.IL.jMt (Y.tup t) ht i y').1 h'
      map_add' := fun y₁ y₂ => by rw [map_add]; rfl
      map_smul' := fun c y₁ => by rw [map_smul]; rfl }
  let ch : G → ℂ := fun g => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹
  have key : ∀ (g₁ : G0g D.nd) (y' : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)),
      ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩ y') =
        ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g) y' := by
    intro g₁
    have tie : ∀ g, D.what₂.embLL ((GlobalTheory.CenLocAt.avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff g) =
        (GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) := fun g => by
      rw [GlobalTheory.CenLocAt.avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      (ad h).comp (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩)
    let F2 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g)
    have hb := (D.what₂.jMt_basis (Y.tup t) ((i : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt i t).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)) b)
      rw [← hx']
      refine (read_rat hB hOk Y cG hC i t ht κ hκ ⟨_, GlobalTheory.CenLocAt.avgC_mem g₁⟩ _ (GlobalTheory.CenLocAt.avgK_comm _ _) tie x' h).trans ?_
      simp only [F2, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    intro y'
    have := LinearMap.congr_fun hF y'
    simpa only [F1, F2, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] using this
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV i).W :=
    { toFun := fun z' => ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z' y)
      map_add' := fun z₁ z₂ => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c z₁ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hl := GlobalTheory.CenLocAt.lin_center Φ (fun g₀ => ch ((R.eG.trans cG).symm g₀) • ad (h * κ ((R.eG.trans cG).symm g₀)) y)
    (fun g₁ => (key g₁ y).trans (sum_reindex _ _ _ _)) z
  exact hl.trans (sum_reindex (R.eG.trans cG) _ ch (fun g => ad (h * κ g) y)).symm

end GlobalTheory.CenTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalRepresentationInputsImply
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Top.Bl.MultQClose

set_option maxHeartbeats 2000000 in

theorem multQ_prmR : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspTraceClass → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.Published.LabesseWaldspurger → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.GreenCuspidal → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), MultQ (prmR N S Γ) := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hL N S Γ
  refine (GlobalTheory.Fc.EvP.and (GlobalTheory.Fc.EvP.of_ev GlobalTheory.Mem.R3.LedRec.ev_exists_sizeData)
    (GlobalTheory.Fc.EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).mono ?_
  rintro κ K - ⟨hLed, hHost⟩ q
  obtain ⟨Z', g1', hη, hA⟩ := GlobalTheory.Mem.R3.LedRec.exists_bare h14 (B := q.B) (C := q.w.C) q.Z q.f (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨L, -, -, hpar, -⟩ := hLed (q.w.st Z') q.x.isOver hη hA
  obtain ⟨hhost, -⟩ := hHost (q.w.st Z') q.x.isOver
  have s := GlobalTheory.Mem.R3.LedRec.sameGrp q.x.what₂.grp g1'
  refine (GlobalTheory.T.equalMultiplicities_rowTest_of_sameGroupTransfer q.B q.w.C q.Z Z' q.w.px q.w.I q.x.what₂.hX q.T q.x.Wt s q.x.what₂.r.z).1 ?_
  have hEx' := GlobalTheory.Mem.R3.DatCopy.copy_exAt Z' s q.x.what₂.exAt
  have hok := q.x.what₂.r.intersectionNumber_baseChange.ok
  have hok' : (GlobalTheory.Mem.R3.famR Z'.st q.w.I q.x.what₂.hX (GlobalTheory.Mem.R3.usedOf q.w.I q.T q.x.Wt)
      (GlobalTheory.Mem.R3.DatCopy.copy Z' s q.x.what₂.r.z).Xg (GlobalTheory.Mem.R3.DatCopy.copy Z' s q.x.what₂.r.z).tr).fam3.Ok3 1 := hok
  clear hok
  generalize GlobalTheory.Mem.R3.DatCopy.copy Z' s q.x.what₂.r.z = y at hEx' hok' ⊢
  have hch := y.pins.char
  have hT : TypesTrue (q.w.st Z').toD7.ntypes y.R.C.P y.R.C.W := by
    rw [y.lev.C, q.w.C_eq]
    exact g1'
  exact GlobalTheory.T.multiplicity_equality_statement h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 y.R y.F (s := 1) hok' hch hEx' hhost ⟨L, hpar⟩ q.B.ccK_top
    y.pins.keep.guard (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hch.base.lev hT)
end GlobalTheory.Mem.Top.Bl.MultQClose
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormPiecesInEveryCellCone
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan.OrbMark

theorem inRCone_pullAdd_of_isCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)),
  IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀),
  IsCell H.bar φ δ₀ → ∀ t : Fin m₀ → ℝ, (∀ i, 0 ≤ t i) →
  ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
    [Module.Finite (𝓞 E) Y] (π : X₀ →ₗ[𝓞 E] Y), Function.Surjective π → ∀ (τ : 𝓞 E ≃+* 𝓞 E) (f : X →+ Y), τ H.w0 = H.w0 →
    Function.Surjective f → (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
  ∀ u : Fin m₀ → LinearMap.BilinForm ℤ Y,
    (∀ i, 0 < t i → pull π (u i) = δ₀ i ∧ pullAdd f (u i) ∈ balForms H.bar X ∧ ∀ y, 0 ≤ pullAdd f (u i) y y) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (pullAdd f (u i)) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  ∀ i, 0 < t i → InRCone δ (pullAdd f (u i)) := by
  intro E _ _ _ H φ htw X₀ _ _ _ m₀ δ₀ h₀ t ht X Y _ _ _ _ _ _ π hπ τ f hτ hf hsm u hu β hβ m δ hδ c hc hβc i hi
  classical
  let S : Finset (Fin m₀) := Finset.univ.filter fun j => 0 < t j
  let s : Fin S.card ↪ Fin m₀ := (S.orderEmbOfFin rfl).toEmbedding
  have hrange : Set.range s = (S : Set (Fin m₀)) := Finset.range_orderEmbOfFin S rfl
  have hs : ∀ j, 0 < t (s j) := fun j => by
    have : s j ∈ (S : Set (Fin m₀)) := hrange ▸ Set.mem_range_self j
    simpa [S] using this
  have hmem : ∀ j, 0 < t j → j ∈ Set.range s := fun j hj => by
    rw [hrange]; simpa [S] using hj
  have h1 : φ.LinearOn (fun j => δ₀ (s j)) := linearOn_comp h₀.linear s
  have e1 : (fun j => δ₀ (s j)) = fun j => pull π (u (s j)) := funext fun j => ((hu _ (hs j)).1).symm
  rw [e1] at h1
  have h2 : φ.LinearOn (fun j => u (s j)) := (linearOn_pull_iff hπ).1 h1
  have h3 : φ.LinearOn (fun j => pullAdd f (u (s j))) := by
    intro a ha
    have hz : ∀ j, φ.evalZ (pullAdd f (u (s j))) = φ.evalZ (u (s j)) := fun j =>
      eval_pull_semilinear_of_isTwInv E H φ htw τ hτ f hf hsm fun x y => ((u (s j) x y : ℤ) : ℝ)
    have := h2 a ha
    simp only [hz]
    rw [← this]
    exact eval_pull_semilinear_of_isTwInv E H φ htw τ hτ f hf hsm fun x y => ∑ j, a j * ((u (s j) x y : ℤ) : ℝ)
  have hsum : toReal β = ∑ j, t (s j) • toReal (pullAdd f (u (s j))) := by
    rw [hβ]
    refine (Fintype.sum_of_injective s s.injective _ _ (fun j hj => ?_) (fun j => rfl)).symm
    have : t j = 0 := le_antisymm (not_lt.1 fun h => hj (hmem j h)) (ht j)
    rw [this, zero_smul]
  obtain ⟨j, rfl⟩ := hmem i hi
  exact GlobalTheory.T.inRealCone_cell_of_linearPiece_through_cellPoint H.bar φ δ (fun j => pullAdd f (u (s j))) hδ (fun j => (hu _ (hs j)).2.1) (fun j => (hu _ (hs j)).2.2) h3
    β c (fun j => t (s j)) hc hs hβc hsum j

end GlobalTheory.PolFan.OrbMark
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedOrbitFormPrimitive
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

theorem eq_one_of_smul_eq_of_orbFun_evalZ_eq_one :
    ∀ {O : Type} [CommRing O] (bar : O → O) (w0 : O) {X₀ : Type} [AddCommGroup X₀] [Module O X₀]
      (v : LinearMap.BilinForm ℤ X₀) (hv : v ∈ balForms bar X₀), IsPrim bar (⟨v, hv⟩ : balForms bar X₀) →
      ∀ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (β : LinearMap.BilinForm ℤ X),
        (OrbMark.orbFun O w0 v).evalZ β = 1 →
        ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1 := by
  intro O _ bar w0 X₀ _ _ v hv hp X _ _ _ β hβ k β' hk
  obtain ⟨τ, f, -, hf, -, H⟩ := GlobalTheory.T.exists_semilinear_pullback_of_markedOrbitIndicator w0 v β hβ
  have hval : ∀ (x₀ y₀ : X₀), ∃ x y, v x₀ y₀ = β x y := by
    intro x₀ y₀
    obtain ⟨x, hx⟩ := hf (Submodule.Quotient.mk x₀)
    obtain ⟨y, hy⟩ := hf (Submodule.Quotient.mk y₀)
    exact ⟨x, y, (H x y x₀ y₀ hx.symm hy.symm).symm⟩
  have hβ' : ∀ x y, (k : ℤ) * β' x y = β x y := fun x y => by rw [← hk]; simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exfalso
    have hv0 : v = 0 := LinearMap.ext₂ fun x₀ y₀ => by
      obtain ⟨x, y, e⟩ := hval x₀ y₀
      rw [e, ← hβ']
      simp
    exact zero_ne_one (hp 0 0 (Subtype.ext (by simp [hv0])))
  · have hkz : (k : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
    have hcan : ∀ {a b : ℤ}, (k : ℤ) * a = k * b → a = b := fun h => mul_left_cancel₀ hkz h
    have hl : ∀ x, f x = 0 → ∀ y, β' x y = 0 := by
      intro x hx y
      obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (f y)
      have e := H x y 0 y₀ (by rw [hx]; rfl) hy₀
      apply hcan
      rw [hβ', e]
      simp
    have hr : ∀ x, f x = 0 → ∀ y, β' y x = 0 := by
      intro x hx y
      obtain ⟨y₀, hy₀⟩ := Submodule.Quotient.mk_surjective _ (f y)
      have e := H y x y₀ 0 hy₀ (by rw [hx]; rfl)
      apply hcan
      rw [hβ', e]
      simp
    obtain ⟨ζ₁, hζ₁⟩ := GlobalTheory.T.exists_intBilinForm_descend_along_surjective f hf β' hl hr
    let m : X₀ →ₗ[ℤ] X₀ ⧸ (CarDim.orad v : Submodule O X₀) :=
      (CarDim.orad v : Submodule O X₀).mkQ.toAddMonoidHom.toIntLinearMap
    let ζ : LinearMap.BilinForm ℤ X₀ := ζ₁.compl₁₂ m m
    have hζ : ∀ x₀ y₀, (k : ℤ) * ζ x₀ y₀ = v x₀ y₀ := by
      intro x₀ y₀
      obtain ⟨x, hx⟩ := hf (Submodule.Quotient.mk x₀)
      obtain ⟨y, hy⟩ := hf (Submodule.Quotient.mk y₀)
      have e1 : ζ x₀ y₀ = β' x y := by
        show ζ₁ (Submodule.Quotient.mk x₀) (Submodule.Quotient.mk y₀) = _
        rw [← hx, ← hy, hζ₁]
      rw [e1, hβ', H x y x₀ y₀ hx.symm hy.symm]
    have hmem : ζ ∈ balForms bar X₀ := by
      refine ⟨fun y z => hcan ?_, fun a y z => hcan ?_⟩
      · rw [hζ, hζ, hv.1]
      · rw [hζ, hζ, hv.2]
    refine hp k ⟨ζ, hmem⟩ (Subtype.ext (LinearMap.ext₂ fun x₀ y₀ => ?_))
    change v x₀ y₀ = ((k • ζ : LinearMap.BilinForm ℤ X₀)) x₀ y₀
    rw [LinearMap.smul_apply, LinearMap.smul_apply, nsmul_eq_mul, hζ]

end OrbMark

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfChernClassesOfRootsEqZeroStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_of_chernClassesOfRoots_eq_zero : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (ι × ℕ) ℝ), chernRoots m Q = 0 → Q ∈ Ideal.span ((Set.range fun τ : ι => (X (τ, 0) - 1 : MvPolynomial (ι × ℕ) ℝ)) ∪ {P | ∃ (τ : ι) (k : ℕ), m τ < k ∧ P = X (τ, k)}) := by
  first | exact @GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero | exact GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero | (intros; apply GlobalTheory.GrassKernel.mem_span_of_chernRoots_eq_zero <;> assumption)
end

