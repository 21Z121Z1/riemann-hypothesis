import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ResidueCharacters.RowDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionSecondAltAlt
section
set_option synthInstance.maxHeartbeats 200000

section
namespace GroupAverageFixedPoints
section
noncomputable section
open scoped TensorProduct
open Module
namespace GlobalTheory.CompanionTheory.LatSpan
section Rep
variable {F M Γ : Type} [Field F] [AddCommGroup M] [Module F M] [Group Γ] [Fintype Γ]
variable (a : Γ →* Module.End F M) (P : Subgroup Γ) [Fintype P] (t : P →* Fˣ) (E : Module.End F M)
end Rep
section Ext
variable {O K K'' Fm : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end Ext
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
section Main
variable {LL O K K'' Fm WL Γ : Type} [Field LL] [CharZero LL] [AddCommGroup WL] [Module LL WL]
  [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm] [Group Γ] [Fintype Γ]
end Main
section Lat
variable {LL Oe K'' V T : Type} [Field LL] [NumberField LL] [AddCommGroup V] [Module LL V] [Module (𝓞 LL) V]
  [IsScalarTower (𝓞 LL) LL V] [CommRing Oe] [IsDomain Oe] [Field K''] [Algebra Oe K''] [IsFractionRing Oe K'']
  [AddCommGroup T] [Module K'' T] [Module Oe T] [IsScalarTower Oe K'' T]
end Lat
end GlobalTheory.CompanionTheory.LatSpan
end
end
end
section
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
section Form
variable {Ks LL WL : Type} [Field Ks] [Field LL] [Algebra Ks LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {WK : Submodule Ks WL}
  {O K K'' : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end Form
section Iso
open Formalism.IndefR.NX Formalism.IndefR.Arith
variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
end Iso
end GlobalTheory.CompanionTheory.LatSpan
end
end
section
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX
section PiLocalization₂
variable {D : D7} (c : NChoice D) (w : D.what₂.places.Pl)
attribute [local instance] algKK
variable {c w}
end PiLocalization₂
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
section Alg
variable {k A G : Type} [Field k] [Ring A] [Algebra k A] [Group G]
end Alg
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith
section Stage2
variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}
attribute [local instance] algKK
end Stage2
end GlobalTheory.CompanionTheory.LatSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.LatSpan
attribute [local instance] algKK
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem lattice_of_lifts_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hPin hRec jD eM hN hjD hSum w j hne h1 h2
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have hgrp := P.tied.div.grp
  have hIe : P.I.eG = B.Q.Rl.eG.trans B.Q.cG := hPin.eGtie
  have hC : ∀ h, (Formalism.L2.DIV.idemOf P.A3.A.X).coeff h = ((D.nexp.eLL0 (P.I.eG h) : D.LL0) : D.what₂.LL) := fun h =>
    D.what₂.embLL.injective ((hgrp.e0 h).trans (D.nStage_trivialCharacter_coeff_eq _).symm)
  obtain ⟨e, he1, he2⟩ := stage2 (w := w) hN P.I.eG B.Q.Sx ((i : ℕ) + 1) (B.Q.Rl.FW i) (B.Q.nexp.fi i) (B.fw.ks i)
    (fun s => by rw [hIe]; exact B.Q.nexp.geq i s) (B.Q.nexp.rho _ h1 h2) (B.Q.nexp.chi _ h1 h2)
    (B.Q.nexp.eF _ _ _ h1 h2) (B.Q.nexp.act _ _ _ h1 h2) (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) hC P.P0 P.ψ0⁻¹
    hgrp.lvl0 (fun u hu => by
      obtain ⟨x, hx1, hx2⟩ := hgrp.psi0 u hu (ex.nch.twI w) (ex.nch.sd w)
      exact ⟨x, hx1, hx2⟩)
  have hd := _root_.Formalism.IndefR.finrank_WL_eq_dW B.Q i
  have hForm := isKsForm_of_iso (B.Q.nexp.fi i) (B.fw.ks i)
  have heM : ∀ x, eM w ((i : ℕ) + 1) x = e (jD ((i : ℕ) + 1) x) := by
    intro x
    obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hForm
    have hx : jD ((i : ℕ) + 1) x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    let f : Fin n → FmK B.Q.Sx ((i : ℕ) + 1) := fun k => ⟨b k, hbK k⟩
    have h5 := hSum w ((i : ℕ) + 1) h1 h2 x n a f ha.symm
    rw [h5, ← ha]
    exact (he1 n a f).symm
  have hWg : (B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) =
      B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i := rfl
  have hrange : Set.range (eM w ((i : ℕ) + 1)) =
      (fun y => e ((B.Q.nexp.fi i).e.symm y)) ''
        ((B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) : Set _) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x), ?_, ?_⟩
      · rw [hjD i x _ (heq_cast hd ((P.JM.eW i).symm x))]
        rw [SetLike.mem_coe, hWg]
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Module.finBasis D.what₂.LL _ k).2
      · simp only [LinearEquiv.symm_apply_apply, heM]
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, hWg] at hy
      let Bs := Module.finBasis D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)
      let z : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL := Bs.equivFun ⟨y, hy⟩
      let x := P.JM.eW i (z ∘ Fin.cast hd.symm)
      have hH : HEq ((P.JM.eW i).symm x) z := by
        simp only [x, LinearEquiv.symm_apply_apply]
        exact (heq_cast hd.symm z).symm
      have h6 := hjD i x z hH
      have h7 : Formalism.IndefR.NX.jDL B.Q.Rl B.Q.F.lv2 i z = y := by
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        have h8 := Bs.sum_equivFun ⟨y, hy⟩
        have h9 : ((∑ k, Bs.equivFun ⟨y, hy⟩ k • Bs k : B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i) : Fin (B.Q.Rl.nW i) → D.what₂.LL) = y :=
          congrArg Subtype.val h8
        rw [AddSubmonoidClass.coe_finset_sum] at h9
        exact h9
      refine ⟨x, ?_⟩
      rw [heM]
      change e _ = e ((B.Q.nexp.fi i).e.symm y)
      rw [← h7, ← h6, LinearEquiv.symm_apply_apply]
  refine isLatIn_span (ex.nch.embW w) (integers_embed _) (eM w ((i : ℕ) + 1)) (Y.MjH ((i : ℕ) + 1)).L
    (Y.MjH_good _).2.1 (Y.MjH_good _).2.2 _ ?_
  rw [hrange]
  exact he2
end GlobalTheory.CompanionTheory.LatSpan
end
end
end
end
end GroupAverageFixedPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.lattice_family_adoption_second_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  first | exact @_root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt | exact _root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt | (intros; apply _root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowDef
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
def RowCAlt (A B : ℝ) : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      RowAt (Fm.L x i) X.ρ A B
def StarSelfDualCondition : Prop := ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
    (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
    (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
    _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ →
      StarS (Fm.L x i) X.ρ C
end UpperTheory.N
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PassIn3AtRealTStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefScale_theta_degree : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Del h0 : ℕ) (c : ℝ) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf (fun Zs => let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs; { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }) S Ks), IsTotallyComplex D.what₂.LL → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → P.A3.fam3.Ok3 1 → PrimRows3 Q.Rl Q.F → ∀ C CH : ℝ, PassIn3 Q.Rl Q.F C CH := by
  first | exact @_root_.GlobalTheory.passIn3_at_realT_alt | exact _root_.GlobalTheory.passIn3_at_realT_alt | (intros; apply _root_.GlobalTheory.passIn3_at_realT_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRows
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.PtSt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
theorem reducedMultiplicity_of_rows' :
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → _root_.GlobalTheory.NRows.PointConditions' D → SumRepresentations.ReducedMultiplicityStatement D := by
  intro hL D I R i _
  have hInt : Rows.IsotInternal D.what₂ := I.isot
  have h42 : SumRepresentations.Conclusion42 D := (I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) R.a R.b).2.2
  have h1 := map_MjSig_eq D i hInt (h42 i) (R.c.parUp i) (R.c.downMem i) (R.typeNZ i)
  exact ⟨h1, (SumRepresentations.good_part_image_iff D.nd D.naut i hInt (h42 i) h1).2 (R.c.goodPart i)⟩
end GlobalTheory.PtSt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
namespace GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC}
variable {ex : Extra D L hT Gi Gl K Yd cX}
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure RealInAlt (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) : Type 1 where
  psiPin : x.R.ψ = Rc.T.theta.W.ψ
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  spPin : HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) S.Y.hK S.G
    x.wd (fun m => _root_.Formalism.IndefR.pwOf_alt S hin (x.wd m)) x.bR)
  Sx : Formalism.IndefR.NX.RatDat D.ntw
  nexp : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx
  stdV : ∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)
  stdX : (∀ a b, D.sp.X'.hT (D.sp.X'.frame a) (D.sp.X'.frame b) = if a = b then 1 else 0) ∧
    D.sp.X'.L0 = Submodule.span (𝓞 D.host.E) (Set.range D.sp.X'.frame)
  tS : Formalism.L2.Theta.GA D (Yc D 0)
  cS : ℝ
  κS : ℝ
  ιS : Formalism.L2.Theta.GA D (Yc D 0) ≃* S.X.B.I.GA
  instEq : S.X.B.I = Formalism.IndefR.RationalEmbedding.inst D
  ιS_eq : HEq ιS (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  sEEc : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL x.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X)
  sEEj : HEq x.sEE sEEc
  seeLev : (∃ t' : Formalism.L2.Theta.GA D (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel tS⁻¹ (levS _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (Formalism.IndefR.Lev.levChi _ (x.R.βY 0) (x.R.dat0 (x.R.toRealDat.levR x.F.lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))
  seeEval : (∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS c') →
    Formalism.IndefR.AutomorphicEvaluation.EvalTieT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS
  uS : ℂ
  uS_norm : ‖uS‖ = 1
  seeDef : ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
    sEEc v = Tw.mk (twAt D.what₂.embLL x.A3.A.v0) ((uS * (κS : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩)
  seeK : 0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H) (hx : x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true))),
      ‖(κ' : ℂ) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (x.R.MY 0) x.R.ν0 x.R.fd0 (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) S.X S.G ιS tS cS) ⟨x.R.HE.e (Tw.out v), hx⟩‖ = ‖v‖) →
    ∀ (v : Tw (twAt D.what₂.embLL x.A3.A.v0) x.R.HE.H), x.R.HE.e (Tw.out v) ∈ (x.R.toRealDat.EEat (x.R.toRealDat.levR x.F.lv2 true)) →
      RealDat.nP x.F.lv2 true * ‖sEEc v‖ ^ 2 = ‖v‖ ^ 2)
  host : HostHyp D
  vpos : ∀ i, (Vc D i).IsPosDef
variable {x : TwIn ex} {Rc : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
set_option maxHeartbeats 4000000 in
def realisationOfInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.Formalism.IndefR.IndefiniteRealisation Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S x.core.Q.c.F where
  Rl := x.R
  sEE := x.sEE
  charW := (x.pins.char)
  zs := rfl
  s0 := (HEq.refl (s0Of x.R x.F))
  s1 := (HEq.refl (s1Of x.R x.F))
  dc := rfl
  sp := HEq.rfl
  col := (HEq.refl (colOf x.R x.F x.sEE))
  allPlaces := x.pins.char.allPl
  trSem := (x.pins.trSem)
  stdChar := x.pins.keep.std
  psiPin := y.psiPin
  signs := (x.pins.keep.signs)
  wdD := x.wd
  wdD_wU := x.wd_wU
  wU_wdD := x.wU_wd
  hin := y.hin
  bR := x.bR
  spPin := (y.spPin)
  frames := fun h => (Formalism.IndefR.Seed.Frm.framesOKg2_iff x.R).2 (x.pins.keep.frames h)
  cG := x.cG
  Sx := y.Sx
  nexp := y.nexp
  stdV := y.stdV
  stdX := y.stdX
  tS := y.tS
  cS := y.cS
  κS := y.κS
  ιS := y.ιS
  instEq := y.instEq
  ιS_eq := y.ιS_eq
  sEEc := y.sEEc
  sEEj := y.sEEj
  seeLev := (y.seeLev)
  seeEval := (y.seeEval)
  uS := y.uS
  uS_norm := y.uS_norm
  seeDef := (y.seeDef)
  seeK := (y.seeK)
  host := y.host
  err_eq := (x.err)
  vpos := y.vpos
set_option maxHeartbeats 4000000 in
def boundedRealisationOfInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : _root_.Formalism.IndefR.RealTBAlt Rc (divisionPairOfAdelicFormsFaceColumnsData x) x.F.Dc x.F.Sp x.F.Zsc S where
  T := x.core
  Q := _root_.GlobalTheory.Mem.R3.realisationOfInput y
  κ := x.geo.κ
  v₀ := (x.geo.v₀)
  fw := (x.geo.fw)
  bar := (x.geo.bar)
  O := (x.geo.O)
  pins := (x.geo.pins)
  rhoGeo := (x.geo.rhoGeo)
  equivAll := (x.geo.equivAll)
  cTie := (x.geo.cTie)
  phase := by
    have h : ∀ i, x.R.toRealDat.LUnif →
        Formalism.IndefR.FWT.PhaseTie x.core x.R.toRealDat x.geo.κ x.geo.v₀ x.geo.O (phEff x.R) i := by
      rw [phEff_one x]
      exact x.geo.phase
    exact (h)
set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 4000000 in
structure RecursiveInput (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S) : Type 1 where
  E : EigIdx D Yd
  labPi : E.Pi → x.A3.A.fam.base.Ix
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  Tp : Formalism.L2.Host.TupTied D x.R.C ex.nch
  tpEq : HEq Tp Rc.T.n.tp
  tupXi : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → x.R.toLevCh.xiH (x.Y.tupT μ) = Tp.xi μ
  mtRead : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (fun i => (x.A3.indefDown (s0Of x.R x.F)).dW i) (fun i v => x.Z.jW i v) ((indefiniteDownJoin (realisationOfInput y)))
set_option maxHeartbeats 4000000 in
def realisationRecursionOfInput {y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc S} (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y) : _root_.Formalism.IndefR.IndefiniteRealisationRecursion (_root_.GlobalTheory.Mem.R3.realisationOfInput y) where
  tupT := x.Y.tupT
  hm := x.Y.hm
  hTop := x.Y.hTop
  hinj := x.Y.hinj
  Ish := (x.Y.Ish)
  I0 := (x.Y.Iz)
  IL := (x.Y.IL)
  Kc := x.Y.Kc
  E := r.E
  labPi := r.labPi
  PY := x.Y.PY
  PW := x.Y.PW
  eFT := (x.Y.eFT)
  piOf := r.piOf
  ιW := x.Y.ιW
  Tp := (r.Tp)
  recR := by
    have h : Formalism.IndefR.RecTie.RecReal x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj ex.p0 x.Y.Ish x.Y.Iz x.Y.IL x.Y.Kc r.E
        r.labPi x.Y.PY x.Y.PW x.Y.eFT r.piOf x.Y.ιW ex.nch r.Tp :=
      ⟨x.pins.char.base, x.Y.tied, x.Y.prtE, x.Y.prtE0, x.Y.prtWE, x.Y.xi, r.tupXi,
        fun w => by rw [x.Y.muAt w, x.Y.tupT_tup], x.Y.isomFin, x.Y.frameMatch⟩
    exact (h)
  tpEq := (r.tpEq)
  tupTie := x.Y.tupTie
  tupT_tup := x.Y.tupT_tup
  muEq := (Eq.refl x.R.mu)
  mtRead := (r.mtRead)
  mjRead := (r.mjRead)
end GlobalTheory.Mem.R3
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTestSetting
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PrimIn
theorem rowTest_setting_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q → (∀ w, (B.Q.Rl.toCx3 B.Q.F).W1 B.Q.F.cr (B.Q.Rl.num B.Q.F 0 0) w → w ∈ B.Q.Rl.twPl) → B.Q.Rl.toRealDat.ExAt → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L → GlobalTheory.GLq.ESerTie D → Finite P.T → GlobalTheory.RowClaim.HidaSetting L B.Q.Rl.toRealDat B.Q.F.lv2 := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hp _hW hEx hsz hser hfin
  have hC := B.Q.charW
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak B.Q.Rl B.Q.F hC hEx).1
  exact
    { size := hsz
      eser := hser
      host := B.Q.host
      hF := hp.hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := hp.qGuard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := B.Q.stdChar
      stdX := B.Q.stdX
      betaX := hp.betaStd.2 }
end GlobalTheory.PrimIn
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeIsoOfSeeEx
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Div.SeeIsoClose
theorem seeIso_of_seeEx_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationExtends Q → (Q.Rl.toCx3 Q.F).SEEIso Q.sEE := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S Ks _ _ _ Q hSee
  exact GlobalTheory.Twist.SeeIsoRow.seeIso_row Q.Rl Q.F S.X S.G S.Y.hK P.Zs P.Dc Q.wdD
    (fun x => _root_.Formalism.IndefR.pwOf_alt S Q.hin (Q.wdD x)) Q.bR Q.sEE Q.sEEc Q.ιS Q.tS Q.cS Q.κS Q.uS
    Q.charW.base.models Q.zs Q.dc (Q.sp.trans Q.spPin) Q.sEEj (Q.seeEval hSee.2) Q.uS_norm Q.seeDef Q.seeK
end GlobalTheory.Div.SeeIsoClose
end
end

