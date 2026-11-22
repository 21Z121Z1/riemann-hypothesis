import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts

-- bundled from Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
section
noncomputable section

namespace Formalism.MainNotions.IntegralModelsLocalData

open Formalism.BasicNotions Formalism.MainNotions.ModuliIntegralCharts

structure Comparison₂ (D : D7) (P : ModuliIntegralCharts.Prov D) (w : P.Dat) (Sh : DV.ShimX D.what₂.Tau) where
  rk_eq : P.rk w = Sh.N
  jj_eq : P.jj w = Sh.j

  fcOf : ∀ p : ℕ, p.Prime → (P.loc w p).Gen (P.loc w p).Xm → Sh.FibComp p
  fcOf_surj : ∀ (p : ℕ) (hp : p.Prime), Function.Surjective (fcOf p hp)
  fibInBd_iff : ∀ (p : ℕ) (hp : p.Prime) η, (Sh.fibInBd p (fcOf p hp η) ↔ ¬ (P.loc w p).abAt η)

  curveHT : ∀ (p : ℕ) n Z', p.Prime → 3 ≤ n →
    (P.loc w p).IsHTBlowup Z' ((P.loc w p).Xn n) → ∀ c : Sh.CurveHT p,
      ∃ (C : (P.ex w p).CrvS Z') (m : ℕ), 0 < m ∧ ∀ τ (i : Fin Sh.N),
        (m : ℝ) * Sh.degHT p c (τ, i) = (P.ex w p).degGr C (D.eTau τ) (i + 1)

  curveDR : ∀ p : ℕ, p.Prime → p ≠ 2 → DV.UnramE D p → p ∉ Sh.lev → ∀ c : Sh.CurveDR p,
      ∃ (CC : (P.loc w p).Crv) (m : ℕ), 0 < m ∧ ∀ τ (i : Fin Sh.N),
        (m : ℝ) * Sh.degDR p c (τ, i) = (P.ex w p).degGrD CC (D.eTau τ) (i + 1)

structure Prov (D : D7) (XD : DivX D) where

  P : ModuliIntegralCharts.Prov D

  dat_surj : letI := D.host.cmStar; ∀ S κ, DV.HidaSetting D XD S κ → ∃ w, Nonempty (Comparison₂ D P w (XD.shv S κ))

def FibOK (D : D7) (XD : DivX D) : Prop :=
  letI := D.host.cmStar
  ∀ S κ, DV.HidaSetting D XD S κ → ∀ p : ℕ, p.Prime →
    Finite ((XD.shv S κ).FibComp p) ∧ Nonempty ((XD.shv S κ).FibComp p)

def DegDRRat (D : D7) (XD : DivX D) : Prop :=
  letI := D.host.cmStar
  ∀ S κ, DV.HidaSetting D XD S κ → ∀ p : ℕ, p.Prime → p ≠ 2 → DV.UnramE D p → p ∉ (XD.shv S κ).lev →
    ∀ c : (XD.shv S κ).CurveDR p, ∃ m : ℕ, 0 < m ∧ ∀ τ (i : Fin (XD.shv S κ).N),
      ∃ z : ℤ, (m : ℝ) * (XD.shv S κ).degDR p c (τ, i) = z

variable (D : D7) (XD : DivX D) (X : Prov D XD)

def adm1 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aHT

def adm2 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aKrull

def adm3 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aNorm

def ArchimedeanSignatureMatching : Prop := ∀ w p, p.Prime → (X.P.ex w p).aTube

def adm5 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aOrd1

def adm6 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aOrd2

def adm7 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aOrd3

def adm8 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aSub

def adm9 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aClose

def adm10 : Prop := ∀ w p, p.Prime → (X.P.ex w p).ChartLiftsThroughSteps

def adm11 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aCl

def adm12 : Prop := ∀ w p, p.Prime → (X.P.ex w p).aHTI

def admitted : Prop :=
  adm1 D XD X ∧ adm2 D XD X ∧ adm3 D XD X ∧ ArchimedeanSignatureMatching D XD X ∧ adm5 D XD X ∧ adm6 D XD X ∧
    adm7 D XD X ∧ adm8 D XD X ∧ adm9 D XD X ∧ adm10 D XD X ∧ adm11 D XD X ∧ adm12 D XD X

def Conclusion0 : Prop := ∀ w p, p.Prime → (X.P.ex w p).p0

def JetConsequence : Prop := ∀ w p, p.Prime → (X.P.ex w p).pC

def AbelianAtGenericPoints : Prop := ∀ w p, p.Prime → (X.P.ex w p).pNV

def IsotypicRankTransfer : Prop := ∀ w p, p.Prime → (X.P.ex w p).pTR

def OrdinarySectionsCond : Prop := ∀ w p, p.Prime → (X.P.ex w p).pORD

def FourierJacobiExpansion' : Prop := ∀ w p, p.Prime → (X.P.ex w p).pFJ

def HodgeTateMapKernel : Prop := ∀ w p, p.Prime → (X.P.ex w p).pHTa

def HodgeTateModel : Prop := ∀ w p, p.Prime → (X.P.ex w p).pHTb

def NefBoundaryHodgeTateCond : Prop := ∀ w p, p.Prime → (X.P.ex w p).pHTc

def GroupConditions : Prop := ∀ w p, p.Prime → (X.P.ex w p).pGG

def DeRhamUnramifiedModel : Prop := ∀ w (p : ℕ), p.Prime → p ≠ 2 → DV.UnramE D p → (X.P.ex w p).pDR

def GlobalIntegralModelCondition : Prop :=
  ∀ w, X.P.LevelForIntegralModel w → ∃ (Z : X.P.Xg w) (m₀ : ℕ) (BD : X.P.DivX Z),
    (∀ p : ℕ, p.Prime → ∃ d : (X.P.ex w p).IvD none,
      X.P.bc p Z = (X.P.ex w p).blowUp (X.P.loc w p).Xm ((X.P.ex w p).jIdl none d)) ∧
    X.P.effD BD ∧ X.P.noVertD BD ∧ X.P.posBdD BD ∧ X.P.ampleOnAbelianBase Z m₀ BD

def aux₃ : Prop :=
  Conclusion0 D XD X ∧ JetConsequence D XD X ∧ AbelianAtGenericPoints D XD X ∧ IsotypicRankTransfer D XD X ∧ OrdinarySectionsCond D XD X ∧ FourierJacobiExpansion' D XD X ∧
    HodgeTateMapKernel D XD X ∧ HodgeTateModel D XD X ∧ NefBoundaryHodgeTateCond D XD X ∧ GroupConditions D XD X ∧ DeRhamUnramifiedModel D XD X ∧ GlobalIntegralModelCondition D XD X

def Stmt : Prop := admitted D XD X → aux₃ D XD X

abbrev ObjClass : Type 1 := ∀ {D : D7} {XD : DivX D}, Prov D XD → Prop

def UniformExportStatement (𝒪 : ObjClass) : Prop := ∀ (D : D7) (XD : DivX D) (X : Prov D XD), 𝒪 X → Stmt D XD X

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

abbrev ProvF : Type 1 := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, Prov (Fm.D x i) (Fm.X x i)

variable (XF : ProvF Fm)

def AdmFx : Prop := ∀ x hx (i : Fm.Ix x), admitted (Fm.D x i) (Fm.X x i) (XF x hx i)

def familyPoincareExtensionAndPointBounds : Prop := ∀ x hx (i : Fm.Ix x), aux₃ (Fm.D x i) (Fm.X x i) (XF x hx i)

def FamilyPacketImplication : Prop := AdmFx Fm XF → familyPoincareExtensionAndPointBounds Fm XF

def InClass (𝒪 : ObjClass) : Prop := ∀ x hx (i : Fm.Ix x), 𝒪 (XF x hx i)

theorem familyPacket_of_uniformPacket {𝒪 : ObjClass} (h : UniformExportStatement 𝒪) (hO : InClass Fm XF 𝒪) : FamilyPacketImplication Fm XF :=
  fun a x hx i => h _ _ _ (hO x hx i) (a x hx i)

end Family

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) (𝒪 : ObjClass) : Prop :=
  Formalism.MainNotions.Closed 𝒞 (fun Fm _ => ∀ XF : ProvF Fm, InClass Fm XF 𝒪 → FamilyPacketImplication Fm XF)

theorem closed_absolute_share_of_uniform_export {𝒪 : ObjClass} (h : UniformExportStatement 𝒪) (𝒞 : Formalism.MainNotions.FamClass) : ClosedAbsoluteShare 𝒞 𝒪 :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ XF hO => familyPacket_of_uniformPacket Fm XF h hO⟩⟩

section Total

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ∀ x (i : Fm.Ix x), Prov (Fm.D x i) (Fm.X x i))

def AdmF : Prop := ∀ x (i : Fm.Ix x), admitted (Fm.D x i) (Fm.X x i) (XF x i)

def OrbitValuationBound : Prop := ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) (Fm.X x i) (XF x i)

def KudlaFamilyStatement : Prop := AdmF Fm XF → OrbitValuationBound Fm XF

theorem AdmFx_of_AdmF (h : AdmF Fm XF) : AdmFx Fm (fun x _ i => XF x i) := fun x _ i => h x i

theorem familyConclusion_of_pointwise (h : OrbitValuationBound Fm XF) : familyPoincareExtensionAndPointBounds Fm (fun x _ i => XF x i) := fun x _ i => h x i

end Total

end Formalism.MainNotions.IntegralModelsLocalData

end
end

-- bundled from Formalism.SharpRestriction.Divisibility.PrinLevClass
section
noncomputable section

namespace Formalism.MainNotions.DIV.Align

open Formalism.BasicNotions Formalism.MainNotions

def tauMul (D : D7) (g : D.R.Psi) : Equiv.Perm D.what₂.Tau :=
  D.eTau.trans ((Equiv.mulRight g).trans D.eTau.symm)

def rtMul (D : D7) (N : ℕ) (g : D.R.Psi) : DV.Rt D.what₂.Tau N → DV.Rt D.what₂.Tau N :=
  fun x => (tauMul D g x.1, x.2)

structure PrinLev {D : D7} (V : DivX D) where

  κg : V.Lev

  κs : V.Lev
  κg_pr : V.levPr κg = {D.host.g 0, D.host.g 1}
  κs_pr : V.levPr κs = {D.host.g 0, D.host.g 1, 3, 5}

def LevB {D : D7} {V : DivX D} (P : PrinLev V) (κ : V.Lev) : Prop := κ = P.κg ∨ κ = P.κs

abbrev PrinLevF {eps : ℝ} (Fm : FamP eps) : Type :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), PrinLev (Fm.X x i)

abbrev PrinLevClass : Type 1 := ∀ {eps : ℝ} (Fm : FamP eps), PrinLevF Fm → Prop

def FanAt (D : D7) (V : DivX D) (P : PrinLev V) : Prop :=
  letI := D.host.cmStar
  ∀ (S : HSpace D.host.E) (κ : V.Lev), DV.HidaSetting D V S κ → LevB P κ → ∀ g : D.R.Psi,
    ∃ (a : Equiv.Perm (V.shv S κ).XC) (b : Equiv.Perm (V.shv S κ).Comp),
      ∀ z,
        (V.shv S κ).compOf (a z) = b ((V.shv S κ).compOf z) ∧
        (V.shv S κ).rfn (a z) = (V.shv S κ).rfn z ∧
        (V.shv S κ).hLo (a z) = (V.shv S κ).hLo z ∧
        (V.shv S κ).hUp (a z) = (V.shv S κ).hUp z ∧
        (V.shv S κ).connN (a z) = (V.shv S κ).connN z ∧
        (V.shv S κ).curvN (a z) = (V.shv S κ).curvN z

def FanArAt (D : D7) (V : DivX D) (P : PrinLev V) : Prop :=
  letI := D.host.cmStar
  ∀ (S : HSpace D.host.E) (κ : V.Lev), DV.HidaSetting D V S κ → LevB P κ → ∀ g : D.R.Psi,
    ∀ T : Finset ℕ, Nat.primeFactors (2 * (NumberField.discr D.host.E).natAbs) ∪ (V.shv S κ).lev ⊆ T →
      ∀ (R : ℝ) (Q : MvPolynomial (DV.Rt D.what₂.Tau (V.shv S κ).N) ℝ),
        (V.shv S κ).arDeg T R (MvPolynomial.rename (rtMul D (V.shv S κ).N g) Q) = (V.shv S κ).arDeg T R Q

def FanGal {eps : ℝ} (Fm : FamP eps) (PL : PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FanAt (Fm.D x i) (Fm.X x i) (PL x hx i)

def FanArGal {eps : ℝ} (Fm : FamP eps) (PL : PrinLevF Fm) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FanArAt (Fm.D x i) (Fm.X x i) (PL x hx i)

theorem fanAt_id (D : D7) (V : DivX D) (P : PrinLev V) : FanAt D V P :=
  fun _ _ _ _ _ => ⟨1, 1, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem fanGal_id {eps : ℝ} (Fm : FamP eps) (PL : PrinLevF Fm) : FanGal Fm PL := fun _ _ _ => fanAt_id _ _ _

def TameAtG {eps : ℝ} (Fm : FamP eps)
    (tc : ∀ x (i : Fm.Ix x), ℕ → ∀ k : Fin 2, (ZMod ((Fm.D x i).host.g k))ˣ →* ℂˣ) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x),
    (∀ k : Fin 2, ∃ om : (ZMod ((Fm.D x i).host.g k))ˣ →* ℂˣ,
      orderOf om = (Fm.D x i).host.g k - 1 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ (Fm.D x i).R.m → tc x i j k = om ^ (2 * j)) ∧
    ∀ j : Fin (Fm.D x i).R.m, ∃ n : ℤ, (∑ τ, (((Fm.D x i).hc τ).e j : ℚ)) = 2 * n

def FunData {eps : ℝ} (Fm : FamP eps) (cF : List ℝ → ℝ)
    (cond : ∀ x (_ : Fm.Ix x), ℕ → ℕ → ℕ) (q0 : ∀ x (_ : Fm.Ix x), ℕ)
    (nb : ∀ x (_ : Fm.Ix x), Fin 2 → ℕ) : Prop :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x),
    (∀ k, 1 ≤ k → k ≤ (Fm.D x i).R.m → ∀ p : ℕ, p.Prime →
      cond x i k p =
        if p = (Fm.D x i).host.g 0 ∨ p = (Fm.D x i).host.g 1 ∨ p = (Fm.D x i).host.pde ∨
            p = (Fm.D x i).host.pde' then 2
        else if p = q0 x i then 1 else 0) ∧
    Real.log (q0 x i : ℝ) ≤ cF Fm.cOut * (Fm.L x i).sc.L ∧
    ∀ k, Real.log (nb x i k : ℝ) ≤ cF Fm.cOut * ((Fm.D x i).R.f : ℝ) ^ 2 * (Fm.L x i).sc.L

end Formalism.MainNotions.DIV.Align

end
end

