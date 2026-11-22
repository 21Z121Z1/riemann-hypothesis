import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.IsRealPtO
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0002

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.RealPtExHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Fock.DRho Matrix

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isRealPtO_iff {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : RPt D m n) (w : Mx D m n) :
    IsRealPtO θ z w ↔ w = Lb D m n z := by
  have e := Formalism.IndefR.Eqv.eq_thetaC D hθ
  subst e
  constructor
  · rintro ⟨h1, h2⟩
    have hf : ∀ i j, finPart D (w i j) = 0 := fun i j => by
      have := congrFun (congrFun h1 i) j
      rw [Matrix.map_apply, Matrix.zero_apply] at this
      exact this
    rw [← Lb_sigH w hf]
    congr 1
    funext ρ i j
    have := congrFun (congrFun (h2 ρ) i) j
    simp only [compAt, Matrix.map_apply, Matrix.of_apply] at this
    rw [sigH_apply]
    exact this
  · rintro rfl
    refine ⟨?_, fun τ => compAt_Lb z τ⟩
    ext i j
    rw [Matrix.map_apply, Matrix.zero_apply]
    exact finPart_Lb z i j

theorem realPtEx_holds : RealPtEx D := by
  intro θ m n hθ z
  exact ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl, fun w hw => (isRealPtO_iff hθ z w).1 hw⟩

theorem realPt_eq {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (z : RPt D m n) : realPt θ z = Lb D m n z :=
  (isRealPtO_iff hθ z _).1 (Classical.epsilon_spec ⟨Lb D m n z, (isRealPtO_iff hθ z _).2 rfl⟩)

end Formalism.IndefR.Mi
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SignsG
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField IsDedekindDomain

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def liftRes (PP : Formalism.L2.DIV.Pl D.host.E) (x : Formalism.L2.DIV.kP PP) : 𝓞 D.host.E :=
  Function.surjInv Ideal.Quotient.mk_surjective x

def supSum {k : Type} [AddCommMonoid k] {r : ℕ} (x : Matrix (Fin r) (Fin r) k) : k :=
  ∑ i : Fin r, if h : i.1 + 1 < r then x i ⟨i.1 + 1, h⟩ else 0

def psiAt (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) (y : D.host.E) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D) (e * incA D (D.host.xi0 * y)))

def SignsAtG {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : Formalism.IndefR.Links.RealDat D A Ks) (F : Formalism.IndefR.Links.Face D A) : Prop :=
  ∀ (e : R.Pg → AE D), (∀ PP : R.Pg, Formalism.L2.NTheta.IsIdemAt (e PP) PP.1) → ∀ u : F.P0,
    D.what₂.embLL ((F.ψ0 u : D.what₂.LLˣ) : D.what₂.LL) =
      ∏ PP : R.Pg, psiAt R.ψ (e PP)
        ((((Ideal.absNorm PP.1.asIdeal : ℕ) : D.host.E))⁻¹ *
          ((liftRes PP.1 (supSum (((R.eG (u : G)) PP : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP.1)) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.L2.DIV.kP PP.1))) : 𝓞 D.host.E) : D.host.E))

end Formalism.IndefR.Mi
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.UnfDefs
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsCutoff (S S0 : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (lev : GA D S0 →* GA D S)
    (μN : Measure (NI S CS)) (μ0 : Measure (GA D S0)) (β : GA D S → ℝ) : Prop :=
  (∀ h, 0 ≤ β h) ∧ Measurable β ∧ ∀ h,
    Integrable (fun p : NI S CS × GA D S0 => β ((p.1 : GA D S) * lev p.2 * h)) (μN.prod μ0) ∧
      ∫ p, β ((p.1 : GA D S) * lev p.2 * h) ∂(μN.prod μ0) = 1

def cutInt (S : HSp D) (ν : Measure (GA D S)) (β : GA D S → ℝ) (Φ : GA D S → ℂ) : ℂ :=
  ∫ h, (β h : ℂ) * Φ h ∂ν

def MU (S : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
    (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) : Subgroup (GA D S) :=
  Subgroup.closure {g | ∃ u : Matrix (Fin ρ) (Fin ρ) (AE D), (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
    HMul.hMul (mt S g) (CS.map (incA D)) = HMul.hMul (CS.map (incA D)) u ∧
    HMul.hMul (mt S g) (BS.map (incA D)) = BS.map (incA D) ∧
    ∃ v : Matrix (Fin ρ) (Fin ρ) (AE D), HMul.hMul (mt S g) (CS'.map (incA D)) = HMul.hMul (CS'.map (incA D)) v}

def MUQ (S : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (S0 : HSp D)
    (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) : Subgroup (MU S CS CS' S0 BS) :=
  (GQ S).subgroupOf (MU S CS CS' S0 BS)

def IsPsiUVal (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (g : GA D S) (v : ℂ) : Prop :=
  ∃ u : Matrix (Fin ρ) (Fin ρ) (AE D), HMul.hMul (mt S g) (CS.map (incA D)) = HMul.hMul (CS.map (incA D)) u ∧
    v = ψ (Algebra.trace (AF D.host.F) (AE D) (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then u i j else 0))

open Classical in

def psiU (ψ : AddChar (AF D.host.F) ℂ) (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (g : GA D S) : ℂ :=
  if h : ∃ v, IsPsiUVal ψ S CS g v then h.choose else 1

def mixedModelBasePoint (S : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) : Mx D ρ S.rank :=
  (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D)

def yMat (T0 : HSp D) (ρ : ℕ) (ε : D.host.E) (z0 : Fin T0.rank → D.host.E) : Mx D T0.rank ρ :=
  fun i j => if j.1 + 1 = ρ then incA D (ε * D.host.xi0⁻¹ * z0 i) else 0

def jac (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (My : Mx D T0.rank ρ) (n : GA D S)
    (Ξ : WO S0 T0 → ℂ) : WO S0 T0 → ℂ :=
  fun x =>
    let w₁ : WO S T0 := HMul.hMul (embP S T0 CS' My + embQ S T0 S0 BS x) (mt S n)
    ψ (symplOH S T0 (embP S T0 CS' My + embQ S T0 S0 BS (HMul.hMul w₁ (BS.map (incA D))))
        (embS S T0 CS (HMul.hMul w₁ (CS'.map (incA D))))) *
      Ξ (HMul.hMul w₁ (BS.map (incA D)))

def xiEv (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ : ℕ} (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (μS : Measure (Mx D T0.rank ρ)) (𝓕S : Set (Mx D T0.rank ρ)) (My : Mx D T0.rank ρ)
    (f : WO S T → ℂ) : WO S0 T0 → ℂ :=
  fun z => RedS ψ S T0 CS μS 𝓕S (fun x0 => Red ψ S T C μ 𝓕 f (embI S T C' (mixedModelBasePoint S CS) + embI S T B0 x0))
    (embP S T0 CS' My + embQ S T0 S0 BS z)

def bIntd (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (A : HSp D) (lev : GA D S0 →* GA D S)
    (ιH : GA D A →* GA D T0) (om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ)) (My : Mx D T0.rank ρ)
    (φ : GA D A → ℂ) (Ξ : WO S0 T0 → ℂ) (G' : GA D S → ℂ) (h'0 : GA D S0) (n : NI S CS)
    (m : MU S CS CS' S0 BS) (h0 : GA D A) : ℂ :=
  G' ((n : GA D S) * (m : GA D S) * lev h'0) * star (psiU ψ S CS (m : GA D S)) * φ h0 *
    jac ψ S T0 CS CS' S0 BS My (n : GA D S) (om00 (h'0, ιH h0) Ξ) 0

def bSharp (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (A : HSp D) (lev : GA D S0 →* GA D S)
    (ιH : GA D A →* GA D T0) (om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ)) (My : Mx D T0.rank ρ)
    (μ0 : Measure (GA D S0)) (𝓕0 : Set (GA D S0)) (μN : Measure (NI S CS)) (𝓕N : Set (NI S CS))
    (μU : Measure (MU S CS CS' S0 BS)) (𝓕U : Set (MU S CS CS' S0 BS)) (μH : Measure (GA D A)) (𝓕H : Set (GA D A))
    (φ : GA D A → ℂ) (Ξ : WO S0 T0 → ℂ) (G' : GA D S → ℂ) : ℂ :=
  ∫ h'0 in 𝓕0, ∫ n in 𝓕N, ∫ m in 𝓕U, ∫ h0 in 𝓕H,
    bIntd ψ S T0 CS CS' S0 BS A lev ιH om00 My φ Ξ G' h'0 n m h0 ∂μH ∂μU ∂μN ∂μ0

def BSharpAbs (ψ : AddChar (AF D.host.F) ℂ) (S T0 : HSp D) {ρ : ℕ} (CS CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (A : HSp D) (lev : GA D S0 →* GA D S)
    (ιH : GA D A →* GA D T0) (om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ)) (My : Mx D T0.rank ρ)
    (μ0 : Measure (GA D S0)) (𝓕0 : Set (GA D S0)) (μN : Measure (NI S CS)) (𝓕N : Set (NI S CS))
    (μU : Measure (MU S CS CS' S0 BS)) (𝓕U : Set (MU S CS CS' S0 BS)) (μH : Measure (GA D A)) (𝓕H : Set (GA D A))
    (φ : GA D A → ℂ) (Ξ : WO S0 T0 → ℂ) (G' : GA D S → ℂ) : Prop :=
  Integrable (fun q : GA D S0 × NI S CS × MU S CS CS' S0 BS × GA D A =>
      bIntd ψ S T0 CS CS' S0 BS A lev ιH om00 My φ Ξ G' q.1 q.2.1 q.2.2.1 q.2.2.2)
    ((μ0.restrict 𝓕0).prod ((μN.restrict 𝓕N).prod ((μU.restrict 𝓕U).prod (μH.restrict 𝓕H))))

example (S S0 : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (lev : GA D S0 →* GA D S)
    (μN : Measure (NI S CS)) (μ0 : Measure (GA D S0)) [IsProbabilityMeasure (μN.prod μ0)] :
    IsCutoff S S0 CS lev μN μ0 (fun _ => 1) :=
  ⟨fun _ => zero_le_one, measurable_const, fun _ => ⟨integrable_const _, by simp⟩⟩

end Formalism.IndefR.Mi

end
end

