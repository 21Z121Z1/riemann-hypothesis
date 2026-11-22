import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Formalism.LocalToGlobal.LatticeGeometry.FormsK
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0002
import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ArithLemmas
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo

namespace Formalism.IndefR.Arith

section Comparison₂

variable {D : D7} {G : DV.Geo D.what₂.LL} {NW : ℕ → ℕ} {CompW : ℕ → Type} [∀ j, Fintype (CompW j)]
  {algW : ∀ j, AlgPkg G D.what₂.Tau (NW j) (CompW j)} {PtY : ℕ → ℕ → Type}
variable (P : FormsPkg D G NW CompW algW PtY) [Algebra P.KO D.what₂.LL]
variable {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module P.KO WL] [IsScalarTower P.KO D.what₂.LL WL]
  [Module (𝓞 P.KO) WL] [IsScalarTower (𝓞 P.KO) P.KO WL]
variable {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0]

def TiedTo (j : ℕ) (w : WeightFamilies.Wt D j) (A : FormsL D.what₂.LL P.KO WL W G0) (ι : P.Cusp j w →ₗ[P.KO] WL) : Prop :=
  w.n = D.R.nV ∧ wtOf w = DV.kapW D j ∧ (∀ a : P.KO, algebraMap P.KO D.what₂.LL a = P.kL a) ∧
    Function.Injective ι ∧ (∀ x, x ∈ A.WK ↔ x ∈ LinearMap.range ι) ∧ ∀ F, ι F ∈ A.MK ↔ F ∈ P.Mlat j w

def NormTie (pos : (D.what₂.LL →+* ℂ) → Prop) (c : ℝ) {j : ℕ} {w : WeightFamilies.Wt D j} (A : FormsL D.what₂.LL P.KO WL W G0)
    (ι : P.Cusp j w →ₗ[P.KO] WL) : Prop :=
  ∀ σ, pos σ → ∀ F, A.nrmAt σ (ι F) = c * P.l2NormAlt j w (σ.comp P.kL) F

theorem NormTie.rigid {pos : (D.what₂.LL →+* ℂ) → Prop} {c : ℝ} (hc : 0 < c) {j : ℕ} {w : WeightFamilies.Wt D j}
    {A : FormsL D.what₂.LL P.KO WL W G0} {ι : P.Cusp j w →ₗ[P.KO] WL} (h : NormTie P pos c A ι) {a : D.what₂.LL}
    (h' : ∀ σ, pos σ → ∀ F, ‖A.j σ (a • ι F)‖ = c * P.l2NormAlt j w (σ.comp P.kL) F)
    {F : P.Cusp j w} (hF : F ≠ 0) {σ : D.what₂.LL →+* ℂ} (hσ : pos σ) : ‖σ a‖ = 1 := by
  have h1 := h σ hσ F
  have h2 := h' σ hσ F
  rw [map_smulₛₗ, norm_smul] at h2
  unfold FormsL.nrmAt at h1
  have h3 : c * P.l2NormAlt j w (σ.comp P.kL) F ≠ 0 :=
    mul_ne_zero hc.ne' fun e => hF ((P.l2Norm_eq_zero_iff _ _ _ _).1 e)
  rw [h1] at h2
  exact mul_right_cancel₀ h3 (h2.trans (one_mul _).symm)

end Comparison₂

section Fam

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type} {Fam : ShimFam D G Lev} (K : FormsKPkg Fam)
variable [Algebra K.fs.KO D.what₂.LL]
variable {WL : Type} [AddCommGroup WL] [Module D.what₂.LL WL] [Module K.fs.KO WL]
  [IsScalarTower K.fs.KO D.what₂.LL WL] [Module (𝓞 K.fs.KO) WL] [IsScalarTower (𝓞 K.fs.KO) K.fs.KO WL]
variable {W : (D.what₂.LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0]

def ActTie (e : G0 ≃* K.Hb) (j : ℕ) (w : WeightFamilies.Wt D j) (A : FormsL D.what₂.LL K.fs.KO WL W G0)
    (ι : K.fs.Cusp j w →ₗ[K.fs.KO] WL) : Prop :=
  ∀ g (F F' : K.fs.Cusp j w), e g • K.fs.inc j w F = K.fs.inc j w F' → A.ρ g (ι F) = ι F'

def CompatibleAtCompactLevel (e : G0 ≃* K.Hb) (pos : (D.what₂.LL →+* ℂ) → Prop) (volRec : ℝ) (j : ℕ) (w : WeightFamilies.Wt D j)
    (A : FormsL D.what₂.LL K.fs.KO WL W G0) (ι : K.fs.Cusp j w →ₗ[K.fs.KO] WL) : Prop :=
  K.κs = Fam.κg ∧ 1 ≤ j ∧ j ≤ D.R.m ∧ TiedTo K.fs j w A ι ∧ ActTie K e j w A ι ∧
    NormTie K.fs pos (Real.sqrt (volRec * dimKap D j)) A ι

end Fam

end Formalism.IndefR.Arith
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.AutomorphicFormsHyp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Filter Topology
  IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.AutomorphicFormsHyp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section General

variable {N : ℕ}

def hK (K : Matrix (Fin N) (Fin N) D.host.E) (x y : Mx D N 1) : AE D :=
  ∑ a, ∑ b, cA D (y a 0) * incA D (K a b) * x b 0

def symplK (K : Matrix (Fin N) (Fin N) D.host.E) (x y : Mx D N 1) : AF D.host.F :=
  Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * hK K x y)

def symplKH (K : Matrix (Fin N) (Fin N) D.host.E) (x y : Mx D N 1) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * symplK K x y

def heisK (ψ : AddChar (AF D.host.F) ℂ) (K : Matrix (Fin N) (Fin N) D.host.E) (w₀ : Mx D N 1) (f : Mx D N 1 → ℂ) :
    Mx D N 1 → ℂ :=
  fun w => ψ (symplKH K w w₀) * f (w + w₀)

def ratK (D : D7) (N : ℕ) : AddSubgroup (Mx D N 1) :=
  ((incA D).toAddMonoidHom.mapMatrix (m := Fin N) (n := Fin 1)).range

abbrev UK (D : D7) (K : Matrix (Fin N) (Fin N) D.host.E) : Type := HA (AF D.host.F) D.sp.cm.sig K

def ratU (K : Matrix (Fin N) (Fin N) D.host.E) : Subgroup (UK D K) := HFinIn (AF D.host.F) D.sp.cm.sig K

def actK (K : Matrix (Fin N) (Fin N) D.host.E) (g : UK D K) (x : Mx D N 1) : Mx D N 1 :=
  HMul.hMul ((HA.mat (AF D.host.F) D.sp.cm.sig K g).1 : Matrix (Fin N) (Fin N) (AE D)) x

structure IsL2ThetaVector (ψ : AddChar (AF D.host.F) ℂ) (K : Matrix (Fin N) (Fin N) D.host.E) (μ : Measure (Mx D N 1))
    (𝓕 : Set (Mx D N 1)) (f : Mx D N 1 → ℂ) : Prop where
  quasi : ∀ γ ∈ ratK D N, ∀ w, f (γ + w) = ψ (-(symplKH K γ w)) * f w
  meas : AEStronglyMeasurable f μ
  fin : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ ≠ ⊤

structure IsL2SplittingUnitary (ψ : AddChar (AF D.host.F) ℂ) (K : Matrix (Fin N) (Fin N) D.host.E) (μ : Measure (Mx D N 1))
    (𝓕 : Set (Mx D N 1)) (om : UK D K → Module.End ℂ (Mx D N 1 → ℂ)) : Prop where
  pres : ∀ g f, IsL2ThetaVector ψ K μ 𝓕 f → IsL2ThetaVector ψ K μ 𝓕 (om g f)
  unit : ∀ g f, IsL2ThetaVector ψ K μ 𝓕 f → ∫⁻ w in 𝓕, ‖om g f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ
  one : ∀ f, IsL2ThetaVector ψ K μ 𝓕 f → om 1 f =ᵐ[μ] f
  mul : ∀ g g' f, IsL2ThetaVector ψ K μ 𝓕 f → om (g * g') f =ᵐ[μ] om g (om g' f)
  Heisenberg₂ : ∀ g w₀ f, IsL2ThetaVector ψ K μ 𝓕 f → om g (heisK ψ K w₀ f) =ᵐ[μ] heisK ψ K (actK K g w₀) (om g f)
  rat : ∀ γ ∈ ratU K, ∀ f, IsL2ThetaVector ψ K μ 𝓕 f → om γ f =ᵐ[μ] fun w => f (actK K γ⁻¹ w)
  cont : ∀ f, IsL2ThetaVector ψ K μ 𝓕 f → ∀ g₀,
    Tendsto (fun g => ∫⁻ w in 𝓕, ‖om g f w - om g₀ f w‖ₑ ^ 2 ∂μ) (𝓝 g₀) (𝓝 0)

end General

def GelbartRogawskiSplit (D : D7) : Prop :=
  ∀ (s : ℤ) (ψ : AddChar (AF D.host.F) ℂ), (s = 1 ∨ s = -1) → IsStdChar D ψ s →
    ∀ (N : ℕ) (K : Matrix (Fin N) (Fin N) D.host.E), (∀ a b, D.sp.cm.sig (K b a) = K a b) → K.det ≠ 0 →
      ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ 1 →
        ∀ (μ : Measure (Mx D N 1)) (𝓕 : Set (Mx D N 1)), μ.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratK D N) 𝓕 μ →
          ∃ om : UK D K → Module.End ℂ (Mx D N 1 → ℂ), IsL2SplittingUnitary ψ K μ 𝓕 om

def WeilExistsO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om

structure IsL2ThetaPair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (f : WO S T → ℂ) : Prop where
  quasi : ∀ γ w, f (ratW T S γ + w) = ψ (-(symplOH S T (ratW T S γ) w)) * f w
  meas : AEStronglyMeasurable f μ
  fin : ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ ≠ ⊤

structure IsL2SplittingPair (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (om : GA D S × GA D T → Module.End ℂ (WO S T → ℂ)) : Prop where
  pres : ∀ p f, IsL2ThetaPair ψ S T μ 𝓕 f → IsL2ThetaPair ψ S T μ 𝓕 (om p f)
  unit : ∀ p f, IsL2ThetaPair ψ S T μ 𝓕 f → ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ
  one : ∀ f, IsL2ThetaPair ψ S T μ 𝓕 f → om 1 f =ᵐ[μ] f
  mul : ∀ p p' f, IsL2ThetaPair ψ S T μ 𝓕 f → om (p * p') f =ᵐ[μ] om p (om p' f)
  Heisenberg₂ : ∀ g h w₀ f, IsL2ThetaPair ψ S T μ 𝓕 f →
    om (g, h) (heisO ψ S T w₀ f) =ᵐ[μ] heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  rat : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsL2ThetaPair ψ S T μ 𝓕 f →
    om (γ, γ') f =ᵐ[μ] fun w => f (actO S T γ⁻¹ γ'⁻¹ w)
  cont : ∀ f, IsL2ThetaPair ψ S T μ 𝓕 f → ∀ p₀,
    Tendsto (fun p => ∫⁻ w in 𝓕, ‖om p f w - om p₀ f w‖ₑ ^ 2 ∂μ) (𝓝 p₀) (𝓝 0)

def WeilL2SplittingExists (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ →
      ∃ om : GA D S × GA D T → Module.End ℂ (WO S T → ℂ), IsL2SplittingPair ψ S T μ 𝓕 om

structure IsWeilPreO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  om_pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)
  om_heis : ∀ g h w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  om_aut : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → om (γ, γ') f 0 = f 0
  om_cont : ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun p : GA D S × GA D T => om p f w
  om_unit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ p f, IsThetaFunO ψ S T f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

def WeilPreExistsO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilPreO ψ S T om

def HeckeEtaExists (D : D7) : Prop := ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ 1

def StepVecO (D : D7) : Prop := GelbartRogawskiSplit D → HeckeEtaExists D → WeilL2SplittingExists D

def StepSmoothO (D : D7) : Prop := WeilL2SplittingExists D → WeilPreExistsO D

def StepCharO (D : D7) : Prop := GelbartRogawskiSplit D → HeckeEtaExists D → WeilPreExistsO D → WeilExistsO D

end Formalism.IndefR.AutomorphicFormsHyp

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxPass
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def prin {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) : CxData A := { X with nP := fun _ => 1 }

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

section Prims

variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

def GUnit (gE : Representation ℂ G X.EE) : Prop := ∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

def GEquiv (gE : Representation ℂ G X.EE) : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), X.Θ t (X.jR t (A.fam.amb.opR t (Sum.inr g) x)) = gE g (X.Θ t (X.jR t x))

def typeSp (gE : Representation ℂ G X.EE) (P : Subgroup G) (ψ : P →* Kˣ) : Submodule ℂ X.EE :=
  ⨅ h : P, LinearMap.ker (gE (h : G) - (A.fam.v0.embedding ((ψ h : Kˣ) : K)) • LinearMap.id)

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
    {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

def EEg : Submodule ℂ X.EE :=
  LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)

def PrincipalInjectiveCommonRange : Prop :=
  Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0) ∧
    ∀ t, Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) ∧
      LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) =
        LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)

def LevType (gE : Representation ℂ G X.EE) (b : Bool) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  X.EEl b = EEg A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp A X gE P ψ

end Prims

section Group

variable {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]

def CharsX (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K)) : Prop :=
  ∀ χ : G → K, χ ∈ Xc ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ

def NearConstantMultiplicities (τ : ∀ s, Representation K G (Ws s)) (P1 : Formalism.IndefR.IndefiniteEpsilonOperator.Pair G K) (nbar de : ℝ) : Prop :=
  ∀ s, (1 - de) * nbar ≤ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ∧ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar

end Group

def CutPassage2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (G : Type) [Group G] [Fintype G]
    (Pl0 T : Type) (m : ℕ) (A : FamIn K G Pl0 T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (C CH : ℝ)
    (gE : Representation ℂ G X.EE) (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ),
    A.fam.Ok s → A.fam.TypesSep →
    X.zs.Stable → X.zs.InBlock → X.H4pos →
    (A.side P0 ψ0 X.zs).Pos → (A.side P1 ψ1 X.zs).Pos →
    (∀ b, X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b) → (∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b) →
    PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) → X.RATmu (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false →
    GUnit A X gE → GEquiv A X gE →
    LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0 →
    LevType A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1 →
    X.nP false = (Nat.card P0 : ℝ) → X.nP true = (Nat.card P1 : ℝ) →
    Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ A.fam.X → Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ → 0 < nbar →
    NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de →
    ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G →
      Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
        (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

def CutPassage2S : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (G : Type) [Group G] [Fintype G]
    (Pl0 T : Type) (m : ℕ) (A : FamIn K G Pl0 T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb) (C CH : ℝ)
    (gE : Representation ℂ G X.EE) (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ),
    A.fam.Ok s → A.fam.TypesSep →
    X.zs.Stable → X.zs.InBlock → X.H4pos →
    (A.side P0 ψ0 X.zs).Pos → (A.side P1 ψ1 X.zs).Pos →
    (∀ b, X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b) → (∀ b, X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b) →
    PrincipalInjectiveCommonRange A X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) → X.RATmu (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false →
    GUnit A X gE → GEquiv A X gE →
    X.nP false = (Nat.card P0 : ℝ) → X.nP true = (Nat.card P1 : ℝ) →
    Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ A.fam.X → Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ → 0 < nbar →
    NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de →
    ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G →
      Passage ((faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
        (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.DatumFock
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

section Subst

abbrev complexSquareMatrixFamily (D : D7) (p : D.what₂.Tau → ℕ) : Type := ∀ τ : D.what₂.Tau, Matrix (Fin (p τ)) (Fin (p τ)) ℂ

abbrev complementBlockMatrixFamily (D : D7) (m : ℕ) (p : D.what₂.Tau → ℕ) : Type :=
  ∀ τ : D.what₂.Tau, Matrix (Fin (m - p τ)) (Fin (m - p τ)) ℂ

abbrev HFam (D : D7) (n : ℕ) : Type := D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ

def zPlus (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) :=
  Matrix.of fun c a => varF τ (a : ℕ) (c : ℕ)

def zMinus (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) :
    Matrix (Fin n) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) :=
  Matrix.of fun c b => varF τ (p τ + (b : ℕ)) (c : ℕ)

def zPlusS (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (h : HFam D n) (τ : D.what₂.Tau) :
    Matrix (Fin n) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) :=
  let hi : Matrix (Fin n) (Fin n) (MvPolynomial (FVar D m n) ℂ) := Matrix.map (h τ)⁻¹ MvPolynomial.C
  let k : Matrix (Fin (p τ)) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) := Matrix.map (k₁ τ) MvPolynomial.C
  let z : Matrix (Fin n) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) := zPlus p τ
  let hz : Matrix (Fin n) (Fin (p τ)) (MvPolynomial (FVar D m n) ℂ) := hi * z
  hz * k

def zMinusS (p : D.what₂.Tau → ℕ) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) (τ : D.what₂.Tau) :
    Matrix (Fin n) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) :=
  let ht : Matrix (Fin n) (Fin n) (MvPolynomial (FVar D m n) ℂ) := Matrix.map (h τ)ᵀ MvPolynomial.C
  let k : Matrix (Fin (m - p τ)) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) :=
    Matrix.map (k₂ τ) fun x => MvPolynomial.C (starRingEnd ℂ x)
  let z : Matrix (Fin n) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) := zMinus p τ
  let hz : Matrix (Fin n) (Fin (m - p τ)) (MvPolynomial (FVar D m n) ℂ) := ht * z
  hz * k

def substVar (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) :
    FVar D m n → MvPolynomial (FVar D m n) ℂ :=
  fun x => if hx : (x.2.1 : ℕ) < p x.1 then zPlusS p k₁ h x.1 x.2.2 ⟨x.2.1, hx⟩
    else zMinusS p k₂ h x.1 x.2.2 ⟨(x.2.1 : ℕ) - p x.1, by have := x.2.1.isLt; omega⟩

def polySubst (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.bind₁ (substVar p k₁ k₂ h)

theorem polySubst_X (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) (x : FVar D m n) :
    polySubst p k₁ k₂ h (MvPolynomial.X x) = substVar p k₁ k₂ h x := by
  simp [polySubst]

theorem substVar_one (p : D.what₂.Tau → ℕ) :
    substVar (m := m) (n := n) p (fun τ => (1 : Matrix (Fin (p τ)) (Fin (p τ)) ℂ))
      (fun τ => (1 : Matrix (Fin (m - p τ)) (Fin (m - p τ)) ℂ)) (fun _ => 1) = MvPolynomial.X := by
  funext ⟨τ, i, c⟩
  have hi := i.isLt
  have e : ∀ k : ℕ, Matrix.map (1 : Matrix (Fin k) (Fin k) ℂ)
      (MvPolynomial.C : ℂ →+* MvPolynomial (FVar D m n) ℂ) = 1 :=
    fun k => Matrix.map_one _ (map_zero _) (map_one _)
  by_cases hx : (i : ℕ) < p τ
  · simp [substVar, hx, zPlusS, zPlus, varF, e, hi]
  · have h3 : p τ + ((i : ℕ) - p τ) < m := by omega
    simp only [substVar, hx, zMinusS, zMinus, varF, e, dif_neg, not_false_eq_true, transpose_one, Matrix.map_one,
      map_zero, map_one, Matrix.one_mul, Matrix.mul_one, Matrix.of_apply]
    rw [dif_pos (by omega)]
    congr 1
    simp only [Prod.mk.injEq, Fin.ext_iff, true_and, and_true]
    omega

def dExp (m : ℕ) (p : D.what₂.Tau → ℕ) (e : D.what₂.Tau → ℤ) (τ : D.what₂.Tau) : ℤ := (p τ : ℤ) - ((m + 1) / 2 : ℕ) - e τ

def fockChar (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) : ℂ :=
  ∏ τ, (k₁ τ).det ^ (a - e τ) * (k₂ τ).det ^ (-a - e τ) * (h τ).det ^ (-dExp m p e τ)

def piAct (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ)
    (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (h : HFam D n) :
    MvPolynomial (FVar D m n) ℂ →ₗ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  fockChar p a e k₁ k₂ h • (polySubst p k₁ k₂ h).toLinearMap

def blockDiagonalOfBlocks (p : D.what₂.Tau → ℕ) (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D m p) (τ : D.what₂.Tau) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j =>
    if hi : (i : ℕ) < p τ then (if hj : (j : ℕ) < p τ then k₁ τ ⟨i, hi⟩ ⟨j, hj⟩ else 0)
    else if hj : (j : ℕ) < p τ then 0
    else k₂ τ ⟨(i : ℕ) - p τ, by have := i.isLt; omega⟩ ⟨(j : ℕ) - p τ, by have := j.isLt; omega⟩

def sgnDiag (p : D.what₂.Tau → ℕ) (τ : D.what₂.Tau) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun i => if (i : ℕ) < p τ then 1 else -1

end Subst

section Equiv

def IsInfEl (θ : InfFam D) (V : HSp D) (g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (x : GA D V) : Prop :=
  x ∈ GinfC V ∧ ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) x = g τ

def FockEquiv (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (p : D.what₂.Tau → ℕ) (a : ℤ) (e : D.what₂.Tau → ℤ) : Prop :=
  IsInfFam θ → IsWeilDatumO ψ S T χS χT om → 2 * a = (S.rank : ℤ) → (∀ τ, p τ ≤ T.rank) → Odd T.rank →
  (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, HasInfExp D χS τ (-(e τ : ℚ))) → (∀ τ, HasInfExp D χT τ (-(e τ : ℚ) - 1 / 2)) →
  (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) →
  (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1 ∧ sS τ * BS τ = BS τ) →
  (∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = sgnDiag p τ ∧ sT τ * BT τ = BT τ * sgnDiag p τ) →
  ∀ (k₁ : complexSquareMatrixFamily D p) (k₂ : complementBlockMatrixFamily D T.rank p) (h : HFam D S.rank),
    (∀ τ, k₁ τ ∈ Matrix.unitaryGroup (Fin (p τ)) ℂ) → (∀ τ, k₂ τ ∈ Matrix.unitaryGroup (Fin (T.rank - p τ)) ℂ) →
    (∀ τ, h τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) →
    ∀ (g : GA D S) (h' : GA D T), IsInfEl θ S (fun τ => BS τ * h τ * (BS τ)⁻¹) g →
      IsInfEl θ T (fun τ => BT τ * blockDiagonalOfBlocks p k₁ k₂ τ * (BT τ)⁻¹) h' →
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ,
          om (g, h') (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) f P) =
            pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) f
              (piAct p a e k₁ k₂ h P)

end Equiv

end Formalism.IndefR.Datum

end
end

