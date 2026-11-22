import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
import Formalism.LocalRingCardinality.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.DataParams
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeometricConstantEquiv
section
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (w : WeightFamilies.Wt D ((i : ℕ) + 1))

abbrev Cusp : Type := T.cuspA ((i : ℕ) + 1) (wtA w) w.n

abbrev res (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := σ.comp (algebraMap T.Q.c.F D.what₂.LL)

def iotaW : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E) :=
  LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast (rank_Wc i)) ∘ₗ T.iota ((i : ℕ) + 1)

def IsLift (g : G) (κ : GA D (Wc D i)) : Prop :=
  Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ

def IsGeo (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∃ lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La,
    LevIs R i (iotaW T i) T.Q.l.M (T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) lev ∧
    ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) ∧
    ∀ g (f : Cusp T i w), ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) =
      actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (fun g => (lev g, LinearMap.id)) g (f : T.R ((i : ℕ) + 1))

def ReadTwist (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ (g : G) (κ : GA D (T.V ((i : ℕ) + 1) (res T σ))), IsLift T R i g (cast (congrArg (GA D) hV) κ) →
      ∀ (f : Cusp T i w) (x : GA D (T.V ((i : ℕ) + 1) (res T σ))),
        T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) ((ρ g f : Cusp T i w) : T.R ((i : ℕ) + 1)) x =
          σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) *
            T.phiJ ((i : ℕ) + 1) (res T σ) (wtA w) (f : T.R ((i : ℕ) + 1)) (x * κ)

def IsIntegralForm (f : Cusp T i w) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.PtM ((i : ℕ) + 1) la),
    T.nrmM ((i : ℕ) + 1) la y (f : T.R ((i : ℕ) + 1)) ≤ 1

def KeepsIntegral (ρ : G →* Module.End T.Q.c.F (Cusp T i w)) : Prop :=
  ∀ g f, IsIntegralForm T i w f → IsIntegralForm T i w (ρ g f)

def ConstEquiv : Prop :=
  ∀ σ : D.what₂.LL →+* ℂ, GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i,
    ∀ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ →
    ∀ chi : G →* (T.Q.c.F)ˣ,
      (∀ g, algebraMap T.Q.c.F D.what₂.LL (chi g : T.Q.c.F) = (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) →
    ∀ ℓ : G → GA D (T.V ((i : ℕ) + 1) (res T σ)), (∀ g, IsLift T R i g (cast (congrArg (GA D) hV) (ℓ g))) →
      CEquiv (T.V ((i : ℕ) + 1) (res T σ)) (res T σ)
        ((rdU (T.U ((i : ℕ) + 1) (res T σ))).comp (T.cuspA ((i : ℕ) + 1) (wtA w) w.n).subtype)
        (T.dict ((i : ℕ) + 1) (res T σ)) (T.mu ((i : ℕ) + 1) (res T σ)) (T.cE ((i : ℕ) + 1) (res T σ)) ρ chi ℓ

omit [Algebra T.Q.c.F D.what₂.LL] in

def IsKappa : Prop :=
  ∀ τ : D.what₂.Tau,
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).1, w.aP τ k = aPl D i ((Wc D i).sig (tauE D τ)).1 τ k) ∧
    (∀ k : Fin (D.R.sigW ((i : ℕ) + 1)).2,
      w.aM τ k = aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ k) ∧ w.n = D.R.nV

def GeoActAt : Prop :=
  ∃ ρ : G →* Module.End T.Q.c.F (Cusp T i w), IsGeo T R i w ρ ∧ ReadTwist T R i w ρ ∧ KeepsIntegral T i w ρ

def GeoAct : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    LawsJ T →
    (∀ x : 𝓞 T.Q.c.F, algebraMap T.Q.c.F D.what₂.LL (x : T.Q.c.F) = D.what₂.OtoLL (T.Q.eO x)) →
    R.toLevCh.Is A.μ0 → R.grp_chiW → ChiR T R →
    ∀ (i : Fin D.R.m) (w : WeightFamilies.Wt D ((i : ℕ) + 1)), IsKappa i w → ConstEquiv T R i w → GeoActAt T R i w

theorem IsGeo.exists_lift {ρ : G →* Module.End T.Q.c.F (Cusp T i w)} (h : IsGeo T R i w ρ) (g : G) :
    ∃ κ, IsLift T R i g κ := by
  obtain ⟨lev, hl, -⟩ := h
  obtain ⟨κ, hκ, -⟩ := hl g
  exact ⟨κ, hκ⟩

end GlobalTheory.IndefiniteRowSideFullHecke.GeometricConstantEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeTransferRankOne
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
  Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def qC (P : Pl D.host.E) : ℂ := (Nat.card (kP P) : ℂ)

def sqrtQ (P : Pl D.host.E) : ℂ := ((Real.sqrt (Nat.card (kP P) : ℝ) : ℝ) : ℂ)

def IsLocAt (V : HSp D) (P : Pl D.host.E) (a : Bridge.Gf V) : Prop :=
  ∃ (e : AE D) (β : GA D V), Formalism.L2.NTheta.IsIdemAt e P ∧ β ∈ GfC V ∧ SuppAt e V β ∧
    a = (finHom V).rangeRestrict β

section Real

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levV (i : Fin D.R.m) (t : T0) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J

abbrev levW (i : Fin D.R.m) : Subgroup (GA D (Wc D i)) :=
  Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)

def IsCosetOpV (i : Fin D.R.m) (t : T0) (P : Pl D.host.E) (m : ℕ) (S : (R.HV i t).H →ₗ[ℂ] (R.HV i t).H) : Prop :=
  ∃ (α : GA D (Vc D i)) (Av : Finset (Bridge.Gf (Vc D i))),
    IsHeckeAt (Vc D i) P m α ∧ Bridge.IsDC (levV R i t) ((finHom (Vc D i)).rangeRestrict α) Av ∧
    (∀ a ∈ Av, IsLocAt (Vc D i) P a) ∧
    ∀ x, (R.HV i t).e (S x) = Bridge.dcOp Av ((R.HV i t).e x)

def IsCosetFamV (i : Fin D.R.m) (t : T0) (P : Pl D.host.E) (tV : ℕ → (R.HV i t).H →ₗ[ℂ] (R.HV i t).H) : Prop :=
  ∀ m, m ≤ D.R.nV → IsCosetOpV R i t P m (tV m)

def mu0At (i : Fin D.R.m) (P : Pl D.host.E) : ℂ := (((R.C.mu0 i).val P : ℂˣ) : ℂ)

def xiAt (t : T0) (P : Pl D.host.E) : ℂ := (((R.xiH t).val P : ℂˣ) : ℂ)

def etaAt (P : Pl D.host.E) : ℂ := ((R.C.eta.val P : ℂˣ) : ℂ)

def cW (i : Fin D.R.m) (P : Pl D.host.E) (k : ℕ) : ℂ := (mu0At R i P ^ k)⁻¹ * (sqrtQ P ^ (k * D.R.nV))⁻¹

def bV (i : Fin D.R.m) (t : T0) (P : Pl D.host.E) : ℂ := mu0At R i P * xiAt R t P * (etaAt R P)⁻¹ * sqrtQ P

def TransferEq (i : Fin D.R.m) (t : T0) (P : Pl D.host.E) (k : ℕ) (Rc : Finset (GA D (Wc D i)))
    (tV : ℕ → (R.HV i t).H →ₗ[ℂ] (R.HV i t).H) : Prop :=
  ∀ x : (R.HV i t).H,
    cW R i P k • heckeOn (R.MW i (sg0 D A)) Rc (R.thF i t x) =
      xiAt R t P ^ k • R.thF i t (KsHecke.TVk (bV R i t P) (qC P) D.R.r D.R.nV D.R.t tV k x)

def TransferAt (i : Fin D.R.m) (t : T0) : Prop :=
  ∀ P : Pl D.host.E, Bridge.SplitOff P ((R.Sb : Set (Pl D.host.E)) ∪ (R.Q t : Set (Pl D.host.E))) →
    (∃ tV, IsCosetFamV R i t P tV) ∧
    ∀ tV, IsCosetFamV R i t P tV → ∀ k, k ≤ D.R.r → ∀ α : GA D (Wc D i), IsHeckeAt (Wc D i) P k α →
      ∀ Rc : Finset (GA D (Wc D i)), Bridge.IsDC (levW R i) α Rc → TransferEq R i t P k Rc tV

end Real

def HeckeTransfer {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) : Prop :=
  R.Char F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (t : T0), TransferAt R i t

theorem rank_Vc (i : Fin D.R.m) : (Vc D i).rank = D.R.nV ∧ D.R.nV = D.R.r + D.R.t :=
  ⟨D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HeckeTransferRankOne
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift Formalism.IndefR.Links
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 D.host.E) ∉ w.asIdeal ^ 2

def PsiUnramAt (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ α : Af D.host.F, (∀ v', v' ≠ v → evalV D.host.F v' α = 0) →
    ((∀ β ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      evalV D.host.F v α ∈ v.adicCompletionIntegers D.host.F)

def SideCond (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  IsSplit (E := D.host.E) v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal ∧ PsiUnramAt ψ v ∧
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → w.valuation D.host.E D.host.xi0 = 1

def excluded (q t : ℕ) : Set ℂ :=
  {(((q : ℝ) ^ (((t : ℝ) - 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) - 1) / 2)) : ℝ) : ℂ),
    (((q : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ)}

section Cusp

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]

def cuspidalL2Subspace : Submodule ℂ (DividedPowerChartLift V ν) :=
  (Submodule.span ℂ {x | ∃ (φ : GA D V → ℂ) (h : MemL2Quotient (GQ V) ν φ),
    IsAutFun V φ ∧ IsCuspFun V φ ∧ x = h.toL2}).topologicalClosure

def IsCuspIrr (W : Submodule ℂ (DividedPowerChartLift V ν)) : Prop := IsIrredSubrep (RG V ν) W ∧ W ≤ cuspidalL2Subspace V ν

variable {V ν} {W : Submodule ℂ (DividedPowerChartLift V ν)}

def locRep (hW : IsCuspIrr V ν W) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Representation ℂ (GLoc D.sp.cm.sig V.gram v) W :=
  ((ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := W)).toMonoidHom.comp hW.1.1.rep).comp
    (emb D.sp.cm.sig V.gram v)

def SphAt (hW : IsCuspIrr V ν W) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  GlobalTheory.LGrp.IsSpherical (locRep hW v) (stabLoc D.sp.cm.sig V.gram (frameLat V) v)

variable (W) in

def HasRealType (θ : InfFam D) (S : D.what₂.Tau → SPar) : Prop :=
  ∃ M : DSModel V S, ∀ τ, ∃ A : M.H τ →L[ℂ] DividedPowerChartLift V ν, A ≠ 0 ∧ (∀ x, A x ∈ W) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x, A (M.rep τ g x) = RG V ν (atTau θ V τ g) (A x)

def NoExcluded (hW : IsCuspIrr V ν W) (μ : (AE D)ˣ →* Circle) (t : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  IsSplit (E := D.host.E) v ∧ ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v),
    GlobalTheory.LFun.UnrAt μ w ∧ ∃ B : Multiset ℂˣ, GlobalTheory.LFun.HasParam D.sp.cm.sig V.gram (frameLat V) h (locRep hW v) B ∧
      ∀ b ∈ B, ((b * (GlobalTheory.LFun.val μ w)⁻¹ : ℂˣ) : ℂ) ∉ excluded (Formalism.UG.qV D.host.F v) t

def Conclusion (hW : IsCuspIrr V ν W) (μ : (AE D)ˣ →* Circle) (ψ : AddChar (AF D.host.F) ℂ)
    (S : Set (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  (∃ v, v ∉ S ∧ SideCond ψ v ∧ NoExcluded hW μ D.R.t v) ∧
  ∀ p : ℕ, SplitsCompletely D p → (∀ v ∈ S, (p : 𝓞 D.host.F) ∉ v.asIdeal) →
    ¬ p ∣ D.host.QS * D.host.q * D.host.d ∧
    ∀ v : HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal →
      NoExcluded hW μ D.R.t v ∧ (p.Coprime (Ideal.absNorm D.host.ccK) → SideCond ψ v)

end Cusp

def IsAdmDatum (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (Φ : WO A B → ℂ) : Prop :=
  IsThetaFunO ψ A B Φ ∧
    IsLatVac (heisO ψ A B) (latO A B (L0c D A) (L0c D B) fun v => ¬ IsSplit (E := D.host.E) v) Φ

section Chain

variable (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
  (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ)
  (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
  (𝓕 : ∀ k, Set (GA D (Yc D k))) (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0)))

inductive IsIterLift : ∀ k, (GA D (Yc D k) → ℂ) → Prop
  | base {f : GA D (Yc D 0) → ℂ} (hf : IsAutFunSm θ (Yc D 0) f) (h : MemL2Quotient (GQ (Yc D 0)) (ν 0) f) (hσ : h.toL2 ∈ σ) :
      IsIterLift 0 f
  | step {k : ℕ} {u : GA D (Yc D k) → ℂ} (hu : IsIterLift k u) {Φ : WO (Yc D k) (Yc D (k + 1)) → ℂ}
      (hΦ : IsAdmDatum ψ (Yc D k) (Yc D (k + 1)) Φ)
      (hi : ∀ h, IntegrableOn (fun g => th k g h Φ * u g) (𝓕 k) (ν k)) :
      IsIterLift (k + 1) fun h => ∫ g in 𝓕 k, th k g h Φ * u g ∂ν k

def liftSpace (k : ℕ) : Submodule ℂ (GA D (Yc D k) → ℂ) := Submodule.span ℂ {F | IsIterLift θ ψ th ν 𝓕 σ k F}

def MeetsLift (k : ℕ) (W : Submodule ℂ (DividedPowerChartLift (Yc D k) (ν k))) : Prop :=
  ∃ F ∈ liftSpace θ ψ th ν 𝓕 σ k, ∃ h : MemL2Quotient (GQ (Yc D k)) (ν k) F, h.toL2 ∉ Wᗮ

end Chain

def typePlaces (D : D7) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

def badPlaces {T : Type} (L : LevCh D T) (t : T) : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  typePlaces D ∪ {v | ∃ w ∈ L.Q t, w.under (𝓞 D.host.F) = v}

def NodeChainStatement (D : D7) : Prop :=
  (∃ N : ℕ, D.R.rankY D.R.m + 1 ≤ N ∧ D.NodeGap ((D.R.t : ℝ) + 2 * (N : ℝ) ^ 3 + 1)) →
  ∀ (T : Type) (L : LevCh D T) (t₀ : T), L.Is t₀ → ∀ (t : T) (θ : InfFam D), IsInfFam θ →
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ),
    IsChainKernel ψ (L.mu t) L.eta D.R.m (Yc D) th →
  ∀ (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
    (𝓕 : ∀ k, Set (GA D (Yc D k))), (∀ k, IsFundamentalDomain (GQ (Yc D k)) (𝓕 k) (ν k)) →
  ∀ (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0))) (hσ : IsCuspIrr (Yc D 0) (ν 0) σ),
    HasRealType σ θ (parA (tparRec D) 0) → (∀ v ∉ typePlaces D, SphAt hσ v) →
  ∀ k, k < D.R.m → ∀ (π : Submodule ℂ (DividedPowerChartLift (Yc D k) (ν k))) (hπ : IsCuspIrr (Yc D k) (ν k) π),
    MeetsLift θ ψ th ν 𝓕 σ k π →
    Conclusion hπ (chrStep (L.mu t) L.eta (k + 1)).2 ψ (badPlaces L t)

def SingleBlockCuspidal (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
  ∀ (V : HSp D), V.rank = D.R.r →
  ∀ (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (π : Submodule ℂ (DividedPowerChartLift V ν)) (hπ : IsCuspIrr V ν π) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    (∀ v ∉ S, SphAt hπ v) →
  ∀ μ : (AE D)ˣ →* Circle, IsHeckeChar D μ → GlobalTheory.LFun.UnrOff μ (S : Set _) → Conclusion hπ μ ψ (S : Set _)

def NoExcludedParameter : Prop := ∀ D : D7, NodeChainStatement D ∧ SingleBlockCuspidal D

example : (4 : ℂ) ∈ excluded 4 3 := Or.inl (by norm_num)

example {C : Type} [CommGroup C] (μ : ℕ → C) (η : C) :
    (chrStep μ η 1).2 = μ 1 ∧ (chrStep μ η 2).2 = μ 2 * η⁻¹ := by
  constructor <;> simp [chrStep, Nat.odd_iff]

end GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LabelSettingScalars
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

open Classical in

def badPl (t : T) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  (R.Pg ∪ R.Q t).image fun PP => PP.under (𝓞 D.host.F)

def rowPart (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : EigSys D) : Submodule ℂ (MMap (R.MY 0)) :=
  partDual R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) Sb c ⊓ R.EEat R.triv

def IsLValue (t : T) (B : GlobalTheory.LFun.Fam D.host.E) (j : ℕ) (l : ℝ) : Prop :=
  GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
               (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (R.toLevCh.mu t j))⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
    0 < l ∧ GlobalTheory.LFun.LSD D (badPl R t) B (R.toLevCh.mu t j) ((1 + (D.R.t : ℂ)) / 2) = (l : ℂ)

def IsIP (t : T) (k : ℕ) (u u' : MMap (R.MY k)) (a : ℂ) : Prop :=
  IsMultIP (R.MY k) (R.νY t k) (R.fdY t k) u u' a

def IsUp (t : T) (k : ℕ) (u : MMap (R.MY k)) (x : MMap (R.MY (k + 1))) : Prop :=
  PiTensorProduct.lift x ∈ R.CC t (k + 1) ∧ ∀ y : R.CC t (k + 1), ∃ a : ℂ,
    IsIP R t (k + 1) x (PiTensorProduct.lift.symm y.1) a ∧ IsIP R t k u (PiTensorProduct.lift.symm (R.ioY t k y).1) a

def topStep (t : T) (y : (R.HX t).H) : MMap (R.MY (D.R.m - 1)) :=
  PiTensorProduct.lift.symm (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1

def IsUpTop (t : T) (u : MMap (R.MY (D.R.m - 1))) (x : (R.HX t).H) : Prop :=
  ∀ y : (R.HX t).H, IsIP R t (D.R.m - 1) u (topStep R t y) ⟪x, y⟫_ℂ

def reached (t : T) (c : EigSys D) (k : ℕ) : Set (MMap (R.MY k)) :=
  Nat.rec (motive := fun k => Set (MMap (R.MY k))) (rowPart R (badPl R t) c : Set (MMap (R.MY 0)))
    (fun k P => {x | ∃ u ∈ P, IsUp R t k u x}) k

theorem reached_zero (t : T) (c : EigSys D) : reached R t c 0 = (rowPart R (badPl R t) c : Set (MMap (R.MY 0))) := rfl

theorem reached_succ (t : T) (c : EigSys D) (k : ℕ) :
    reached R t c (k + 1) = {x | ∃ u ∈ reached R t c k, IsUp R t k u x} := rfl

def StepScalar (t : T) (c : EigSys D) (k : ℕ) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c k, ∃ x, IsUp R t k u x) ∧
  ∀ u₁ ∈ reached R t c k, ∀ u₂ ∈ reached R t c k, ∀ x₁ x₂, IsUp R t k u₁ x₁ → IsUp R t k u₂ x₂ →
    ∃ a : ℂ, IsIP R t k u₁ u₂ a ∧ IsIP R t (k + 1) x₁ x₂ ((Λ : ℂ) * a)

def TopScalar (t : T) (c : EigSys D) (Λ : ℝ) : Prop :=
  (∀ u ∈ reached R t c (D.R.m - 1), ∃ x, IsUpTop R t u x) ∧
  ∀ u₁ ∈ reached R t c (D.R.m - 1), ∀ u₂ ∈ reached R t c (D.R.m - 1), ∀ x₁ x₂, IsUpTop R t u₁ x₁ → IsUpTop R t u₂ x₂ →
    ∃ a : ℂ, IsIP R t (D.R.m - 1) u₁ u₂ a ∧ ⟪x₁, x₂⟫_ℂ = (Λ : ℂ) * a

def ScalarsWith (κ : ℕ → ℝ) : Prop :=
  ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
    (∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B) ∧
    ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
      (∀ k, k + 1 < D.R.m → ∃ l, IsLValue R t B (k + 1) l ∧ StepScalar R t c k (κ (k + 1) * l)) ∧
      ∃ l, IsLValue R t B D.R.m l ∧ TopScalar R t c (κ D.R.m * l)

def Scalars : Prop := ∃ κ : ℕ → ℝ, (∀ j, 1 ≤ j → j ≤ D.R.m → 0 < κ j) ∧ ScalarsWith R κ

def IsLabelOf {g : ℕ} [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {κ : Type} [CommRing κ] (e : ZMod g ≃+* κ)
    (x : (ZMod g)ˣ) (χ : κˣ →* ℂˣ) : Prop :=
  ∀ z : (ZMod g)ˣ, GlobalTheory.GLq.thetaOf L 1 (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) x) (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) z) =
    ((χ (Units.map (e : ZMod g →+* κ).toMonoidHom z) : ℂˣ) : ℂ)

def GoodTypes : Prop :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  ∃ (eR : G ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg)
    (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (L : ∀ k : Fin 2, GlobalTheory.GLq.LabelDatum (D.host.g k)),
    (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧
    (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) ∧
    (∀ k, (L k).teich = D.ntypes.teichC k ∧ ∀ f, D.ntypes.eSer k f = GlobalTheory.GLq.eSerC (L k) D.R.r f) ∧
    ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (j : Fin D.R.m),
      IsLabelOf (L kv.1) (iso kv) (D.nd.chiT kv.1 kv.2 j) (R.chi ((j : ℕ) + 1) (plg kv).1) ∨
      IsLabelOf (L kv.1) (iso kv) (D.nd.chiT kv.1 kv.2 j) (R.chi ((j : ℕ) + 1) (plg kv).1)⁻¹

structure HidaSetting : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  chain : R.IsChain
  thP : R.IsThP
  scal : R.IsScal F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  good : GoodTypes R

def OneStepAt : Prop := HidaSetting R F → Scalars R

def OneStep : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), OneStepAt R F

theorem rowPart_mono {Sb Sb' : Finset (HeightOneSpectrum (𝓞 D.host.F))} (h : Sb ⊆ Sb') (c : EigSys D) :
    rowPart R Sb c ≤ rowPart R Sb' c := by
  refine inf_le_inf_right _ fun u hu => ?_
  rw [partDual, mem_partFull] at hu ⊢
  refine ⟨hu.1, fun P d Rp hR => hu.2 P d Rp ?_⟩
  obtain ⟨e, f, ϖ, α, h1, h2⟩ := hR
  exact ⟨e, f, ϖ, α, fun v hv => h1 v (h hv), h2⟩

theorem GoodTypes.record {R : RealDat D A Ks} (h : GoodTypes R) : R.grp_record := by
  obtain ⟨eR, plg, iso, -, h1, h2, h3, -⟩ := h
  exact ⟨eR, plg, iso, h1, h2, h3⟩

theorem IsLValue.unique {R : RealDat D A Ks} {t : T} {B : GlobalTheory.LFun.Fam D.host.E} {j : ℕ} {l l' : ℝ}
    (h : IsLValue R t B j l) (h' : IsLValue R t B j l') : l = l' := by
  exact_mod_cast h.2.2.symm.trans h'.2.2

theorem IsUpTop.unique {R : RealDat D A Ks} {t : T} {u : MMap (R.MY (D.R.m - 1))} {x x' : (R.HX t).H}
    (v : (R.MY (D.R.m - 1)).Vec) (hv : ∏ τ, ⟪(v τ : (R.MY (D.R.m - 1)).H τ), (v τ : (R.MY (D.R.m - 1)).H τ)⟫_ℂ ≠ 0)
    (h : IsUpTop R t u x) (h' : IsUpTop R t u x') : x = x' :=
  ext_inner_right ℂ fun y => hasPeterssonInner_unique _ _ _ _ _ v hv (h y) (h' y)

end GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars

end
end

