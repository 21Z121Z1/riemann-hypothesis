import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.IndefiniteReal.IsWeilDatum
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxCutE
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

section CutE

variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

def LiftsEig (P : Subgroup G) (ψ : P →* Kˣ) (C : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop) : Prop :=
  ∀ j, (A.fam.L j A.fam.μ0).Z0 (A.fam.lvlA P ψ) (X.Zl j A.fam.μ0) =
    (A.fam.L j A.fam.μ0).inV0 (A.fam.lvlA P ψ) (Formalism.L2.Col.eigSum (A.fam.L j A.fam.μ0).op (C j))

def LiftsTyp (C : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop) : Prop :=
  ∀ j x, C j x → A.fam.IsType (A.fam.L j A.fam.μ0) (A.fam.tr j) x

def HeckeRatR : Prop := (A.fam.R A.fam.μ0).OkH

def HeckeRatL : Prop := ∀ j : Fin m, (A.fam.L j A.fam.μ0).OkH

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

def CutProviso : Prop :=
  ∀ (s : ℕ) (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop),
    A.fam.Ok s → HeckeRatL A → LiftsEig A X P0 ψ0 C0 → LiftsEig A X P1 ψ1 C1 →
      ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Proviso

def CutTypes : Prop :=
  ∀ (s : ℕ) (C0 C1 : ∀ j : Fin m, ((A.fam.L j A.fam.μ0).Pl × ℕ → K) → Prop),
    A.fam.Ok s → A.fam.TypesSep → X.zs.Stable → LiftsEig A X P0 ψ0 C0 → LiftsEig A X P1 ψ1 C1 →
      LiftsTyp A C0 → LiftsTyp A C1 → ∀ b, (lv (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).Types

def CutPartsOrth : Prop :=
  ∀ s : ℕ, A.fam.Ok s → HeckeRatR A → X.zs.Stable → ∀ b, X.PartsOrth b (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc)

end CutE

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxToPkgFamIn
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def crdOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : Crd A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) where
  toR Zs b t := match b with
    | false => (A.fam.R t).toF (A.fam.lvl P0 ψ0) (Zs.Z t)
    | true => (A.fam.R t).toF (A.fam.lvl P1 ψ1) (Zs.Z t)
  toL Zs b j t := match b with
    | false => (A.fam.L j t).toF (A.fam.lvlA P0 ψ0) (Zs.Zl j t)
    | true => (A.fam.L j t).toF (A.fam.lvlA P1 ψ1) (Zs.Zl j t)

def cxPkgF (A : FamIn K G Pl0 T m) {s : ℕ} (hOk : A.fam.Ok s) (hsep : A.fam.TypesSep)
    (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) (X : CxData A.fam.amb)
    (Y : CxData.CxCol (fc := faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) X) (C CH : ℝ)
    (hL : X.CxLinks (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) Y C CH) :
    IndefPkg A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH :=
  cxPkg _ X Y C CH hL fun b => match b with
    | false => A.side_WF hOk P0 ψ0 X.zs hL.stable hL.inBlock hsep
    | true => A.side_WF hOk P1 ψ1 X.zs hL.stable hL.inBlock hsep

end Concrete

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.InjectiveDecompositionAction
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.InjectiveDecompositionAction

variable {D : D7}

def FirstPropositionFrame (D : D7) : Subgroup (AE D)ˣ where
  carrier := {x | (x : AE D) * cA D (x : AE D) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    calc (a : AE D) * b * (cA D a * cA D b) = (a * cA D a) * (b * cA D b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : ((a⁻¹ : (AE D)ˣ) : AE D) * a = 1 := by simp
    have h2 : cA D ((a⁻¹ : (AE D)ˣ) : AE D) * cA D (a : AE D) = 1 := by rw [← map_mul, h1, map_one]
    calc ((a⁻¹ : (AE D)ˣ) : AE D) * cA D ((a⁻¹ : (AE D)ˣ) : AE D)
        = ((a⁻¹ : (AE D)ˣ) : AE D) * cA D ((a⁻¹ : (AE D)ˣ) : AE D) * ((a : AE D) * cA D (a : AE D)) := by
          rw [ha, mul_one]
      _ = (((a⁻¹ : (AE D)ˣ) : AE D) * a) * (cA D ((a⁻¹ : (AE D)ˣ) : AE D) * cA D (a : AE D)) := by ring
      _ = 1 := by rw [h1, h2, one_mul]

def SuppAtU (D : D7) (e : AE D) (x : (AE D)ˣ) : Prop :=
  (e + cA D e) * ((x : AE D) - 1) = (x : AE D) - 1

def SvNSchur (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ T : Module.End ℂ (Hth ψ V W),
    (∀ w₀ (Φ Φ' : Hth ψ V W), (Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W w₀ Φ →
      (T Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W w₀ (T Φ)) →
    (∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratL V W) 𝓕 μ → ∀ Φ : Hth ψ V W,
        ∫⁻ w in 𝓕, ‖(T Φ : WA V W → ℂ) w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖(Φ : WA V W → ℂ) w‖ₑ ^ 2 ∂μ) →
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ Φ : Hth ψ V W, T Φ = c • Φ

def ThetaNZ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∃ Φ : Hth ψ V W, (Φ : WA V W → ℂ) 0 ≠ 0

def SplitFormsNZ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Prop :=
  ∀ e, IsSplitIdem D e → ∃ ℓ : Hth ψ V W →ₗ[ℂ] ℂ,
    (∀ u : WA V W, (∀ i j, cA D e * u i j = u i j) →
      ∀ Φ Φ' : Hth ψ V W, (Φ' : WA V W → ℂ) = Heisenberg₂ ψ V W u Φ → ℓ Φ' = ℓ Φ) ∧
    ∃ Φ, ℓ Φ ≠ 0

def CharDet (V : HSp D) : Prop :=
  ∀ c : GA D V →* Circle, Continuous c →
    ∃ lam : FirstPropositionFrame D →* Circle, Continuous lam ∧
      ∀ (g : GA D V) (x : FirstPropositionFrame D), (((x : (AE D)ˣ)) : AE D) = (mt V g).det → c g = lam x

def SecondCharacterFact (D : D7) : Prop :=
  ∀ lam : FirstPropositionFrame D →* Circle, Continuous lam →
    (∀ (x : FirstPropositionFrame D) (q : D.host.E), (((x : (AE D)ˣ)) : AE D) = incA D q → lam x = 1) →
    (∀ e, IsSplitIdem D e → ∀ x : FirstPropositionFrame D, SuppAtU D e (x : (AE D)ˣ) → lam x = 1) →
    ∀ x, lam x = 1

def ConsequenceOfAdmissibleConstants : Prop :=
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W)),
    SvNSchur ψ V W → ThetaNZ ψ V W → SplitFormsNZ ψ V W → CharDet V → CharDet W → SecondCharacterFact D →
    IsWeilDatum ψ V W χ χ' ω → IsWeilDatum ψ V W χ χ' ω' → ω = ω'

end Formalism.IndefR.InjectiveDecompositionAction

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

namespace Formalism.IndefR.RationalEmbedding

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

abbrev inst : Formalism.MainNotions.S.AutInst := Formalism.L2.SG.InstExistsPf.instOf D

def iota : GA D (D.sp.Y 0) ≃ₜ* (inst D).GA :=
  (Formalism.L2.SG.AdBridge.toHA (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1).symm

theorem iota_symm_isBridge : Formalism.L2.SG.AdBridge.IsBridge (inst D) (iota D).symm :=
  Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) (Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)).1

theorem iota_rat (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iota D g ∈ (inst D).GFset := by
  have hS := Formalism.L2.SG.Closed.adelic_isomorphism_statement (inst D)
  have hb := Formalism.L2.SG.AdBridge.toHA_isBridge (inst D) hS.1
  have hGF := hS.2.1 _ hb
  have hg : Formalism.L2.SG.AdBridge.toHA (inst D) hS.1 (iota D g) = g :=
    (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).apply_symm_apply g
  rw [← (Formalism.L2.SG.AdBridge.toHA (inst D) hS.1).injective.mem_set_image (a := iota D g)
    (s := (inst D).GFset), hGF, hg]
  exact Iff.rfl

end Formalism.IndefR.RationalEmbedding

end
end

