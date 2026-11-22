import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0361
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0363
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GlobalLocalFactorization
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0303
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearMapVaryPureTensorFactorSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.VarySplitFactor.exists_linearMap_pure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x : Place D → WO S T → ℂ) (f : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (Φ₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v))), ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → x (.inl v) = Tm (onHalf φ S T BS BT e Φ₀.1) → ∃ T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ] (WO S T → ℂ), T₀ Φ₀ = f ∧ (∀ u, ∃ x' : Place D → WO S T → ℂ, (∀ p, p ≠ .inl v → x' p = x p) ∧ x' (.inl v) = Tm (onHalf φ S T BS BT e u.1) ∧ IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (T₀ u)) ∧ ∀ g h, gAt S (.inl v) g = g → gAt T (.inl v) h = h → ∀ a b, IsDetAt e S g a → IsDetAt e T h b → ∀ u u' : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)), u'.1 = linOm v (grpCo φ S BS g) (grpCo φ T BT h) u.1 → om (g, h) (T₀ u) = ((splitFacO χS χT a b : Circle) : ℂ) • T₀ u' := by
  intro D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW _hθ hB hC x f hx v φ e he BS BT Φ₀ Tm hT hxv
  classical
  have hcoord := GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hB.2.2.1 hB.2.2.2.1 v φ e he BS BT
  have hsplit := GlobalTheory.SplitCoordModel.bijOn_and_om_linear D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕
    hW hB hC v e e he.1 he.2.1 (Or.inl rfl) T.rank S.rank (mapCo φ S T BS BT) hcoord.1 Tm hT
  have honHalf : ∀ Φ, onHalf φ S T BS BT e Φ = pull e (mapCo φ S T BS BT) Φ := fun Φ => rfl
  let xf : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →
      Place D → WO S T → ℂ :=
    fun u => Function.update x (.inl v) (Tm (onHalf φ S T BS BT e u.1))
  have hres : ∀ u, IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (xf u) := by
    intro u
    refine ⟨fun p => ?_, ?_⟩
    · by_cases hp : p = .inl v
      · subst hp
        simp only [xf, Function.update_self]
        rw [honHalf]
        exact hsplit.1.mapsTo u.2
      · simp only [xf, Function.update_of_ne hp]
        exact hx.1.1 p
    · apply (hx.1.2.union (Set.finite_singleton (Sum.inl v : Place D))).subset
      intro p hp
      by_cases h : p = .inl v
      · exact Or.inr h
      · left
        simpa [xf, Function.update_of_ne h] using hp
  have hEU := fun u => GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕
    hB hC (xf u) (hres u)
  let F := fun u => (hEU u).exists.choose
  have hF : ∀ u, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (xf u) (F u) :=
    fun u => (hEU u).exists.choose_spec
  have huniq : ∀ y f1 f2, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f1 →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y f2 → f1 = f2 := fun y f1 f2 h1 h2 =>
    (GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC y h1.1).unique
      h1 h2
  have hlin := (GlobalTheory.PureLinear.isPure_linear_and_dRho D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hC).1
  have hscale : ∀ (y z : Place D → WO S T → ℂ) (g : WO S T → ℂ) (q : Place D) (c : ℂ),
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → z p = y p) → z q = c • y q →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • g) := by
    intro y z g q c hy hz hzq
    have := hlin y y z g g q (c - 1) hy hy (fun _ _ => rfl) hz
      (by rw [hzq, sub_smul, one_smul, sub_add_cancel])
    rwa [sub_smul, one_smul, sub_add_cancel] at this
  have hOnAdd : ∀ (Φ Ψ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ),
      onHalf φ S T BS BT e (Φ + Ψ) = onHalf φ S T BS BT e Φ + onHalf φ S T BS BT e Ψ := by
    intro Φ Ψ
    funext t
    simp only [onHalf, Pi.add_apply]
    split_ifs <;> simp
  have hOnSmul : ∀ (c : ℂ) (Φ : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) → ℂ),
      onHalf φ S T BS BT e (c • Φ) = c • onHalf φ S T BS BT e Φ := by
    intro c Φ
    funext t
    simp only [onHalf, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  let T₀ : GlobalTheory.SplitWeil.SB (Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v)) →ₗ[ℂ]
      (WO S T → ℂ) :=
    { toFun := F
      map_add' := by
        intro u u'
        have hz := hlin (xf u) (xf u') (xf (u + u')) (F u) (F u') (.inl v) 1 (hF u) (hF u')
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (by
            simp only [xf, Function.update_self, Submodule.coe_add]
            rw [hOnAdd, map_add, one_smul])
        rw [one_smul] at hz
        exact huniq _ _ _ (hF (u + u')) hz
      map_smul' := by
        intro c u
        have hz := hscale (xf u) (xf (c • u)) (F u) (.inl v) c (hF u)
          (fun p hp => by simp only [xf, Function.update_of_ne hp])
          (by
            simp only [xf, Function.update_self, Submodule.coe_smul]
            rw [hOnSmul, map_smul])
        exact huniq _ _ _ (hF (c • u)) hz }
  have hT₀ : ∀ u, T₀ u = F u := fun u => rfl
  refine ⟨T₀, ?_, fun u => ⟨xf u, fun p hp => by simp only [xf, Function.update_of_ne hp],
    by simp only [xf, Function.update_self], hF u⟩, ?_⟩
  · rw [hT₀]
    have hxx : xf Φ₀ = x := by
      simp only [xf]
      rw [← hxv]
      exact Function.update_eq_self _ _
    exact huniq _ _ _ (hF Φ₀) (hxx ▸ hx)
  · intro g h hg hh a b ha hb u u' hu'
    have laws := GlobalTheory.PlaceComponent.gAt_laws D
    have hgp : ∀ p, p ≠ Sum.inl v → gAt S p g = 1 := fun p hp => by
      rw [← hg]; exact ((laws.1 S (.inl v) g).2.2 p hp)
    have hhp : ∀ p, p ≠ Sum.inl v → gAt T p h = 1 := fun p hp => by
      rw [← hh]; exact ((laws.1 T (.inl v) h).2.2 p hp)
    have hsupp : ∀ (V : HSp D) (k : GA D V), gAt V (.inl v) k = k → SuppAt e V k := by
      intro V k hk i j
      have hm := (laws.1 V (.inl v) k).1
      rw [hk] at hm
      have key : Formalism.L2.Theta.mt V k - 1 =
          idem D (Sum.inl v) • (Formalism.L2.Theta.mt V k - 1) := by
        conv_lhs => rw [hm]
        rw [smul_sub, sub_smul, one_smul]
        abel
      rw [he.2.1]
      have := congrFun (congrFun key i) j
      rw [Matrix.smul_apply, smul_eq_mul] at this
      exact this.symm
    have hom := GlobalTheory.PlaceTensor.PureOm.isPure_om D ψ θ S T χS χT om sS sT ΛS ΛT f₀ μ 𝓕 hW hB hC
      (xf u) (F u) (hF u) g h
    have hact := hsplit.2 g h (hsupp S g hg) (hsupp T h hh) a b ha hb
      (grpCo φ S BS g) (grpCo φ T BT h) (hcoord.2 g h) u.1 u.2
    have hz := hscale (xf u') (fun p => om (gAt S p g, gAt T p h) (xf u p)) (F u') (.inl v)
      ((splitFacO χS χT a b : Circle) : ℂ) (hF u')
      (fun p hp => by
        simp only [xf, Function.update_of_ne hp, hgp p hp, hhp p hp]
        have h11 : ((1 : GA D S), (1 : GA D T)) = 1 := rfl
        rw [h11, map_one]; rfl)
      (by
        simp only [xf, Function.update_self, hg, hh]
        rw [honHalf, hact, honHalf, hu'])
    exact huniq _ _ _ hom hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsMovedNotProportional
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open MeasureTheory ValuativeRel Matrix IsLocalRing
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.StandardLatticeStabilizers

namespace GlobalTheory.PlaceCompare.Spherical

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n'' n' n : Type} [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n]

def sph (α : kˣ) (n'' n' n : Type) [Fintype n''] [Fintype n'] [Fintype n] : Matrix n' n'' k × Matrix n n' k → ℂ :=
  tens (ind (stdL k n'') (scal α (stdL k n'))) (ind (stdL k n') (scal α (stdL k n)))

def moved (g : GL n' k) (Ξ : Matrix n' n'' k × Matrix n n' k → ℂ) (x : Matrix n' n'' k × Matrix n n' k) : ℂ :=
  Ξ ((g⁻¹ : GL n' k).val * x.1, x.2 * g.val)

def homLat (α : kˣ) (n'' n' n : Type) : AddSubgroup (Matrix n' n'' k × Matrix n n' k) where
  carrier := {x | (∀ r s, ((α⁻¹ : kˣ) : k) * x.1 r s ∈ 𝒪[k]) ∧ ∀ r s, ((α⁻¹ : kˣ) : k) * x.2 r s ∈ 𝒪[k]}
  add_mem' h h' := ⟨fun r s => by simpa [mul_add] using add_mem (h.1 r s) (h'.1 r s),
    fun r s => by simpa [mul_add] using add_mem (h.2 r s) (h'.2 r s)⟩
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  neg_mem' h := ⟨fun r s => by simpa using h.1 r s, fun r s => by simpa using h.2 r s⟩

end Local

def GoodMoved : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k Circle) (ν : Measure k) (α α' : kˣ), HasConductor ψ (α * α') → IsUnitVol ν →
    ∀ (n'' n' n : Type) [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n] (σ j : ℕ),
      Even j →
      let Λ₀ := mono (2 * σ + 1 + 1 + 1) (stdL k n'') (idl α α' (σ + 2 + j / 2) j)
      let Λ₁ := mono (2 * σ + 1 + 1) (stdL k n') (idl α α' (σ + 2 + j / 2) (j + 1))
      let Λ₂ := mono (2 * σ + 1) (stdL k n) (idl α α' (σ + 2 + j / 2) (j + 1 + 1))
      ∃ e : ℤ, (valuation k (α : k) = 1 → valuation k (α' : k) = 1 → e = 0) ∧ ∀ μ₁ μ₂, IsUnram μ₁ → IsUnram μ₂ →
        OneCell ψ ν σ μ₁ μ₂ (ind Λ₀ (scal α Λ₁)) (ind Λ₁ (scal α Λ₂)) (stab Λ₁) (stab Λ₂) ∧
        ∀ L : Rec k n'' n' n σ, IsRec ψ μ₁ μ₂ (stab Λ₂) (fun _ => 1) L → ∀ g : GL n' k, GeneralLinearGroup.det g = 1 →
          CellValue ψ ν σ μ₁ μ₂ (ind Λ₀ (scal α Λ₁)) (ind Λ₁ (scal α Λ₂)) 1 (stab Λ₁) (stab Λ₂) (KO k n') (KO k n) L
            (((√(resCard k : ℝ) : ℝ) : ℂ) ^ e) (L (moved g (sph α n'' n' n)) 1)

def GoodConst : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k Circle) (ν : Measure k) (α α' : kˣ), HasConductor ψ (α * α') → IsUnitVol ν →
    ∀ (n'' n' n : Type) [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n] (σ j : ℕ),
      Even j →
      let Λ₀ := mono (2 * σ + 1 + 1 + 1) (stdL k n'') (idl α α' (σ + 2 + j / 2) j)
      let Λ₁ := mono (2 * σ + 1 + 1) (stdL k n') (idl α α' (σ + 2 + j / 2) (j + 1))
      let Λ₂ := mono (2 * σ + 1) (stdL k n) (idl α α' (σ + 2 + j / 2) (j + 1 + 1))
      ∃ r : ℝ, 0 < r ∧ (∃ e : ℤ, r = √(resCard k : ℝ) ^ e) ∧ (valuation k (α : k) = 1 → valuation k (α' : k) = 1 → r = 1) ∧
        ∀ μ₁ μ₂, IsUnram μ₁ → IsUnram μ₂ → ∀ L : Rec k n'' n' n σ, IsRec ψ μ₁ μ₂ (stab Λ₂) (fun _ => 1) L →
          CellValue ψ ν σ μ₁ μ₂ (ind Λ₀ (scal α Λ₁)) (ind Λ₁ (scal α Λ₂)) 1 (stab Λ₁) (stab Λ₂) (KO k n') (KO k n) L 1
            (L ((r : ℂ) • sph α n'' n' n) 1)

def GoodPoint : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (ψ : AddChar k Circle) (ν : Measure k) (α α' : kˣ), HasConductor ψ (α * α') → IsUnitVol ν →
    ∀ (n'' n' n : Type) [Fintype n''] [DecidableEq n''] [Fintype n'] [DecidableEq n'] [Fintype n] [DecidableEq n] (σ j : ℕ),
      Even j →
      let Λ₀ := mono (2 * σ + 1 + 1 + 1) (stdL k n'') (idl α α' (σ + 2 + j / 2) j)
      let Λ₁ := mono (2 * σ + 1 + 1) (stdL k n') (idl α α' (σ + 2 + j / 2) (j + 1))
      let Λ₂ := mono (2 * σ + 1) (stdL k n) (idl α α' (σ + 2 + j / 2) (j + 1 + 1))
      ∃ e : ℤ, (valuation k (α : k) = 1 → valuation k (α' : k) = 1 → e = 0) ∧
        dSym ψ ν σ (ind Λ₀ (scal α Λ₁)) (ind Λ₁ (scal α Λ₂)) = ((√(resCard k : ℝ) : ℝ) : ℂ) ^ e • sph α n'' n' n

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum IsDedekindDomain NumberField
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_unram_char (D : D7) (n : ℕ) :
    ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ n ∧ UnramEverywhere D χ := by
  obtain ⟨η, h1, h2, h3, -⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  refine ⟨η ^ n, ⟨?_, fun x => ?_⟩, ⟨h3.1, fun e he a => ?_⟩, fun x a b c => ?_⟩
  · have : ((η ^ n : (AE D)ˣ →* Circle) : (AE D)ˣ → Circle) = fun x => η x ^ n := by
      funext x; simp
    rw [this]
    exact h1.1.pow n
  · rw [MonoidHom.pow_apply, h1.2 x, one_pow]
  · rw [MonoidHom.pow_apply, h3.2 e he a, pow_one]
  · rw [MonoidHom.pow_apply, h2 x a b c, one_pow]

variable {c : Comm D}

def VacMid (v : VCom c) (t : Tup c) : Prop :=
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∉ v.tP) Ψ₁ →
    Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∉ v.tP) Ψ₂ →
    BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∉ v.tP) (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)

end Global

end GlobalTheory.PlaceCompare.Spherical

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FixLev
variable {D : D7}

theorem continuous_mt (V : HSp D) : Continuous (mt V) :=
  Units.continuous_val.comp continuous_subtype_val

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem map_mt_mul (q : SplitPt D k) (V : HSp D) (g h : GA D V) :
    (mt V (g * h)).map q.pr = (mt V g).map q.pr * (mt V h).map q.pr := by
  rw [GlobalTheory.SplitCut.mt_mul, Matrix.map_mul]

theorem frame_mul {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (A B : Matrix (Fin N) (Fin N) k) :
    F.γ * A * F.β * (F.γ * B * F.β) = F.γ * (A * B) * F.β := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem frame_cancel {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) {A B : Matrix Y Y k}
    (h : F.β * A * F.γ = F.β * B * F.γ) : A = B := by
  have := congrArg (fun M => F.γ * M * F.β) h
  simp only [Matrix.mul_assoc] at this
  simpa [← Matrix.mul_assoc, F.γβ] using this

theorem frame_conj {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (A : Matrix (Fin N) (Fin N) k) :
    F.β * (F.γ * A * F.β) * F.γ = A := by
  simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
  rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def locHom (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) : GA D V →* GL Y k where
  toFun g := ⟨F.γ * (mt V g).map q.pr * F.β, F.γ * (mt V g⁻¹).map q.pr * F.β,
    by rw [frame_mul, ← map_mt_mul, mul_inv_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ],
    by rw [frame_mul, ← map_mt_mul, inv_mul_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (mt V 1).map q.pr * F.β = 1
    rw [GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (mt V (g * h)).map q.pr * F.β = F.γ * (mt V g).map q.pr * F.β * (F.γ * (mt V h).map q.pr * F.β)
    rw [frame_mul, map_mt_mul])

theorem locHom_val (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    (locHom q V F g).val = F.γ * (mt V g).map q.pr * F.β := rfl

theorem locHom_spec (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    (mt V g).map q.pr = F.β * (locHom q V F g).val * F.γ := by
  rw [locHom_val, frame_conj]

theorem continuous_locHom (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) :
    Continuous (locHom q V F) := by
  have h1 : Continuous fun g : GA D V => F.γ * (mt V g).map q.pr * F.β :=
    (continuous_const.matrix_mul ((continuous_mt V).matrix_map q.cont_pr)).matrix_mul continuous_const
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  refine (h1.comp continuous_inv).congr fun g => ?_
  change F.γ * (mt V g⁻¹).map q.pr * F.β = ((locHom q V F g)⁻¹ : GL Y k).val
  rw [← map_inv, locHom_val]

end Local

theorem list_prod_single {M : Type} [Monoid M] {ι : Type} [DecidableEq ι] (f : ι → M) (i : ι)
    (hf : ∀ i', i' ≠ i → f i' = 1) : ∀ l : List ι, l.Nodup → i ∈ l → (l.map f).prod = f i
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, hl, h => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons]
    by_cases ha : a = i
    · subst ha
      rw [List.prod_eq_one fun y hy => ?_, mul_one]
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
      exact hf b fun e => hl.1 (e ▸ hb)
    · rw [hf a ha, one_mul]
      exact list_prod_single f i hf l hl.2 ((List.mem_cons.1 h).resolve_left (Ne.symm ha))

theorem map_mt_list_prod {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (V : HSp D) (l : List (GA D V)) : (mt V l.prod).map q.pr = (l.map fun g => (mt V g).map q.pr).prod := by
  induction l with
  | nil => simp [GlobalTheory.SplitCut.mt_one]
  | cons a l ih => rw [List.prod_cons, map_mt_mul, ih, List.map_cons, List.prod_cons]

theorem exists_section (V : HSp D) {n : ℕ} (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) :
    ∃ Ψ : (∀ i, GL (Y i) (k i)) → GA D V, Continuous Ψ ∧ (∀ x, Ψ x ∈ grpAt V (fun p => ∃ i, p = (q i).v)) ∧
      (∀ x i, (mt V (Ψ x)).map (q i).pr = (F i).β * (x i).val * (F i).γ) ∧
      ∀ g ∈ grpAt V (fun p => ∃ i, p = (q i).v), ∀ x,
        (∀ i, (mt V g).map (q i).pr = (F i).β * (x i).val * (F i).γ) → Ψ x = g := by
  choose gl hgc hgl hgu using fun i => GlobalTheory.T.exists_continuous_local_GL_embedding_splitPlace D (k i) (q i) V (Y i) (F i)
  have hmat : ∀ (h : Fin n → GA D V), (∀ i, SuppAt (q i).e V (h i)) → ∀ i,
      (mt V ((List.finRange n).map h).prod).map (q i).pr = (mt V (h i)).map (q i).pr := fun h hh i => by
    rw [map_mt_list_prod, List.map_map]
    exact list_prod_single (fun i' => (mt V (h i')).map (q i).pr) i
      (fun i' hi' => GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace D (k i) (k i') (q i) (q i') V (h i') (fun e => hi' (hq e).symm) (hh i'))
      _ (List.nodup_finRange n) (List.mem_finRange i)
  refine ⟨fun x => ((List.finRange n).map fun i => gl i (x i)).prod, ?_, fun x => ?_, fun x i => ?_, fun g hg x hx => ?_⟩
  · exact continuous_list_prod _ fun i _ => (hgc i).comp (continuous_apply i)
  · refine Subgroup.list_prod_mem (K := grpAt V (fun p => ∃ i, p = (q i).v)) fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem D (k i) (q i) V _ (hgl i (x i)).1 _ ⟨i, rfl⟩
  · rw [hmat (fun i => gl i (x i)) (fun i => (hgl i (x i)).1) i]
    exact (hgl i (x i)).2
  · obtain ⟨h, hh, rfl⟩ := GlobalTheory.T.unitarySupported_splitPlaces_eq_prod_local_parts D V n k q hq g hg
    show ((List.finRange n).map fun i => gl i (x i)).prod = _
    congr 1
    refine List.map_congr_left fun i _ => (hgu i (h i) (x i) (hh i) ((hmat h hh i).symm.trans (hx i))).symm

open GlobalTheory.SeeSaw GlobalTheory.StepData in

theorem fixLev_compact_open : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G → ∀ j, j < D.R.m →
    v.JG j ≤ grpAt (c.V j) (· ∈ v.gP) ∧ IsCompact (v.JG j : Set (GA D (c.V j))) ∧
    IsOpen (((v.JG j).subgroupOf (grpAt (c.V j) (· ∈ v.gP)) : Subgroup _) : Set (grpAt (c.V j) (· ∈ v.gP))) := by
  intro D c v n G hG j hj
  have ha : ∀ i, j + ((G i).s + 1 - j) = (G i).s + 1 := fun i => by have := (G i).hs; omega
  set V := c.V j
  have hP : (· ∈ v.gP) = fun p => ∃ i, p = (G i).q.v := funext fun p => propext (hG.places p)
  have hMat : ∀ i a ha g x, (G i).Mat j a ha g x ↔ x = locHom (G i).q V ((G i).FY j a ha) g := fun i a ha g x => by
    constructor
    · intro h
      exact Units.ext (frame_cancel ((G i).FY j a ha) (h.symm.trans (locHom_spec _ _ _ g)))
    · rintro rfl
      exact locHom_spec _ _ _ g
  let Js : ∀ i, Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((G i).s + 1 - j)) (G i).k) := fun i =>
    (((G i).S.T (Fin D.R.t)).lev j _ (ha i)).J
  have hJ : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (Js i) := fun i =>
    GlobalTheory.UnfoldedEntries.isCO_lev (T := (G i).S.T (Fin D.R.t)) (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _) j _ (ha i)
  have hmem : ∀ g, g ∈ v.JG j ↔ g ∈ grpAt V (· ∈ v.gP) ∧ ∀ i, locHom (G i).q V ((G i).FY j _ (ha i)) g ∈ Js i := by
    intro g
    rw [hG.lev j hj g]
    refine and_congr_right fun _ => ⟨fun H i => H i _ (ha i) _ ((hMat _ _ _ _ _).2 rfl), fun H i a ha' x hx => ?_⟩
    have e : a = (G i).s + 1 - j := by omega
    subst e
    rw [(hMat _ _ _ _ _).1 hx]
    exact H i
  refine ⟨fun g hg => ((hmem g).1 hg).1, ?_, ?_⟩
  · obtain ⟨Ψ, hc, hin, hloc, huniq⟩ := exists_section V (fun i => (G i).k) (fun i => (G i).q) hG.inj
      (fun i => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((G i).s + 1 - j)) (fun i => (G i).FY j _ (ha i))
    have himg : (v.JG j : Set (GA D V)) = Ψ '' Set.pi Set.univ fun i => (Js i : Set _) := by
      ext g
      constructor
      · intro hg
        obtain ⟨h1, h2⟩ := (hmem g).1 hg
        refine ⟨fun i => locHom (G i).q V ((G i).FY j _ (ha i)) g, fun i _ => h2 i, huniq g (hP ▸ h1) _ fun i => ?_⟩
        exact locHom_spec _ _ _ g
      · rintro ⟨x, hx, rfl⟩
        refine (hmem _).2 ⟨hP ▸ hin x, fun i => ?_⟩
        have e : locHom (G i).q V ((G i).FY j _ (ha i)) (Ψ x) = x i :=
          Units.ext (frame_cancel ((G i).FY j _ (ha i)) ((locHom_spec _ _ _ _).symm.trans (hloc x i)))
        rw [e]
        exact hx i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hJ i).2).image hc
  · have hset : (((v.JG j).subgroupOf (grpAt V (· ∈ v.gP)) : Subgroup _) : Set (grpAt V (· ∈ v.gP))) =
        ⋂ i, (fun g : grpAt V (· ∈ v.gP) => locHom (G i).q V ((G i).FY j _ (ha i)) g.1) ⁻¹' (Js i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact ((hmem g.1).trans (and_iff_right g.2))
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hJ i).1.preimage ((continuous_locHom _ _ _).comp continuous_subtype_val)

end GlobalTheory.FixLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → FlatFB D := by
  first | exact @GlobalTheory.LocMod.flatFB_holds | exact GlobalTheory.LocMod.flatFB_holds | (intros; apply GlobalTheory.LocMod.flatFB_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiProductMapHaarFiniteOnCompactsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiProductMap_haar_finiteOnCompacts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → ρ < c → ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ m : Measure (GL n k), m.IsHaarMeasure → IsFiniteMeasureOnCompacts (((m.prod (volN ν n c (ρ + 1))).prod (Measure.pi fun _ : n => ν)).map (prodRFJ ρ)) := by
  first | exact @GlobalTheory.HaarR.finite_on_compacts_prodRFJ | exact GlobalTheory.HaarR.finite_on_compacts_prodRFJ | (intros; apply GlobalTheory.HaarR.finite_on_compacts_prodRFJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealGeneratedByOneAlmostEverywhereStatement
section
open Formalism.BasicNotions IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_generated_by_one_almostEverywhere : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 → ∃ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ v ∉ S, ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ ((c : D.host.F) : D.host.E) ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = (o : D.host.E) := by
  first | exact @GlobalTheory.IdeleGen.aeGen | exact GlobalTheory.IdeleGen.aeGen | (intros; apply GlobalTheory.IdeleGen.aeGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocalGeneratorAtBasePrimeStatement
section
open Formalism.BasicNotions IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionalIdeal_localGenerator_at_basePrime : ∀ (D : D7) (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), I ≠ 0 → ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ a : D.host.E, a ≠ 0 ∧ ∃ c : 𝓞 D.host.F, c ∉ v.asIdeal ∧ ((c : D.host.F) : D.host.E) * a ∈ I ∧ ∀ b ∈ I, ∃ o : 𝓞 D.host.E, ((c : D.host.F) : D.host.E) * b = a * (o : D.host.E) := by
  first | exact @GlobalTheory.fracIdeal_locGen | exact GlobalTheory.fracIdeal_locGen | (intros; apply GlobalTheory.fracIdeal_locGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodMajorantLevelConjUnitaryAdelicMaximalCompactStatement
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → ∀ l : Lvl T, l.Good → HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) ∧ ∃ q : stab d, ConjBy (q : GA D T) l.K (Kmax T b) := by
  first | exact @GlobalTheory.RegSch.good_level_conj_stab | exact GlobalTheory.RegSch.good_level_conj_stab | (intros; apply GlobalTheory.RegSch.good_level_conj_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GoodPositionSplitLinesReadCompletionsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPosition_splitLines_read_completions_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (x : Pl D), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) ∧ IsSelfDualC (c.V j) (N j) ∧ latV (c.V j) (N j) (· = x) = latV (c.V j) (v.N j) (· = x)) → (∀ j ρ h, IsSelfDualC _ (o.M j ρ h) ∧ IsSelfDualC _ (M j ρ h) ∧ latV _ (M j ρ h) (· = x) = latV _ (o.M j ρ h) (· = x)) → (GoodAt v o x → GoodAt { v with N := N } { o with M := M } x) ∧ (SplitAt v o x → SplitAt { v with N := N } { o with M := M } x) := by
  first | exact @GlobalTheory.LocCongr.goodAt_splitAt_congr | exact GlobalTheory.LocCongr.goodAt_splitAt_congr | (intros; apply GlobalTheory.LocCongr.goodAt_splitAt_congr <;> assumption)
end

