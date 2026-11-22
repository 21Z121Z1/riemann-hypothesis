import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0795
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0002
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0005
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Development.WeilBound.CoreStatements.LocalThetaKernels.Bundle0003
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0004
import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair
import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairU
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0001
import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0007
import Development.WeilBound.ThetaLifts.CartanFactorisation.KillInf
import Development.WeilBound.ThetaLifts.Reductions.ArchimedeanMatchedMapsCompare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0798
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedDisintegrationComposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0648
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureExtensionByScalar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0423
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairFirstStep
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue.TensorOne

theorem mem_of_separating {κ V Y : Type} [AddCommGroup V] [Module ℂ V] (D : Submodule ℂ (κ → ℂ))
    (hD : FiniteDimensional ℂ D) (s : κ → V) (ev : Y → V →ₗ[ℂ] ℂ)
    (hsep : ∀ v, (∀ y, ev y v = 0) → v = 0) (hs : ∀ y, (fun k => ev y (s k)) ∈ D) (L : V →ₗ[ℂ] ℂ) :
    (fun k => L (s k)) ∈ D := by
  classical
  by_contra hl
  let l : κ → ℂ := fun k => L (s k)
  let D' : Submodule ℂ (κ → ℂ) := D ⊔ Submodule.span ℂ {l}
  have : FiniteDimensional ℂ D' := Submodule.finiteDimensional_sup _ _
  have hlD' : l ∈ D' := Submodule.mem_sup_right (Submodule.mem_span_singleton_self l)
  have hDD' : ∀ w ∈ D, w ∈ D' := fun w hw => Submodule.mem_sup_left hw
  let D0 : Submodule ℂ D' := D.comap D'.subtype
  have hnot : (⟨l, hlD'⟩ : D') ∉ D0 := hl
  obtain ⟨f, hfl, hf0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hf0' : ∀ w (hw : w ∈ D), f ⟨w, hDD' w hw⟩ = 0 := fun w hw => by
    have : f ⟨w, hDD' w hw⟩ ∈ D0.map f := Submodule.mem_map_of_mem (show (⟨w, hDD' w hw⟩ : D') ∈ D0 from hw)
    rw [hf0] at this
    exact (Submodule.mem_bot ℂ).1 this
  let e : κ → Module.Dual ℂ D' := fun k => (LinearMap.proj k).comp D'.subtype
  have hspan : Submodule.span ℂ (Set.range e) = ⊤ := by
    have hco : (Submodule.span ℂ (Set.range e)).dualCoannihilator = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      refine Subtype.ext (funext fun k => ?_)
      exact hw (e k) (Submodule.subset_span ⟨k, rfl⟩)
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range e))
    rw [hco] at this
    rw [← this]
    simp
  have hfm : f ∈ Submodule.span ℂ (Set.range e) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hfm
  have hval : ∀ w : D', f w = ∑ k ∈ c.support, c k * w.1 k := fun w => by
    rw [← hc]
    simp [Finsupp.sum, e, LinearMap.sum_apply]
  let A : V := ∑ k ∈ c.support, c k • s k
  have hA : A = 0 := hsep A fun y => by
    have := hf0' _ (hs y)
    rw [hval] at this
    simpa [A, map_sum] using this
  apply hfl
  have : f ⟨l, hlD'⟩ = L A := by
    rw [hval]
    simp [A, map_sum, l]
  rw [this, hA, map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem sl₁_eq {F : H E a b → ℂ} {m₂ : GA E b} {φ : Sm E a} (h : φ.1 = fun x => F (x, m₂)) : sl₁ F m₂ = φ := by
  have hex : ∃ φ : Sm E a, φ.1 = fun x => F (x, m₂) := ⟨φ, h⟩
  unfold sl₁
  rw [dif_pos hex]
  exact Subtype.ext (hex.choose_spec.trans h.symm)

theorem ap₁_prod (T : Sm E a →ₗ[ℂ] Sm E a) (φ₁ : Sm E a) (φ₂ : Sm E b) :
    ap₁ T (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) = fun x => (T φ₁).1 x.1 * φ₂.1 x.2 := by
  funext x
  have e : sl₁ (fun x : H E a b => φ₁.1 x.1 * φ₂.1 x.2) x.2 = φ₂.1 x.2 • φ₁ :=
    sl₁_eq (funext fun y => by
      show φ₂.1 x.2 * φ₁.1 y = φ₁.1 y * φ₂.1 x.2
      ring)
  simp only [ap₁, e, map_smul]
  show φ₂.1 x.2 * (T φ₁).1 x.1 = _
  ring

theorem translate_mem {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} (hU : IsStable U₁) {F : H E a b → ℂ}
    (hF : F ∈ pairSpace U₁ U₂) (g : Hf E a b) :
    (fun y => F (y * finH g)) ∈ pairSpace U₁ (⊤ : Submodule ℂ (Sm E b)) := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ₁, h₁, φ₂, -, rfl⟩ := hG
    exact Submodule.subset_span ⟨act (.fin g.1) φ₁, hU _ _ h₁, act (.fin g.2) φ₂, trivial, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add G G' _ _ h h' => exact Submodule.add_mem _ h h'
  | smul c G _ h => exact Submodule.smul_mem _ c h

section Slices

variable {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)}

theorem sl_mem (hS : PairSlices) {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (m : GA E b) : sl₁ F m ∈ U₁ :=
  ((hS E a b U₁ U₂ F hF).1 m).1

theorem sl_val (hS : PairSlices) {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (m : GA E b) (y : GA E a) :
    (sl₁ F m).1 y = F (y, m) :=
  congrFun ((hS E a b U₁ U₂ F hF).1 m).2 y

theorem ap₁_add (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) {F G : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂)
    (hG : G ∈ pairSpace U₁ U₂) : ap₁ T (F + G) = ap₁ T F + ap₁ T G := by
  funext x
  have e : sl₁ (F + G) x.2 = sl₁ F x.2 + sl₁ G x.2 :=
    sl₁_eq (funext fun y => by
      show (sl₁ F x.2).1 y + (sl₁ G x.2).1 y = F (y, x.2) + G (y, x.2)
      rw [sl_val hS hF, sl_val hS hG])
  simp only [ap₁, e, map_add, Pi.add_apply]
  rfl

theorem ap₁_smul (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (c : ℂ) :
    ap₁ T (c • F) = c • ap₁ T F := by
  funext x
  have e : sl₁ (c • F) x.2 = c • sl₁ F x.2 :=
    sl₁_eq (funext fun y => by
      show c * (sl₁ F x.2).1 y = c * F (y, x.2)
      rw [sl_val hS hF])
  simp only [ap₁, e, map_smul, Pi.smul_apply]
  rfl

theorem ap₁_zero (T : Sm E a →ₗ[ℂ] Sm E a) : ap₁ T (0 : H E a b → ℂ) = 0 := by
  funext x
  have e : sl₁ (0 : H E a b → ℂ) x.2 = 0 := sl₁_eq rfl
  simp only [ap₁, e, map_zero]
  rfl

theorem ap₁_sum (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) {κ : Type} (s : Finset κ) (G : κ → H E a b → ℂ)
    (hG : ∀ k ∈ s, G k ∈ pairSpace U₁ U₂) : ap₁ T (∑ k ∈ s, G k) = ∑ k ∈ s, ap₁ T (G k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ap₁_zero T
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      ap₁_add hS T (hG k (Finset.mem_insert_self k s))
        (Submodule.sum_mem _ fun j hj => hG j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hG j (Finset.mem_insert_of_mem hj)]

theorem ap₁_mem (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) {U₁' : Submodule ℂ (Sm E a)}
    (hT : ∀ ψ ∈ U₁, T ψ ∈ U₁') {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) : ap₁ T F ∈ pairSpace U₁' U₂ := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hG
    rw [ap₁_prod]
    exact Submodule.subset_span ⟨T φ₁, hT _ h₁, φ₂, h₂, rfl⟩
  | zero => rw [ap₁_zero]; exact Submodule.zero_mem _
  | add G G' hG hG' h h' => rw [ap₁_add hS T hG hG']; exact Submodule.add_mem _ h h'
  | smul c G hG h => rw [ap₁_smul hS T hG]; exact Submodule.smul_mem _ c h

theorem ap₁_mul (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) (hT : ∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ))
    {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (o : Op E a) (g₁ : GA E a) (g₂ : GA E b)
    (ho : ∀ (ψ : Sm E a) y, (act o ψ).1 y = ψ.1 (y * g₁)) (x : H E a b) :
    ap₁ T F (x * (g₁, g₂)) = (T (act o (sl₁ F (x.2 * g₂)))).1 x.1 := by
  rw [hT o _ (sl_mem hS hF _), ho]
  rfl

theorem ap₁_translate (hS : PairSlices) (T : Sm E a →ₗ[ℂ] Sm E a) (hT : ∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ))
    {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (o : Op E a) (g₁ : GA E a) (g₂ : GA E b)
    (ho : ∀ (ψ : Sm E a) y, (act o ψ).1 y = ψ.1 (y * g₁)) (x : H E a b) :
    ap₁ T F (x * (g₁, g₂)) = ap₁ T (fun y => F (y * (g₁, g₂))) x := by
  rw [ap₁_mul hS T hT hF o g₁ g₂ ho]
  have e : sl₁ (fun y : H E a b => F (y * (g₁, g₂))) x.2 = act o (sl₁ F (x.2 * g₂)) :=
    sl₁_eq (funext fun y => by
      rw [ho, sl_val hS hF]
      rfl)
  simp only [ap₁, e]

theorem typeH_ap₁ (hS : PairSlices) {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))}
    {W₁ : Submodule ℂ (Kinf E a → ℂ)} {W₂ : Submodule ℂ (Kinf E b → ℂ)} (hW₁ : FiniteDimensional ℂ W₁)
    (hW₂ : FiniteDimensional ℂ W₂) (T : Sm E a →ₗ[ℂ] Sm E a) (hT : ∀ o, ∀ ψ ∈ U₁, T (act o ψ) = act o (T ψ))
    {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (hty : TypeH K₁ K₂ W₁ W₂ F) : TypeH K₁ K₂ W₁ W₂ (ap₁ T F) := by
  refine ⟨fun u₁ h₁ u₂ h₂ x => ?_, fun x => ?_⟩
  · rw [ap₁_translate hS T hT hF (.fin u₁) _ _ (fun _ _ => rfl)]
    have e : (fun y => F (y * (finGL E a u₁, finGL E b u₂))) = F := funext (hty.1 u₁ h₁ u₂ h₂)
    rw [e]
  · have hD := GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd W₁ W₂ hW₁ hW₂
    let s : Kinf E a × Kinf E b → Sm E a :=
      fun k => act (.cpt k.1) (sl₁ F (x.2 * infGL E b (Unitary.toUnits k.2)))
    let ev : GA E a → Sm E a →ₗ[ℂ] ℂ := fun y => (LinearMap.proj y).comp (Sm E a).subtype
    have hs : ∀ y, (fun k => ev y (s k)) ∈ GlobalTheory.CompanionTheory.LimV.prodSpan W₁ W₂ := fun y => by
      have e : (fun k => ev y (s k)) = fun k : Kinf E a × Kinf E b =>
          F ((y, x.2) * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) :=
        funext fun k => sl_val hS hF _ _
      rw [e]
      exact hty.2 (y, x.2)
    have h := mem_of_separating _ hD s ev (fun v hv => Subtype.ext (funext hv)) hs ((ev x.1).comp T)
    have e : (fun k : Kinf E a × Kinf E b =>
        ap₁ T F (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) =
        fun k => ((ev x.1).comp T) (s k) :=
      funext fun k => ap₁_mul hS T hT hF (.cpt k.1) _ _ (fun _ _ => rfl) x
    rw [e]
    exact h

end Slices

theorem pairStep₁_of_slices : PairSlices → PairStep₁ := by
  intro hS E _ _ _ a b ι _ K₁ K₂ W₁ W₂ U₁ U₁' U₂ T f hW₁ hW₂ hU hT hTm hf hty hne
  refine ⟨?_, fun i => ap₁_mem hS T hTm (hf i), fun i => typeH_ap₁ hS hW₁ hW₂ T hT (hf i) (hty i), ?_⟩
  · obtain ⟨i, m₂, φ, hφ, hTφ⟩ := hne
    intro h0
    apply hTφ
    refine Subtype.ext (funext fun x => ?_)
    have h := congrFun (congrFun h0 i) (x, m₂)
    simp only [ap₁, sl₁_eq hφ] at h
    exact h
  · intro h c hc
    funext i x
    classical
    have hmem : ∀ j g, (fun y => f j (y * finH g)) ∈ pairSpace U₁ (⊤ : Submodule ℂ (Sm E b)) :=
      fun j g => translate_mem hU (hf j) g
    have e : heckeAct h f i = ∑ j, ∑ g ∈ (h i j).support, (h i j g) • (fun y => f j (y * finH g)) := by
      funext y
      simp [heckeAct, Finsupp.sum, Finset.sum_apply]
    have step : ap₁ T (heckeAct h f i) x = heckeAct h (fun i => ap₁ T (f i)) i x := by
      rw [e, ap₁_sum (U₁ := U₁) (U₂ := ⊤) hS T _ _
        (fun j _ => Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hmem j g))]
      simp only [heckeAct, Finset.sum_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ap₁_sum (U₁ := U₁) (U₂ := ⊤) hS T _ _ (fun g _ => Submodule.smul_mem _ _ (hmem j g)), Finset.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [ap₁_smul (U₁ := U₁) (U₂ := ⊤) hS T (hmem j g), Pi.smul_apply, smul_eq_mul]
      exact congrArg _ (ap₁_translate hS T hT (hf j) (.fin g.1) (finGL E a g.1) (finGL E b g.2)
        (fun _ _ => rfl) x).symm
    have hc' : heckeAct h f i = c • f i := congrFun hc i
    rw [← step, hc', ap₁_smul hS T (hf i)]
    rfl

end GlobalTheory.CompanionTheory.EGlue.TensorOne

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolReOf2T
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG PositivityTheory.ThKF PositivityTheory.HoweDualityUnitaryAlt
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem cmp_finT (hM : MaxFinT) {R R₂ : RealMaps F a a'} {Rf Rf₂ : FinMaps F a a'} (m : IsMatched B G X om om' R Rf)
    (v : Pl F) (n₂ : Nontrivial (Rf₂.Pi v)) (o : (SB _).map (Rf₂.p v) = ⊤) (o' : (SB _).map (Rf₂.p' v) = ⊤)
    (x₁ : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p v) ⊓ SB _))
    (x₂ : Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p' v) ⊓ SB _))
    (eq₂ : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      Rf₂.p v φ = Rf₂.p' v φ' → Rf₂.p v φ₁ = Rf₂.p' v φ₁') :
    ∃ (e : Rf.Pi v →ₗ[ℂ] Rf₂.Pi v) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ SB _, e (Rf.p v x) = Rf₂.p v x) ∧
      ∀ x ∈ SB _, e (Rf.p' v x) = c • Rf₂.p' v x := by
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M om
    ⟨p1.base, ⟨_, _, p1.herm⟩, ⟨_, _, p1.skew⟩, p1.good, ⟨_, _, p1.weil⟩⟩ v
  choose A' hA' hA'' using fun (i : UAt σ G.W (evFin F v)) (x : SB (Fin a' × Fin (a + a') → Fv F v)) => ex_fin p2 v i x x.2
  have ac : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)),
      Acts (evFin F v) (om (1, i.1)) x (ω (1, i.1) x) := fun i x => (hω.acts 1 (one_at _) i i.2 x x.2 _).2 rfl
  have pr : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)), ω (1, i.1) x ∈ SB _ :=
    fun i x => hω.pres 1 (one_at _) i i.2 x x.2
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  exact schur_match (SB _) (SB _) (Rf.p v) (Rf.p' v) (Rf₂.p v) (Rf₂.p' v) (m.fin.onto v) (m.fin.onto' v) o o'
    (fun x hx => (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).1 _ _ (maxFinP m v).1 x₁) x hx).1)
    (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).2 _ _ (maxFinP m v).2 x₂))
    (fun i : UAt σ G.W (evFin F v) => ω (1, i.1) ∘ₗ Submodule.subtype _) A' pr hA'
    (fun i x x' => m.fin.equiv v i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun i x x' => eq₂ i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun N hN => m.fin.irred v N fun h hh x hx y _ e hp => by
      rw [(hω.acts 1 (one_at _) h hh x hx y).1 e]; exact hN ⟨h, hh⟩ ⟨x, hx⟩ hp)
    (rank_SB _)

theorem polRe_of2T (hH : PositivityTheory.ThKR.JoinTri) (hM : MaxFinT) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    (hJ : CartanConj) (hV : CartanMove) (hK : KCoinv) (hI : ILeft) : PolRe := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' R Rf m V V' W R₂ Rf₂ m₂ ⟨c₂, hc₂, hc⟩
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨h, hh, hh'⟩ := hJ F E σ B _ G.W W _ _ p1.base p1.skew m₂.triple.geo.hW
  obtain ⟨g, hg, hg', hP⟩ := hV F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 V W (reG G V V' W).M rfl (pairV m₂.triple) h hh hh'
  obtain ⟨g', hk, hk', hP'⟩ := hV F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 V' W (reG G V V' W).M' rfl (pairV' m₂.triple) h hh hh'
  obtain ⟨T, hT, -⟩ := hO F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 g hg h hh
  obtain ⟨T', hT', -⟩ := hO F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 g' hk h hh
  obtain ⟨e, c, c0, he, he'⟩ := archimedean_matched_maps_compare hH hO hL hQ hC ⟨m₂.triple, real_trans hO hL hQ m.triple m₂.triple m.real ⟨hg, hg'⟩ ⟨hk, hk'⟩
    ⟨hh, hh'⟩ hT hT' (hP T hT) (hP' T' hT'), m₂.fin⟩ m₂
  choose ef cf cf0 hef hef' using fun v => cmp_finT (R₂ := R₂) hM m v (m₂.fin.nontriv v) (m₂.fin.onto v) (m₂.fin.onto' v)
    (maxFinP m₂ v).1 (maxFinP m₂ v).2 (m₂.fin.equiv v)
  have cf1 : ∀ v ∉ X.T, cf v = 1 := fun v hv => by
    obtain ⟨s1, s2⟩ := m₂.fin.sph v hv
    have x1 := hef v _ (p1.good.vac v).1
    rw [(m.fin.sph v hv).1, hef' v _ (p2.good.vac v).1] at x1
    have x2 : cf v • Rf₂.p v (G.M.vac v) = (1 : ℂ) • Rf₂.p v (G.M.vac v) := by
      rw [one_smul]; exact (congrArg (cf v • ·) s1).trans x1
    exact smul_left_injective ℂ s2 x2
  let Λ : ℂ := c * ∏ v ∈ X.T, cf v
  refine ⟨c₂ * Λ, mul_ne_zero hc₂ (mul_ne_zero c0 (Finset.prod_ne_zero_iff.2 fun v _ => cf0 v)), ?_⟩
  rintro Φ Φ' hΦ' ⟨S, hS, k, k', f, φ, f', φ', h1, h2, rfl, rfl, eq⟩ x
  choose u hu hu' using fun i => (show f i ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) from hP T hT ▸ (h1 i).1)
  choose u' hw hw' using fun i => (show f' i ∈ ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) from hP' T' hT' ▸ (h2 i).1)
  have e1 := move_sum p1.good hT u φ (fun i => (h1 i).2.1) fun i => ev_of_off (h1 i).2.2
  have e2 := move_sum p2.good hT' u' φ' (fun i => (h2 i).2.1) fun i => ev_of_off (h2 i).2.2
  have fu : ∀ i, T (u i) = f i := hu'
  have fu' : ∀ i, T' (u' i) = f' i := hw'
  simp only [fu] at e1
  simp only [fu'] at e2
  have s1 : ∑ i, pure (u i) (φ i) ∈ schA F _ := sum_mem fun i _ =>
    GlobalTheory.TensUniq.pure_mem_schA _ _ (h1 i).2.1 ((good_std p1.good).congr (ev_of_off (h1 i).2.2))
  have so : ∑ i, pure (u' i) (φ' i) ∈ G.M'.So B.ψ B.τ₁ := by
    have := (hK F E σ B a a' G X om om' R Rf m).2 (g', h)⁻¹ _ hΦ'
    rwa [← e2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have e3 : Λ • ∑ i, pure (u' i) (φ' i) = ∑ i, pure (Λ • u' i) (φ' i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => funext fun y => (mul_assoc _ _ _).symm
  have pm : PolMatch B (reG G V V' W) X R₂ Rf₂ (∑ i, pure (u i) (φ i)) (Λ • ∑ i, pure (u' i) (φ' i)) := by
    refine ⟨S, hS, k, k', u, φ, fun i => Λ • u' i, φ', fun i => ⟨hu i, (h1 i).2⟩,
      fun i => ⟨Submodule.smul_mem _ _ (hw i), (h2 i).2⟩, rfl, e3, ?_⟩
    have := congrArg (TensorProduct.map e (PiTensorProduct.map fun v : S => ef v)) eq
    simp only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [← fu i, show e (R.p (T (u i))) = R₂.p (u i) from he _ (hu i)]
      simp only [hef _ _ ((h1 i).2.1 _)]
    · rw [← fu' j, show e (R.p' (T' (u' j))) = c • R₂.p' (u' j) from he' _ (hw j)]
      simp only [hef' _ _ ((h2 j).2.1 _)]
      rw [MultilinearMap.map_smul_univ, TensorProduct.smul_tmul_smul, map_smul, TensorProduct.smul_tmul',
        Finset.prod_coe_sort S cf, ← Finset.prod_subset hS fun v _ hv => cf1 v hv]
  have := hc _ _ (Submodule.smul_mem _ Λ (so_re V V' W so)) pm (x * h)
  rw [← e1, ← e2, I_move hI p1 s1, I_move hI p2 (so_le p2.good _ so), mul_assoc, ← I_smul]
  exact this

end GlobalTheory.CompanionTheory.ThetaK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOfLocalIdentitiesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_product_of_local_identities : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), SWFree σ J T hT → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (m : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) m → ∀ C : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact C → m (hermOf (Fv F v) σ T hT) C < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FibCpt.fibre_compact_lt_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedDisintegrationCompositionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staged_disintegration_composition : ∀ (V₁ D H₁ H₃ A P Y₁ Y₃ : Type) [TopologicalSpace V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D] [MeasurableSpace D] [BorelSpace D] [TopologicalSpace H₁] [T2Space H₁] [LocallyCompactSpace H₁] [SecondCountableTopology H₁] [MeasurableSpace H₁] [BorelSpace H₁] [TopologicalSpace H₃] [T2Space H₃] [LocallyCompactSpace H₃] [SecondCountableTopology H₃] [MeasurableSpace H₃] [BorelSpace H₃] [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P] [AddCommGroup H₃] [IsTopologicalAddGroup H₃] (μ₁ : Measure V₁) (δ : Measure D) (ν₁ : Measure H₁) (ν₃ : Measure H₃) (α : Measure A) (ρ : Measure P) [IsLocallyFiniteMeasure μ₁] [IsLocallyFiniteMeasure δ] [IsLocallyFiniteMeasure ν₁] [ν₃.IsAddHaarMeasure] [IsLocallyFiniteMeasure α] [IsLocallyFiniteMeasure ρ] (f₁ : V₁ → Y₁) (ι₁ : H₁ → Y₁) (q₁ : V₁ → H₁) (U₁ : Set V₁) (m₁ : H₁ → Measure V₁) (f₃ : D → Y₃) (ι₃ : H₃ → Y₃) (q₃ : D → H₃) (U₃ : Set D) (m₃ : H₃ → Measure D) (Q : H₁ × P × A → H₃), IsOpen U₁ → IsOpen U₃ → Continuous q₁ → Continuous q₃ → Function.Injective ι₁ → Function.Injective ι₃ → (∀ v, f₁ v = ι₁ (q₁ v)) → (∀ v, f₃ v = ι₃ (q₃ v)) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ₁ f₁ ι₁ U₁ ν₁ Set.univ m₁ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily δ f₃ ι₃ U₃ ν₃ Set.univ m₃ → Continuous Q → ∀ ψ : V₁ × A × P × D → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.1 ∈ U₁ ∧ p.2.2.2 ∈ U₃) → (∀ p, 0 ≤ ψ p) → Continuous (fun z : H₁ × P × H₃ => ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y)) ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1)) ∧ ∀ f : H₁ × P × H₃ → ℝ≥0∞, Measurable f → ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, s, Y)) * f (q₁ x, s, q₃ Y + Q (q₁ x, s, a)) ∂δ ∂ρ ∂α ∂μ₁ = ∫⁻ z, f z * (∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y)) ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1)) ∂(ν₁.prod (ρ.prod ν₃)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.StageAbs.stages_abstract | exact GlobalTheory.CompanionTheory.WeilSiegel.StageAbs.stages_abstract | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.StageAbs.stages_abstract <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOneStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_absolute_character_one : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (x : GA E N) (w : ℕ → ℂ), Tendsto w atTop (𝓝 0) → Tendsto (fun k => absFn N (w k) x) atTop (𝓝 1) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one | exact GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one | (intros; apply GlobalTheory.CompanionTheory.LimV.absFn_tendsto_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureExtensionByScalarStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_extension_by_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (μ : Measure (HA (AF F) σ (blockOne (algebraMap F E t) J))) 𝓕, IsHaarH F E σ (M + 1) _ μ → IsFDH F E σ (M + 1) _ μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ (Φ : (Fin (n + 1) → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 1) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, Φ (actW (AF F) σ _ h (consTup X)) ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J T))) → ∫⁻ X, Φ X ∂(thetaMeas σ _ μ 𝓕 (framesE σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T))) = ∫⁻ y, Ψ y ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.FrameTheta.theta_stage_frames <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuous
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.SiegelWeil

theorem swSection_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle)
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω →
    ∀ (f : WO (dblSp A) B → ℂ), IsThetaFunO ψ (dblSp A) B f →
    ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    Continuous (swSection A B ν 𝓖 ω f) := by
  intro D ψ A B χ ω hω f hf ν 𝓖 hν
  rw [GlobalTheory.Core.Rk.IP.swSection_eq_swSec A B ν 𝓖 ω f]
  exact (GlobalTheory.Core.Rk.IP.swSec_integrable_continuous D ψ A B χ ω hω ν 𝓖 hν f hf).2

end GlobalTheory.CompanionTheory.SiegelWeil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusElementLeviEmbeddingStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_element_levi_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (t : ℝ),
  aT E (r + s) r t = GlobalTheory.CompanionTheory.CTFin.lev (Ad E) r s (aT E r r t, 1) := by
  first | exact @GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev | exact GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev | (intros; apply GlobalTheory.CompanionTheory.Conc.LevAt.aT_eq_lev <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedFirstBlockRestrictionStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typed_first_block_restriction : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₁ : Subgroup (GL (Fin r) (Af E))) (W₁ : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K₁ : Set (GL (Fin r) (Af E))) ∧ FiniteDimensional ℂ W₁ ∧ ∀ f ∈ typeF K W, ∀ y : GA E s, (fun x : GA E r => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₁ W₁ := by
  first | exact @GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF | exact GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF | (intros; apply GlobalTheory.CompanionTheory.LimV.SliceL.slice_typeF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestrictionStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typed_second_block_restriction : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₂ : Subgroup (GL (Fin s) (Af E))) (W₂ : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K₂ : Set (GL (Fin s) (Af E))) ∧ FiniteDimensional ℂ W₂ ∧ ∀ f ∈ typeF K W, ∀ x : GA E r, (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₂ W₂ := by
  first | exact @GlobalTheory.CompanionTheory.LimV.SliceR.slice_right | exact GlobalTheory.CompanionTheory.LimV.SliceR.slice_right | (intros; apply GlobalTheory.CompanionTheory.LimV.SliceR.slice_right <;> assumption)
end

