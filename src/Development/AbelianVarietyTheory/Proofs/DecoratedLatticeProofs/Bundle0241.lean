import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0225
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0336
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HandHom
variable {D : D7}

theorem mixS_smul {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (T : HSp D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)) (a : ℂ) (f : WO V T → ℂ) (x : Mx D T.rank ρ) :
    d.mixS T ψ μ 𝓕 (a • f) x = a • d.mixS T ψ μ 𝓕 f x := by
  funext w₀
  simp only [HypDec.mixS, Pi.smul_apply, smul_eq_mul, HypDec.integrandS_eq]
  rw [← integral_const_mul]
  congr 1; funext a'; ring

theorem mixT_smul {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (S : HSp D) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (a : ℂ) (f : WO S W → ℂ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (a • f) y = a • d.mixT S ψ μ 𝓕 f y := by
  funext w₀
  simp only [HypDec.mixT, Pi.smul_apply, smul_eq_mul, HypDec.integrandT_eq]
  rw [← integral_const_mul]
  congr 1; funext a'; ring

theorem flatAt_smul (ψ : AddChar (AF D.host.F) ℂ) {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ)
    (dW : HypDec W W₀ σ) (μS : Measure (Mx D W.rank ρ)) (𝓕S : Set (Mx D W.rank ρ)) (μT : Measure (Mx D σ V₀.rank))
    (𝓕T : Set (Mx D σ V₀.rank)) (νU : Measure (UX D ρ)) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (a : ℂ)
    (Ψ : WO V W → ℂ) :
    GlobalTheory.MixPer.flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y (a • Ψ) = a • GlobalTheory.MixPer.flatAt ψ dV dW μS 𝓕S μT 𝓕T νU x y Ψ := by
  funext w
  simp only [GlobalTheory.MixPer.flatAt, GlobalTheory.MixPer.flatFun, GlobalTheory.MixPer.evalAt, mixS_smul, mixT_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext u; ring

end GlobalTheory.HandHom

namespace GlobalTheory.HandHom
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem flatBF_smul {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) (a : ℂ) (Ψ : WO B.V J.W → ℂ) :
    flatBF s (a • Ψ) = a • flatBF s Ψ := by
  simp only [GlobalTheory.Unf.flatBF, GlobalTheory.MixPer.flat, flatAt_smul]

theorem flatFB_smul {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) (a : ℂ) (Ψ : WO J.W B.V → ℂ) :
    flatFB s (a • Ψ) = a • flatFB s Ψ := by
  simp only [GlobalTheory.Unf.flatFB, GlobalTheory.MixPer.flatLast, flatAt_smul]

theorem handBF_smul {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D}
    {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') (φ : GA D B.A → ℂ) (a : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) :
    handBF s l φ (a • Ξ) = star a • handBF s l φ Ξ := by
  funext h w
  simp only [GlobalTheory.Unf.handBF, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (φ _) a]
  rw [integral_const_mul, star_mul']

theorem handBF_zero {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D}
    {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') (φ : GA D B.A → ℂ) :
    handBF s l φ 0 = 0 := by
  funext h w
  simp [GlobalTheory.Unf.handBF]

theorem handFB_smul {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B)
    (vL : VolM D B.L.rank J.W₀.rank) (c b : ℂ) (Y : GA D J.W₀ → WO J.W₀ B.L → ℂ) (Ξ : WO J.W₀ B.V₀ → ℂ) :
    handFB s vL (c • Y) (b • Ξ) = (star c * b) • handFB s vL Y Ξ := by
  funext h₁
  simp only [GlobalTheory.Unf.handFB, GlobalTheory.Unf.pairKer, GlobalTheory.MixPer.contractT, GlobalTheory.MixPer.thPair, LinearMap.map_smul,
    Pi.smul_apply, smul_eq_mul, star_mul']
  simp_rw [show ∀ x y : ℂ, b * x * (star c * y) = (star c * b) * (x * y) from fun x y => by ring, integral_const_mul]

theorem per_smul {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (a b : ℂ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) :
    B.per ψ (a • φ) (b • f) = a * b * B.per ψ φ f := by
  simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer, GlobalTheory.MixPer.besFun, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ x y z : ℂ, a * x * (b * y) * z = (a * b) * (x * y * z) from fun x y z => by ring, integral_const_mul]

end GlobalTheory.HandHom

namespace GlobalTheory.HandHom
variable {D : D7}

theorem hand_hom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), (∀ (Ψ₁ : WO B.V J.W → ℂ) (Ψ₂ : WO J.W B'.V → ℂ) (a b : ℂ), handFB s₂ vL (handBF s₁ l φ (flatBF s₁ (a • Ψ₁))) (flatFB s₂ (b • Ψ₂)) = (a * b) • handFB s₂ vL (handBF s₁ l φ (flatBF s₁ Ψ₁)) (flatFB s₂ Ψ₂)) ∧ (∀ Ξ₂, handFB s₂ vL (handBF s₁ l φ 0) Ξ₂ = 0) ∧ ∀ (a b : ℂ) (φ' : GA D B'.A → ℂ) (f : GA D B'.V → ℂ), B'.per ψ (a • φ') (b • f) = a * b * B'.per ψ φ' f := by
  intro D ψ σ B J B' s₁ s₂ l vL φ
  refine ⟨fun Ψ₁ Ψ₂ a b => ?_, fun Ξ₂ => ?_, fun a b φ' f => per_smul B' ψ a b φ' f⟩
  · rw [flatBF_smul, flatFB_smul, handBF_smul, handFB_smul, star_star]
  · rw [handBF_zero]
    funext h₁
    simp [GlobalTheory.Unf.handFB, GlobalTheory.Unf.pairKer, GlobalTheory.MixPer.contractT, GlobalTheory.MixPer.thPair]

end GlobalTheory.HandHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
namespace GlobalTheory.BiComb

variable {D : D7}

theorem heisO_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO V S → ℂ)
    (w u : WO A S) (v : WO L S) :
    heisO ψ V S ((o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      heisO ψ A S w (fun u' => F ((o.resS S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem heisO_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (F : WO S V → ℂ)
    (w u : WO S A) (v : WO S L) :
    heisO ψ S V ((o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      heisO ψ S A w (fun u' => F ((o.resT S).symm (u', v))) u := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem comb_resS_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO A S →₀ ℂ)
    (F : WO V S → ℂ) (u : WO A S) (v : WO L S) :
    comb ψ V S (c.mapDomain fun w => (o.resS S).symm (w, 0)) F ((o.resS S).symm (u, v)) =
      comb ψ A S c (fun u' => F ((o.resS S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO A S => (o.resS S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resS S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply hinj, heisO_resS_slice]

theorem comb_resT_slice (ψ : AddChar (AF D.host.F) ℂ) {V A L S : HSp D} (o : OrthDec V A L) (c : WO S A →₀ ℂ)
    (F : WO S V → ℂ) (u : WO S A) (v : WO S L) :
    comb ψ S V (c.mapDomain fun w => (o.resT S).symm (w, 0)) F ((o.resT S).symm (u, v)) =
      comb ψ S A c (fun u' => F ((o.resT S).symm (u', v))) u := by
  classical
  have hinj : Function.Injective fun w : WO S A => (o.resT S).symm (w, 0) := fun a b h => by
    have := congrArg (o.resT S) h
    simp only [AddEquiv.apply_symm_apply, Prod.mk.injEq, and_true] at this
    exact this
  simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finsupp.mapDomain_apply hinj, heisO_resT_slice]

section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_isOne (Y Y' : Type) [Fintype Y] [Fintype Y'] : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {x : Matrix Y Y' k | ∀ r q, x r q ∈ 𝒪[k]} := GlobalTheory.SplitFlip.isCompact_intMatrix
  exact ⟨⟨_, GlobalTheory.LocFlat.CFac.Span.indicator_one_mem_SB hc ⟨hc.isClosed, GlobalTheory.SplitFlip.isOpen_intMatrix⟩⟩, rfl⟩

end Loc

theorem source_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := GlobalTheory.T.exists_local_model_slice_source_line

theorem target_slice_model : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := GlobalTheory.T.exists_local_model_slice_target_line

theorem comb_bimodel_and_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''], (∀ (A S A' : HSp D) (FA : Frame k A.rank n') (FS : Frame k S.rank n) (FA' : Frame k A'.rank n'') Λ c c' (Ξ₁ O₁ : SB (Matrix n n' k)) (Ξ₂ O₂ : SB (Matrix n'' n k)) (Ξ O : SB (Matrix n n' k × Matrix n'' n k)), p.IsBiModel ψ FA FS FA' Λ → p.IsCombAt ψ FA FS c Ξ₁.1 → p.IsCombAt ψ FS FA' c' Ξ₂.1 → IsOne O₁ → IsOne O₂ → (∀ q, Ξ.1 q = Ξ₁.1 q.1 * Ξ₂.1 q.2) → (∀ q, O.1 q = O₁.1 q.1 * O₂.1 q.2) → Λ Ξ = biComb ψ A S A' c c' (Λ O)) ∧ ∀ (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), IsStdChar D ψ (-1) → p.IsCoreFrame B s FA F₀ → (∀ T₀ c (Ξ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ F₀ FS T₀ → p.IsCombAt ψ FA FS c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toCols₁ * a fun r => x r (Sum.inr ())) → (∀ x, O.1 x = Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toCols₁ * a fun r => x r (Sum.inr ())) → T₀ Ψ = comb ψ B.V₀ S (c.mapDomain fun w => (B.o.resS S).symm (w, 0)) (T₀ O)) ∧ ∀ T₀ c (Ξ : Matrix n' n k → ℂ) (a : (n → k) → ℂ) Ψ O, p.IsModel ψ FS F₀ T₀ → p.IsCombAt ψ FS FA c Ξ → Ξ ∈ SB _ → a ∈ SB _ → (∀ x, Ψ.1 x = Ξ x.toRows₁ * a (x (Sum.inr ()))) → (∀ x, O.1 x = Set.indicator {x : Matrix n' n k | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) x.toRows₁ * a (x (Sum.inr ()))) → T₀ Ψ = comb ψ S B.V₀ (c.mapDomain fun w => (B.o.resT S).symm (w, 0)) (T₀ O) := by
  intro D k _ _ _ _ p ψ n n' n'' _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · intro A S A' FA FS FA' Λ c c' Ξ₁ O₁ Ξ₂ O₂ Ξ O hΛ hc hc' hO₁ hO₂ hΞ hO
    funext u v
    obtain ⟨T₁, hT₁, e₁⟩ := hΛ.1 Ξ₂ v
    let P : SB (Matrix n n' k × Matrix n'' n k) := ⟨_, GlobalTheory.LocFlat.CFac.prodFn_mem_SB O₁.2 Ξ₂.2⟩
    rw [e₁ Ξ₁ Ξ hΞ u, hc.2 T₁ hT₁ O₁ Ξ₁ hO₁ rfl]
    have hf : T₁ O₁ = fun u' => comb ψ S A' c' (Λ O u') v := by
      funext u'
      rw [← e₁ O₁ P (fun q => rfl) u']
      obtain ⟨T₂, hT₂, e₂⟩ := hΛ.2 O₁ u'
      rw [e₂ Ξ₂ P (fun q => rfl) v, hc'.2 T₂ hT₂ O₂ Ξ₂ hO₂ rfl]
      have hg : T₂ O₂ = Λ O u' := funext fun v' => (e₂ O₂ O hO v').symm
      rw [hg]
    rw [hf]
    rfl
  · intro ρ B S s FA F₀ FS _ hF
    refine ⟨?_, ?_⟩
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := source_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resS S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n n'
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resS S).symm ((B.o.resS S x).1, (B.o.resS S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resS_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resS S).symm (u', (B.o.resS S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]
    · intro T₀ c Ξ a Ψ O hT hc hΞ ha hΨ hO
      funext x
      obtain ⟨T₁, hT₁, e⟩ := target_slice_model D k p ψ n n' ρ B S s FA F₀ FS hF T₀ hT a ha (B.o.resT S x).2
      obtain ⟨O₁, hO₁⟩ := exists_isOne (k := k) n' n
      have h1 := hc.2 T₁ hT₁ O₁ ⟨Ξ, hΞ⟩ hO₁ rfl
      have hx : x = (B.o.resT S).symm ((B.o.resT S x).1, (B.o.resT S x).2) := by simp
      rw [hx, e ⟨Ξ, hΞ⟩ Ψ hΨ, h1, comb_resT_slice]
      have hg : T₁ O₁ = fun u' => T₀ O ((B.o.resT S).symm (u', (B.o.resT S x).2)) :=
        funext fun u' => (e O₁ O (fun y => by rw [hO₁]; exact hO y) u').symm
      rw [hg]

end GlobalTheory.BiComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergDerivativeDiagonalHalfEqSchrodingerDerStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_diagonalHalf_eq_schrodingerDerivative : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ (τ : D.what₂.Tau) (X : Matrix (Fin B.rank) (Fin A.rank) ℂ) (x : Mx D B.rank A.rank), sch ψ A B ν 𝓨 (Formalism.IndefR.Datum.dRho (heisO ψ (dblSp A) B) θ τ (X * (dblDec A).qX.map (tauE D τ)) f) x = deriv (fun t : ℝ => sch ψ A B ν 𝓨 f (x + lineAt θ τ X t)) 0 := by
  first | exact @GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag | exact GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag | (intros; apply GlobalTheory.StdUnn.DiagDeriv.sch_dRho_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeisTarget

variable {D : D7}

theorem symplOH_skew' (S T : HSp D) (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH; rw [GlobalTheory.OrientedHeis.symplO_skew, mul_neg]

theorem symplO_eq_two (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add, add_halves, map_one, one_mul]

variable {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)

theorem mixT_heis_incX {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.incX S ξ) f) y =
      ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) • d.mixT S ψ μ 𝓕 f y := by
  funext w₀
  have key : ∀ ξ' : Mx D ρ S.rank,
      heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀)
        (heisO ψ S T (d.incX S ξ) f))) 0 =
      ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) *
        heisO ψ S T (d.incX S (ξ' + ξ)) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 := by
    intro ξ'
    rw [HypDec.integrandT_eq, HypDec.integrandT_eq]
    simp only [heisO]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.incX S)]
    congr 1
    · congr 1
      have h1 := d.symplOH_incX_incX S ξ' ξ
      have h2 : symplOH S T (d.inc0 S w₀) (d.incX S ξ) = 0 := by
        rw [symplOH_skew', d.wittDecomp_sympl_inclIsotropic_inclAnisotropic S ξ w₀, neg_zero]
      have h3 := symplOH_skew' S T (d.incAdj S y) (d.incX S ξ)
      simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, h1, h2, h3,
        symplO_eq_two]
      ring
    · congr 1
      abel
  show ∫ ξ' in 𝓕, _ ∂μ = ψ _ * ∫ ξ' in 𝓕, _ ∂μ
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact covolOne_integral_add hμ (fun ξ' => heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0)
    (d.integrandT_periodic hf y w₀) ξ

theorem mixedModelTarget_heisenberg_anisotropic_part {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (f : WO S T → ℂ) (v : WO S T₀) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (heisO ψ S T (d.inc0 S v) f) y = heisO ψ S T₀ v (d.mixT S ψ μ 𝓕 f y) := by
  funext w₀
  have key : ∀ ξ' : Mx D ρ S.rank,
      heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀)
        (heisO ψ S T (d.inc0 S v) f))) 0 =
      ψ (symplOH S T₀ w₀ v) *
        heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S (w₀ + v)) f)) 0 := by
    intro ξ'
    rw [HypDec.integrandT_eq, HypDec.integrandT_eq]
    simp only [heisO]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.inc0 S)]
    congr 1
    · congr 1
      have h1 := d.wittDecomp_sympl_inclIsotropic_inclAnisotropic S ξ' v
      have h2 : symplOH S T (d.incAdj S y) (d.inc0 S v) = 0 := by
        rw [HypDec.incAdj_apply]; exact d.wittDecomp_sympl_inclDual_inclAnisotropic S _ v
      have h3 := d.wittDecomp_sympl_inclAnisotropic_inclAnisotropic S w₀ v
      simp only [GlobalTheory.OrientedHeis.symplOH_add_left, h1, h2, h3]
      ring
    · congr 1
      abel
  show ∫ ξ' in 𝓕, _ ∂μ = ψ _ * ∫ ξ' in 𝓕, _ ∂μ
  simp_rw [key]
  rw [integral_const_mul]

end GlobalTheory.HeisTarget

namespace GlobalTheory.HeisTarget

variable {D : D7}

theorem hasSum_mixT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    HasSum (fun y : Matrix (Fin S.rank) (Fin ρ) D.host.E => d.mixT S ψ μ 𝓕 f (rat y) 0) (f 0) := by
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := GlobalTheory.T.wittMixedCoords_conj_hermitianAdjoint D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hg : IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) :=
    ((GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hψ S T).2.2.1 f).2 hf
  have h5 := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ T T₀ S ρ d ⟨μ', 𝓕', hμ'⟩ _ hg).2.2.2.2 0
  have hx : (D.host.xi0 : D.host.E) ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let σ : Matrix (Fin S.rank) (Fin ρ) D.host.E ≃ Matrix (Fin S.rank) (Fin ρ) D.host.E :=
    { toFun := fun y => D.host.xi0⁻¹ • y
      invFun := fun y => D.host.xi0 • y
      left_inv := fun y => by simp only [smul_smul, mul_inv_cancel₀ hx, one_smul]
      right_inv := fun y => by simp only [smul_smul, inv_mul_cancel₀ hx, one_smul] }
  rw [← σ.hasSum_iff] at h5
  have e : ∀ y : Matrix (Fin S.rank) (Fin ρ) D.host.E,
      d.mixS S ψ μ' 𝓕' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) (rat (σ y)) 0 =
        starRingEnd ℂ (d.mixT S ψ μ 𝓕 f (rat y) 0) := by
    intro y
    show d.mixS S ψ μ' 𝓕' _ (rat (D.host.xi0⁻¹ • y)) 0 = _
    rw [rat_smul, hsw f (rat y)]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger]
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f (d.ext0 S 0) = starRingEnd ℂ (f 0) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger]
  simp only [Function.comp_def, e, h0] at h5
  exact Complex.hasSum_conj'.1 h5

theorem heisenbergTarget (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.HeisenbergTarget D := by
  intro ψ hψ S T T₀ ρ d μ 𝓕 hμ f hf
  exact ⟨fun ξ y => mixT_heis_incX d hμ hf ξ y, fun w₀ y => mixedModelTarget_heisenberg_anisotropic_part d f w₀ y, hasSum_mixT hψ d hμ hf⟩

theorem main : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.HeisenbergTarget D := heisenbergTarget

end GlobalTheory.HeisTarget

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactorStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicContinuationValue_nnrealPow_factor : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c → (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  first | exact @GlobalTheory.StdUnn.holValueAt_npow_sub_mul | exact GlobalTheory.StdUnn.holValueAt_npow_sub_mul | (intros; apply GlobalTheory.StdUnn.holValueAt_npow_sub_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIdealIsUnitSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl IsBase onHalf phiQ rdQ)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homLatticeIdeal_isUnit_splitPlace : ∀ (D : D7) (PP : Pl D.host.E), ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → ∀ (v : FinPl D) (φ : SplitProj D v), IsProjAt φ PP → ((∃ a : D.host.E, a ∈ D.host.AA ∧ Valued.v (rdQ φ a) = 1) ∧ ∀ a : D.host.E, a ∈ D.host.AA → Valued.v (rdQ φ a) ≤ 1) := by
  first | exact @GlobalTheory.NormIdealUnit.unit_at_split_place | exact GlobalTheory.NormIdealUnit.unit_at_split_place | (intros; apply GlobalTheory.NormIdealUnit.unit_at_split_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfPartEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixHalf

variable {D : D7}

theorem infPart_eq_zero {e : AE D} (he : IsSplitIdem D e) {z : AE D} (hz : cA D e * z = z) : infPart D z = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have h4 : (e + cA D e) * cA D e = cA D e := by rw [add_mul, h2, he', zero_add]
  rw [← hz, ← h4, h3, map_mul, map_mul, h0, zero_mul, zero_mul]

theorem map_infPart_mul {l m n : ℕ} {x : Mx D l m} (hx : x.map (infPart D) = 0) (y : Mx D m n) :
    (x ⬝ y).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

theorem symplO_extX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) (w : WO S T) :
    symplO S T (d.extX T x) w = symplO S T (d.extX T x) (d.extY T (w ⬝ d.jY)) := by
  unfold symplO
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY,
    HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY, Matrix.mul_one, Matrix.mul_zero, pairS, hO_eq_trace S₀, trace_zero]

theorem rank_qX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.qX.rank = ρ := by
  refine le_antisymm (by simpa using Matrix.rank_le_height d.qX) ?_
  have h : d.qX * d.e = 1 := d.e'e
  have := Matrix.rank_mul_le_left d.qX d.e
  rwa [h, Matrix.rank_one, Fintype.card_fin] at this

theorem mixS_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ S T f → (∃ U : AddSubgroup (Mx D T.rank ρ), IsOpen (U : Set (Mx D T.rank ρ)) ∧ ∀ u ∈ U, (∀ i j, cA D e * u i j = u i j) → ∀ x, d.mixS T ψ μ 𝓕 f (x + u) = d.mixS T ψ μ 𝓕 f x) ∧ ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → d.mixS T ψ μ 𝓕 f x ≠ 0 → x ∈ K := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
  obtain ⟨hX, hY, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ f hf
  obtain ⟨U, hU, hl⟩ := hf.level
  have hhalf : ∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → x.map (infPart D) = 0 := fun x hx => by
    ext i j; exact infPart_eq_zero he (hx i j)
  have cX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have cY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  refine ⟨⟨U.comap (d.extX T), hU.preimage cX, fun u hu hu' x => ?_⟩, ?_⟩
  · have := hX x u
    rw [hl _ hu (map_infPart_mul (hhalf u hu') _)] at this
    exact this.symm
  · let r : WO S T →+ Mx D T.rank ρ :=
      { toFun := fun w => w ⬝ d.jY, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
    have cr : Continuous r := continuous_id.matrix_mul continuous_const
    obtain ⟨K, hK, hmem⟩ := GlobalTheory.IsoMeanAnnih.finPart_mem_compact D S T T.rank ρ 1 d.qX
      (by rw [Matrix.rank_one, Fintype.card_fin]) (rank_qX d) ψ hψ (U.comap ((d.extY T).comp r))
      (hU.preimage (cY.comp cr))
    obtain ⟨g, hg, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    have hs : Continuous fun b : Af D.host.F ⊗[D.host.F] D.host.E => (g.symm (0, b) : AE D) :=
      hc.comp (continuous_const.prodMk continuous_id)
    refine ⟨(fun y => y.map fun b => (g.symm (0, b) : AE D)) '' K, hK.image (continuous_id.matrix_map hs),
      fun x hx h0 => ⟨x.map (finPart D), hmem x fun u hu hu' => ?_, ?_⟩⟩
    · have h1 := hY x (u ⬝ d.jY)
      rw [hl (d.extY T (u ⬝ d.jY)) hu (map_infPart_mul (map_infPart_mul hu' _) _)] at h1
      have h2 : GlobalTheory.IsoMean.emb S T 1 d.qX x = d.extX T x := by
        change (rat (1 : Matrix (Fin T.rank) (Fin T.rank) D.host.E) ⬝ x : Mx D T.rank ρ) ⬝ d.pX = x ⬝ d.pX
        rw [rat_one, Matrix.one_mul]
      rw [h2, symplO_extX]
      have h3 : (ψ (symplO S T (d.extX T x) (d.extY T (u ⬝ d.jY))) - 1) • d.mixS T ψ μ 𝓕 f x = 0 := by
        rw [sub_smul, one_smul]; exact sub_eq_zero.2 h1.symm
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right h0)
    · ext i j
      simp only [Matrix.map_apply]
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext ((infPart_eq_zero he (hx i j)).symm.trans (hg _).1.symm) (hg _).2.symm

end GlobalTheory.MixHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnitaryAdelicEqSumFiniteCosetsRealIntegrStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unitaryAdelic_eq_sum_finiteCosets_realIntegrals : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D), W.SigOK → ∀ (K : Subgroup (GL (Fin W.rank) (Lev.EAf D))) (ν : Measure (GA D W)), IsMeasLev W K ν → IsOpen {h : GA D W | finE W h ∈ K} → ∀ Fr : Frames W, IsFrames W Fr → ∀ mR : ∀ ρ, Measure (Upq W ρ), (∀ ρ, Lev.IsMinf (mR ρ)) → ∀ Z : GA D W → ℂ, Continuous Z → Integrable Z ν → (∀ g, ∀ k ∈ levA W K, Z (g * k) = Z g) → ∫⁻ b, ∑' x : FinCos W (levA W K), ‖Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ))‖ₑ ∂(Measure.pi mR) < ⊤ ∧ ∫ g, Z g ∂ν = ∫ b, ∑' x : FinCos W (levA W K), Z (x.rep * realElt θ W fun ρ => realMat W Fr ρ (b ρ)) ∂(Measure.pi mR) := by
  first | exact @GlobalTheory.CosetDisint.integral_eq_cosetSum | exact GlobalTheory.CosetDisint.integral_eq_cosetSum | (intros; apply GlobalTheory.CosetDisint.integral_eq_cosetSum <;> assumption)
end

