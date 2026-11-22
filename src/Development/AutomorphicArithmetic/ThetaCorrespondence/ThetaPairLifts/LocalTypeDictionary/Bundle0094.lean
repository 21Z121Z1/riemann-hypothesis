import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3638
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3637
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsFinitePlaceThetaMatch
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3640

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockFImageEqZeroOrExistsEqSmul
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.fockF_image_eq_zero_or_exists_eq_smul : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T), IsFinF W.ψ W.θ true FA FW (X.f t) → IsFinF W.ψ W.θ false FA' FW (X.f' t) → ∃ (Pi : ModuleCat.{0} ℂ) (rf : GA D WW → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ → Module.End ℂ Pi) (p : (WO A WW → ℂ) →ₗ[ℂ] Pi) (p' : (WO A' WW → ℂ) →ₗ[ℂ] Pi), IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' ∧ ((∀ P, p (fockF W.ψ W.θ true FA FW (X.f t) P) = 0) ∨ ∃ (P : PolF D WW.rank A.rank) (P' : PolF D WW.rank A'.rank) (κ : ℂ), p (fockF W.ψ W.θ true FA FW (X.f t) P) ≠ 0 ∧ p (fockF W.ψ W.θ true FA FW (X.f t) P) = κ • p' (fockF W.ψ W.θ false FA' FW (X.f' t) P')) := by
  intro hH hPr _ hLM
  refine GlobalTheory.BotDict.gBig_three GlobalTheory.BotDict.bottom_dictionary GlobalTheory.BotDict.bottom_dictionary GlobalTheory.BotDict.bottom_dictionary ?_
  intro D T Lc sc G μ₀ C x b hL hd _ _ W i j A A' WW X hX FA FA' FW t hf hf'
  classical
  obtain ⟨_, _, _, _, _, -, -, -, hd⟩ := hd W i j A A' WW X hX
  have e : Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) =
      G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  have e' : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  refine _root_.GlobalTheory.BotMatch.bottom_matching_of_triangle hH hPr hLM W.ψ_std W.θ_is X hX.is t (hd t).1 (e ▸ chrEq_nu G t i j hL)
    (GlobalTheory.T.exists_embedding_splitPrime_gridLocalTensorPlaces hL t) (fun w hw hu => ?_) (fun w hw => ?_) (GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum hL t).1
    ((GlobalTheory.T.gridLocalTensorPlaces_splitIdempotent_sum hL t).2 _ (hX.is.idem t)).1 FA FA' FW hf hf'
  · have hu' : GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E)
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) w := by
      rw [e', ← e]; exact hu
    by_cases hs : w.under (𝓞 D.host.F) ∈ G.pl.S0
    · rcases G.pl.mem_S0_of_sum_eq.1 hs with h | h
      · exact GlobalTheory.ThetaGridRamifiedOverBasePlace.thetaGridCharacterQuotient_not_unramified_over_basePlace hL t i j w h hu'
      · exact GlobalTheory.FunObj.SqNum.not_unrAt_alpha_div_beta_over_S₁ hL t i j w h hu'
    · rcases Finset.mem_union.1 hw with h | h
      · unfold Places.W0 at h
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
        exact hs (by rw [G.pl.under_w hv]; exact hv)
      · exact GlobalTheory.TwistRam.not_unrAt_alpha_div_beta hL t i j w w h rfl hs hu'
  · obtain ⟨ε, hε⟩ := GlobalTheory.StabDense.exists_placeIdem (D := D) (w.under (𝓞 D.host.F))
    have hs : w.under (𝓞 D.host.F) ∉ G.pl.S0 := fun hs =>
      hw (G.pl.w _) (Finset.mem_union_left _ (by unfold Places.W0; exact Finset.mem_image_of_mem _ hs)) (G.pl.under_w hs)
    have h1 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.level_character_unramified_mu G μ₀ hL t _ ε hε hs (fun P hP => hw P (Finset.mem_union_right _ hP)) j) rfl
    have h2 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.grid_characters_unramified G μ₀ hL t _ ε hε hs i).1 rfl
    have h3 := GlobalTheory.BasePairChar.unrAt_of_unramAt hε (GlobalTheory.T.grid_characters_unramified G μ₀ hL t _ ε hε hs i).2 rfl
    have h4 : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (Lc.eta ^ n) w := fun n => by
      induction n with
      | zero => rw [pow_zero]; exact fun _ _ => map_one Circle.toUnits
      | succ n ih => rw [pow_succ]; exact ih.mul h3
    exact ⟨h1.mul (h4 _), h2.mul (h4 _)⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFiniteDataMatchEachStage
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
namespace GlobalTheory.StageFinMatch
end GlobalTheory.StageFinMatch
namespace GlobalTheory.StageFinMatch
theorem theta_bottom_finite_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      ∃ κ : ℂ, κ ≠ 0 ∧ r (X.f t) = κ • r' (X.f' t) := by
  intro hP hK hL
  refine gBig_two' (_root_.GlobalTheory.T.finite_place_theta_matching hP hK hL) (_root_.GlobalTheory.T.theta_stage_unique hP hK hL) fun {D T Lc sc} G μ₀ C x b₀ hA hB => ?_
  intro W i j a b A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, P, P', κ, hne, heq⟩ := hA W i j a b A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j a b A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have m1 : GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true FA FW :=
    Submodule.subset_span ⟨_, P, hf, rfl⟩
  have m2 : GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
    Submodule.subset_span ⟨_, P', hf', rfl⟩
  have k : p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) =
      (c * κ) • p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') := by
    rw [hE _ m1, hE' _ m2, heq, LinearEquiv.map_smul, smul_smul]
  have kne : p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f t) P) ≠ 0 := by
    rw [hE _ m1]
    exact smul_ne_zero hc ((LinearEquiv.map_ne_zero_iff E).mpr hne)
  rw [hp _ hf P, hp' _ hf' P', ← LinearEquiv.map_smul, TensorProduct.smul_tmul'] at k
  rw [hp _ hf P] at kne
  have kne' : q P ⊗ₜ[ℂ] r (X.f t) ≠ 0 := fun h0 => kne (by rw [h0, map_zero])
  exact tmul_right_prop (e.injective k) kne'
end GlobalTheory.StageFinMatch
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_finiteData_match_each_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      ∃ κ : ℂ, κ ≠ 0 ∧ r (X.f t) = κ • r' (X.f' t) := by
  first | exact @_root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match | exact _root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match | (intros; apply _root_.GlobalTheory.StageFinMatch.theta_bottom_finite_match <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageNonzeroAtFinitePlaces
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
namespace GlobalTheory.StageFinNonzero
theorem theta_stage_finite_part_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      r' (X.f' t) ≠ 0 := by
  intro hP hK hL
  refine gBig_of_two (_root_.GlobalTheory.T.finite_place_theta_matching hP hK hL) (_root_.GlobalTheory.T.theta_stage_unique hP hK hL) fun {D T Lc sc} G μ₀ C x b₀ hA hB => ?_
  intro W i j a b A A' WW X hX FA FA' FW t hf hf' Pi rf rl p p' hm Pr Pf q q' r r' e hq hq' hp hp'
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, P, P', κ, hne, heq⟩ := hA W i j a b A A' WW X hX FA FA' FW t hf hf'
  obtain ⟨E, c, hc, hE, hE'⟩ := hB W i j a b A A' WW X hX FA FA' FW t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' hm₀ hm
  have m2 : GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false FA' FW :=
    Submodule.subset_span ⟨_, P', hf', rfl⟩
  have n0 : p₀' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at heq
    exact hne heq
  have n1 : p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
    rw [hE' _ m2]
    exact (LinearEquiv.map_ne_zero_iff E).mpr n0
  intro h0
  rw [hp' _ hf' P', h0, TensorProduct.tmul_zero, map_zero] at n1
  exact n1 rfl
end GlobalTheory.StageFinNonzero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_stage_nonzero_at_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
    ∀ (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (t : T),
    GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f t) → GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' t) →
    ∀ (Pi : ModuleCat.{0} ℂ) rf rl p p', GlobalTheory.SquareComm.IsMatch W.ψ W.θ FA FA' FW (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2))
      (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2)) (X.ω t) (X.ω' t) Pi rf rl p p' →
    ∀ (Pr Pf : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr)
      (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
      Function.Surjective q → Function.Surjective q' →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW f P) = e (q P ⊗ₜ r f)) →
      (∀ f, GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW f → ∀ P, p' (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
      r' (X.f' t) ≠ 0 := by
  first | exact @_root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero | exact _root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero | (intros; apply _root_.GlobalTheory.StageFinNonzero.theta_stage_finite_part_ne_zero <;> assumption)
end
end

