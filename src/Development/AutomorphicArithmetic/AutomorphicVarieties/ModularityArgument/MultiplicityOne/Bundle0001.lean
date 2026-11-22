import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockGA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CmbPiA
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.REndoOf
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CuspReadPTrue
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0007
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.TestsEx
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.Bundle0006
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ValNil
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.ThetaFixTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.RCountAt
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Classical

namespace UpperTheory.V.Z.Mult

def NoData : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∀ D : CD E n, ¬ D.Has π → D.Reg →
    (∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∃ B, D.Sat w B ∧ inv B = B) →
    ¬ ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def GeomTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → dimW lam ≠ 0 ∧
    ∀ f, GlobalTheory.BCT.IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) →
      trOn (forms S lam K') (hop S K' f) = dimW lam * geomU S lam f

def LevTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (K' K'' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K'' → (∀ w, K'' w ≤ K' w) →
    ∀ f, GlobalTheory.BCT.IsTest (KL n) K' f → trOn (forms S lam K'') (hop S K'' f) = trOn (forms S lam K') (hop S K' f)

def EvalD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (Z : Finset (Pl E)), SplitIn S Z → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    (∀ w ∉ Z, K' w = KL n w) → ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
    ∃ (t : ι → ∀ w : Pl E, SmIrr (GLw n w)) (B : ι → Pl E → Multiset ℂˣ),
      (∀ i, (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU (σ i) w) ∧ (∀ w ∈ Z, Cp (σ i) w (t i w)) ∧
        ∀ w, Off Z w → IsSplitAt w → ∃ τ, Cp (σ i) w τ ∧ HasSatGL w τ.ρ (B i w)) ∧
      ∀ f : ∀ w : Pl E, GLw n w → ℂ, (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ e₁ e₂ k, GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) ∧
        trOn (forms S lam K') (hop S K' (famU Z T f e₁ e₂ k)) =
          dimW lam * ∑ i, (∏ w ∈ Z, trc (t i w).ρ (KGL w n) (f w)) * val1 T e₁ e₂ (B i) ^ k

def CpUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ w, IsSplitAt w →
  ∀ τ τ' : SmIrr (GLw n w), Cp σ w τ → Cp σ w τ' →
    (∀ B, HasSatGL w τ.ρ B → HasSatGL w τ'.ρ B) ∧ ∀ f, trc τ.ρ (KGL w n) f = trc τ'.ρ (KGL w n) f

def LevInd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) → K ≤ KL n w →
  ∃ f : GLw n w → ℂ, Lc (KGL w n) f ∧ (∀ K₁ ≤ K, IsHecke K₁ fun x : UL n w => f x.1) ∧
    ∀ τ : SmIrr (GLw n w), fixed (τ.ρ.comp (UL n w).subtype) K ≠ ⊥ → trc τ.ρ (KGL w n) f ≠ 0

def LcLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ f : GLw n w → ℂ, Lc (KGL w n) f →
  ∃ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) ∧ K ≤ KL n w ∧ IsHecke K fun x : UL n w => f x.1

def ChoiceM : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S →
  ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w, ¬ IsSplitAt w → K' w = KL n w) →
  ∃ (Z : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)) (w₀ : Pl E) (f₀ : GLw n w₀ → ℂ),
    SplitIn S Z ∧ (∀ w ∈ S, w ∉ Z → K' w = KL n w) ∧ (∀ w, Off Z w → (CG.mk π).HasSat w (B w) ∧ μ.UnrAt w) ∧
    (∀ w ∈ Z, π.IsLocComp w (τ w)) ∧ w₀ ∈ Z ∧ Lc (KGL w₀ n) f₀ ∧ trc (τ w₀).ρ (KGL w₀ n) f₀ ≠ 0 ∧
    ∀ y, f₀ y ≠ 0 → y.val.charpoly.Separable

def OffSec : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' K'' : ∀ w : Pl E, Subgroup (UL n w)), (∀ w ∈ S, K' w = K'' w) →
  globLev S K' = globLev S K''

def CountAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (Z : Finset (Pl E)), SplitIn S Z →
  ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w ∉ Z, K' w = KL n w) →
    ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
    ∃ (J : Type) (_ : Fintype J) (C : J → Pl E → Multiset ℂˣ),
      (∀ j, ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (C j w).card = n ∧ C j w ≠ B w) ∧
      ∀ f : ∀ w : Pl E, GLw n w → ℂ, (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ e₁ e₂, val1 T e₁ e₂ B = 1 → (∀ j, val1 T e₁ e₂ (C j) = 0) →
        ∀ k, GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) ∧ (1 ≤ k → trOn (forms S lam K') (hop S K' (famU Z T f e₁ e₂ k)) =
          dimW lam * ((Nat.card {i // At π (σ i)} : ℂ) * ∏ w ∈ Z, trc (τ w).ρ (KGL w n) (f w)))

def RCountAt : Prop := CompOf → EvalD → CpUniq → Places → CountAt

def Ident : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ lam : InfinitePlace E → DomWeight n, ∃ a : ℝ, 0 < a ∧
  ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
  ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)) (f : ∀ w : Pl E, GLw n w → ℂ),
    (∀ w, Off Z w → (CG.mk π).HasSat w (B w) ∧ μ.UnrAt w) →
    (∀ w ∈ Z, π.IsLocComp w (τ w) ∧ Lc (KGL w n) (f w) ∧ trc (τ w).ρ (KGL w n) (f w) ≠ 0) →
    (∃ w ∈ Z, ∀ y, f w y ≠ 0 → y.val.charpoly.Separable) →
    ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w ∉ Z, K' w = KL n w) →
    (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
    ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ → (Nat.card {i // At π (σ i)} : ℝ) = a

def RIdent : Prop := NoData → CountAt → GeomTr → G2s → MatchUnit → MatchSplit → EndoBlockS → StableBlockSA → Ident

def RMult : Prop := Ident → CountAt → LevTr → GeomTr → LevInd → LcLev → ChoiceM → OffSec → MuEx → Mult

end UpperTheory.V.Z.Mult
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableGA
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem pow_norm_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (U : H →L[ℂ] H) (k : ℕ) :
    ‖U ^ k‖ ≤ (‖U‖ + 1) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity))

private theorem final_bd (κ g t : ℂ) (hκ : κ ≠ 0) (C a b u ρ : ℝ) (N k : ℕ) (hρ : 0 < ρ) (hu : 0 ≤ u) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ ρ ^ k) (hb : b ≤ (u + 1) ^ k)
    (h : ‖κ * 1 * g - t / 2‖ ≤ C * (1 + k) ^ N * a + C * b * (ρ / (u + 1)) ^ k) :
    ‖g - t / (2 * κ)‖ ≤ ‖κ‖⁻¹ * (2 * |C|) * (1 + k) ^ N * ρ ^ k := by
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  have e : κ * 1 * g - t / 2 = κ * (g - t / (2 * κ)) := by field_simp
  rw [e, norm_mul] at h
  have h1 : (1 : ℝ) ≤ (1 + k) ^ N := one_le_pow₀ (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have h2 : C * (1 + k) ^ N * a ≤ |C| * (1 + k) ^ N * ρ ^ k :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) ha ha0 (by positivity)
  have h3 : C * b * (ρ / (u + 1)) ^ k ≤ |C| * (1 + k) ^ N * ρ ^ k := by
    calc C * b * (ρ / (u + 1)) ^ k ≤ |C| * (u + 1) ^ k * (ρ / (u + 1)) ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self C) hb hb0 (abs_nonneg C)) (by positivity)
      _ = |C| * 1 * ρ ^ k := by
          rw [mul_assoc, ← mul_pow, mul_one]
          congr 2
          field_simp
      _ ≤ _ := by gcongr
  rw [mul_assoc, mul_assoc, le_inv_mul_iff₀ hκ']
  linarith

end UpperTheory.Zero.ConvolutionTheory.EB

open UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Z.Mult.stableGA :
    PiFin → PiAdm → GrowthPiJ → CmbPiA → CuspReadI → UpperTheory.V.Z.Mult.StableBlockGA := by
  intro hFin hAdm hG hPi hR E _ _ _ hE n hn l₁ l₂
  have hSp := specP _ (cuspReadP_inf hR)
  haveI : Nontrivial (InfinitePlace E) := GlobalTheory.T.nontrivial_infinite_place_of_unramified E hE
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  haveI : BorelSpace (GA E 0) := ⟨rfl⟩
  obtain ⟨μ₁, hμ₁⟩ := haarEx E n
  obtain ⟨μ₂, hμ₂⟩ := haarEx E 0
  obtain ⟨D, -, hD⟩ := hG E n hn μ₁ μ₂
  obtain ⟨A⟩ := arEx E n 0 l₁ l₂ D
  obtain ⟨u₁, hu₁⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E n
  obtain ⟨u₂, hu₂⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E 0
  obtain ⟨κ, hκ, hell⟩ := cmbEll E hE n 0 l₁ l₂ D A μ₁ μ₂ hμ₁ hμ₂
  obtain ⟨c₁, hc₁, hl⟩ := hPi E hE n hn l₁ l₂ D A u₁ u₂ hu₁
  refine ⟨c₁ / ‖2 * κ‖, div_pos hc₁ (norm_pos_iff.2 (mul_ne_zero two_ne_zero hκ)),
    fun π hreg hdual hinf S hS Z hZ B τ hB hτ => ?_⟩
  have hθ : ThetaFix π := DiscreteGroups.T1.G.thetaFixOf E n hn π hdual
  obtain ⟨c₀, hc₀, htr⟩ := hl π hreg hdual hinf S hS Z hZ B τ hB hτ
  refine ⟨c₀ / (2 * κ), by rw [norm_div, hc₀], fun φ hφ hrg => ?_⟩
  obtain ⟨L, hL⟩ := lvEx E n 0 Z φ hφ
  obtain ⟨c, hc, htest⟩ := cmbTest E n 0 l₁ l₂ D A S Z L hS hZ u₁ u₂ hu₁ hu₂
  obtain ⟨k1, k2, -⟩ := kgFacts E n S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) (fun w hw => (L.off w hw).1)
  obtain ⟨k3, -, -⟩ := kgFacts E 0 S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) (fun w hw => (L.off w hw).2)
  have hT := fun W hW => testsEx hAdm E n hn l₁ l₂ D A π hθ (Kg S L.L₁) W k1 k2 hW
  obtain ⟨kp, ko, -⟩ := hT ⊥ inferInstance
  haveI : CompleteSpace ((piSp D π A.blk.I)ᗮ : Submodule ℂ A.blk.Hb) := (Submodule.isClosed_orthogonal _).completeSpace_coe
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, a3⟩ := hSp E n 0 l₁ l₂ D A S Z L hS hZ {π} Set.subsingleton_singleton
    (fun π' h => by rw [Set.mem_singleton_iff.1 h]; exact hθ.1) (piSp D π A.blk.I)ᗮ ko (fun W hW => (hT W hW).2.2)
  refine ⟨J, hJ, D₁, B₁, fun j => ⟨(a1 j).1 π rfl, fun w hw => ((a1 j).2 w hw).1⟩, fun j => (a2 j).1,
    fun T hTS hd e₁ e₂ ρ hT' hρ hv => ?_⟩
  obtain ⟨U, R, hR, hU, hn'⟩ := a3 T e₁ e₂ ρ ⟨hTS, hT'⟩ hd hρ fun j => by
    rw [valNil E n Z T S (D₂ j) (B₁ j) (B₂ j) e₁ e₂ hS hZ hTS hd fun w hw => ((a1 j).2 w hw).2]
    exact hv j
  obtain ⟨o₁, o₂, r₀, r₁, hr₀, hr₁, hk⟩ := powRep E n 0 l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hL hR hU
  have b₁ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₁ o₁
  have b₂ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₂ o₂
  have hfin := hFin E n hn D π hθ A.μa A.μb A.ha A.hb _ _ Unit _ _ _ _ _ _ ((Kg S L.L₁).prod (Kg S L.L₂)) o₁.ka o₁.kb o₁.ψ
    (k1.prod k3) (fun x y u hu h => (idmAct E n 0 l₁ l₂ D A S Z L hS hZ).2.1 T φ _ _ hL x y u.1 hu.1 u.2 hu.2 h)
  obtain ⟨C, N, hb⟩ := hD π hθ A.blk.I _ _ _ _ A.tw (c * (1 + r₀)) (c * r₁) (ρ / (‖U‖ + 1)) b₁.1 b₂.1 hfin b₁.2.1 b₂.2.1
    (by positivity) (by positivity) (by positivity)
  obtain ⟨CU, u1, -, u3⟩ := hU
  obtain ⟨v1, v2⟩ := (repAlg E A.blk (chi l₁) (chi l₂)).1 CU _ _ u1
  rw [u3] at v2
  have p1 := powNorm A.blk.Hb (piSp D π A.blk.I) U _ (kp _ _ v1 v2) le_rfl
  have p2 := powNorm A.blk.Hb (piSp D π A.blk.I)ᗮ U ρ (ko _ _ v1 v2) hn'.le
  obtain ⟨-, hs⟩ := seenFam E n 0 S Z L hZ φ T e₁ e₂ hL ⟨hTS, hT'⟩
  refine ⟨‖κ‖⁻¹ * (2 * |C|), N, fun k => ?_⟩
  obtain ⟨Cm, c1, c2, c3⟩ := hk k
  have hrk : 0 ≤ r₀ + k * r₁ := by positivity
  obtain ⟨q1, q2⟩ := (repAlg E A.blk (chi l₁) (chi l₂)).1 Cm _ _ c1
  have ht := (htest φ T _ _ Cm _ hL hrg hrk c1).2
  have he := hell S Z L hS hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k Cm _ hL hrg ⟨hTS, hT'⟩ hrk c1
  have hw := htr L φ T _ _ Cm _ hL (hs k).1 hd c1
  rw [c3] at q2
  have hb' := hb k (U ^ k) Cm.Φ _ q1 q2 (p1 k).1 (p2 k).1
    (by rw [show c * (1 + r₀) + k * (c * r₁) = c * (1 + (r₀ + k * r₁)) by ring]; exact ht) hw
  rw [he, c2, (hs k).2.2.2] at hb'
  have hf := final_bd κ _ _ hκ C _ _ ‖U‖ ρ N k hρ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (p2 k).2 (pow_norm_le U k) hb'
  refine le_of_eq_of_le (congrArg norm ?_) hf
  ring
end
end

