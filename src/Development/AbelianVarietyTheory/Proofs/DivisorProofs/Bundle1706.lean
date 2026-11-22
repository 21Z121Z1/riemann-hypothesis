import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleMod
section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.AdeleTensorModule

theorem adele_mod (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 1 ≤ N)
    (y : FiniteAdeleRing (𝓞 F) F) (hy : y ∈ Formalism.UG.intAd F) :
    ∃ a : 𝓞 F, ∃ w ∈ Formalism.UG.intAd F,
      y = algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) + (N : FiniteAdeleRing (𝓞 F) F) * w := by
  have hN0 : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨a, ha⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx (R := 𝓞 F) (K := F) y hy (N : 𝓞 F) hN0
  refine ⟨a, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((N : F)⁻¹) *
    (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)), fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) ((N : F)⁻¹) *
      (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀]
    have hv : Valued.v (algebraMap F (v.adicCompletion F) (N : F)) = v.intValuation (N : 𝓞 F) := by
      have := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.val_R (K := F) v (N : 𝓞 F)
      rwa [map_natCast (algebraMap (𝓞 F) F)] at this
    have h0 : v.intValuation (N : 𝓞 F) ≠ 0 := v.intValuation_ne_zero _ hN0
    rw [hv]
    calc (v.intValuation (N : 𝓞 F))⁻¹ * Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
        ≤ (v.intValuation (N : 𝓞 F))⁻¹ * v.intValuation (N : 𝓞 F) := by
          gcongr
          exact ha v
      _ = 1 := inv_mul_cancel₀ h0
  · rw [← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hNF, map_one, one_mul]
    ring

theorem tens_mod (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (hN : 1 ≤ N) (x : E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (hx : x ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F)) :
    ∃ a ∈ Formalism.UG.intOE E,
      ∃ z ∈ Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F),
        x = Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a +
          (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * z := by
  set S := Formalism.UG.tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (Formalism.UG.intOE E) (Formalism.UG.intAd F) with hS
  set ι := Formalism.UG.inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) with hι
  have hl : ∀ a ∈ Formalism.UG.intOE E, ι a ∈ S := fun a ha =>
    Subring.subset_closure (Or.inl ⟨⟨a, ha⟩, rfl⟩)
  have hr : ∀ w ∈ Formalism.UG.intAd F, (1 : E) ⊗ₜ[F] w ∈ S := fun w hw =>
    Subring.subset_closure (Or.inr ⟨⟨w, hw⟩, rfl⟩)
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨y, rfl⟩
    · exact ⟨a, a.2, 0, zero_mem _, by rw [mul_zero, add_zero]; rfl⟩
    · obtain ⟨a, w, hw, e⟩ := adele_mod F N hN y y.2
      refine ⟨algebraMap F E (a : F), ⟨algebraMap (𝓞 F) (𝓞 E) a, rfl⟩, (1 : E) ⊗ₜ[F] w, hr w hw, ?_⟩
      have e2 := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := E)
        (B := FiniteAdeleRing (𝓞 F) F)) e
      rw [map_add, map_mul, map_natCast, AlgHom.commutes] at e2
      exact e2
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by rw [map_zero, mul_zero, add_zero]⟩
  | one => exact ⟨1, one_mem _, 0, zero_mem _, by rw [map_one, mul_zero, add_zero]⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    obtain ⟨b, hb, w, hw, rfl⟩ := ihy
    exact ⟨a + b, add_mem ha hb, z + w, add_mem hz hw, by rw [map_add]; ring⟩
  | neg x _ ihx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    exact ⟨-a, neg_mem ha, -z, neg_mem hz, by rw [map_neg]; ring⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := ihx
    obtain ⟨b, hb, w, hw, rfl⟩ := ihy
    refine ⟨a * b, mul_mem ha hb, ι a * w + z * ι b + (N : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * (z * w),
      add_mem (add_mem (mul_mem (hl a ha) hw) (mul_mem hz (hl b hb)))
        (mul_mem (natCast_mem S N) (mul_mem hz hw)), ?_⟩
    rw [map_mul]; ring

theorem main : ∀ {D : Formalism.BasicNotions.D7} (N : ℕ), (1 : ℕ) ≤ N → ∀ x ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
    ∃ a ∈ Formalism.UG.intOE ((Formalism.BasicNotions.D7.host D).E), ∃ z ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D,
      x = (Formalism.MainNotions.StandardLatticesGL3.inc D : (Formalism.BasicNotions.D7.host D).E → Formalism.MainNotions.StandardLatticesGL3.AE D) a +
        (↑N : Formalism.MainNotions.StandardLatticesGL3.AE D) * z :=
  fun {D} N hN x hx => tens_mod ℚ D.host.E N hN x hx

end GlobalTheory.AdeleTensorModule

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HatPullback

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fm_mulVec_tmul (M : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    GlobalTheory.UnRep.fm F M *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i := by
  funext i
  simp [GlobalTheory.UnRep.fm, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

theorem fm_mul' (A B : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.UnRep.fm F (A * B) = GlobalTheory.UnRep.fm F A * GlobalTheory.UnRep.fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)

theorem fm_one' : GlobalTheory.UnRep.fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

theorem fm_mulVec_mem_hat (M : Matrix (Fin n) (Fin n) E) {L L' : Set (Fin n → E)}
    (h : ∀ x ∈ L, M *ᵥ x ∈ L') {w : Fin n → GlobalTheory.AdLat.RA F E} (hw : w ∈ GlobalTheory.AdLat.hat F L) :
    GlobalTheory.UnRep.fm F M *ᵥ w ∈ GlobalTheory.AdLat.hat F L' := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [fm_mulVec_tmul]
    exact AddSubgroup.subset_closure ⟨a, ha, M *ᵥ x, h x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (A : GL (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (w : Fin n → GlobalTheory.AdLat.RA F E),
    GlobalTheory.UnRep.fm F A.1 *ᵥ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      w ∈ GlobalTheory.AdLat.hat F ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n A Λ w
  have hmem : ∀ x : Fin n → E, x ∈ ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) :
      Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ A.1 *ᵥ x ∈ Λ := fun x => by
    simp [Matrix.mulVecLin_apply]
  constructor
  · intro hw
    have h2 := fm_mulVec_mem_hat (F := F) (A⁻¹).1
      (L := (Λ : Set (Fin n → E)))
      (L' := ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) :
        Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))
      (fun y hy => by
        rw [hmem, Matrix.mulVec_mulVec, A.mul_inv, Matrix.one_mulVec]
        exact hy) hw
    rwa [Matrix.mulVec_mulVec, ← fm_mul', A.inv_mul, fm_one', Matrix.one_mulVec] at h2
  · intro hw
    exact fm_mulVec_mem_hat (F := F) A.1 (fun x hx => (hmem x).1 hx) hw

end GlobalTheory.HatPullback
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZeroStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  first | exact @GlobalTheory.GhostKer.mu_dvd_of_ghost | exact GlobalTheory.GhostKer.mu_dvd_of_ghost | (intros; apply GlobalTheory.GhostKer.mu_dvd_of_ghost <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedAtLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TwistRam

theorem not_unrAt_alpha_div_beta : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) (P : HeightOneSpectrum (𝓞 D.host.E)), P ∈ L.Q t →
      P.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w P hP hu hS
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt w := G.ch.unr _ hm.1 hm.2 w hS
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hS (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : ¬ (L.xiH t).UnrAt w := by
    refine (hL.Q_ram t w).2 ?_
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (P := P) (Q := w) hu.symm with h | h
    · exact Or.inl (h ▸ hP)
    · exact Or.inr ⟨P, hP, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  have e0 : alpha G t i j / beta G i j = G.nu t i (j + 1) := mul_div_mul_right_eq_div _ _ _
  rw [e0, GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL)]
  intro hn
  apply hxi
  have e : L.xiH t = GlobalTheory.FunObj.SqNum.nuH G t i j * G.ch.chiH (D.R.m - i) / L.C.mu0 j := by
    rw [GlobalTheory.FunObj.SqNum.nuH, div_mul_cancel, mul_div_cancel_left]
  rw [e, div_eq_mul_inv]
  exact (hn.mul hchi).mul hmu.inv

end GlobalTheory.TwistRam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaDivBetaRamifiedFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj.SqNum

theorem not_unrAt_alpha_div_beta_over_S₁ : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∈ S1 D →
      ¬ GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j / beta G i j) w := by
  intro D T L sc G μ₀ hL t i j w hw
  have e : alpha G t i j / beta G i j = G.nu t i ((j : ℕ) + 1) := by
    simp only [alpha, beta, GridData.nu]
    exact mul_div_mul_right_eq_div _ _ _
  rw [e, GlobalTheory.LFun.unrAt_iff_of_chrEq (chrEq_nu (G := G) (t := t) (i := i) (j := j) hL) w]
  intro hu
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  refine (G.ch.lev1 _ hi1 hi2 w hw).2 fun x hx h1 => ?_
  have a1 := (L.C.isMu0 j).tame w x hx h1
  have a2 := hL.xi_tame t w x hx h1
  have a3 := hu x hx
  simp only [nuH, div_eq_mul_inv, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv, a1, a2, one_mul] at a3
  exact inv_eq_one.1 a3

end GlobalTheory.FunObj.SqNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaHFinIdlIncU
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl finIdl_incU)

noncomputable section

namespace GlobalTheory.BottomReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem xiH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t : T) (a : D.host.Eˣ) :
    (L.xiH t).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) = 1 := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 := (L.xiH t).2.2 a
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU] at h1
  have h2 := HChar.inf_eq_one_of_order hn ho a
  rw [HChar.inf, MonoidHom.comp_apply] at h2
  rw [h2, one_mul] at h1
  exact h1

theorem nuH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (i j : Fin D.R.m) (a : D.host.Eˣ) :
    (nuH G t i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      (nuH G t' i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) := by
  simp only [nuH, Subgroup.coe_div, Subgroup.coe_mul, MonoidHom.div_apply, MonoidHom.mul_apply,
    xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]

theorem prod_pow_eq {N : ℕ} (χ : HeckeU D N) (e : ℤ) (ν : HChar D.host.E) (hf : ∀ x, χ.f x ^ e = (ν⁻¹).1 (finIdl D x))
    (a : D.host.E) (ha : a ≠ 0) :
    ∏ τ, (Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ)) ^ (e * χ.n τ) =
      ((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D (Units.mk0 a ha))) : ℂˣ) : ℂ) := by
  set u := Units.mk0 a ha
  set φ := Formalism.L2.Host.embTau D
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := congrArg (fun z : ℂˣ => (z : ℂ)) (hf (GlobalTheory.NormSum.UnramHecke.incU D u))
  simp only [Units.val_zpow_eq_zpow_val] at hB
  have hB' : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e =
      (((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D u))) : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    exact hB
  have hX : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹ :=
    eq_inv_of_mul_eq_one_left hA
  rw [hX, inv_zpow', ← Finset.prod_zpow] at hB'
  simp_rw [mul_comm e, zpow_mul]
  have := congrArg (·⁻¹) hB'
  simp only [inv_inv] at this
  rw [← this, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_neg, neg_neg]

theorem alphaH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (i j : Fin D.R.m) (a : D.host.Eˣ) :
    (alphaH L t i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      (alphaH L t' i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) := by
  simp only [alphaH, Subgroup.coe_mul, MonoidHom.mul_apply, xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]

theorem exps_eq_of {N N₁ : ℕ} (χ : HeckeU D N) (χ₁ : HeckeU D N₁) (e e₁ : ℤ) (ν ν₁ : HChar D.host.E)
    (hν : ∀ a : D.host.Eˣ, ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      ν₁.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)))
    (hf : ∀ x, χ.f x ^ e = (ν⁻¹).1 (finIdl D x)) (hf₁ : ∀ x, χ₁.f x ^ e₁ = (ν₁⁻¹).1 (finIdl D x)) (τ : D.what₂.Tau) :
    e * χ.n τ = e₁ * χ₁.n τ := by
  have hc := GlobalTheory.SplitWeight.exps_eq_zero (Formalism.L2.Host.embTau D) (GlobalTheory.SplitWeight.embTau_inj D)
    (GlobalTheory.SplitWeight.embTau_ne_conj D) (fun τ => e * χ.n τ - e₁ * χ₁.n τ) (fun a ha => by
      have hne : ∀ τ, Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
        div_ne_zero (by simpa using ha) (by exact_mod_cast norm_ne_zero_iff.2 (by simpa using ha))
      simp_rw [zpow_sub₀ (hne _), Finset.prod_div_distrib, prod_pow_eq χ e _ hf a ha, prod_pow_eq χ₁ e₁ _ hf₁ a ha, hν]
      exact div_self (Units.ne_zero _))
  have h := congrFun hc τ
  simpa [sub_eq_zero] using h

theorem pair_real_eq {δ t0 δ₁ t₁ : ℂ} {Q Q₁ : ℕ} (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ : GlobalTheory.NormSum.Pair D ⊤ δ₁ t₁ Q₁)
    (ν ν₁ : HChar D.host.E) (hν : ∀ a : D.host.Eˣ, ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      ν₁.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)))
    (hf : ∀ x, P.W.chV'.f x ^ P.W.ep' = (ν⁻¹).1 (finIdl D x))
    (hf₁ : ∀ x, P₁.W.chV'.f x ^ P₁.W.ep' = (ν₁⁻¹).1 (finIdl D x)) (hd : P.d = P₁.d) :
    (∀ τ, P.W.ep' * P.W.chV'.n τ = P₁.W.ep' * P₁.W.chV'.n τ) ∧ P.n = P₁.n := by
  have h := exps_eq_of P.W.chV' P₁.W.chV' P.W.ep' P₁.W.ep' ν ν₁ hν hf hf₁
  refine ⟨h, funext fun τ => ?_⟩
  have h1 := P.wt τ
  have h2 := P₁.wt τ
  rw [h τ, hd] at h1
  have : (P.n τ : ℤ) = P₁.n τ := by omega
  exact_mod_cast this

theorem bottom_real_eq {μ₀ : T} (hL : L.Is μ₀) {i j : Fin D.R.m} {t t' : T} {𝔪 𝔪₁ : Ideal (𝓞 D.host.E)}
    {δ t0 δ₁ t₁ : ℂ} {Q Q₁ : ℕ} {P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q} {P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ₁ t₁ Q₁}
    (h : IsBottom G t i j 𝔪 P P') (h₁ : IsBottom G t' i j 𝔪₁ P₁ P₁') :
    (P.a = P₁.a ∧ P.d = P₁.d ∧ P.n = P₁.n ∧ (∀ τ, P.W.ep' * P.W.chV'.n τ = P₁.W.ep' * P₁.W.chV'.n τ) ∧
        ∀ τ, P.W.ep * P.W.chV.n τ = P₁.W.ep * P₁.W.chV.n τ) ∧
      (P'.a = P₁'.a ∧ P'.d = P₁'.d ∧ P'.n = P₁'.n ∧ (∀ τ, P'.W.ep' * P'.W.chV'.n τ = P₁'.W.ep' * P₁'.W.chV'.n τ) ∧
        ∀ τ, P'.W.ep * P'.W.chV.n τ = P₁'.W.ep * P₁'.W.chV.n τ) := by
  obtain ⟨ha, ha', hd, hd'⟩ := h.rank
  obtain ⟨hb, hb', he, he'⟩ := h₁.rank
  have hν := nuH_finIdl_incU G hL t t' i j
  have hdd : P.d = P₁.d := by rw [hd, he]
  have hdd' : P'.d = P₁'.d := by rw [hd', he', hdd]
  obtain ⟨r1, r2⟩ := pair_real_eq P P₁ _ _ hν h.chars.2 h₁.chars.2 hdd
  obtain ⟨r1', r2'⟩ := pair_real_eq P' P₁' _ _ hν h.chars'.2 h₁.chars'.2 hdd'
  refine ⟨⟨by rw [ha, hb], hdd, r2, r1, ?_⟩, ⟨by rw [ha', hb'], hdd', r2', r1', ?_⟩⟩
  · exact exps_eq_of P.W.chV P₁.W.chV P.W.ep P₁.W.ep _ _ (fun _ => rfl) h.chars.1 h₁.chars.1
  · refine exps_eq_of P'.W.chV P₁'.W.chV P'.W.ep P₁'.W.ep (alphaH L t i j)⁻¹ (alphaH L t' i j)⁻¹ (fun a => ?_)
      (fun x => by rw [inv_inv]; exact h.chars'.1 x) (fun x => by rw [inv_inv]; exact h₁.chars'.1 x)
    show ((alphaH L t i j).1 _)⁻¹ = ((alphaH L t' i j).1 _)⁻¹
    rw [alphaH_finIdl_incU hL t t' i j a]

end GlobalTheory.BottomReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaUnramifiedOutside
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FunObj

theorem alpha_unrAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) ∉ G.pl.S0 →
      (∀ P ∈ L.Q t, P.under (𝓞 D.host.F) ≠ w.under (𝓞 D.host.F)) → GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (alpha G t i j) w := by
  intro D T L sc G μ₀ hL t i j w hS hQ
  have hmu : (L.C.mu0 j).UnrAt w := (L.C.isMu0 j).unr _ fun k hk => hS (by
    have h : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
      rw [map_natCast]; exact hk
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have hxi : (L.xiH t).UnrAt w := by
    by_contra hc
    rcases (hL.Q_ram t _).1 hc with h | ⟨P, h, hc'⟩
    · exact hQ _ h rfl
    · exact hQ P h (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc')
  have h1 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.mu0 j) w).2 hmu
  have h2 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 hxi
  have h3 := (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 (L.C.isEta.unr w)
  have h4 : ∀ n : ℕ, GlobalTheory.LFun.UnrAt (F := D.host.F) (E := D.host.E) (L.eta ^ n) w := fun n => by
    induction n with
    | zero => rw [pow_zero]; exact fun _ _ => Units.ext rfl
    | succ n ih => rw [pow_succ]; exact ih.mul h3
  exact (h1.mul h2).mul (h4 _)

end GlobalTheory.FunObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniSimpleZerosGenericSections
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BertiniTop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem bertini : Quoted → Bertini := by
  intro hq F _ _ T hG hB δ f hf
  obtain ⟨-, hdeg, hdim⟩ :=
    GlobalTheory.ImageDegree.degree_image_eq_topSelf hq F T.toLinSys hG.alg.variety hG.alg.bpf hB
  have hprime : T.imageIdeal.IsPrime := HeightExists.isPrime_imageIdeal (S := T.toLinSys) hG.alg.variety
  have hhom : ∀ a ∈ T.imageIdeal, ∀ n : ℕ, homogeneousComponent n a ∈ T.imageIdeal := by
    intro a ha n
    have h := T.toLinSys.isHomogeneous_imageIdeal n ha
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin T.N) F) a n : MvPolynomial (Fin T.N) F) =
      homogeneousComponent n a from MvPolynomial.decomposition.decompose'_apply a n] at h
  have hδ : (δ : ℤ) = T.del := by
    rw [GlobalTheory.ChowDegree.degree_eq_hilbertDegree_of_isChowForm F T.D T.N δ T.imageIdeal f hf hprime hhom]
    exact hdeg
  refine ⟨hδ, ?_⟩
  obtain ⟨d₁, g₁, hg₁, hg₁I, hg₁v⟩ := GlobalTheory.T.exists_form_outside_imageIdeal_vanishing_on_boundary F T hG hB
  obtain ⟨d₂, g₂, hg₂, hg₂I, hg₂f⟩ := GlobalTheory.T.exists_form_finite_fibres_birational_linearSystem F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨Q₁, hQ₁, hQ₁v⟩ := GlobalTheory.T.exists_eliminationForm_generalLinearForms_cone F T.D T.N (d₁ + d₂) T.imageIdeal (g₁ * g₂) hG.alg.variety.one_le hprime hhom
    hdim (hg₁.mul hg₂) fun h => (hprime.mem_or_mem h).elim hg₁I hg₂I
  obtain ⟨Q₂, hQ₂, -, hQ₂n⟩ :=
    GlobalTheory.PencilDisc.exists_poly_noSquare F T.D T.N δ f hf.isChowFormInt.pos hf.homog hf.irred
  refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, fun E _ _ s hs => ?_⟩
  have hs' : aeval (fun p : Fin T.D × Fin T.N => algebraMap E (AlgebraicClosure E) (s p.1 p.2)) (Q₁ * Q₂) ≠ 0 := by
    have h := MvPolynomial.aeval_algebraMap_apply (AlgebraicClosure E)
      (fun p : Fin T.D × Fin T.N => s p.1 p.2) (Q₁ * Q₂)
    exact fun h0 => hs ((map_eq_zero (algebraMap E (AlgebraicClosure E))).1 (h.symm.trans h0))
  rw [map_mul] at hs'
  have hns : NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) :=
    hQ₂n _ _ (right_ne_zero_of_mul hs')
  obtain ⟨hfin, hopen⟩ := GlobalTheory.T.linearSection_finite_inOpen_off_badForm F T hG δ f hf (g₁ * g₂)
    (fun K _ _ x hx => by rw [map_mul, hg₁v K x hx, zero_mul])
    (fun K _ _ y => (hg₂f K y).subset fun x hx => ⟨right_ne_zero_of_mul (by simpa only [map_mul] using hx.1), hx.2⟩)
    E s hns.1 fun x hx h0 => by
      refine left_ne_zero_of_mul hs' (hQ₁v (AlgebraicClosure E) (fun i j => algebraMap E _ (s i j)) _
        (hG.alg.bpf.coords_ne_zero _) (fun a ha => ?_) h0 ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx))
      have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 ha
      rwa [LinSys.baseHom_ptOver] at this
  exact GlobalTheory.T.linearSection_etale_of_squarefree_chowForm F T hG δ f hf hδ E s hfin hopen hns

end GlobalTheory.BertiniTop
end

