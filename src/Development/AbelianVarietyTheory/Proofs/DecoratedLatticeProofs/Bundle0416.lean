import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
import Formalism.LocalToGlobal.Divisibility.Bundle0002
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0396
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0395
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionInvariantPairFunctionalResidue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

namespace GlobalTheory

theorem latPair_hasVal_residue_of_transvections : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (P : GlobalTheory.LatPair.Pair k n) (c : k), 2 ≤ Fintype.card n → c ≠ 0 → (∀ x : n → k, x ∈ P.lat ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∀ (x : n → k) (a : 𝓀[k]), P.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → P.HasVal (x + Pi.single b ((t : k) * x d)) a) → ∃ ε : 𝓀[k], ε ≠ 0 ∧ ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]), P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * ε) := by
  intro k _ _ _ _ n _ _ i P c _hcard hc hlat hcl
  classical
  set e : n → (n → k) := fun b => c • (Pi.single b (1:k) : n → k) with he_def
  have hcoef : ∀ b j, c⁻¹ * e b j = (Pi.single b (1:k) : n → k) j := by
    intro b j
    by_cases h : j = b
    · subst h; simp [he_def, hc]
    · simp [he_def, Pi.single_apply, h]
  have hmem : ∀ b, e b ∈ P.lat := fun b => (hlat _).2 (fun j => by
    rw [hcoef]
    by_cases h : j = b
    · subst h; simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_apply, h, if_false]; exact zero_mem _)
  let v : n → 𝓀[k] := fun b => P.fn ⟨e b, hmem b⟩
  have hv : ∀ b, P.HasVal (e b) (v b) := fun b => P.hasVal_fn ⟨e b, hmem b⟩
  have hzero : ∀ a, a ≠ i → v a = 0 := by
    intro a ha
    have h1 := hcl (e i) (v i) (hv i) a i 1 ha (Or.inl ha)
    have h2 : e i + Pi.single a (((1:𝒪[k]) : k) * e i i) = e i + e a := by
      congr 1
      funext j
      by_cases h : j = a
      · subst h; simp [he_def]
      · simp [he_def, Pi.single_apply, h]
    rw [h2] at h1
    have h3 := h1.sub (hv i)
    rw [add_sub_cancel_left, sub_self] at h3
    exact (hv a).unique h3
  have hsum : ∀ (s : n → 𝒪[k]) (S : Finset n),
      P.HasVal (∑ b ∈ S, s b • e b) (∑ b ∈ S, IsLocalRing.residue 𝒪[k] (s b) * v b) := by
    intro s S
    induction S using Finset.induction_on with
    | empty => simpa using (hv i).sub (hv i)
    | insert b S hb ih =>
      rw [Finset.sum_insert hb, Finset.sum_insert hb]
      exact ((hv b).smul (s b)).add ih
  have hval : ∀ (x : n → k) (hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k]),
      P.HasVal x (IsLocalRing.residue 𝒪[k] ⟨c⁻¹ * x i, hx i⟩ * v i) := by
    intro x hx
    let s : n → 𝒪[k] := fun b => ⟨c⁻¹ * x b, hx b⟩
    have hx' : (∑ b, s b • e b) = x := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j]
      · change ((s j : 𝒪[k]) : k) * (c * (Pi.single j (1:k) : n → k) j) = x j
        simp only [s, Pi.single_eq_same, mul_one]
        field_simp
      · intro b _ hb
        change ((s b : 𝒪[k]) : k) * (c * (Pi.single b (1:k) : n → k) j) = 0
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    have := hsum s Finset.univ
    rw [hx', Finset.sum_eq_single i (fun b _ hb => by rw [hzero b hb, mul_zero]) (by simp)] at this
    exact this
  refine ⟨v i, ?_, hval⟩
  intro h0
  apply P.fn_ne
  refine LinearMap.ext fun y => ?_
  have := hval y ((hlat y).1 y.2)
  rw [h0, mul_zero] at this
  exact (P.hasVal_fn y).unique this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShape
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

theorem GlobalTheory.LatPairStab.stable_lattice_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (L : Submodule 𝒪[k] (n → k)) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x ∈ L, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → x + Pi.single b ((t : k) * x d) ∈ L) → (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∃ x ∈ L, ∃ j, x j = c) → (∀ x : n → k, x ∈ L ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∨ (∀ x : n → k, x ∈ L ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) := by
  intro k _ _ _ _ n _ _ i L c hcard hc hcl hbd hex
  obtain ⟨x₀, hx₀, j, hj⟩ := hex
  obtain ⟨a, hai, haj⟩ : ∃ a, a ≠ i ∧ a ≠ j := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset n) ⊆ {i, j} := fun b _ => by
      by_cases hbi : b = i
      · simp [hbi]
      · simp [h b hbi]
    have h1 := Finset.card_le_card hsub
    have h2 : ({i, j} : Finset n).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ] at h1
    omega

  have hsm : ∀ (s : 𝒪[k]) (b : n) (y : k), (s • (Pi.single b y : n → k) : n → k) = (Pi.single b ((s : k) * y) : n → k) := by
    intro s b y
    ext m
    by_cases hm : m = b
    · subst hm; simp [Subring.smul_def]
    · simp [hm, Subring.smul_def]

  have ha : ∀ t : 𝒪[k], Pi.single a ((t : k) * c) ∈ L := by
    intro t
    have h := L.sub_mem (hcl x₀ hx₀ a j t haj (Or.inl hai)) hx₀
    simpa [hj] using h
  have hca : Pi.single a c ∈ L := by simpa using ha 1

  have hsing : ∀ b, b ≠ i → ∀ t : 𝒪[k], Pi.single b ((t : k) * c) ∈ L := by
    intro b hbi t
    by_cases hba : b = a
    · subst hba; exact ha t
    · have h := L.sub_mem (hcl (Pi.single a c) hca b a t hba (Or.inl hbi)) hca
      simpa using h

  have hi : ∀ t : 𝒪[k], t ∈ IsLocalRing.maximalIdeal 𝒪[k] → Pi.single i ((t : k) * c) ∈ L := by
    intro t ht
    have h := L.sub_mem (hcl (Pi.single a c) hca i a t (Ne.symm hai) (Or.inr ht)) hca
    simpa [Ne.symm hai] using h

  have hsum : ∀ x : n → k, (∀ b, Pi.single b (x b) ∈ L) → x ∈ L := by
    intro x h
    rw [← Finset.univ_sum_single x]
    exact L.sum_mem (fun b _ => h b)
  have hoff : ∀ x : n → k, (∀ j, c⁻¹ * x j ∈ 𝒪[k]) → ∀ b, b ≠ i → Pi.single b (x b) ∈ L := by
    intro x hx b hb
    have e : x b = (c⁻¹ * x b) * c := by field_simp
    rw [e]
    exact hsing b hb ⟨_, hx b⟩
  by_cases hci : Pi.single i c ∈ L
  · left
    intro x
    refine ⟨hbd x, fun hx => hsum x fun b => ?_⟩
    by_cases hb : b = i
    · subst hb
      have e : Pi.single b (x b) = ((⟨c⁻¹ * x b, hx b⟩ : 𝒪[k]) • (Pi.single b c : n → k) : n → k) := by
        rw [hsm]; congr 1; show x b = (c⁻¹ * x b) * c; field_simp
      rw [e]; exact L.smul_mem _ hci
    · exact hoff x hx b hb
  · right
    have hm : ∀ x (hx : x ∈ L), (⟨c⁻¹ * x i, hbd x hx i⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      intro x hx
      by_contra hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu
      obtain ⟨v, hv⟩ := hu

      have hy : x - Pi.single i (x i) ∈ L := by
        apply hsum
        intro b
        by_cases hb : b = i
        · subst hb; simp
        · have := hoff x (hbd x hx) b hb
          simpa [hb] using this
      have hxi : Pi.single i (x i) ∈ L := by
        have := L.sub_mem hx hy
        simpa using this
      apply hci
      have h1 : ((↑(v⁻¹) : 𝒪[k]) * (v : 𝒪[k])) = 1 := Units.inv_mul v
      rw [hv] at h1
      have h2 := congrArg (fun z : 𝒪[k] => (z : k)) h1
      simp only [Subring.coe_mul, OneMemClass.coe_one] at h2
      set w : k := ((↑(v⁻¹) : 𝒪[k]) : k)
      have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
      have e : Pi.single i c = ((↑(v⁻¹) : 𝒪[k]) • (Pi.single i (x i) : n → k) : n → k) := by
        rw [hsm]; congr 1
        show c = w * x i
        linear_combination -(c * h2) + (w * x i) * hcc
      rw [e]; exact L.smul_mem _ hxi
    intro x
    constructor
    · intro hx
      exact ⟨hbd x hx, ⟨c⁻¹ * x i, hbd x hx i⟩, hm x hx, rfl⟩
    · rintro ⟨hx, s, hs, hsx⟩
      refine hsum x fun b => ?_
      by_cases hb : b = i
      · subst hb
        have e : x b = (s : k) * c := by rw [hsx]; field_simp
        rw [e]; exact hi s hs
      · exact hoff x hx b hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommon
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrueBranch

section Gen

open Formalism.L2.DIV Formalism.L2.Col

variable {ι : Type} [Fintype ι] {N n : ℕ}

theorem cSpan_eq_VV {m : ℕ} (lam : ι → DomWeight m) : CSpan lam = Formalism.L2.DIV.VV ℂ lam := by
  unfold CSpan Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, Formalism.L2.Col.nablaSq_eq_delSq]
  rfl

theorem det_ne_zero_of_mem_unitary {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : k.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hk)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem polOf_fnOf_frOne (G : ι → Matrix (Fin N) (Fin N) ℂ) (sh : ι → ℤ) (o : Frames G) (ho : ∀ τ, o.1 τ = 1)
    (P : MvPolynomial (ι × Fin N × Fin N) ℂ) : Formalism.L2.Col.polOf G sh o (fnOf G sh 1 P) = P := by
  have e : (fun τ => (o.1 τ)⁻¹) = (1 : ι → Matrix (Fin N) (Fin N) ℂ) := funext fun τ => by rw [ho τ, inv_one]; rfl
  have h := Formalism.L2.Col.polOf_fnOf G sh o P
  rwa [e] at h

theorem fnOf_actP_tr (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (P : Pol ℂ ι n) (y y' : Frames G) (h : IsTr (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) y y') :
    fnOf G (shiftOf lam) 1 (actP lam g P) y = fnOf G (shiftOf lam) 1 P y' := by
  have e1 := congrFun (Formalism.L2.Col.fnOf_mul G (shiftOf lam) (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) 1 P) y
  have e2 := Formalism.L2.Col.fnOf_tr (G := G) (G' := G) (shiftOf lam) 1 (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P y' y h
  have e3 : (fun τ => (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ * ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) =
      fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ * (1 : ι → Matrix (Fin n) (Fin n) ℂ) τ := by
    funext τ; simp
  rw [e2, e3, e1]
  have e4 : actP lam g P = (∏ τ, ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ.det ^ shiftOf lam τ) •
      Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ) P := by
    simp only [actP, detTwK, trAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Matrix.det_transpose]
    simp [detPow, shiftOf, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [e4]

theorem brEqv_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (o : Frames G)
    (ho : ∀ τ, o.1 τ = 1) :
    BrEqv hN G G' lam sg (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  refine ⟨?_, ?_⟩
  · rintro _ ⟨P, -, rfl⟩
    refine ⟨c • (Br.brStdP hN lam sg P : Pol ℂ ι n), ?_, ?_⟩
    · rw [cSpan_eq_VV]; exact (Formalism.L2.DIV.VV ℂ sg).smul_mem c (Br.brStdP hN lam sg P).2
    · simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
  · rintro k kt hk hb _ ⟨P, hP, rfl⟩ Φ' hΦ' z z' hz
    have hk0 : ∀ τ, (k τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose]; exact det_ne_zero_of_mem_unitary (hk τ)
    have hkt0 : ∀ τ, (kt τ)ᵀ.det ≠ 0 := fun τ => by
      rw [Matrix.det_transpose, (hb τ).det, mul_one, ← Matrix.det_transpose]; exact hk0 τ
    let g : ι → GL (Fin n) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hk0 τ)
    let g' : ι → GL (Fin N) ℂ := fun τ => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hkt0 τ)
    have hblk : ∀ τ, GlobalTheory.BranchFormula.IsBlock hN ((g' τ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
        ((g τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) 1 := fun τ => (hb τ).transpose
    have hPV : P ∈ Formalism.L2.DIV.VV ℂ lam := cSpan_eq_VV lam ▸ hP
    have hE := GlobalTheory.BranchFormula.brEquiv_all ℂ hN lam sg hS g g' (fun τ => hblk τ) ⟨P, hPV⟩
    have h2 : (Br.brStdP hN lam sg (actP lam g' P) : Pol ℂ ι n) = actP sg g (Br.brStdP hN lam sg P : Pol ℂ ι n) :=
      congrArg Subtype.val hE
    have hΦe : Φ' = fnOf G (shiftOf lam) 1 (actP lam g' P) := by
      funext y
      have hd : ∀ τ, IsUnit (kt τ * y.1 τ).det := fun τ => by
        rw [Matrix.det_mul]
        refine IsUnit.mul (Ne.isUnit ?_) (y.2 τ)
        rw [← Matrix.det_transpose]; exact hkt0 τ
      let y' : Frames G := ⟨fun τ => kt τ * y.1 τ, hd⟩
      rw [hΦ' y y' (fun τ => rfl), fnOf_actP_tr G lam g' P y y' (fun τ => by
        show kt τ * y.1 τ = ((kt τ)ᵀ)ᵀ * y.1 τ
        rw [Matrix.transpose_transpose])]
    rw [hΦe]
    simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply]
    rw [h2, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, fnOf_actP_tr G' sg g _ z z' (fun τ => by
      rw [hz τ]
      show k τ * z.1 τ = ((k τ)ᵀ)ᵀ * z.1 τ
      rw [Matrix.transpose_transpose])]

theorem ne_formula (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ)
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (c : ℂ) (hc : c ≠ 0) (o : Frames G) (ho : ∀ τ, o.1 τ = 1) :
    ∃ Φ ∈ ValC G lam, (fnOf G' (shiftOf sg) 1 ∘ₗ (c • ((Formalism.L2.DIV.VV ℂ sg).subtype ∘ₗ Br.brStdP hN lam sg)) ∘ₗ
      Formalism.L2.Col.polOf G (shiftOf lam) o) Φ ≠ 0 := by
  have hp := polOf_fnOf_frOne G (shiftOf lam) o ho
  have h1 := GlobalTheory.BranchFormula.onePlace Formalism.L2.DIV.BrJ.branching_interlacing_pairs
  choose f hf hf0 using fun τ => (h1 N n hN (lam τ) (sg τ) (hI τ) (hS τ)).2.2.1
  have hn : ∀ τ, f τ ∈ nablaSq ℂ N (lam τ) := fun τ => by rw [Formalism.L2.Col.nablaSq_eq_delSq]; exact hf τ
  have hmem : Formalism.L2.DIV.ten f ∈ Formalism.L2.DIV.VV ℂ lam := GlobalTheory.Proof.TensorMapDescent.ten_mem lam f hn
  have ht := GlobalTheory.BranchFormula.tensor ℂ ι N n hN lam sg hI hS f ⟨_, hmem⟩ hn rfl
  refine ⟨fnOf G (shiftOf lam) 1 (Formalism.L2.DIV.ten f), ⟨_, (cSpan_eq_VV lam).symm ▸ hmem, rfl⟩, fun h => ?_⟩
  simp only [LinearMap.comp_apply, hp, LinearMap.smul_apply, Submodule.subtype_apply] at h
  have h' : (Br.brStdP hN lam sg (Formalism.L2.DIV.ten f) : Pol ℂ ι n) =
      Formalism.L2.DIV.ten fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ hN (lam τ) (sg τ) (f τ) := ht
  rw [h', map_smul] at h
  have h0 := Formalism.L2.Col.fnOf_injective G' (shiftOf sg) 1 (fun _ => by simp) ⟨fun _ => 1, fun _ => by simp⟩
    (((smul_eq_zero.1 h).resolve_left hc).trans (map_zero _).symm)
  exact GlobalTheory.Proof.TensorMapDescent.ten_ne_zero _ hf0 h0

end Gen

section True

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

theorem half_mul (R : Ranks) (j : ℕ) : ((j * (R.t + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨a, ha⟩ := R.t_odd
  have h1 : (R.t + 1) / 2 = a + 1 := by omega
  have h2 : j * (R.t + 1) / 2 = j * (a + 1) := by
    rw [ha, show j * (2 * a + 1 + 1) = 2 * (j * (a + 1)) by ring]; omega
  rw [h1, h2]; push_cast; ring

theorem domWeight_ext {M : ℕ} {a b : DomWeight M} (h : a.w = b.w) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem lamT_record (j : ℕ) : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u j = GlobalTheory.Mem.Col2.lamT (B.hcW u) j := by
  funext τ
  apply domWeight_ext
  funext i
  show (Examples₂.lamOf (B.hcW u τ) j).w i - ((j * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (Examples₂.lamOf (B.hcW u τ) j).w i + -((j : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

theorem sgT_record (a : I.ι) : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = (I.perIn u a).sgT := by
  funext τ
  apply domWeight_ext
  funext i
  show (B.wts.sgW τ).w i - ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) =
    (B.wts.sgW τ).w i + -((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ))
  rw [half_mul]; ring

end True

section Main

theorem branching_true_columns : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  intro B X I _ _ l Z u hN
  have hM := fun τ => GlobalTheory.BranchMembers.members B.fields B.Word B.R B.wts B.wts_isOk u τ
  have hI' : ∀ τ, Formalism.L2.Col.Br.Interlace hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).1
  have hS' : ∀ τ, Formalism.L2.Col.Br.SameShift (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ) :=
    fun τ => (hM τ).2
  have hc : (∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
      (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ((map_ne_zero _).2 (l.per u I.mu0).tz_ne)
  have hlow : lowOf I l Z u = fnOf _ (shiftOf (I.perIn u I.mu0).sgT) 1 ∘ₗ
      ((∏ τ, Formalism.L2.Col.embAt B.embLL B.fields.emb τ (I.perIn u I.mu0).tz ^
        (-Formalism.L2.Col.Br.nBr (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m τ) ((I.perIn u I.mu0).sgT τ))) •
        ((Formalism.L2.DIV.VV ℂ (I.perIn u I.mu0).sgT).subtype ∘ₗ
          Formalism.L2.Col.Br.brStdP hN (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m) (I.perIn u I.mu0).sgT)) ∘ₗ
      Formalism.L2.Col.polOf _ (shiftOf (GlobalTheory.Mem.Col2.lamT (B.hcW u) B.R.m)) ⟨fun _ => 1, fun _ => by simp⟩ := by
    unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]
    rfl
  refine ⟨?_, ?_, ?_, fun a z c y => ?_⟩
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0]; exact hI'
  · rw [lamT_record I l Z u, sgT_record I l Z u I.mu0, hlow]
    exact brEqv_formula hN _ _ _ _ hS' _ _ (fun _ => rfl)
  · rw [lamT_record I l Z u, hlow]
    exact ne_formula hN _ _ _ _ hI' hS' _ hc _ (fun _ => rfl)
  · unfold lowOf
    rw [lamT_record I l Z u, sgT_record I l Z u a]
    rfl

end Main

end GlobalTheory.TrueBranch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TupLevel

theorem odd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (h : (2 : 𝓞 E) ∉ P.asIdeal) :
    Odd (Ideal.absNorm P.asIdeal) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  haveI := P.isPrime
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h2
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) 2 h2
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact absurd hx (by norm_num)
  have h1 : (2 : 𝓞 E ⧸ P.asIdeal) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, two_nsmul] at this
    rw [two_mul, this]
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact h (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_ofNat]; exact h3))
  · exact h0 h3

theorem odd_levC {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    (hX : X.Ok) (hPr : Pr.Ok) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (u : Pr.Word)
    (h2 : ∀ P ∈ Formalism.L2.Col.Sall sel mu u, (2 : 𝓞 X.E) ∉ P.asIdeal) : Odd (levC sel mu cst u) := by
  have hp : Odd (∏ P : Formalism.L2.Col.rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) :=
    Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun P _ =>
      odd_absNorm P.1 (h2 P.1 (Finset.mem_union.2 (Or.inr P.2)))
  obtain ⟨P₀, hP₀⟩ : (Pr.vT u).Nonempty := Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)
  have hT : Odd (Pr.T u) := hPr.vT_norm u P₀ hP₀ ▸ odd_absNorm P₀ (h2 P₀ (Finset.mem_union.2 (Or.inl hP₀)))
  exact hp.pow.mul (hT.mul hp.pow)

theorem levC_pos_odd_and_off : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι), 0 < levC I.sel (I.tup a) (I.cst a) u ∧ Odd (levC I.sel (I.tup a) (I.cst a) u) ∧ (∀ Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) := by
  intro B X I hI _ u a
  obtain ⟨hXo, hPr, -⟩ := base_fields_primes_ok B X
  have hc : (B.primes X).cond = B.host.QS * B.host.q * B.host.d := rfl
  have h2 := fun Q (hQ : Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u) =>
    GlobalTheory.DatumJets.HidaSetting.notMem_Sall hPr hI.sel_ok u Nat.prime_two (hI.ram_mem 2 Nat.prime_two B.host.toHostRaw.two_dvd_condN)
      (by rw [hc]; exact B.host.toHostRaw.two_dvd_condN) hQ
  have ho : Odd (levC I.sel (I.tup a) (I.cst a) u) :=
    odd_levC hXo hPr (I.cst a) u fun Q hQ h => h2 Q hQ (by exact_mod_cast h)
  refine ⟨ho.pos, ho, fun Q hQ h => ?_⟩
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q.asIdeal
  by_cases hd : l ∣ B.host.QS * B.host.q * B.host.d
  · exact GlobalTheory.DatumJets.HidaSetting.notMem_Sall hPr hI.sel_ok u hl (hI.ram_mem l hl hd) (by rw [hc]; exact hd) hQ hlP
  · exact UpperTheory.Ram.natCast_notMem_of_coprime Q.isPrime.ne_top hlP ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm h

end GlobalTheory.TupLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedPeriodEqIntegralBesselPeriodsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedPeriod_eq_integral_besselPeriods : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter), IsStdChar D ψ (-1) → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℂ, ∀ (T : Cu X u hK), IntegrableOn (Ph X u hK T) Fs (X.B.I.muA X.B.μf) ∧ ∀ f : X.B.I.GA → ℂ, RowFun X f → ∫ x in Fs, f x * Ph X u hK T x ∂(X.B.I.muA X.B.μf) = c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u) := by
  first | exact @GlobalTheory.Core.Mi.unfoldedPer | exact GlobalTheory.Core.Mi.unfoldedPer | (intros; apply GlobalTheory.Core.Mi.unfoldedPer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitIdealCompletionAtPlaceEqIntegralAdelesAtPlacStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitIdealCompletionAtPlace_eq_integralAdelesAtPlace : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_one_eq_intAt | exact GlobalTheory.SeeSaw.idV_one_eq_intAt | (intros; apply GlobalTheory.SeeSaw.idV_one_eq_intAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeylStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUnn_subgroup_eq_top_of_leviUnipotentWeyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (GlobalTheory.StdUnn.G D n)), (∀ (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D)), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 a.1 0 0 (GlobalTheory.MixModel.adj (a⁻¹).1) → g ∈ S) → (∀ (g : GlobalTheory.StdUnn.G D n) (b : Mx D n n), GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b 0 1 → g ∈ S) → (∀ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 → g ∈ S) → S = ⊤ := by
  first | exact @GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl | exact GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl | (intros; apply GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylElementActsOnSchrodingerByFourierStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylElement_acts_on_schrodinger_by_fourier : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ μ : D.host.E, IsSkew μ → ∀ w : GA D (dblSp A), IsWeyl A w → mt (dblSp A) w ⬝ (dblDec A).jX = -(incA D μ • (dblDec A).jY) → mt (dblSp A) w ⬝ (dblDec A).jY = incA D μ⁻¹ • (dblDec A).jX → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x, sch ψ A B ν 𝓨 (omh (w, 1) f) x = ∫ y, sch ψ A B ν 𝓨 f y * ψ (trA (incA D (-D.host.xi0 / μ) * Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  first | exact @GlobalTheory.StdUnn.WeylFourier.sch_weyl | exact GlobalTheory.StdUnn.WeylFourier.sch_weyl | (intros; apply GlobalTheory.StdUnn.WeylFourier.sch_weyl <;> assumption)
end

