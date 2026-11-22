import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFockOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniquene
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH MvPolynomial Matrix
open GlobalTheory.ArchRec GlobalTheory.FockDeg GlobalTheory.FockAlg.HarmStable

namespace GlobalTheory.ArchRec.Joint

variable {p q r s : ℕ}

theorem mem_pR_of_herm {Z : TH.Mat p q} (hZ : IsPC Z) (h : Zᴴ = Z) : Z ∈ pR p q := by
  refine ⟨?_, hZ⟩
  have hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  show Zᴴ * TH.Jm p q + TH.Jm p q * Z = 0
  rw [h, hJ]
  ext a b
  have := hZ a b
  rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem sameBlock_symm {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem exists_pR {Z : TH.Mat p q} (hZ : IsPC Z) :
    ∃ A ∈ pR p q, ∃ B ∈ pR p q, Z = (1 / 2 : ℂ) • A + (-Complex.I / 2) • B := by
  refine ⟨Z + Zᴴ, mem_pR_of_herm ?_ ?_, Complex.I • (Z - Zᴴ), mem_pR_of_herm ?_ ?_, ?_⟩
  · intro a b h
    simp [hZ a b h, hZ b a (sameBlock_symm h)]
  · rw [conjTranspose_add, conjTranspose_conjTranspose, add_comm]
  · intro a b h
    simp [hZ a b h, hZ b a (sameBlock_symm h)]
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    simp [← smul_neg]
  · rw [smul_smul, show -Complex.I / 2 * Complex.I = 1 / 2 by
      linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I]
    module

theorem minusPart_eq_zero_of_raise {σ : Type} (a : TH.Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    {Φ : MvPolynomial σ ℂ} {d : ℕ} (hΦ : Φ.IsHomogeneous d)
    (h : ∀ Z ∈ pR p q, (a Z Φ).IsHomogeneous (d + 2)) (Z : TH.Mat p q) (hZ : IsPC Z) :
    minusPart (a Z) Φ = 0 := by
  obtain ⟨A, hA, B, hB, rfl⟩ := exists_pR hZ
  have hm : a ((1 / 2 : ℂ) • A + (-Complex.I / 2) • B) Φ ∈ homogeneousSubmodule σ ℂ (d + 2) := by
    rw [map_add, map_smul, map_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h A hA)) (Submodule.smul_mem _ _ (h B hB))
  rw [minusPart_eq_zero_iff]
  intro e
  rw [homogeneousComponent_of_mem (show Φ ∈ homogeneousSubmodule σ ℂ d from hΦ)]
  split_ifs with he
  · rw [homogeneousComponent_of_mem hm, if_neg (by omega)]
  · simp

theorem raise_of_minusPart {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) {Φ : Pol p q r s} {d : ℕ}
    (hΦ : Φ.IsHomogeneous d) (h : minusPart (omAct p q r s M) Φ = 0) :
    (omAct p q r s M Φ).IsHomogeneous (d + 2) := by
  rw [omAct_eq_parts hM, h, add_zero, plusPart_omAct hM]
  exact upOp_mem M d Φ hΦ

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem hc_mem_hwSub {σ : Type} {a : TH.Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)}
    (ha : ∀ Y, IsKC Y → DegZero (a Y)) {μ : Ix p q → ℚ} {Φ : MvPolynomial σ ℂ}
    (h : Φ ∈ hwSub a μ) (d : ℕ) : homogeneousComponent d Φ ∈ hwSub a μ := by
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h ⊢
  refine ⟨fun c => ?_, fun c e hce => ?_⟩
  · rw [← (ha _ (isKC_Eab (by cases c <;> trivial))).comm, h.1, map_smul]
  · rw [← (ha _ (isKC_Eab ?_)).comm, h.2 c e hce, map_zero]
    rcases c with c | c <;> rcases e with e | e <;> simp_all [sameBlock, posC]

theorem hc_mem_J (X : ProvA) {Φ : Pol p q r s} (h : Φ ∈ (X.fock p q r s).J) (d : ℕ) :
    homogeneousComponent d Φ ∈ (X.fock p q r s).J := by
  have g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 →
      minusPart A (homogeneousComponent d Φ) = 0 := by
    intro A hA
    rw [minusPart_eq_zero_iff] at hA ⊢
    intro e
    rw [hc_hc]
    split_ifs with he
    · rw [← he]; exact hA e
    · simp
  exact ⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩

theorem smul_mem_J (X : ProvA) {Φ : Pol p q r s} (h : Φ ∈ (X.fock p q r s).J) (c : ℂ) :
    c • Φ ∈ (X.fock p q r s).J := by
  have g : ∀ A : Module.End ℂ (Pol p q r s), minusPart A Φ = 0 → minusPart A (c • Φ) = 0 := by
    intro A hA
    rw [minusPart_eq_zero_iff] at hA ⊢
    intro e
    rw [map_smul, map_smul, map_smul, hA, smul_zero]
  exact ⟨fun Z hZ => g _ (h.1 Z hZ), fun Z hZ => g _ (h.2 Z hZ)⟩

theorem line (X : ProvA) {μ : Ix p q → ℚ} {μ' : Ix r s → ℚ} {P Φ : Pol p q r s}
    (hJ : P ∈ (X.fock p q r s).J) (h : P ∈ hwSub (fockAct1 p q r s) μ)
    (h' : P ∈ hwSub (fockAct2 p q r s) μ') (h0 : Φ ≠ 0) (gJ : Φ ∈ (X.fock p q r s).J)
    (g : Φ ∈ hwSub (fockAct1 p q r s) μ) (g' : Φ ∈ hwSub (fockAct2 p q r s) μ') :
    ∃ c : ℂ, P = c • Φ := by
  have h2 := (GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 μ μ'
  have hs : JointShape p q r s μ μ' := by
    by_contra hs
    exact h0 ((Submodule.eq_bot_iff _).1 (h2.2 hs) Φ ⟨⟨g, g'⟩, Submodule.subset_span gJ⟩)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
    ⟨Φ, ⟨g, g'⟩, Submodule.subset_span gJ⟩
    (fun e => h0 (congrArg Subtype.val e))).1 (h2.1 hs) ⟨P, ⟨h, h'⟩, Submodule.subset_span hJ⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem cJoint_iff (X : ProvA) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (Φ : Pol p q r s) :
    CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔
      Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ := by
  constructor
  · rintro ⟨⟨d, hd, h1, h2⟩, h3⟩
    exact ⟨⟨minusPart_eq_zero_of_raise _ hd h1, minusPart_eq_zero_of_raise _ hd h2⟩, h3⟩
  · rintro ⟨hJ, h1, h2⟩
    obtain ⟨d, hd⟩ : ∃ d, homogeneousComponent d Φ ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h1.1
      rw [← sum_homogeneousComponent Φ]
      exact Finset.sum_eq_zero fun d _ => hc d
    obtain ⟨c, hc⟩ := line X hJ h1.2 h2.2 hd (hc_mem_J X hJ d)
      (hc_mem_hwSub (fun _ => degZero_fockAct1) h1.2 d)
      (hc_mem_hwSub (fun _ => degZero_fockAct2) h2.2 d)
    have hh : Φ.IsHomogeneous d := by
      rw [hc]
      exact (homogeneousSubmodule _ ℂ d).smul_mem c (homogeneousComponent_mem d Φ)
    exact ⟨⟨d, hh, fun Z hZ => raise_of_minusPart (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ.2) hh (hJ.1 Z hZ.2),
      fun Z hZ => raise_of_minusPart (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ.2) hh (hJ.2 Z hZ.2)⟩, h1, h2⟩

theorem joint_harmonics : ∀ (X : ProvA) (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
    (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔
      Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ) ∧
    (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ →
      ∃ c : ℝ, 0 < c ∧ JointHW (X.fock p q r s) μ μ' ((c : ℂ) • Φ)) ∧
    ∀ Φ Φ', CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ →
      CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ' → ∃ c : ℂ, Φ' = c • Φ := by
  intro X p q r s μ μ'
  refine ⟨cJoint_iff X μ μ', fun Φ h => ?_, fun Φ Φ' h h' => ?_⟩
  · obtain ⟨hJ, h1, h2⟩ := (cJoint_iff X μ μ' Φ).1 h
    have hn : 0 < ‖(X.fock p q r s).ι Φ‖ :=
      norm_pos_iff.2 fun e => h1.1 ((X.fock p q r s).ι_inj (e.trans (map_zero _).symm))
    have hc : ((‖(X.fock p q r s).ι Φ‖⁻¹ : ℝ) : ℂ) • Φ ≠ 0 :=
      smul_ne_zero (Complex.ofReal_ne_zero.2 (inv_pos.2 hn).ne') h1.1
    refine ⟨‖(X.fock p q r s).ι Φ‖⁻¹, inv_pos.2 hn, smul_mem_J X hJ _,
      ⟨hc, Submodule.smul_mem _ _ h1.2⟩, ⟨hc, Submodule.smul_mem _ _ h2.2⟩, ?_⟩
    rw [map_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  · obtain ⟨hJ, h1, h2⟩ := (cJoint_iff X μ μ' Φ).1 h
    obtain ⟨hJ', h1', h2'⟩ := (cJoint_iff X μ μ' Φ').1 h'
    exact line X hJ' h1'.2 h2'.2 h1.1 hJ h1.2 h2.2

end GlobalTheory.ArchRec.Joint

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockIsometry

open Complex GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars GlobalTheory.VacuumFockLaws
open scoped Classical ComplexConjugate

variable {D : D7} {V W : HSp D}

theorem commScalar_unitMap {B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    {B' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} {ε : D.what₂.Tau → Fin V.rank → ℝ}
    {ε' : D.what₂.Tau → Fin W.rank → ℝ} (hε : ∀ τ a, ε τ a = 1 ∨ ε τ a = -1)
    (hB : ∀ τ, (B τ)ᴴ * gramAt D V τ * B τ = diagonal fun a => (ε τ a : ℂ))
    (hB' : ∀ τ, (B' τ)ᴴ * gramAt D W τ * B' τ = diagonal fun a => (ε' τ a : ℂ))
    (c c' : ℂ) (k l : FVar D W.rank V.rank) :
    commScalar V W k.1 l.1 (c • unitMap (B k.1) (B' k.1) k.2.1 k.2.2) (c' • unitMap (B l.1) (B' l.1) l.2.1 l.2.2) =
      if k = l then -(2 * Real.pi * I) *
        ((2 * (tauE D k.1 D.host.xi0 * (c * conj c' * ((ε' k.1 k.2.1 * ε k.1 k.2.2 : ℝ) : ℂ))).re : ℝ) : ℂ)
      else 0 := by
  obtain ⟨τ, i, j⟩ := k
  obtain ⟨τ', i', j'⟩ := l
  by_cases hτ : τ = τ'
  · subst hτ
    have htr := GlobalTheory.FockVecInj.trace_unitMap (G := gramAt D V τ) (G' := gramAt D W τ)
      (ε := fun a => ((ε τ a : ℝ) : ℂ)) (ε' := fun a => ((ε' τ a : ℝ) : ℂ))
      (fun a => by rcases hε τ a with h | h <;> simp [h]) (hB τ) (hB' τ) i j i' j'
    have hh : hermAt V W τ (c • unitMap (B τ) (B' τ) i j) (c' • unitMap (B τ) (B' τ) i' j') =
        (c * conj c') * (if i = i' ∧ j = j' then ((ε' τ i : ℝ) : ℂ) * ((ε τ j : ℝ) : ℂ) else 0) := by
      rw [← htr]
      simp only [hermAt, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
        smul_eq_mul, Complex.star_def]
      ring
    simp only [commScalar, symplAt, hh]
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij
      simp
    · have hne : ¬ ((τ, i, j) : FVar D W.rank V.rank) = (τ, i', j') := by
        intro h
        exact hij ⟨congrArg (fun x => x.2.1) h, congrArg (fun x => x.2.2) h⟩
      rw [if_neg hij, if_neg hne]
      simp
  · have hne : ¬ ((τ, i, j) : FVar D W.rank V.rank) = (τ', i', j') := fun h => hτ (congrArg Prod.fst h)
    simp only [commScalar, if_neg hτ, if_neg hne]

private theorem omDir_smul_unitMap_unitMap_eq_ite {S T : HSp D} {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {εS : D.what₂.Tau → Fin S.rank → ℝ}
    {εT : D.what₂.Tau → Fin T.rank → ℝ} (hεS : ∀ τ a, εS τ a = 1 ∨ εS τ a = -1)
    (hBS : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = diagonal fun a => (εS τ a : ℂ))
    (hBT : ∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = diagonal fun a => (εT τ a : ℂ))
    (c : ℂ) (k l : FVar D T.rank S.rank) :
    GlobalTheory.FockIndep.omDir S T k.1 (c • unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) l.1
                 (unitMap (BS l.1) (BT l.1) l.2.1 l.2.2) =
      if k = l then 2 * (tauE D k.1 D.host.xi0 * (c * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ))).re else 0 := by
  have h := commScalar_unitMap (B := BS) (B' := BT) hεS hBS hBT c 1 k l
  rw [GlobalTheory.ThetaSquare.commScalar_eq, one_smul, map_one, mul_one] at h
  have h2 : (-(2 * (Real.pi : ℂ) * I)) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  split_ifs at h ⊢ with hkl
  · exact_mod_cast mul_left_cancel₀ h2 h
  · exact_mod_cast mul_left_cancel₀ h2 (h.trans (mul_zero _).symm)

private theorem scal_lemma_2 {S T : HSp D} {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} {εS : D.what₂.Tau → Fin S.rank → ℝ}
    {εT : D.what₂.Tau → Fin T.rank → ℝ} (hεS : ∀ τ a, εS τ a = 1 ∨ εS τ a = -1)
    (hεT : ∀ τ a, εT τ a = 1 ∨ εT τ a = -1)
    (hBS : ∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = diagonal fun a => (εS τ a : ℂ))
    (hBT : ∀ τ, (BT τ)ᴴ * gramAt D T τ * BT τ = diagonal fun a => (εT τ a : ℂ))
    (hsS : ∀ τ, sS τ * BS τ = BS τ * diagonal fun a => (εS τ a : ℂ))
    (hsT : ∀ τ, sT τ * BT τ = BT τ * diagonal fun a => (εT τ a : ℂ))
    (hdet : ∀ τ, IsUnit (BS τ).det) (k l : FVar D T.rank S.rank) :
    (-(fockScale D k.1 : ℂ)⁻¹) * ((fockScale D l.1 : ℂ)⁻¹ * (-(4 * (Real.pi : ℂ) * I) *
      ((GlobalTheory.FockIndep.omDir S T k.1 (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) l.1
          (unitMap (BS l.1) (BT l.1) l.2.1 l.2.2) : ℝ) +
        I * (GlobalTheory.FockIndep.omDir S T k.1 (cplxO (sS k.1) (sT k.1) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2)) l.1
          (unitMap (BS l.1) (BT l.1) l.2.1 l.2.2) : ℝ)))) = if k = l then 1 else 0 := by
  have e1 := omDir_smul_unitMap_unitMap_eq_ite hεS hBS hBT 1 k l
  rw [one_smul] at e1
  have e2 := omDir_smul_unitMap_unitMap_eq_ite hεS hBS hBT (I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ))) k l
  have hc := GlobalTheory.FockVecInj.cplxO_unitMap (hdet k.1) (hsS k.1) (hsT k.1) k.2.1 k.2.2
  rw [← hc] at e2
  rw [e1, e2]
  split_ifs with hkl
  · subst hkl
    have hx := GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero (D := D) k.1
    have hs := GlobalTheory.VacuumFockLaws.fockScale_sq (D := D) k.1
    have hne := GlobalTheory.VacuumFockLaws.fockScale_ne (D := D) k.1
    have hab : ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) = 1 := by
      rcases hεT k.1 k.2.1 with h | h <;> rcases hεS k.1 k.2.2 with h' | h' <;> simp [h, h']
    have r1 : (tauE D k.1 D.host.xi0 * (1 * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ))).re = 0 := by
      simp [Complex.mul_re, hx]
    have r2 : (tauE D k.1 D.host.xi0 * (I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) *
        ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ))).re = -(tauE D k.1 D.host.xi0).im := by
      have hI : I * ((εT k.1 k.2.1 : ℂ) * (εS k.1 k.2.2 : ℂ)) * ((εT k.1 k.2.1 * εS k.1 k.2.2 : ℝ) : ℂ) = I := by
        push_cast
        linear_combination I * hab
      rw [hI]
      simp [Complex.mul_re]
    rw [r1, r2]
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * hs + (-(8 * (Real.pi : ℂ) * ((tauE D k.1 D.host.xi0).im : ℂ))) * Complex.I_sq
  · simp

theorem ipO_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → (∀ ρ, IsFockVacAt (heisO ψ S T) θ ρ (cplxO (sS ρ) (sT ρ)) f) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ P Q, ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f P) (pureTensorO ψ θ S T sS sT BS BT f Q) = fockIp P Q * (nrm2 μ 𝓕 f : ℂ) := by
  intro D ψ θ S T hψ hθ sS BS sT BT pS pT _ _ hcS hcT hoS hoT f hf hvac μ 𝓕 hcov P Q
  obtain ⟨hHaar, hFD, -⟩ := hcov
  have hoS' : ∀ ρ, ∃ ε : Fin S.rank → ℝ, (∀ a, ε a = 1 ∧ (a : ℕ) < pS ρ ∨ ε a = -1 ∧ pS ρ ≤ (a : ℕ)) ∧
      ((BS ρ)ᴴ * gramAt D S ρ * BS ρ = diagonal fun a => (ε a : ℂ)) ∧
      sS ρ * BS ρ = BS ρ * diagonal fun a => (ε a : ℂ) := hoS
  have hoT' : ∀ ρ, ∃ ε : Fin T.rank → ℝ, (∀ a, ε a = 1 ∧ (a : ℕ) < pT ρ ∨ ε a = -1 ∧ pT ρ ≤ (a : ℕ)) ∧
      ((BT ρ)ᴴ * gramAt D T ρ * BT ρ = diagonal fun a => (ε a : ℂ)) ∧
      sT ρ * BT ρ = BT ρ * diagonal fun a => (ε a : ℂ) := hoT
  choose εS hεS using hoS'
  choose εT hεT using hoT'
  have hεS1 : ∀ ρ a, εS ρ a = 1 ∨ εS ρ a = -1 := fun ρ a => ((hεS ρ).1 a).imp And.left And.left
  have hεT1 : ∀ ρ a, εT ρ a = 1 ∨ εT ρ a = -1 := fun ρ a => ((hεT ρ).1 a).imp And.left And.left
  have hdet : ∀ ρ, IsUnit (BS ρ).det := by
    intro ρ
    rw [isUnit_iff_ne_zero]
    intro h0
    have hd := congrArg Matrix.det (hεS ρ).2.1
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at hd
    refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
    rcases hεS1 ρ a with h | h <;> simp [h]

  let a : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ) := fun k =>
    { toFun := fun g => ⟨aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g,
        GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2⟩
      map_add' := fun g g' => Subtype.ext (GlobalTheory.FockIndep.aPlus_add hψ hθ k.1 (cplxO (sS k.1) (sT k.1))
        (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2 g'.2)
      map_smul' := fun c g => Subtype.ext (GlobalTheory.FockIndep.aPlus_smul hψ hθ k.1 (cplxO (sS k.1) (sT k.1))
        (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) c g.2) }
  let e : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ) := fun k =>
    { toFun := fun g => ⟨annih (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g,
        GlobalTheory.FockIndep.annih_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2⟩
      map_add' := fun g g' => Subtype.ext (GlobalTheory.FockIndep.annih_add hψ hθ k.1 (cplxO (sS k.1) (sT k.1))
        (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g.2 g'.2)
      map_smul' := fun c g => Subtype.ext (GlobalTheory.FockIndep.annih_smul hψ hθ k.1 (cplxO (sS k.1) (sT k.1))
        (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) c g.2) }
  let b : FVar D T.rank S.rank → Module.End ℂ (thetaSub S T ψ) := fun k => (-(fockScale D k.1 : ℂ)⁻¹) • e k
  have haa : ∀ i j g, a i (a j g) = a j (a i g) := fun i j g => Subtype.ext
    (GlobalTheory.FockIndep.aPlus_comm' (hψ := hψ) (hθ := hθ) (hS := hcS) (hT := hcT) (τ := i.1)
      (z := unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) (τ' := j.1) (z' := unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) (hf := g.2))
  have hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then (1 : ℂ) else 0) • g := by
    intro i j g
    apply Subtype.ext
    have hg : IsThetaFunO ψ S T g := g.2
    have hag := GlobalTheory.FockIndep.annih_theta hψ hθ i.1 (cplxO (sS i.1) (sT i.1)) (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) hg
    change (-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) (aPlus (heisO ψ S T) θ j.1 (cplxO (sS j.1) (sT j.1))
          (unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) g) =
      aPlus (heisO ψ S T) θ j.1 (cplxO (sS j.1) (sT j.1)) (unitMap (BS j.1) (BT j.1) j.2.1 j.2.2)
        ((-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
          (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) g) + (if i = j then (1 : ℂ) else 0) • (g : WO S T → ℂ)
    rw [GlobalTheory.FockIndep.annih_aPlus (hψ := hψ) (hθ := hθ) (hS := hcS) (hT := hcT) (hf := hg),
      GlobalTheory.FockIndep.aPlus_smul hψ hθ j.1 (cplxO (sS j.1) (sT j.1)) (unitMap (BS j.1) (BT j.1) j.2.1 j.2.2) _ hag,
      smul_add, smul_smul, scal_lemma_2 hεS1 hεT1 (fun ρ => (hεS ρ).2.1) (fun ρ => (hεT ρ).2.1) (fun ρ => (hεS ρ).2.2)
        (fun ρ => (hεT ρ).2.2) hdet i j]
  have hvac' : ∀ i, b i ⟨f, hf⟩ = 0 := fun i => Subtype.ext (by
    change (-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
      (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) f = 0
    rw [hvac i.1 (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2), smul_zero])
  obtain ⟨hmem, hip⟩ := fock_of_ccr (thetaSub S T ψ) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    a b (fun _ _ => rfl) haa (fun i j g => by convert hba i j g) ⟨f, hf⟩ hvac'

  have thd : ∀ τ z (x : WO S T → ℂ), IsThetaFunO ψ S T x →
      IsThetaFunO ψ S T (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z x) :=
    fun τ z x hx => (GlobalTheory.ThetaSquare.derSkew hψ hθ τ z).2.1 x hx
  have sk : ∀ τ z (x y : WO S T → ℂ), IsThetaFunO ψ S T x → IsThetaFunO ψ S T y →
      GlobalTheory.Ker.ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z x) y =
        -GlobalTheory.Ker.ipO μ 𝓕 x (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z y) :=
    fun τ z x y hx hy => (GlobalTheory.ThetaSquare.derSkew hψ hθ τ z).2.2 μ 𝓕 hHaar hFD x y hx hy
  have hann : ∀ τ z (g : WO S T → ℂ), annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) z g =
      Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g +
        I • Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) z) g := fun _ _ _ => rfl
  have hconj : ∀ τ, starRingEnd ℂ (-(fockScale D τ : ℂ)⁻¹) = -(fockScale D τ : ℂ)⁻¹ := fun τ => by
    rw [map_neg, map_inv₀, Complex.conj_ofReal]
  have hadj1 : ∀ i (x y : thetaSub S T ψ), GlobalTheory.Ker.ipO μ 𝓕 (a i x) y = GlobalTheory.Ker.ipO μ 𝓕 x (b i y) := by
    intro i x y
    have hx : IsThetaFunO ψ S T x := x.2
    have hy : IsThetaFunO ψ S T y := y.2
    change GlobalTheory.Ker.ipO μ 𝓕 (aPlus (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) x) y =
      GlobalTheory.Ker.ipO μ 𝓕 x ((-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) y)
    rw [GlobalTheory.FockIndep.aPlus_eq, hann, GlobalTheory.Size.ipO_smul_left,
      GlobalTheory.Size.ipO_add_left hψ hHaar hFD (thd _ _ _ hx) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hx)) hy,
      GlobalTheory.Size.ipO_smul_left, sk _ _ _ _ hx hy, sk _ _ _ _ hx hy, GlobalTheory.Size.ipO_smul_right,
      GlobalTheory.Size.ipO_add_right hψ hHaar hFD hx (thd _ _ _ hy) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hy)),
      GlobalTheory.Size.ipO_smul_right, hconj, Complex.conj_I]
    ring
  have hadj2 : ∀ i (x y : thetaSub S T ψ), GlobalTheory.Ker.ipO μ 𝓕 x (a i y) = GlobalTheory.Ker.ipO μ 𝓕 (b i x) y := by
    intro i x y
    have hx : IsThetaFunO ψ S T x := x.2
    have hy : IsThetaFunO ψ S T y := y.2
    change GlobalTheory.Ker.ipO μ 𝓕 x (aPlus (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) y) =
      GlobalTheory.Ker.ipO μ 𝓕 ((-(fockScale D i.1 : ℂ)⁻¹) • annih (heisO ψ S T) θ i.1 (cplxO (sS i.1) (sT i.1))
        (unitMap (BS i.1) (BT i.1) i.2.1 i.2.2) x) y
    rw [GlobalTheory.FockIndep.aPlus_eq, hann, GlobalTheory.Size.ipO_smul_right,
      GlobalTheory.Size.ipO_add_right hψ hHaar hFD hx (thd _ _ _ hy) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hy)),
      GlobalTheory.Size.ipO_smul_right, GlobalTheory.Size.ipO_smul_left,
      GlobalTheory.Size.ipO_add_left hψ hHaar hFD (thd _ _ _ hx) (GlobalTheory.OrientedHeis.theta_smul _ (thd _ _ _ hx)) hy,
      GlobalTheory.Size.ipO_smul_left, sk _ _ _ _ hx hy, sk _ _ _ _ hx hy, map_inv₀, Complex.conj_ofReal, map_neg,
      Complex.conj_I]
    ring
  have hzero : ∀ x : WO S T → ℂ, GlobalTheory.Ker.ipO μ 𝓕 x 0 = 0 := fun x => by
    simp [GlobalTheory.Ker.ipO]
  have key : ∀ β R, GlobalTheory.Ker.ipO μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f R)
      (pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial β 1)) =
        R.coeff β * ((GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact β : ℂ) * GlobalTheory.Ker.ipO μ 𝓕 f f) :=
    hip (GlobalTheory.Ker.ipO μ 𝓕) (fun x y z => GlobalTheory.Size.ipO_add_left hψ hHaar hFD x.2 y.2 z.2)
      (fun c x z => GlobalTheory.Size.ipO_smul_left μ 𝓕 c x z) hzero hadj1 hadj2
  have mem : ∀ R, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f R) := hmem
  change GlobalTheory.Ker.ipO μ 𝓕 _ _ = _
  rw [← GlobalTheory.Size.ipO_self]
  refine MvPolynomial.induction_on' Q (fun u c => ?_) (fun p q hp hq => ?_)
  · rw [show MvPolynomial.monomial u c = c • MvPolynomial.monomial u (1 : ℂ) by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, GlobalTheory.Size.ipO_smul_right, key]
    have hF : fockIp P (c • MvPolynomial.monomial u (1 : ℂ)) =
        P.coeff u * starRingEnd ℂ c * (GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact u : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      unfold fockIp
      rw [Finset.sum_eq_single u]
      · simp [MvPolynomial.coeff_monomial, GlobalTheory.IndefiniteRowSideFullHecke.VacuumFockVectors.multiFact]
      · intro k _ hk
        simp [MvPolynomial.coeff_monomial, Ne.symm hk]
      · intro hu
        rw [MvPolynomial.mem_support_iff, not_not] at hu
        simp [hu]
    rw [hF]
    ring
  · rw [map_add, GlobalTheory.Size.ipO_add_right hψ hHaar hFD (mem P) (mem p) (mem q), hp, hq]
    simp only [fockIp, MvPolynomial.coeff_add, map_add, mul_add, add_mul, Finset.sum_add_distrib]

end GlobalTheory.FockIsometry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointPartAtMovedRationalPointRow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDat

theorem frMapAdj_partAt_actO_finW : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) = Matrix.of fun i j => GlobalTheory.LiftDat.rowAdj T βT a e (y i) 0 j := by
  intro D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2 e he a k₀ hab hmov hgen h1 h2' h3 h4 y
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hp : ∀ (c : AE D) (z : WO S T), GlobalTheory.LiftLevel.partAt c z = c • z := fun c z => by
    ext i j; simp [GlobalTheory.LiftLevel.partAt, smul_eq_mul]
  have hcomm : GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) =
      actO S T k₀ 1 (GlobalTheory.LiftLevel.partAt (cA D e) (finW S T y)) := by
    rw [hp, hp]
    show _ = HMul.hMul (HMul.hMul (mt T 1) ((cA D e • finW S T y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S k₀⁻¹)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hx : IsHalf (cA D e) (GlobalTheory.LiftLevel.partAt (cA D e) (finW S T y)) := fun i j => by
    simp only [GlobalTheory.LiftLevel.partAt, Matrix.map_apply, ← mul_assoc, hcc]
  rw [hcomm, hmov.2.2 _ hx]
  unfold GlobalTheory.LiftLevel.adjA frMapAdj
  rw [C.m.gS]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hi : ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E)⁻¹).map (incA D) = 1 := by
    rw [inv_one]; exact Matrix.map_one (incA D) (map_zero _) (map_one _)
  rw [hi, Matrix.one_mul]
  ext i j
  simp only [rowAdj, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    GlobalTheory.LiftLevel.partAt, finW]

end GlobalTheory.LiftDat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameIdempotentCutMatrix_mem_stabiliser_reduction : ∀ {D : D7} (n : ℕ) (β γ y : GL (Fin n) (EAf D)) (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → IsIntM (toEAf D e • γ.1) → IsIntM (toEAf D e • (γ⁻¹ : GL (Fin n) (EAf D)).1) → IsIntM (toEAf D (cA D e) • γ.1) → IsIntM (toEAf D (cA D e) • (γ⁻¹ : GL (Fin n) (EAf D)).1) → y.1 = β.1 * (toEAf D (e + cA D e) • γ.1 + (1 - toEAf D (e + cA D e)) • (1 : Matrix (Fin n) (Fin n) (EAf D))) * (β⁻¹ : GL (Fin n) (EAf D)).1 → y ∈ St β ∧ ∀ PP ∈ Z, ((redFn β PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) = redM PP (toEAf D e • γ.1) := by
  first | exact @GlobalTheory.FrameIdem.cut_mem_St_red | exact GlobalTheory.FrameIdem.cut_mem_St_red | (intros; apply GlobalTheory.FrameIdem.cut_mem_St_red <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeAlgebraLiftMonoidSum
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem freeAlgebra_lift_eq_sum_monomials {B : Type} [Ring B] [Algebra ℂ B] {X : Type} (f : X → B) (p : FreeAlgebra ℂ X) : FreeAlgebra.lift ℂ f p = Finsupp.sum (FreeAlgebra.equivMonoidAlgebraFreeMonoid p).coeff fun (w : FreeMonoid X) (c : ℂ) => c • (w.toList.map f).prod := by
  set e := (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℂ X ≃ₐ[ℂ] MonoidAlgebra ℂ (FreeMonoid X))
  have he : ∀ x : X, e (FreeAlgebra.ι ℂ x) = MonoidAlgebra.of ℂ (FreeMonoid X) (FreeMonoid.of x) := by
    intro x
    simp [e, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  have hF : ((FreeAlgebra.lift ℂ f).comp e.symm.toAlgHom) = MonoidAlgebra.lift ℂ B (FreeMonoid X) (FreeMonoid.lift f) := by
    rw [← (MonoidAlgebra.lift ℂ B (FreeMonoid X)).apply_symm_apply ((FreeAlgebra.lift ℂ f).comp e.symm.toAlgHom)]
    congr 1
    apply FreeMonoid.hom_eq
    intro x
    have hx : e.symm (MonoidAlgebra.of ℂ (FreeMonoid X) (FreeMonoid.of x)) = FreeAlgebra.ι ℂ x := by
      rw [← he x, e.symm_apply_apply]
    rw [MonoidAlgebra.of_apply] at hx
    rw [MonoidAlgebra.lift_symm_apply]
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom, hx, FreeAlgebra.lift_ι_apply, FreeMonoid.lift_eval_of]
  have := AlgHom.congr_fun hF (e p)
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply, MonoidAlgebra.lift_apply, FreeMonoid.lift_apply] at this
  exact this
end GlobalTheory
end

