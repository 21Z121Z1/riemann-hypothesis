import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0773
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductPermEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0774
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0377
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0499
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0596
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PosDefFactor
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.CartFrames

open Matrix
open scoped ComplexOrder

theorem herm_eig {k : ℕ} {A : Matrix (Fin k) (Fin k) ℂ} (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ * (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1 ∧
    (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) * ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ = 1 ∧
    A = (hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ))ᴴ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [← Matrix.star_eq_conjTranspose]
    exact h

theorem posDef_factor {k : ℕ} {P : Matrix (Fin k) (Fin k) ℂ} (hP : P.PosDef) :
    ∃ B C : Matrix (Fin k) (Fin k) ℂ, Bᴴ * B = P ∧ B * C = 1 ∧ C * B = 1 := by
  obtain ⟨h1, h2, h3⟩ := herm_eig hP.isHermitian
  set U : Matrix (Fin k) (Fin k) ℂ := (hP.isHermitian.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hU
  set d := hP.isHermitian.eigenvalues with hd
  have hpos : ∀ i, 0 < d i := hP.eigenvalues_pos
  let r : Fin k → ℂ := fun i => ((Real.sqrt (d i) : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    simpa [r] using (Real.sqrt_pos.2 (hpos i)).ne'
  have hrr : ∀ i, star (r i) * r i = (d i : ℂ) := fun i => by
    simp only [r, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hpos i).le]
  have hdiag : diagonal r * diagonal (fun i => (r i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact mul_inv_cancel₀ (hr0 i)
  have hdiag' : diagonal (fun i => (r i)⁻¹) * diagonal r = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; exact inv_mul_cancel₀ (hr0 i)
  refine ⟨diagonal r * Uᴴ, U * diagonal (fun i => (r i)⁻¹), ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
    calc U * diagonal (star r) * (diagonal r * Uᴴ) = U * (diagonal (star r) * diagonal r) * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (fun i => (d i : ℂ)) * Uᴴ := by
          rw [diagonal_mul_diagonal]; congr 3; funext i; exact hrr i
      _ = P := h3.symm
  · calc diagonal r * Uᴴ * (U * diagonal fun i => (r i)⁻¹)
        = diagonal r * (Uᴴ * U) * diagonal (fun i => (r i)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hdiag]
  · calc U * diagonal (fun i => (r i)⁻¹) * (diagonal r * Uᴴ)
        = U * (diagonal (fun i => (r i)⁻¹) * diagonal r) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hdiag', Matrix.mul_one, h2]

theorem exists_frame {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) :
    ∃ (ε : Fin k → Bool) (f : GL (Fin k) ℂ),
      (f.1)ᴴ * G * f.1 = diagonal (PositivityTheory.Rg.Sw.sgn ε) ∧ (f.1)ᴴ * (G * s) * f.1 = 1 := by
  obtain ⟨hss, hiso, hP⟩ := h
  obtain ⟨B, C, hBB, hBC, hCB⟩ := posDef_factor hP

  have hPs : (G * s) * s = G := by rw [Matrix.mul_assoc, hss, Matrix.mul_one]
  have hsP : sᴴ * (G * s) = G := by rw [← Matrix.mul_assoc]; exact hiso
  have hCtBt : Cᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBC, conjTranspose_one]

  have hHh : (B * s * C).IsHermitian := by
    have e : (B * s * C)ᴴ = Cᴴ * (sᴴ * (Bᴴ * B)) * C := by
      rw [conjTranspose_mul, conjTranspose_mul]
      calc Cᴴ * (sᴴ * Bᴴ) = Cᴴ * (sᴴ * Bᴴ) * (B * C) := by rw [hBC, Matrix.mul_one]
        _ = Cᴴ * (sᴴ * (Bᴴ * B)) * C := by simp only [Matrix.mul_assoc]
    show (B * s * C)ᴴ = B * s * C
    rw [e, hBB, hsP, ← hPs, ← hBB]
    calc Cᴴ * (Bᴴ * B * s) * C = (Cᴴ * Bᴴ) * (B * s * C) := by simp only [Matrix.mul_assoc]
      _ = B * s * C := by rw [hCtBt, Matrix.one_mul]
  have hHH : (B * s * C) * (B * s * C) = 1 := by
    calc (B * s * C) * (B * s * C) = B * s * (C * B) * s * C := by simp only [Matrix.mul_assoc]
      _ = B * (s * s) * C := by rw [hCB, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hss, Matrix.mul_one, hBC]
  obtain ⟨h1, h2, h3⟩ := herm_eig hHh
  set V : Matrix (Fin k) (Fin k) ℂ := (hHh.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) with hV
  set l := hHh.eigenvalues with hl
  set H := B * s * C with hH

  have hHV : H * V = V * diagonal (fun i => (l i : ℂ)) := by
    conv_lhs => rw [h3]
    calc V * diagonal (fun i => (l i : ℂ)) * Vᴴ * V = V * diagonal (fun i => (l i : ℂ)) * (Vᴴ * V) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one]

  have hsq : diagonal (fun i => (l i : ℂ)) * diagonal (fun i => (l i : ℂ)) = 1 := by
    calc diagonal (fun i => (l i : ℂ)) * diagonal (fun i => (l i : ℂ))
        = (Vᴴ * V) * diagonal (fun i => (l i : ℂ)) * (Vᴴ * V) * diagonal (fun i => (l i : ℂ)) := by
          rw [h1, Matrix.one_mul, Matrix.mul_one]
      _ = Vᴴ * (V * diagonal (fun i => (l i : ℂ)) * Vᴴ) * (V * diagonal (fun i => (l i : ℂ))) := by
          simp only [Matrix.mul_assoc]
      _ = Vᴴ * H * (H * V) := by rw [← h3, hHV]
      _ = Vᴴ * (H * H) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHH, Matrix.mul_one, h1]
  have hl2 : ∀ i, l i = 1 ∨ l i = -1 := fun i => by
    have e := congrFun (congrFun hsq i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, Matrix.one_apply_eq] at e
    have e' : l i * l i = 1 := by exact_mod_cast e
    exact mul_self_eq_one_iff.mp e'
  have hsgn : PositivityTheory.Rg.Sw.sgn (fun i => decide (0 < l i)) = fun i => (l i : ℂ) := by
    funext i
    rcases hl2 i with e | e <;> simp [PositivityTheory.Rg.Sw.sgn, e]
  let f : GL (Fin k) ℂ := ⟨C * V, Vᴴ * B, by
    calc C * V * (Vᴴ * B) = C * (V * Vᴴ) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hCB], by
    calc Vᴴ * B * (C * V) = Vᴴ * (B * C) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBC, Matrix.mul_one, h1]⟩
  have hf : f.1 = C * V := rfl
  have hfP : (f.1)ᴴ * (G * s) * f.1 = 1 := by
    rw [hf, conjTranspose_mul, ← hBB]
    calc Vᴴ * Cᴴ * (Bᴴ * B) * (C * V) = Vᴴ * (Cᴴ * Bᴴ) * (B * C) * V := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCtBt, hBC, Matrix.mul_one, Matrix.mul_one, h1]
  have hsf : s * f.1 = f.1 * diagonal (fun i => (l i : ℂ)) := by
    rw [hf]
    calc s * (C * V) = (C * B) * s * C * V := by rw [hCB, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = C * (H * V) := by rw [hH]; simp only [Matrix.mul_assoc]
      _ = C * V * diagonal (fun i => (l i : ℂ)) := by rw [hHV, Matrix.mul_assoc]
  refine ⟨fun i => decide (0 < l i), f, ?_, hfP⟩
  rw [hsgn]
  calc (f.1)ᴴ * G * f.1 = (f.1)ᴴ * ((G * s) * s) * f.1 := by rw [hPs]
    _ = (f.1)ᴴ * (G * s) * (s * f.1) := by simp only [Matrix.mul_assoc]
    _ = ((f.1)ᴴ * (G * s) * f.1) * diagonal (fun i => (l i : ℂ)) := by
        rw [hsf]; simp only [Matrix.mul_assoc]
    _ = diagonal (fun i => (l i : ℂ)) := by rw [hfP, Matrix.one_mul]

theorem exists_frames : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∃ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → GL (Fin V.rank) ℂ), PositivityTheory.SiegelWeilFormula.Gen.IsFrames (HSpace.gram V) θ ε fr ∧ ∀ τ, ((fr τ).1)ᴴ * (gramAt D V τ * s τ) * (fr τ).1 = 1 := by
  intro D V θ s hθ hs
  choose ε fr h1 h2 using fun τ => exists_frame (hs τ)
  refine ⟨ε, fr, fun τ => ?_, h2⟩
  have e : (HeckeCharacterZeroLocus.SiegelWeilU.JR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) (HSpace.gram V)).map (θ τ) = gramAt D V τ := by
    ext a b
    exact (hθ τ).1 _
  rw [e]
  exact h1 τ

end GlobalTheory.CompanionTheory.CartFrames
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardModuleSubGeneric
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents Zc Zc.Seg GlobalTheory.BZSeg
open GlobalTheory.Parabolic (Embeds)

namespace GlobalTheory.CompanionTheory.StdSubCusp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def top (Δ : Segment k) : IrrGL k := Δ.first.nu ((Δ.len - 1 : ℕ) : ℂ)

def Emb {p q : ℕ} (a : Fin p → IrrGL k) (b : Fin q → IrrGL k) : Prop :=
  ∃ (N : ℕ) (ha : ∑ i, (a i).1 = N) (hb : ∑ i, (b i).1 = N)
    (f : (prodIrr a ha).IntertwiningMap (prodIrr b hb)), Function.Injective f

theorem Emb.of_equiv {p q N : ℕ} {a : Fin p → IrrGL k} {b : Fin q → IrrGL k} (ha : ∑ i, (a i).1 = N)
    (hb : ∑ i, (b i).1 = N) (h : Nonempty ((prodIrr a ha).Equiv (prodIrr b hb))) : Emb a b := by
  obtain ⟨E⟩ := h
  exact ⟨N, ha, hb, E.toIntertwiningMap, E.toLinearEquiv.injective⟩

theorem Emb.trans {p q r : ℕ} {a : Fin p → IrrGL k} {b : Fin q → IrrGL k} {c : Fin r → IrrGL k} (h : Emb a b)
    (h' : Emb b c) : Emb a c := by
  obtain ⟨N, ha, hb, f, hf⟩ := h
  obtain ⟨N', hb', hc, g, hg⟩ := h'
  obtain rfl : N = N' := hb.symm.trans hb'
  exact ⟨N, ha, hc, g.comp f, hg.comp hf⟩

theorem prod₂_map_injective_right {r t : ℕ} {U W W' : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin r) k) U) {ρ : Representation ℂ (GL (Fin t) k) W}
    {ρ' : Representation ℂ (GL (Fin t) k) W'} (g : ρ.IntertwiningMap ρ') (hg : Function.Injective g) :
    ∃ F : (prod₂ σ ρ).IntertwiningMap (prod₂ σ ρ'), Function.Injective F := by
  have hι : Function.Injective (GlobalTheory.ParIndExact.extTensorMapRight σ g) :=
    Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hg
  have hι' : Function.Injective (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
      (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom) := hι
  exact ⟨parIndMap (two (stdSum rfl)) (compMap (GlobalTheory.ParIndExact.extTensorMapRight σ g)
    (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom), GlobalTheory.ParIndExact.parIndMap_injective _ _ hι'⟩

end GlobalTheory.CompanionTheory.StdSubCusp

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProducts
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem continuous_integral_mul_of_bdd {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y}
    {f : X → Y → ℂ} (hf : Continuous fun w : X × Y => f w.1 w.2) {B : ℝ} (hB : ∀ x y, ‖f x y‖ ≤ B)
    {g : Y → ℂ} (hg : Integrable g ν) : Continuous fun x => ∫ y, f x y * g y ∂ν := by
  refine continuous_of_dominated (bound := fun y => B * ‖g y‖) (fun x => ?_)
    (fun x => ae_of_all _ fun y => ?_) (hg.norm.const_mul B) (ae_of_all _ fun y => ?_)
  · have h1 : Continuous (f x) := hf.comp (continuous_const.prodMk continuous_id)
    exact h1.aestronglyMeasurable.mul hg.1
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB x y) (norm_nonneg _)
  · have h1 : Continuous fun x => f x y := hf.comp (continuous_id.prodMk continuous_const)
    exact h1.mul continuous_const

theorem integral_integral_mul_of_bdd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {F : X × Y → ℂ} (hF : AEStronglyMeasurable F (μ.prod ν)) {B : ℝ} (hB : ∀ w, ‖F w‖ ≤ B)
    {a : X → ℂ} {c : Y → ℂ} (ha : Integrable a μ) (hc : Integrable c ν) :
    ∫ x, (∫ z, F (x, z) * c z ∂ν) * a x ∂μ = ∫ w, F w * (a w.1 * c w.2) ∂(μ.prod ν) := by
  have hI : Integrable (fun w : X × Y => F w * (a w.1 * c w.2)) (μ.prod ν) :=
    (ha.mul_prod hc).bdd_mul hF (ae_of_all _ hB)
  rw [integral_prod _ hI]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  show (∫ z, F (x, z) * c z ∂ν) * a x = ∫ z, F (x, z) * (a x * c z) ∂ν
  rw [← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun z => by ring)

variable {D : D7} {r s p : ℕ}

theorem rowT_rowJ (x : Mx D r p) (z : Mx D s p) : rowT (rowJ x z) = x := by
  refine Matrix.ext fun i j => ?_
  simp [rowT, rowJ]

theorem rowB_rowJ (x : Mx D r p) (z : Mx D s p) : rowB (rowJ x z) = z := by
  refine Matrix.ext fun i j => ?_
  simp [rowB, rowJ]

theorem rowJ_rowT_rowB (y : Mx D (r + s) p) : rowJ (rowT y) (rowB y) = y := by
  refine Matrix.ext fun i j => ?_
  induction i using Fin.addCases with
  | left a => simp [rowT, rowJ]
  | right b => simp [rowB, rowJ]

theorem continuous_rowT : Continuous (rowT : Mx D (r + s) p → Mx D r p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_rowB : Continuous (rowB : Mx D (r + s) p → Mx D s p) :=
  continuous_matrix fun _ _ => continuous_id.matrix_elem _ _

theorem continuous_rowJ : Continuous fun w : Mx D r p × Mx D s p => rowJ w.1 w.2 := by
  refine continuous_matrix fun i j => ?_
  induction i using Fin.addCases with
  | left a =>
    simp only [rowJ, Fin.addCases_left]
    exact continuous_fst.matrix_elem a j
  | right b =>
    simp only [rowJ, Fin.addCases_right]
    exact continuous_snd.matrix_elem b j

theorem continuous_th_one {ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D} {b₀ : HermE D ρ}
    {μ : Measure (Mx D ρ p)} {Ω : G D p → Mx D ρ p → ℂ} (hΩ : IsTh ψ χ θ b₀ μ Ω) : Continuous (Ω 1) :=
  hΩ.cont.comp (continuous_const.prodMk continuous_id)

theorem integrable_conj {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} (hf : Integrable f μ) :
    Integrable (fun x => conj (f x)) μ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf

theorem stepTotal : ProdTh → ProdMeas → StepTotal := by
  intro hP hM D r s p μr Fr μs Fs μ F hr hs h ψ hψ χr χs θ hθ br bs b hb Tr Ts u hu hbd horth
  obtain ⟨B, hB⟩ := hbd
  have hμ := hM D r s p μr Fr μs Fs μ F hr hs h
  subst hμ
  haveI : SecondCountableTopology (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.2.1
  haveI : SecondCountableTopology (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.2.1
  haveI : SecondCountableTopology (Mx D (r + s) p) := (GlobalTheory.MixModel.lattice_Mx D (r + s) p).2.2.1
  haveI : FirstCountableTopology (Mx D r p) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  haveI : IsTopologicalAddGroup (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).1
  haveI : IsTopologicalAddGroup (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).1
  haveI : LocallyCompactSpace (Mx D r p) := (GlobalTheory.MixModel.lattice_Mx D r p).2.1
  haveI : LocallyCompactSpace (Mx D s p) := (GlobalTheory.MixModel.lattice_Mx D s p).2.1
  haveI : BorelSpace (Mx D r p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D s p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D (r + s) p) := ⟨rfl⟩
  haveI := hr.1
  haveI := hs.1
  have hcJ := continuous_rowJ (D := D) (r := r) (s := s) (p := p)
  have hcF : Continuous fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2) := hu.comp hcJ
  have key : ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs →
      ∫ x, (∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) * conj (Ωr 1 x) ∂μr = 0 := by
    intro Ωr Ωs hΩr hΩs
    have hT := hP D r s p μr Fr μs Fs hr hs ψ hψ χr χs θ hθ br bs b hb Ωr Ωs hΩr hΩs
    have h0 := horth _ hT
    have hm : Continuous fun y : Mx D (r + s) p => u y * conj (Ωr 1 (rowT y) * Ωs 1 (rowB y)) :=
      hu.mul (Complex.continuous_conj.comp (((continuous_th_one hΩr).comp continuous_rowT).mul
        ((continuous_th_one hΩs).comp continuous_rowB)))
    rw [integral_map hcJ.aemeasurable hm.aestronglyMeasurable] at h0
    rw [integral_integral_mul_of_bdd (F := fun w : Mx D r p × Mx D s p => u (rowJ w.1 w.2))
      hcF.aestronglyMeasurable (fun w => hB _)
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hr (hΩr.mem 1)))
      (integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1)))]
    simpa only [rowT_rowJ, rowB_rowJ, map_mul] using h0
  have hv : ∀ Ωs, IsTh ψ χs θ bs μs Ωs → ∀ x, ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs = 0 := by
    intro Ωs hΩs
    have hi : Integrable (fun z => conj (Ωs 1 z)) μs :=
      integrable_conj (GlobalTheory.CompanionTheory.BigCellJ.integrable_schwartzA hθ hs (hΩs.mem 1))
    refine congrFun (Tr (fun x => ∫ z, u (rowJ x z) * conj (Ωs 1 z) ∂μs) ?_ ?_ ?_)
    · exact continuous_integral_mul_of_bdd (f := fun x z => u (rowJ x z)) hcF (fun _ _ => hB _) hi
    · refine ⟨B * ∫ z, ‖conj (Ωs 1 z)‖ ∂μs, fun x => ?_⟩
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hi.norm.const_mul B) (ae_of_all _ fun z => ?_)
      show ‖u (rowJ x z) * conj (Ωs 1 z)‖ ≤ B * ‖conj (Ωs 1 z)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · exact fun Ωr hΩr => key Ωr Ωs hΩr hΩs
  have hz : ∀ x, (fun z => u (rowJ x z)) = 0 := fun x =>
    Ts (fun z => u (rowJ x z)) (hu.comp (hcJ.comp (continuous_const.prodMk continuous_id))) ⟨B, fun _ => hB _⟩
      fun Ωs hΩs => hv Ωs hΩs x
  funext y
  rw [← rowJ_rowT_rowB y]
  exact congrFun (hz (rowT y)) (rowB y)

end GlobalTheory.CompanionTheory.ThTot

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveReductionMaximalCompact
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RhoSplit

theorem exists_lift {A B C : Type} [Group A] [Group B] [Group C] (φ : A →* C) (ι : B →* C)
    (hι : Function.Injective ι) (h : ∀ a, φ a ∈ ι.range) : ∃ ρ : A →* B, ∀ a, φ a = ι (ρ a) := by
  refine ⟨((MonoidHom.ofInjective hι).symm.toMonoidHom).comp (φ.codRestrict ι.range h), fun a => ?_⟩
  have := (MonoidHom.ofInjective hι).apply_symm_apply (φ.codRestrict ι.range h a)
  exact (congrArg Subtype.val this).symm

theorem inL_injective {O L : Type} [CommRing O] [IsLocalRing O] [Field L] [Algebra O L]
    (h : Function.Injective (algebraMap O L)) {n : ℕ} :
    Function.Injective (inL (O := O) (L := L) (n := n)) := by
  intro a b e
  apply Units.ext
  ext i j
  apply h
  have := congrArg (fun g : GL (Ix n) L => g.1 i j) e
  simpa using this

theorem mem_level_square_congruence_iff {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (ϖ : O) (κ : GL (Ix n) O) :
    κ ∈ Gam2 (n := n) ϖ ↔
      ∀ i j, κ.1 i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ Ideal.span {ϖ ^ 2} := by
  have h1 : (1 : Matrix (Ix n) (Ix n) (O ⧸ Ideal.span {ϖ ^ 2})) =
      (1 : Matrix (Ix n) (Ix n) O).map (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2})) :=
    (Matrix.map_one _ (map_zero _) (map_one _)).symm
  unfold Gam2
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one, h1]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    exact Ideal.Quotient.eq.1 (by simpa using this)
  · intro h
    ext i j
    simpa using Ideal.Quotient.eq.2 (h i j)

theorem isOpen_ideal (D : D7) (v : Pl D) (ϖ : Ov D v) (h : ϖ ≠ 0) :
    IsOpen {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} := by
  have hc : algebraMap (Ov D v) (Lv D v) (ϖ ^ 2) ≠ 0 := by
    intro e
    exact pow_ne_zero 2 h (Subtype.val_injective (by simpa using e))
  set c := algebraMap (Ov D v) (Lv D v) (ϖ ^ 2) with hcdef
  have hO : IsOpen ((Valued.v.valuationSubring : ValuationSubring (Lv D v)) : Set (Lv D v)) :=
    Valued.isOpen_valuationSubring _
  have hs : {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} =
      (fun x => c⁻¹ * x) ⁻¹' ((Valued.v.valuationSubring : ValuationSubring (Lv D v)) : Set (Lv D v)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have : c⁻¹ * algebraMap (Ov D v) (Lv D v) (z * ϖ ^ 2) = algebraMap (Ov D v) (Lv D v) z := by
        rw [map_mul, ← hcdef]; field_simp
      simp only [Set.mem_preimage, this]
      exact z.2
    · intro hx
      refine ⟨⟨c⁻¹ * x, hx⟩ * ϖ ^ 2, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
      rw [map_mul, ← hcdef]
      have : algebraMap (Ov D v) (Lv D v) ⟨c⁻¹ * x, hx⟩ = c⁻¹ * x := rfl
      rw [this]; field_simp
  rw [hs]
  exact hO.preimage (continuous_const.mul continuous_id)

theorem continuous_entry (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (i j : Ix n) :
    Continuous fun k : KAt D n v => (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j := by
  have h1 : Continuous fun k : KAt D n v =>
      splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v k) :=
    (continuous_splitHom τ).comp ((continuous_proj _ _ v).comp continuous_subtype_val)
  have h2 : Continuous fun k : KAt D n v =>
      (splitHom D.sp.cm.sig (Jst D n) τ (proj D.sp.cm.sig (Jst D n) v k)).1 :=
    Units.continuous_val.comp h1
  exact h2.matrix_elem (finSumFinEquiv i) (finSumFinEquiv j)

theorem exists_rho (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    ∃ ρ : KAt D n v →* GL (Ix n) (Ov D v),
      (∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k)) ∧
      Function.Surjective ρ ∧
      ∀ ϖ : Ov D v, Irreducible ϖ → MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v)))) := by
  have hinj : Function.Injective (inL (O := Ov D v) (L := Lv D v) (n := n)) :=
    inL_injective Subtype.val_injective
  have hmem : ∀ k : KAt D n v, ((thU D n v τ).comp ((proj D.sp.cm.sig (Jst D n) v).comp (KAt D n v).subtype)) k ∈
      (inL (O := Ov D v) (L := Lv D v) (n := n)).range := by
    intro k
    have hk : (k : G D n) ∈ GlobalTheory.LocIntw.KUpAd D.sp.cm.sig (Jst D n) := (Subgroup.mem_inf.1 k.2).1
    exact (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ _).1 ((GlobalTheory.LocIntw.mem_KUpAd.1 hk).1 v)
  obtain ⟨ρ, hρ⟩ := exists_lift _ _ hinj hmem
  have hρ' : ∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k) := hρ
  refine ⟨ρ, hρ', ?_, ?_⟩
  · intro κ
    obtain ⟨g, hg⟩ := (GlobalTheory.T.bijective_local_unitary_to_GL D n v τ).2 (inL (L := Lv D v) κ)
    have hK := (GlobalTheory.T.mem_maximal_compact_iff_integral_image D n v τ g).2 ⟨κ, hg.symm⟩
    have h1 : emb D.sp.cm.sig (Jst D n) v g ∈ KAt D n v :=
      Subgroup.mem_inf.2 ⟨GlobalTheory.LocIntw.emb_mem_KUpAd hK, by rw [← range_emb]; exact ⟨g, rfl⟩⟩
    refine ⟨⟨_, h1⟩, hinj ?_⟩
    rw [← hρ', proj_emb_self, hg]
  · intro ϖ hϖ
    have hU := isOpen_ideal D v ϖ hϖ.ne_zero
    set U := {x : Lv D v | ∃ y ∈ Ideal.span {ϖ ^ 2}, algebraMap (Ov D v) (Lv D v) y = x} with hUdef
    have hs : ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v))) =
        ⋂ i : Ix n, ⋂ j : Ix n, (fun k : KAt D n v =>
          (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j - (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j) ⁻¹' U := by
      ext k
      have he : ∀ i j, (thU D n v τ (proj D.sp.cm.sig (Jst D n) v k)).1 i j -
          (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j =
          algebraMap (Ov D v) (Lv D v) ((ρ k).1 i j - (1 : Matrix (Ix n) (Ix n) (Ov D v)) i j) := by
        intro i j
        have h1 : (1 : Matrix (Ix n) (Ix n) (Lv D v)) i j =
            algebraMap (Ov D v) (Lv D v) ((1 : Matrix (Ix n) (Ix n) (Ov D v)) i j) := by
          by_cases h : i = j
          · subst h
            rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
          · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
        rw [hρ', map_sub, h1]
        rfl
      simp only [Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe, mem_level_square_congruence_iff, he, hUdef, Set.mem_setOf_eq]
      constructor
      · exact fun h i j => ⟨_, h i j, rfl⟩
      · intro h i j
        obtain ⟨y, hy, e⟩ := h i j
        have hA : Function.Injective (algebraMap (Ov D v) (Lv D v)) := Subtype.val_injective
        have e' := hA e
        rw [← e']
        exact hy
    rw [hs]
    refine IsOpen.measurableSet (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hU.preimage ?_)
    exact (continuous_entry D n v τ i j).sub continuous_const

end GlobalTheory.CompanionTheory.Jp.RhoSplit

end
end

