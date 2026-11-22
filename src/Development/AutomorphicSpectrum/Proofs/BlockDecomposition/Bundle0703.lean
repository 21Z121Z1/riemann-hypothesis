import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0678
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairLocalAuxiliaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0663
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1437
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSiegelWeilUnramifiedMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0691
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.UnipotentTateFunctionalEquation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.RealLocalIntegrals.RealGammaLimits.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValMeasurableEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndexEqDiagonal
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.Tr

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

theorem isInt_mul {r s t : Type} [Fintype s] {M : Matrix r s (w.adicCompletion E)}
    {N : Matrix s t (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) : IsInt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact (Ov E w).sum_mem fun k _ => (Ov E w).mul_mem (hM i k) (hN k j)

theorem isInt_of_GLint {n : ℕ} {g : GL (Fin n) (w.adicCompletion E)} (hg : g ∈ GLint (Fin n) (Ov E w)) :
    IsInt w g.val := by
  obtain ⟨f, rfl⟩ := hg
  intro i j
  exact (f.val i j).2

theorem isInt_sandwich {r s : ℕ} {u : GL (Fin r) (w.adicCompletion E)} {v : GL (Fin s) (w.adicCompletion E)}
    (hu : u ∈ GLint (Fin r) (Ov E w)) (hv : v ∈ GLint (Fin s) (Ov E w))
    (M : Matrix (Fin r) (Fin s) (w.adicCompletion E)) : IsInt w (u.val * M * v.val) ↔ IsInt w M := by
  constructor
  · intro h
    have key := isInt_mul (isInt_mul (isInt_of_GLint (inv_mem hu)) h) (isInt_of_GLint (inv_mem hv))
    have h1 : (u⁻¹).val * u.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : v.val * (v⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : (u⁻¹).val * (u.val * M * v.val) * (v⁻¹).val = M := by
      calc (u⁻¹).val * (u.val * M * v.val) * (v⁻¹).val
          = ((u⁻¹).val * u.val) * M * (v.val * (v⁻¹).val) := by simp only [Matrix.mul_assoc]
        _ = M := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at key
  · intro h
    exact isInt_mul (isInt_mul (isInt_of_GLint hu) h) (isInt_of_GLint hv)

def phi {a b : ℕ} {L : Type} [Field L] (p : GL (Fin a) L) (q : GL (Fin b) L) :
    Matrix (Fin a) (Fin b) L ≃+ Matrix (Fin a) (Fin b) L where
  toFun X := p.val * X * (q⁻¹).val
  invFun Y := (p⁻¹).val * Y * q.val
  left_inv X := by
    have h1 : (p⁻¹).val * p.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (q⁻¹).val * q.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (p⁻¹).val * (p.val * X * (q⁻¹).val) * q.val
        = ((p⁻¹).val * p.val) * X * ((q⁻¹).val * q.val) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  right_inv Y := by
    have h1 : p.val * (p⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 : q.val * (q⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc p.val * ((p⁻¹).val * Y * q.val) * (q⁻¹).val
        = (p.val * (p⁻¹).val) * Y * (q.val * (q⁻¹).val) := by simp only [Matrix.mul_assoc]
      _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]

theorem relIndex_of_equiv {A B : Type} [AddGroup A] [AddGroup B] (φ : A ≃+ B) (H K : AddSubgroup A)
    (H' K' : AddSubgroup B) (hH : ∀ X, X ∈ H ↔ φ X ∈ H') (hK : ∀ X, X ∈ K ↔ φ X ∈ K') :
    H.relIndex K = H'.relIndex K' := by
  have key : ∀ (P : AddSubgroup A) (P' : AddSubgroup B), (∀ X, X ∈ P ↔ φ X ∈ P') →
      P.map φ.toAddMonoidHom = P' := by
    intro P P' h
    ext Y
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (h X).1 hX
    · intro hY
      exact ⟨φ.symm Y, (h _).2 (by simpa using hY), by simp⟩
  rw [← key H H' hH, ← key K K' hK]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _ φ.injective).symm

theorem mem_latD {ϖ : w.adicCompletion E} {a b i j : ℕ} {W : Matrix (Fin a) (Fin b) (w.adicCompletion E)} :
    W ∈ latD ϖ a b i j ↔
      ∀ (r : Fin a) (s : Fin b), (if (r : ℕ) < i ∧ j ≤ (s : ℕ) then ϖ * W r s else W r s) ∈ Ov E w := Iff.rfl

theorem unif_mem {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ∈ Ov E w := by
  have : Valued.v ϖ ≤ 1 := by
    rw [h]
    exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 this

theorem unif_ne {ϖ : w.adicCompletion E} (h : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  intro h0
  rw [IsUnifV, h0, map_zero] at h
  exact WithZero.zero_ne_coe h

theorem diag_iff_latD {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {a b : ℕ} (i j : ℕ)
    (W : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (IsInt w (diagJ a ϖ i * W) ∧ IsInt w (ϖ • (W * diagJ b ϖ⁻¹ j))) ↔ W ∈ latD ϖ a b i j := by
  have hm := unif_mem hϖ
  have h0 := unif_ne hϖ
  have hc : ∀ x : w.adicCompletion E, ϖ * (x * ϖ⁻¹) = x := fun x => by field_simp
  rw [mem_latD]
  constructor
  · rintro ⟨h1, h2⟩ r s
    have a1 := h1 r s
    have a2 := h2 r s
    simp only [diagJ, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul] at a1 a2
    by_cases hr : (r : ℕ) < i <;> by_cases hs : (s : ℕ) < j
    · rw [if_neg (by omega)]
      rw [if_pos hs, hc] at a2
      exact a2
    · rw [if_pos ⟨hr, by omega⟩]
      rw [if_pos hr] at a1
      exact a1
    · rw [if_neg (by omega)]
      rw [if_neg hr, one_mul] at a1
      exact a1
    · rw [if_neg (by omega)]
      rw [if_neg hr, one_mul] at a1
      exact a1
  · intro h
    refine ⟨fun r s => ?_, fun r s => ?_⟩
    · have a := h r s
      simp only [diagJ, Matrix.diagonal_mul]
      by_cases hr : (r : ℕ) < i
      · rw [if_pos hr]
        by_cases hs : j ≤ (s : ℕ)
        · rwa [if_pos ⟨hr, hs⟩] at a
        · rw [if_neg (by omega)] at a
          exact (Ov E w).mul_mem hm a
      · rw [if_neg hr, one_mul]
        rwa [if_neg (by omega)] at a
    · have a := h r s
      simp only [diagJ, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
      by_cases hs : (s : ℕ) < j
      · rw [if_pos hs, hc]
        rwa [if_neg (by omega)] at a
      · rw [if_neg hs, mul_one]
        by_cases hr : (r : ℕ) < i
        · rwa [if_pos ⟨hr, by omega⟩] at a
        · rw [if_neg (by omega)] at a
          exact (Ov E w).mul_mem hm a

theorem diagJ_mul_inv {L : Type} [Field L] {ϖ : L} (h0 : ϖ ≠ 0) (n j : ℕ) :
    diagJ n ϖ j * diagJ n ϖ⁻¹ j = 1 := by
  rw [diagJ, diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext r
  split_ifs <;> simp [h0]

theorem mem_latM_iff {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {a b i j : ℕ}
    {m : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)}
    {k₁ p : GL (Fin a) (w.adicCompletion E)} {k₂ q : GL (Fin b) (w.adicCompletion E)}
    (hk₁ : k₁ ∈ GLint (Fin a) (Ov E w)) (hp : p ∈ GLint (Fin a) (Ov E w))
    (hk₂ : k₂ ∈ GLint (Fin b) (Ov E w)) (hq : q ∈ GLint (Fin b) (Ov E w))
    (e₁ : m.1.val = k₁.val * diagJ a ϖ i * p.val) (e₂ : m.2.val = k₂.val * diagJ b ϖ j * q.val)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    X ∈ latM ϖ m ↔ phi p q X ∈ latD ϖ a b i j := by
  set W := phi p q X with hW
  have hX : X = (p⁻¹).val * W * q.val := ((phi p q).symm_apply_apply X).symm
  have hpp : p.val * (p⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqq : q.val * (q⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hkk : k₂.val * (k₂⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD := diagJ_mul_inv (unif_ne hϖ) b j
  have f₁ : m.1.val * X = k₁.val * (diagJ a ϖ i * W) * q.val := by
    calc m.1.val * X = k₁.val * diagJ a ϖ i * (p.val * (p⁻¹).val) * W * q.val := by
          rw [e₁, hX]; simp only [Matrix.mul_assoc]
      _ = k₁.val * (diagJ a ϖ i * W) * q.val := by
          rw [hpp, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hx : m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val) = 1 := by
    calc m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val)
        = k₂.val * diagJ b ϖ j * (q.val * (q⁻¹).val) * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
          rw [e₂]; simp only [Matrix.mul_assoc]
      _ = k₂.val * (diagJ b ϖ j * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
          rw [hqq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD, Matrix.mul_one, hkk]
  have hinv : (m.2⁻¹).val = (q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
    calc (m.2⁻¹).val = (m.2⁻¹).val * (m.2.val * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val)) := by
          rw [hx, Matrix.mul_one]
      _ = ((m.2⁻¹).val * m.2.val) * ((q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val) := by
          simp only [Matrix.mul_assoc]
      _ = (q⁻¹).val * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have f₂ : ϖ • (X * (m.2⁻¹).val) = (p⁻¹).val * (ϖ • (W * diagJ b ϖ⁻¹ j)) * (k₂⁻¹).val := by
    have : X * (m.2⁻¹).val = (p⁻¹).val * (W * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
      calc X * (m.2⁻¹).val
          = (p⁻¹).val * W * (q.val * (q⁻¹).val) * diagJ b ϖ⁻¹ j * (k₂⁻¹).val := by
            rw [hinv, hX]; simp only [Matrix.mul_assoc]
        _ = (p⁻¹).val * (W * diagJ b ϖ⁻¹ j) * (k₂⁻¹).val := by
            rw [hqq, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
  have s₁ := isInt_sandwich hk₁ hq (diagJ a ϖ i * W)
  have s₂ := isInt_sandwich (inv_mem hp) (inv_mem hk₂) (ϖ • (W * diagJ b ϖ⁻¹ j))
  rw [← diag_iff_latD hϖ i j W, ← s₁, ← s₂, ← f₁, ← f₂]
  exact Iff.rfl

theorem latM_relIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (i j : ℕ), i ≤ a → j ≤ b → ∀ m : GLw a w × GLw b w, Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 → Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 → (intSub a b w).relIndex (latM ϖ m) = (intSub a b w).relIndex (latD ϖ a b i j) := by
  intro E _ _ _ a b w ϖ hϖ i j _ _ m h₁ h₂
  obtain ⟨k₁, hk₁, p, hp, e₁⟩ := Set.mem_of_indicator_ne_zero h₁
  obtain ⟨k₂, hk₂, q, hq, e₂⟩ := Set.mem_of_indicator_ne_zero h₂
  refine relIndex_of_equiv (phi p q) _ _ _ _ (fun X => ?_) (mem_latM_iff hϖ hk₁ hp hk₂ hq e₁ e₂)
  constructor
  · intro h
    exact (isInt_sandwich hp (inv_mem hq) X).2 h
  · intro h
    exact (isInt_sandwich hp (inv_mem hq) X).1 h

end GlobalTheory.CompanionTheory.CtS.Tr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelsNeighbourhoodBasisStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_levels_neighbourhood_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ),
    ∀ U ∈ nhds (0 : Fin n → Fin M → Af F ⊗[F] E), ∃ N : ℕ, 0 < N ∧
      (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExhaustionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_exhaustion : PositivityTheory.SiegelWeilFormula.Gunr.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.GunrExhaust.exhaust | exact GlobalTheory.CompanionTheory.GunrExhaust.exhaust | (intros; apply GlobalTheory.CompanionTheory.GunrExhaust.exhaust <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComparisonSplit
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses

namespace GlobalTheory.CompanionTheory.LcSplit

theorem level_pick {H : Type} [Group H] [TopologicalSpace H] (σ : H →* H) (hc : Continuous σ) (hi : ∀ g, σ (σ g) = g)
    (K A₁ A₂ : Subgroup H) (f₁ f₂ : H → ℂ) (ho₁ : IsOpen (A₁ : Set H)) (ho₂ : IsOpen (A₂ : Set H)) (hK : A₁ ≤ K)
    (h₁ : IsHecke A₁ f₁) (h₂ : IsHecke A₂ f₂) :
    ∃ L : Subgroup H, IsOpen (L : Set H) ∧ L ≤ K ∧ (∀ k ∈ L, σ k ∈ L) ∧ IsHecke L f₁ ∧ IsHecke L f₂ := by
  have hAo : IsOpen ((A₁ ⊓ A₂ : Subgroup H) : Set H) := by
    rw [Subgroup.coe_inf]; exact ho₁.inter ho₂
  refine ⟨(A₁ ⊓ A₂) ⊓ (A₁ ⊓ A₂).comap σ, ?_, fun x hx => hK hx.1.1, fun k hk => ⟨hk.2, ?_⟩,
    ⟨h₁.1, fun k hk => h₁.2 k hk.1.1⟩, ⟨h₂.1, fun k hk => h₂.2 k hk.1.2⟩⟩
  · rw [Subgroup.coe_inf]
    exact hAo.inter (hAo.preimage hc)
  · show σ (σ k) ∈ A₁ ⊓ A₂
    rw [hi]; exact hk.1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem exists_level (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (hφ₁ : IsTestP φ₁) (hφ₂ : IsTestP φ₂) (w : Pl E) :
    ∃ L : Subgroup (GLw a w × GLw b w), IsOpen (L : Set (GLw a w × GLw b w)) ∧ L ≤ K2 a b w ∧ (∀ k ∈ L, sgP a b w k ∈ L) ∧
      IsHecke L (φ₁ w) ∧ IsHecke L (φ₂ w) := by
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨K₁, K₂, hl₁, hl₂, ht⟩ := hφ₁
  obtain ⟨K₁', K₂', hl₁', hl₂', ht'⟩ := hφ₂
  refine level_pick (sgP a b w) hc hi (K2 a b w) ((K₁ w).prod (K₂ w)) ((K₁' w).prod (K₂' w)) _ _ ?_ ?_ ?_ (ht.1 w) (ht'.1 w)
  · rw [Subgroup.coe_prod]; exact (hl₁.1 w).1.prod (hl₂.1 w).1
  · rw [Subgroup.coe_prod]; exact (hl₁'.1 w).1.prod (hl₂'.1 w).1
  · exact Subgroup.prod_mono (hl₁.1 w).2.1 (hl₂.1 w).2.1

theorem fv_split (S : Set (Pl E)) (hS : IsSection S) (w : Pl E) (hw : w ∈ S) (hs : IsSplitAt w)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (y : Yv a b (w.under (𝓞 (maximalRealSubfield E)))) :
    fv S φ₁ φ₂ _ y = φ₁ w (evw ⟨w, rfl⟩ y) * φ₂ w (evw ⟨w, rfl⟩ (thv a b _ y)) := by
  unfold fv
  have key : ∀ u : Above (w.under (𝓞 (maximalRealSubfield E))), u.1 ∈ S → u = ⟨w, rfl⟩ := by
    intro u hu
    exact Subtype.ext ((hS w).unique ⟨hu, u.2⟩ ⟨hw, rfl⟩)
  rw [finprod_eq_single _ (⟨w, rfl⟩ : Above (w.under (𝓞 (maximalRealSubfield E))))]
  · rw [finprod_eq_if, if_pos hw, if_pos hs]
  · intro u hu
    rw [finprod_eq_if, if_neg (fun h => hu (key u h))]

theorem th_split (a b : ℕ) (w : Pl E) (hs : IsSplitAt w) :
    (thL a w).prodMap (thL b w) = MonoidHom.id (GLw a w × GLw b w) := by
  unfold thL
  rw [if_pos hs, if_pos hs]
  ext x <;> rfl

theorem seen_split (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (w : Pl E) (hs : IsSplitAt w) :
    seen φ₁ φ₂ w = fun y => hint (K2 a b w) fun z => φ₁ w z * φ₂ w (z⁻¹ * y) := by
  funext y
  unfold seen
  rw [if_pos hs]

theorem locEl_sep {n : ℕ} (w : Pl E) (hs : IsSplitAt w) (δ : GL (Fin n) E) (h : polE δ ∈ Ell E n) :
    (nrmL n w (locEl n w δ)).val.charpoly.Separable := by
  have : (nrmL n w (locEl n w δ)).val.charpoly = (polE δ).map (algebraMap E (w.adicCompletion E)) := by
    unfold nrmL locEl polE
    rw [if_pos hs, if_pos hs]
    exact Matrix.charpoly_map _ _
  rw [this]
  exact h.2.2.1.map

theorem target_side (hU : GlobalTheory.BCT.Unr E) (w : Pl E) (hs : IsSplitAt w)
    (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E) (hδ₁ : polE δ₁ ∈ Ell E a) (hδ₂ : polE δ₂ ∈ Ell E b) :
    Good (MonoidHom.id _) (K2 a b w) (locEl a w δ₁, locEl b w δ₂) ∧
    ∀ C : Set (GLw a w × GLw b w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (GLw a w × GLw b w)) (locEl a w δ₁, locEl b w δ₂) : Set _)
      (K2 (E := E) a b w : Set (GLw a w × GLw b w)) | ∃ k ∈ K2 (E := E) a b w,
        (Quotient.out q * k)⁻¹ * (locEl a w δ₁, locEl b w δ₂) * MonoidHom.id (GLw a w × GLw b w) (Quotient.out q * k) ∈ C}.Finite := by
  have h1 := GlobalTheory.CompanionTheory.LocGoodProof.locGood E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)
  have h2 := (GlobalTheory.CompanionTheory.TwistOrbit.locSupp E hU a b w (locEl a w δ₁, locEl b w δ₂) (locEl_sep w hs δ₁ hδ₁) (locEl_sep w hs δ₂ hδ₂)).1
  rw [th_split a b w hs] at h1 h2
  exact ⟨h1, h2⟩

theorem pair_integral_points_open_compact (a b : ℕ) (w : Pl E) :
    IsOpen ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) ∧ IsCompact ((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)) := by
  obtain ⟨hKo₁, hKc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨hKo₂, hKc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  rw [Subgroup.coe_prod]
  exact ⟨hKo₁.prod hKo₂, hKc₁.prod hKc₂⟩

theorem locCompareSplit : LocCompareSplit := by
  intro hCj E _ _ _ hU a b S hS φ₁ φ₂ hφ₁ hφ₂ δ₁ δ₂ hδ₁ hδ₂ w hw hs
  obtain ⟨e, he1, he3, he4, heδ⟩ := GlobalTheory.CompanionTheory.SplitIso.split_iso hCj E a b _ ⟨w, rfl⟩ hs
  obtain ⟨hc, hi, hk⟩ := sgP_facts E a b w
  obtain ⟨L, hLo, hLK, hLs, hH₁, hH₂⟩ := exists_level φ₁ φ₂ hφ₁ hφ₂ w
  obtain ⟨hKo, hKc⟩ := pair_integral_points_open_compact (E := E) a b w
  obtain ⟨hG, hF⟩ := target_side hU w hs δ₁ δ₂ hδ₁ hδ₂
  set y := pv a b (w.under (𝓞 (maximalRealSubfield E))) (ratF E a δ₁, ratF E b δ₂) with hy
  have hN : (e y).1 * sgP a b w (e y).2 = (locEl a w δ₁, locEl b w δ₂) := by
    rw [hy, heδ]
    exact Prod.ext (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E a w δ₁ hs) (GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL E b w δ₂ hs)
  have ht := GlobalTheory.EulerTw.Transport.twOrb_transport _ _ e (thv a b _) (swTw (sgP a b w))
    (Kv a b _) ((K2 a b w).prod (K2 a b w)) y (fv S φ₁ φ₂ _) (fun z => φ₁ w z.1 * φ₂ w (sgP a b w z.2))
    he3 he4 (fun g => by
      have h2 : evw ⟨w, rfl⟩ (thv a b _ g) = sgP a b w (e g).2 := by
        rw [← he1, he3]; rfl
      show φ₁ w (e g).1 * φ₂ w (sgP a b w (e g).2) = _
      rw [he1, ← h2, fv_split S hS w hw hs])
  rw [ht, seen_split φ₁ φ₂ w hs, th_split a b w hs]
  have hsc := GlobalTheory.T.twisted_orbital_pair_convolution _ (sgP a b w) (K2 a b w) hc hi hk hKo hKc (e y).1 (e y).2 (φ₁ w) (φ₂ w) L hLo hLK hLs hH₁ hH₂
    (by rw [hN]; exact hG) (by rw [hN]; exact hF)
  rw [hN] at hsc
  exact hsc

end GlobalTheory.CompanionTheory.LcSplit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
section
noncomputable section

namespace GlobalTheory.CompanionTheory.EisDict

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open PositivityTheory.RgEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def sec : (Af F ⊗[F] E) →+ AE F E :=
  (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) (LinearMap.id : E →ₗ[F] E)).toAddMonoidHom

theorem sec_tmul (a : Af F) (x : E) : sec F E (a ⊗ₜ[F] x) = ((0, a) : AF F) ⊗ₜ[F] x := rfl

theorem sec_finPart (z : AE F E) : sec F E (HeckeCharacterZeroLocus.ThmBIn.finPart F E z) = finOne F • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | tmul a x =>
    change sec F E (HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x) = _
    rw [sec_tmul, TensorProduct.smul_tmul']
    congr 1
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = 0 * a.1
      simp
    · change a.2 = 1 * a.2
      simp

theorem finPart_finOne_smul (z : AE F E) :
    HeckeCharacterZeroLocus.ThmBIn.finPart F E (finOne F • z) = HeckeCharacterZeroLocus.ThmBIn.finPart F E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    change HeckeCharacterZeroLocus.ThmBIn.sndA F (finOne F • a) ⊗ₜ[F] x = HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x
    congr 1
    change 1 * a.2 = a.2
    simp

theorem sec_mem {y : Af F ⊗[F] E} (hy : y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : sec F E y ∈ intHat F E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨(0, a), ?_, fun v => ha v, x, ?_⟩
    · exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · rw [sec_tmul]
      change _ = pairA F 0 a • ((1 : AF F) ⊗ₜ[F] (x : E))
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
  | zero => simpa using (intHat F E).zero_mem
  | add x y _ _ hx hy => simpa using (intHat F E).add_mem hx hy
  | neg x _ hx => simpa using (intHat F E).neg_mem hx

theorem finPart_mem {z : AE F E} (hz : z ∈ intHat F E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z h =>
    obtain ⟨a, -, ha, o, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨HeckeCharacterZeroLocus.ThmBIn.sndA F a, fun v => ha v, o, ?_⟩
    change HeckeCharacterZeroLocus.ThmBIn.finPart F E (a • ((1 : AF F) ⊗ₜ[F] (o : E))) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  | zero => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).zero_mem
  | add x y _ _ hx hy => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).add_mem hx hy
  | neg x _ hx => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).neg_mem hx

theorem mem_intAd_iff (z : AE F E) :
    eqv F E z ∈ intAd E ↔ HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [GroundTheory.BlockD.ThmBHecke.mem_intAE_iff, ← GroundTheory.BlockD.ThmBHecke.adeleEquiv_snd,
    GroundTheory.Global.mem_integralFiniteAdeles]
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  rfl

theorem dict : Dict := by
  intro F E _ _ _ _ _
  refine ⟨GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv, GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm,
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA, fun z => ?_, fun x => ?_⟩
  · rw [mem_intAd_iff]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← sec_finPart]
      exact sec_mem h
    · rw [← finPart_finOne_smul]
      exact finPart_mem h
  · exact (PositivityTheory.ThKCT.Tate.absE_eq x).symm

end GlobalTheory.CompanionTheory.EisDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSiegelWeilUnramifiedMeasureStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_siegel_weil_unramified_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ (c : HermR (Fv F v) σ n) (A : Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact A → IsOpen A → MeasurableSet A ∧ mv c A ≠ ⊤ ∧ ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ gramNear (Fv F v) σ J c (U k)) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramNear (Fv F v) σ J c (U k)) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramNear (Fv F v) σ J c (U k))).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.avgFree_tendsto | exact GlobalTheory.CompanionTheory.AvgFree.avgFree_tendsto | (intros; apply GlobalTheory.CompanionTheory.AvgFree.avgFree_tendsto <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCyclePointDictionaryStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_point_dictionary : GlobalTheory.CompanionTheory.MixZ.PtDict := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ptDict | exact GlobalTheory.CompanionTheory.MixZ.ptDict | (intros; apply GlobalTheory.CompanionTheory.MixZ.ptDict <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultIntegralPowerBoundStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mult_integral_power_bound : ∀ σ : ℝ, 0 < σ → σ < 1 → ∀ N : ℕ, 1 ≤ N → ∃ K : ℝ, ∀ q : ℝ, 0 < q →
    Integrable (fun t : ℝˣ => |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N) Ad3.mulR ∧
    ∫ t : ℝˣ, |(t : ℝ)| ^ (σ - 1) / (1 + |(t : ℝ)⁻¹| * q) ^ N ∂Ad3.mulR ≤ K * q ^ (σ - 1) := by
  first | exact @GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le | exact GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le | (intros; apply GlobalTheory.CompanionTheory.PowerKernel.kernel_integral_le <;> assumption)
end

