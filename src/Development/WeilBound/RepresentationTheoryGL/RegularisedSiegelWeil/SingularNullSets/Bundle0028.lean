import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0027
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1977
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

section GlobalTheory

variable {R : Type}

theorem block_matrix_apply_top_right (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (Fin.castAdd n i) (Fin.natAdd n j) = b i j := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₂]

theorem submatrix_fromBlocks_mul [Ring R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one [Ring R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

end GlobalTheory

theorem adj_neg_one : adj (-1 : Mx D n n) = -1 := by
  show (Matrix.map (-1 : Mx D n n) ⇑(Formalism.L2.Theta.cA D)).transpose = -1
  rw [show Matrix.map (-1 : Mx D n n) ⇑(Formalism.L2.Theta.cA D) = (Formalism.L2.Theta.cA D).mapMatrix (-1) from rfl,
    map_neg, map_one, Matrix.transpose_neg, Matrix.transpose_one]

private theorem blk4_neg_one_lemma {R : Type} [Ring R] :
    blk4 (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = -1 := by
  rw [← block_matrix_one (R := R) (n := n)]
  delta GlobalTheory.StdUnn.blk4
  rw [show Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = -Matrix.fromBlocks 1 0 0 1 by
    rw [Matrix.fromBlocks_neg, neg_zero]]
  exact congrFun (congrFun (Matrix.submatrix_neg _) _) _

theorem mat_ww {w : G D p} (hw : IsW w) :
    mat (w * w)⁻¹ = blk4 ((-1 : GL (Fin p) (AE D)) : Matrix _ _ _) 0 0 (adj (((-1 : GL (Fin p) (AE D))⁻¹ : GL _ _) : Matrix _ _ _)) := by
  have hM : mat (w * w) = -1 := by
    rw [mat_mul, show mat w = blk4 0 1 (-1) 0 from hw, submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    exact blk4_neg_one_lemma
  have h1 := mat_mul_inv (w * w)
  rw [hM, neg_one_mul, neg_eq_iff_eq_neg] at h1
  rw [h1, inv_neg_one, Units.val_neg, Units.val_one, adj_neg_one, blk4_neg_one_lemma]

theorem good_neg {S : Finset (Pl D)} {e : AE D} {f : Mx D ρ p → ℂ} (hf : Good S e f) (c : ℂ) :
    Good S e (fun z => c * f (-z)) := by
  delta PositivityTheory.Rg.Rsw.L.Good at hf ⊢
  intro x
  beta_reduce
  have hi : IntOff S (-x) ↔ IntOff S x := by
    delta PositivityTheory.Rg.Rsw.L.IntOff
    constructor
    · intro H v hv i j
      have h1 := neg_mem (H v hv i j)
      rwa [Matrix.neg_apply, map_neg, neg_neg] at h1
    · intro H v hv i j
      rw [Matrix.neg_apply, map_neg]
      exact neg_mem (H v hv i j)
  have h := hf (-x)
  by_cases hx : IntOff S x
  · rw [if_pos hx, h, if_pos (hi.2 hx), smul_neg]
  · rw [if_neg hx, h, if_neg (fun H => hx (hi.1 H)), mul_zero]

theorem kOff_entry {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) (k l : Fin (n + n)) :
    (∀ w, compInf D.host.F D.host.E w (mat g k l) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) k l) ∧
    (∀ v ∈ S, cv D v (mat g k l) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) k l) ∧
    (∀ v ∉ S, cv D v (mat g k l) ∈ intLoc D.host.F D.host.E v) := by
  exact ⟨fun w => kOff_inf hg w k l, fun v hv => kOff_at hg hv k l, fun v hv => (kOff_int hg hv k l).1⟩

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThProd
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

open PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.ThTot

namespace PositivityTheory.Rg.Rsw.L.LThProd

variable {D : D7}

theorem rowB_eq {m p : ℕ} (y : Mx D (m + 1) p) : rowB (r := m) (s := 1) y = y.submatrix (fun _ => Fin.last m) id := by
  funext a j
  show y (Fin.natAdd m a) j = y (Fin.last m) j
  rw [natAdd_one]

theorem succ (hW : L.WMaj) {p : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D}
    (hθ : IsInfFam θ) : ∀ (k : ℕ) (b₀ : HermE D (k + 1)), IsDiagInv b₀ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ →
    ResEta D χ (k + 1) → ∀ (μ : Measure (Mx D (k + 1) p)) (𝓕 : Set (Mx D (k + 1) p)), IsCovolOne (ratMx D (k + 1) p) μ 𝓕 →
    ∀ η : Fin (k + 1) → Mx D 1 p → ℂ, (∀ i, η i ∈ schwartzA θ 1 p) →
    ∃ Ω, IsTh ψ χ θ b₀ μ Ω ∧ ∀ y, Ω 1 y = ∏ i, η i (y.submatrix (fun _ => i) id)
  | 0, b₀, hb, χ, hχ, hr, μ, 𝓕, hμ, η, hη => by
    obtain ⟨Ω, hT, h1⟩ := oneTh hW μ 𝓕 hμ hψ b₀ hb.2 hχ hr hθ (η 0) (hη 0)
    refine ⟨Ω, hT, fun y => ?_⟩
    rw [Fin.prod_univ_one, h1]
    congr 1
    funext a j
    rw [Fin.fin_one_eq_zero a]
    rfl
  | k + 1, b₀, hb, χ, hχ, hr, μ, 𝓕, hμ, η, hη => by
    obtain ⟨ε, hε, hεr⟩ := GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta D 1
    obtain ⟨μr, 𝓕r, hμr⟩ := GlobalTheory.MixModel.exists_isCovolOne D (k + 1) p
    obtain ⟨μs, 𝓕s, hμs⟩ := GlobalTheory.MixModel.exists_isCovolOne D 1 p
    obtain ⟨Ωr, hTr, hr1⟩ := succ hW hψ hθ k (topH b₀) (topH_diag hb) (χ * ε⁻¹) (hecke_mul_inv hχ hε)
      (resEta_mul_inv hr (by simpa using hεr)) μr 𝓕r hμr (fun i => η (Fin.castSucc i)) fun i => hη _
    obtain ⟨Ωs, hTs, hs1⟩ := oneTh hW μs 𝓕s hμs hψ (botH b₀) (botH_det hb) hε (by simpa using hεr) hθ
      (η (Fin.last (k + 1))) (hη _)
    have hP := GlobalTheory.CompanionTheory.ThTot.ProductTheta.prodTh_of_schwTensor GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor D (k + 1) 1 p μr 𝓕r μs 𝓕s
      hμr hμs ψ hψ (χ * ε⁻¹) ε θ hθ (topH b₀) (botH b₀) b₀ (diagonal_hermitian_is_block hb) Ωr Ωs hTr hTs
    rw [inv_mul_cancel_right,
      ← GlobalTheory.CompanionTheory.ThTot.ProdMeasPf.prodMeas D (k + 1) 1 p μr 𝓕r μs 𝓕s μ 𝓕 hμr hμs hμ] at hP
    refine ⟨_, hP, fun y => ?_⟩
    show Ωr 1 (rowT y) * Ωs 1 (rowB y) = _
    rw [hr1, hs1, rowB_eq]
    conv_rhs => rw [Fin.prod_univ_castSucc]
    rfl

end PositivityTheory.Rg.Rsw.L.LThProd

namespace PositivityTheory.Rg.Rsw.L

theorem thProd (hW : WMaj) : ThProd := by
  intro D ρ p m ψ hψ b₀ hb χ hχ hr hρ θ hθ η hη
  obtain ⟨k, rfl⟩ : ∃ k, ρ = k + 1 := ⟨ρ - 1, by omega⟩
  exact LThProd.succ hW hψ hθ k b₀ hb χ hχ hr m.μ m.𝓕 m.hμ η hη

end PositivityTheory.Rg.Rsw.L

end
end

