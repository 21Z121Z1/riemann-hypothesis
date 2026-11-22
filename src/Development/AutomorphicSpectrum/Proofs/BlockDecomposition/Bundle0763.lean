import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0755
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeight

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZero
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Abstract
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

open scoped Pointwise in

theorem mean_add_left (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] {s : Set G}
    (hs : IsAddFundamentalDomain Γ s μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) (t : G) :
    ∫ y in s, f (t + y) ∂μ = ∫ y in s, f y ∂μ := by
  have hFD : IsAddFundamentalDomain Γ (t +ᵥ s) μ := hs.vadd_of_comm t
  have h1 : ∫ y in (t +ᵥ s), f y ∂μ = ∫ y in s, f (t + y) ∂μ := by
    have hemb : MeasurableEmbedding (fun y : G => t + y) := (Homeomorph.addLeft t).measurableEmbedding
    exact (measurePreserving_add_left μ t).setIntegral_image_emb hemb f s
  rw [← h1]
  exact hFD.setIntegral_eq hs (fun g x => hf g.1 g.2 x)

theorem exists_bound_of_periodic (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    (f : G → ℂ) (hc : Continuous f) (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : ∃ C, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x => ?_⟩
  obtain ⟨γ, hγ, hk⟩ := hcov x
  rw [← hf γ hγ x]
  exact hC _ hk

theorem const_of_coefficients (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) (A : Type) [AddCommGroup A] (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a))
    (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y) (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1)
    (hn : ∀ a x, ‖χ a x‖ = 1) (hker : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 ≠ ∞) (φ : G → ℂ) (hφ : Continuous φ)
    (hper : ∀ γ ∈ Γ, ∀ x, φ (γ + x) = φ x) (hco : ∀ a, a ≠ 0 → ∫ x in 𝓕, χ a x * φ x ∂μ = 0) (y : G) : φ y = φ 0 := by
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨C, hC⟩ := exists_bound_of_periodic Γ hK hcov φ hφ hper
  have hint : ∀ (a : A) (f : G → ℂ), Continuous f → (∀ x, ‖f x‖ ≤ C) → IntegrableOn (fun x => χ a x * f x) 𝓕 μ := by
    intro a f hf hb
    refine Measure.integrableOn_of_bounded (M := C) hfin ((hc a).mul hf).aestronglyMeasurable (.of_forall fun x => ?_)
    rw [norm_mul, hn, one_mul]
    exact hb x
  have hshift : ∀ a, ∫ x in 𝓕, χ a x * φ (y + x) ∂μ = ∫ x in 𝓕, χ a x * φ x ∂μ := by
    intro a
    by_cases h : a = 0
    · subst h
      simp only [h0, one_mul]
      exact mean_add_left Γ μ h𝓕 φ hper y
    · have hp : ∀ γ ∈ Γ, ∀ x, χ a (γ + x) * φ (γ + x) = χ a x * φ x := fun γ hγ x => by
        rw [hper γ hγ, hx, (hker γ).2 hγ a, one_mul]
      have h1 := mean_add_left Γ μ h𝓕 (fun x => χ a x * φ x) hp y
      rw [hco a h] at h1 ⊢
      have h2 : ∫ x in 𝓕, χ a (y + x) * φ (y + x) ∂μ = χ a y * ∫ x in 𝓕, χ a x * φ (y + x) ∂μ := by
        rw [← integral_const_mul]
        exact integral_congr_ae (.of_forall fun x => by simp only [hx, mul_assoc])
      rw [h2] at h1
      have hne : χ a y ≠ 0 := fun e => by simpa [e] using hn a y
      exact (mul_eq_zero.1 h1).resolve_left hne
  have hφy : Continuous fun x => φ (y + x) := hφ.comp (continuous_const.add continuous_id)
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha h0 hn hker μ 𝓕 hμ h𝓕
    (fun x => φ (y + x) - φ x) (hφy.sub hφ)
    (fun γ hγ x => by
      show φ (y + (γ + x)) - φ (γ + x) = φ (y + x) - φ x
      rw [add_left_comm, hper γ hγ, hper γ hγ])
    (fun a => by
      have e : ∀ x, χ a x * (φ (y + x) - φ x) = χ a x * φ (y + x) - χ a x * φ x := fun x => mul_sub _ _ _
      simp only [e]
      rw [integral_sub (hint a _ hφy fun x => hC _) (hint a _ hφ hC), hshift a, sub_self])
  have h := congrFun key 0
  simp only [add_zero, Pi.zero_apply] at h
  exact sub_eq_zero.1 h

end Abstract

set_option synthInstance.maxHeartbeats 400000 in

theorem const_of_coeff : ∀ {D : D7} {p : ℕ} {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)}, IsCovolOneH lp 𝓖p →
    ∀ {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ φ : hermA D p → ℂ, Continuous φ → IsPer φ →
    (∀ a : HermE D p, a.1 ≠ 0 → ∫ y in 𝓖p, φ y * chn ψ a y ∂lp = 0) → ∀ y, φ y = φ 0 := by
  intro D p lp 𝓖p hC ψ hψ φ hφ hper hco y
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D p p
  haveI : BorelSpace (Mx D p p) := ⟨rfl⟩
  haveI : BorelSpace (hermA D p) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D p) := GlobalTheory.CompanionTheory.FourierN.isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D p) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := p)
  refine const_of_coefficients (ratHerm D p) K hK hcov (GlobalTheory.CompanionTheory.FourierN.hermSub D p) (fun a x => ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 x.1))
    (fun a => hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr a.1).neg.comp continuous_subtype_val))
    (fun a x y => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr a.1 (x.1 + y.1)) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul])
    (fun a b x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr (a.1 + b.1) x.1) = _
      rw [GlobalTheory.CompanionTheory.FourierN.pr_add_left, neg_add, AddChar.map_add_eq_mul])
    (fun x => by
      show ψ (-GlobalTheory.CompanionTheory.FourierN.pr 0 x.1) = 1
      rw [GlobalTheory.CompanionTheory.FourierN.pr_zero_left, neg_zero, AddChar.map_zero_eq_one])
    (fun a x => hψ.2.1 _)
    (fun x => ⟨fun h => GlobalTheory.CompanionTheory.FourierN.rat_ker hψ x (fun a ha => h ⟨a, ha⟩), fun hx a => GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ x hx a.1⟩)
    lp 𝓖p hlam hFD (by rw [h1]; exact ENNReal.one_ne_top) φ hφ hper
    (fun a ha => (integral_congr_ae (.of_forall fun x => mul_comm _ _)).trans
      (hco ⟨a.1, a.2⟩ (fun e => ha (Subtype.ext e)))) y

end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFirstBlockGroupEmbedding
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

open GlobalTheory.StdUnn.Model
open GlobalTheory.CompanionTheory.JacobiMaps (b11 b12 b21 b22 block_matrix_of_blocks upperLeft_block upperRight_block lowerLeft_block_entry lowerRight_block continuous_block_matrix continuous_bl
  block_mul₂ bl_add block_sub blockRowSubstitution_one blockMatrix_zero blockMatrix_neg_one adj_bl adjoint_symplectic_block_product mkG isU_mat)

variable {D : D7} {n ρ p : ℕ}

def firstM (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ)) : Mx D (n + n) (n + n) :=
  blk4 (bl hn (b11 M) 0 0 1) (bl hn (b12 M) 0 0 0) (bl hn (b21 M) 0 0 0) (bl hn (b22 M) 0 0 1)

theorem first_block_embedding_block (hn : ρ + p = n) (a b c d : Mx D ρ ρ) :
    firstM hn (blk4 a b c d) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  rw [firstM, upperLeft_block, upperRight_block, lowerLeft_block_entry, lowerRight_block]

def firstMon (hn : ρ + p = n) : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n) where
  toFun := firstM hn
  map_one' := by
    rw [← block_matrix_one (R := AE D) (n := ρ), first_block_embedding_block, blockRowSubstitution_one]
    have e : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
    rw [e, block_matrix_one]
  map_mul' M N := by
    rw [← block_matrix_of_blocks M, ← block_matrix_of_blocks N]
    generalize b11 M = a
    generalize b12 M = b
    generalize b21 M = c
    generalize b22 M = d
    generalize b11 N = a'
    generalize b12 N = b'
    generalize b21 N = c'
    generalize b22 N = d'
    rw [submatrix_fromBlocks_mul, first_block_embedding_block, first_block_embedding_block, first_block_embedding_block, submatrix_fromBlocks_mul]
    simp only [block_mul₂, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem firstM_isU (hn : ρ + p = n) (M : Mx D (ρ + ρ) (ρ + ρ))
    (h : (adj M * blk4 0 1 (-1) 0 * M : Mx D (ρ + ρ) (ρ + ρ)) = blk4 0 1 (-1) 0) :
    (adj (firstM hn M) * blk4 0 1 (-1) 0 * firstM hn M : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := by
  rw [← block_matrix_of_blocks M] at h ⊢
  generalize b11 M = a at h ⊢
  generalize b12 M = b at h ⊢
  generalize b21 M = c at h ⊢
  generalize b22 M = d at h ⊢
  rw [adjoint_symplectic_block_product] at h
  obtain ⟨e1, e2, e3, e4⟩ := blockMatrixTwoByTwoFin_injective h
  have z : bl hn (0 : Mx D ρ ρ) 0 0 (0 : Mx D p p) = 0 := blockMatrix_zero hn
  have o : bl hn (1 : Mx D ρ ρ) 0 0 (1 : Mx D p p) = 1 := blockRowSubstitution_one hn
  have m : bl hn (-1 : Mx D ρ ρ) 0 0 (-1 : Mx D p p) = -1 := blockMatrix_neg_one hn
  rw [first_block_embedding_block, adjoint_symplectic_block_product]
  simp only [adj_bl, adj_one, adj_zero, block_mul₂, block_sub, bl_add, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    Matrix.one_mul, add_zero, zero_add, sub_zero, zero_sub, sub_self, e1, e2, e3, e4, z, o, m]

def firstF (hn : ρ + p = n) (g : G D ρ) : G D n :=
  mkG (Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g)) (firstM_isU hn _ (isU_mat g))

theorem matHom_firstF (hn : ρ + p = n) (g : G D ρ) :
    matHom _ D.sp.cm.sig (Jst D n) (firstF hn g) = Units.map (firstMon hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) := rfl

def firstG (hn : ρ + p = n) : G D ρ →* G D n where
  toFun := firstF hn
  map_one' := matHom_injective _ D.sp.cm.sig (Jst D n) (by rw [matHom_firstF, map_one, map_one, map_one])
  map_mul' g h := matHom_injective _ D.sp.cm.sig (Jst D n) (by
    rw [map_mul, matHom_firstF, matHom_firstF, matHom_firstF, map_mul, map_mul])

theorem mat_firstG (hn : ρ + p = n) (h : G D ρ) : mat (firstG hn h) = firstM hn (mat h) := rfl

theorem continuous_firstM (hn : ρ + p = n) : Continuous (firstM (D := D) hn) :=
  continuous_block_matrix (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const
      continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)
    (continuous_bl hn (continuous_id.matrix_submatrix _ _) continuous_const continuous_const continuous_const)

theorem continuous_firstG (hn : ρ + p = n) : Continuous (firstG (D := D) hn) := by
  have h0 : Continuous (Units.map (firstMon (D := D) hn : Mx D (ρ + ρ) (ρ + ρ) →* Mx D (n + n) (n + n))) :=
    Continuous.units_map _ (continuous_firstM hn)
  have h : Continuous fun g : G D ρ => Units.map (firstMon (D := D) hn) (matHom _ D.sp.cm.sig (Jst D ρ) g) :=
    h0.comp (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D ρ)).continuous
  exact (isEmbedding_matHom (AF D.host.F) D.sp.cm.sig (Jst D n)).continuous_iff.2 h

end GlobalTheory.CompanionTheory.FirstBlockEmb

namespace GlobalTheory.CompanionTheory.FirstBlockEmb

theorem exists_first_emb : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n), ∃ ι : G D ρ →* G D n, Continuous ι ∧
  ∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1) := by
  intro D n ρ p hn
  refine ⟨firstG hn, continuous_firstG hn, fun h a b c d e => ?_⟩
  exact (mat_firstG hn h).trans ((congrArg (firstM hn) e).trans (first_block_embedding_block hn a b c d))

end GlobalTheory.CompanionTheory.FirstBlockEmb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugation
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc GlobalTheory.CompanionTheory.FourierN
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n : ℕ}

theorem adj_mul_sq (x y : Mx D n n) : adj (x * y) = adj y * adj x := adj_mul x y

theorem rat_mul_sq (x y : Matrix (Fin n) (Fin n) D.host.E) : (rat (x * y) : Mx D n n) = rat x * rat y := rat_mul x y

theorem rat_one_sq : (rat (1 : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n) = 1 :=
  Matrix.map_one _ (map_zero (incA D)) (map_one (incA D))

theorem adj_one_sq : adj (1 : Mx D n n) = 1 := by
  rw [← rat_one_sq, ← rat_conjTranspose, Matrix.conjTranspose_one]

theorem rat_gl_mul_inv (a : GL (Fin n) D.host.E) : (rat a.1 * rat (a⁻¹).1 : Mx D n n) = 1 := by
  rw [← rat_mul_sq, show a.1 * (a⁻¹).1 = 1 from by simp, rat_one_sq]

theorem rat_gl_inv_mul (a : GL (Fin n) D.host.E) : (rat (a⁻¹).1 * rat a.1 : Mx D n n) = 1 := by
  rw [← rat_mul_sq, show (a⁻¹).1 * a.1 = 1 from by simp, rat_one_sq]

def congH (u : Matrix (Fin n) (Fin n) D.host.E) (b : hermA D n) : hermA D n :=
  ⟨rat u * b.1 * adj (rat u), by
    show adj (rat u * b.1 * adj (rat u)) = _
    have hb : adj b.1 = b.1 := b.2
    rw [adj_mul_sq, adj_mul_sq, adj_adj, hb, mul_assoc]⟩

theorem congH_val (u : Matrix (Fin n) (Fin n) D.host.E) (b : hermA D n) :
    (congH u b).1 = rat u * b.1 * adj (rat u) := rfl

theorem congH_cancel {u v : Matrix (Fin n) (Fin n) D.host.E} (h : (rat u * rat v : Mx D n n) = 1) (b : hermA D n) :
    congH u (congH v b) = b := by
  apply Subtype.ext
  have h' : (adj (rat v) * adj (rat u) : Mx D n n) = 1 := by rw [← adj_mul_sq, h, adj_one_sq]
  rw [congH_val, congH_val]
  calc rat u * (rat v * b.1 * adj (rat v)) * adj (rat u)
      = (rat u * rat v) * b.1 * (adj (rat v) * adj (rat u)) := by simp only [mul_assoc]
    _ = b.1 := by rw [h, h', one_mul, mul_one]

theorem continuous_congH (u : Matrix (Fin n) (Fin n) D.host.E) : Continuous (congH (D := D) u) :=
  Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _

theorem congH_rat (u : Matrix (Fin n) (Fin n) D.host.E) {b : hermA D n} (hb : b ∈ ratHerm D n) : congH u b ∈ ratHerm D n := by
  obtain ⟨η, hη⟩ := hb
  have hη' : b.1 = rat η := hη.symm
  refine ⟨u * η * uᴴ, ?_⟩
  show rat (u * η * uᴴ) = rat u * b.1 * adj (rat u)
  rw [rat_mul_sq, rat_mul_sq, rat_conjTranspose, hη']

def tauH (a : GL (Fin n) D.host.E) : hermA D n ≃ₜ+ hermA D n where
  toFun := congH (a⁻¹).1
  invFun := congH a.1
  left_inv := congH_cancel (rat_gl_mul_inv a)
  right_inv := congH_cancel (rat_gl_inv_mul a)
  map_add' b c := by
    apply Subtype.ext
    show rat (a⁻¹).1 * (b.1 + c.1) * adj (rat (a⁻¹).1) = rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1) + rat (a⁻¹).1 * c.1 * adj (rat (a⁻¹).1)
    rw [mul_add, add_mul]
  continuous_toFun := continuous_congH _
  continuous_invFun := continuous_congH _

theorem tauH_apply (a : GL (Fin n) D.host.E) (b : hermA D n) : tauH a b = congH (a⁻¹).1 b := rfl

theorem tauH_rat (a : GL (Fin n) D.host.E) (b : hermA D n) : tauH a b ∈ ratHerm D n ↔ b ∈ ratHerm D n := by
  refine ⟨fun h => ?_, fun h => congH_rat _ h⟩
  have := congH_rat a.1 h
  rwa [tauH_apply, congH_cancel (rat_gl_mul_inv a)] at this

theorem exists_levi_rat (a : GL (Fin n) D.host.E) :
    ∃ q : G D n, q ∈ GF D n ∧ mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
  obtain ⟨q, hq⟩ := exists_levi (D := D) (n := n) (Matrix.GeneralLinearGroup.map (incA D) a)
  have hq' : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
    rw [hq, ← map_inv]
    rfl
  refine ⟨q, ?_, hq'⟩
  have e1 : a.1 * (a⁻¹).1 = 1 := by simp
  have e2 : (a⁻¹).1 * a.1 = 1 := by simp
  have e3 : ((a⁻¹).1)ᴴ * a.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have e4 : a.1ᴴ * ((a⁻¹).1)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
  let x : GL (Fin (n + n)) D.host.E := ⟨blk4 a.1 0 0 ((a⁻¹).1)ᴴ, blk4 (a⁻¹).1 0 0 a.1ᴴ,
    by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e1, e3]; exact block_matrix_one,
    by rw [submatrix_fromBlocks_mul]; simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e2, e4]; exact block_matrix_one⟩
  have hm : x.1.map (incA D) = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1)) := by
    simp only [x, blk4_map_alt]
    rw [Matrix.map_zero _ (map_zero _)]
    rfl
  refine ⟨x, ?_, Units.ext (hm.trans hq'.symm)⟩
  apply rat_injective (D := D)
  have h2 : adj (mat q) * JR (AF D.host.F) (Jst D n) * mat q = JR (AF D.host.F) (Jst D n) := q.2
  rw [hq', ← hm] at h2
  erw [rat_mul, rat_mul]
  exact h2

theorem nb_levi {nb : hermA D n → G D n} (hnb : IsNMap nb) (a : GL (Fin n) D.host.E) {q : G D n}
    (hq : mat q = blk4 (rat a.1) 0 0 (adj (rat (a⁻¹).1))) (b : hermA D n) : nb b * q = q * nb (tauH a b) := by
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  show mat (nb b) * mat q = mat q * mat (nb (tauH a b))
  rw [hnb, hnb, hq, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, tauH_apply, congH_val]
  have e : rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) = b.1 * adj (rat (a⁻¹).1) := by
    rw [← mul_assoc, ← mul_assoc, rat_gl_mul_inv, one_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e]

theorem trace_cg (a : GL (Fin n) D.host.E) (β : HermE D n) (b : hermA D n) :
    Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n) =
      Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n) := by
  have h1 : ((cg a β).1.map (incA D) : Mx D n n) = adj (rat a.1) * rat β.1 * rat a.1 := by
    show rat (_ * β.1 * a.1) = _
    rw [rat_mul_sq, rat_mul_sq]
    rfl
  have h2 : (adj (rat (a⁻¹).1) * adj (rat a.1) : Mx D n n) = 1 := by rw [← adj_mul_sq, rat_gl_mul_inv, adj_one_sq]
  show Matrix.trace ((cg a β).1.map (incA D) * (tauH a b).1 : Mx D n n) = Matrix.trace (rat β.1 * b.1 : Mx D n n)
  rw [h1, tauH_apply, congH_val]
  have e : adj (rat a.1) * rat β.1 * rat a.1 * (rat (a⁻¹).1 * b.1 * adj (rat (a⁻¹).1)) =
      adj (rat a.1) * ((rat β.1 * b.1) * adj (rat (a⁻¹).1)) := by
    calc _ = adj (rat a.1) * rat β.1 * (rat a.1 * rat (a⁻¹).1) * b.1 * adj (rat (a⁻¹).1) := by simp only [mul_assoc]
      _ = _ := by rw [rat_gl_mul_inv]; simp only [mul_assoc, mul_one]
  rw [e, Matrix.trace_mul_comm, mul_assoc, h2, mul_one]

set_option synthInstance.maxHeartbeats 400000 in

theorem fc_levi : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ F : G D n → ℂ, Continuous F →
    LeftInv (GF D n) F → ∀ {nb : hermA D n → G D n} {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)}, CoefData nb lam 𝓖 →
    ∀ (a : GL (Fin n) D.host.E) (β : HermE D n), ∃ q : G D n, ∀ g, fc ψ lam 𝓖 nb F β (q * g) = fc ψ lam 𝓖 nb F (cg a β) g := by
  intro D n ψ hψ F _ hinv nb lam 𝓖 hC a β
  obtain ⟨hnb, hlam, hFD, hvol⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D n n
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (hermA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (hermA D n) := isClosed_hermA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : DiscreteTopology (ratHerm D n) := discrete_ratHerm
  haveI : SecondCountableTopology (ratHerm D n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratHerm D n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨q, hqF, hq⟩ := exists_levi_rat (D := D) a
  refine ⟨q, fun g => ?_⟩
  let f : hermA D n → ℂ := fun c =>
    F (nb c * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) c.1 : Mx D n n)))
  have hf : ∀ γ ∈ ratHerm D n, ∀ x, f (γ + x) = f x := by
    intro γ hγ x
    have e1 : F (nb (γ + x) * g) = F (nb x * g) := by
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have e2 : ψ (-pr (cg a β).1 (γ + x).1) = ψ (-pr (cg a β).1 x.1) := by
      rw [show (γ + x).1 = γ.1 + x.1 from rfl, pr_add_right, neg_add, AddChar.map_add_eq_mul, ker_of_rat hψ γ hγ, one_mul]
    show F (nb (γ + x) * g) * ψ (-pr (cg a β).1 (γ + x).1) = F (nb x * g) * ψ (-pr (cg a β).1 x.1)
    rw [e1, e2]
  have key := mean_transport (ratHerm D n) (ratHerm D n) (tauH a) (tauH_rat a) lam lam hFD hFD hvol hvol f hf
  unfold fc
  refine Eq.trans (integral_congr_ae (.of_forall fun b => ?_)) key
  show F (nb b * (q * g)) * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) =
    F (nb (tauH a b) * g) * ψ (-halfTr (Matrix.trace (HMul.hMul ((cg a β).1.map (incA D)) (tauH a b).1 : Mx D n n)))
  rw [trace_cg, ← mul_assoc, nb_levi hnb a hq b, mul_assoc, hinv q hqF]

end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalForm
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

section Field
variable {E : Type} [Field E] {c : E →+* E}

theorem exists_congr_diag_rank (h2 : (2 : E) ≠ 0) (hc : ∀ t, c (c t) = t) {n ρ p : ℕ} (hn : ρ + p = n)
    {G : Matrix (Fin n) (Fin n) E} (hG : ∀ a b, c (G a b) = G b a) (hr : ρ ≤ G.rank) :
    ∃ (a : Matrix (Fin n) (Fin n) E) (d₁ : Fin ρ → E) (d₂ : Fin p → E), a.det ≠ 0 ∧
      (a.map c).transpose * G * a = bl hn (Matrix.diagonal d₁) 0 0 (Matrix.diagonal d₂) ∧
      (∀ i, c (d₁ i) = d₁ i) ∧ (∀ i, c (d₂ i) = d₂ i) ∧ ∀ i, d₁ i ≠ 0 := by
  classical
  obtain ⟨P, d, hP, hPG, hd, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2 hc hG
  have hQ : (P.map c).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero c).mpr hP
  have hrk : (Matrix.diagonal d).rank = G.rank := by
    rw [← hPG, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (isUnit_iff_ne_zero.mpr hQ),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.mpr hP)]
  rw [Matrix.rank_diagonal, Fintype.card_subtype] at hrk
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (hr.trans hrk.ge)
  let e : Fin ρ ⊕ Fin p ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  let A : Finset (Fin n) := Finset.univ.map ⟨fun i : Fin ρ => e (Sum.inl i), fun i j h => Sum.inl_injective (e.injective h)⟩
  have hAc : A.card = ρ := by simp [A]
  let e' : {x // x ∈ A} ≃ {x // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_coe, hAc, hTc])
  let σ : Equiv.Perm (Fin n) := e'.extendSubtype
  have hσ : ∀ i : Fin ρ, d (σ (e (Sum.inl i))) ≠ 0 := by
    intro i
    have hm : σ (e (Sum.inl i)) ∈ T := Equiv.extendSubtype_mem e' _ (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    simpa using hTS hm
  refine ⟨(P.map c).submatrix id σ, fun i => d (σ (e (Sum.inl i))), fun j => d (σ (e (Sum.inr j))), ?_, ?_,
    fun i => hd _, fun j => hd _, hσ⟩
  · rw [Matrix.det_permute']
    refine mul_ne_zero ?_ hQ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · have hmc : (((P.map c).submatrix id σ).map c).transpose * G * (P.map c).submatrix id σ
        = (P.transpose * G * P.map c).submatrix σ σ := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id, hc]
    rw [hmc, hPG, Matrix.submatrix_diagonal_equiv]
    unfold PositivityTheory.Rg.Rsw.bl
    rw [Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext x
    obtain ⟨y, rfl⟩ := e.surjective x
    cases y <;> simp [e]

end Field

theorem exists_cg_dsum {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (β : HermE D n) (hr : ρ ≤ β.1.rank) :
    ∃ (a : GL (Fin n) D.host.E) (b₀ : HermE D ρ) (β' : HermE D p), IsDiagInv b₀ ∧ cg a β = dsum hn b₀ β' := by
  obtain ⟨G, hG⟩ := β
  have hc : ∀ t : D.host.E, D.sp.cm.sig.toRingHom (D.sp.cm.sig.toRingHom t) = t := fun t => star_star t
  obtain ⟨a, d₁, d₂, ha, hEq, hd₁, hd₂, hne⟩ := exists_congr_diag_rank (c := D.sp.cm.sig.toRingHom) two_ne_zero hc hn
    (G := G) (fun i j => congrFun (congrFun hG j) i) hr
  have hdiag : ∀ {m : ℕ} (d : Fin m → D.host.E), (∀ i, D.sp.cm.sig.toRingHom (d i) = d i) →
      ((Matrix.diagonal d).map ⇑D.sp.cm.sig).transpose = Matrix.diagonal d := by
    intro m d hd
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    congr 1
    funext i
    exact hd i
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a ha, ⟨Matrix.diagonal d₁, hdiag d₁ hd₁⟩,
    ⟨Matrix.diagonal d₂, hdiag d₂ hd₂⟩, ⟨Matrix.isDiag_diagonal _, ?_⟩, ?_⟩
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  · exact Subtype.ext hEq

end GlobalTheory.CompanionTheory.PcFc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKFiniteStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_k_finite : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : GlobalTheory.CompanionTheory.ModelS.SmF n, F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev → ∃ S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n), FiniteDimensional ℂ S ∧ F ∈ S ∧ ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite | exact GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite | (intros; apply GlobalTheory.CompanionTheory.ModelS.FFin.fRaw_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeightStatement
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_k_highest_weight : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : GlobalTheory.CompanionTheory.ModelS.SmF n, F.1 = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev → (∀ a b : Fin n, a < b → GlobalTheory.CompanionTheory.ModelS.Kf a b F = 0) ∧ ∀ a : Fin n, GlobalTheory.CompanionTheory.ModelS.Kf a a F = (GlobalTheory.CompanionTheory.ModelS.muZ lam lev a : ℂ) • F := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.f_highest | exact GlobalTheory.CompanionTheory.ModelS.f_highest | (intros; apply GlobalTheory.CompanionTheory.ModelS.f_highest <;> assumption)
end

