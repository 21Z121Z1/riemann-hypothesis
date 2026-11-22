import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0767
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitKAOfGenLt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0761
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0772
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0768
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

def pull (a : GL (Fin n) (AE D)) (b : hermA D n) : hermA D n :=
  ⟨(a⁻¹).1 * b.1 * adj (a⁻¹).1, by
    have hb : adj b.1 = b.1 := b.2
    change adj _ = _
    rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]⟩

theorem adj_one' : adj (1 : Mx D n n) = 1 := by
  show ((1 : Mx D n n).map (cA D))ᵀ = 1
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

def astar (a : GL (Fin n) (AE D)) : GL (Fin n) (AE D) :=
  ⟨adj (a⁻¹).1, adj a.1,
    by
      rw [← adj_mul]
      have : a.1 * (a⁻¹).1 = 1 := by simp
      rw [this, adj_one'],
    by
      rw [← adj_mul]
      have : (a⁻¹).1 * a.1 = 1 := by simp
      rw [this, adj_one']⟩

def gAt (θ : InfFam D) (a : GL (Fin n) (AE D)) (τ : D.what₂.Tau) : GL (Fin n) ℂ :=
  Matrix.GeneralLinearGroup.map ((θ τ).comp (infPart D)) a

def latAt (h : Matrix (Fin n) (Fin n) (AE D))
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) :
    AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) :=
  (latLoc D.host.F (stdLattice D.host.E n) v).toAddSubgroup.map
    (Matrix.mulVecLin (PositivityTheory.SiegelWeilFormula.Gen.matV v h)).toAddMonoidHom

end GlobalTheory.CompanionTheory.MM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AeZeroCountEqIntersectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_zero_count_eq_intersection : ∀ (Y : Var ℂ) (Δ : Y.Dv) (L : LB Y.X) (r : L.ι → Y.Fnˣ) (hL : L.IsLB) (n : ℕ) (b : Fin n → L.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤), Presents Δ L r → ∀ᵐ C ∂(volume : Measure (Fin Y.dim → Fin n → ℂ)), ((({y : CxPts Y.str (RingHom.id ℂ) | ∀ (k : Fin Y.dim) (i : L.ι), y ∈ ptsIn Y.str (RingHom.id ℂ) (L.U i) → ∑ j, C k j * secVal Y.str (RingHom.id ℂ) (b j) i y = 0}).ncard : ℕ) : ℤ) = Y.inter fun _ => Δ := by
  first | exact @GlobalTheory.CompanionTheory.KoszulCount.koszul_count | exact GlobalTheory.CompanionTheory.KoszulCount.koszul_count | (intros; apply GlobalTheory.CompanionTheory.KoszulCount.koszul_count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropyOfRange
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.AnisoRange

theorem bddAbove_isotropic_dims {D : D7} (V : HSp D) :
    BddAbove {k | ∃ W : Submodule D.host.E V.V, Module.finrank D.host.E W = k ∧ ∀ x ∈ W, ∀ y ∈ W, V.hT x y = 0} := by
  haveI := V.fd
  refine ⟨Module.finrank D.host.E V.V, ?_⟩
  rintro k ⟨W, rfl, -⟩
  exact Submodule.finrank_le W

theorem one_le_wittIdx {D : D7} (V : HSp D) {v : V.V} (hv : v ≠ 0) (h : V.hT v v = 0) :
    1 ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := by
  refine le_csSup (bddAbove_isotropic_dims V) ⟨Submodule.span D.host.E {v}, finrank_span_singleton hv, ?_⟩
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  simp [h]

theorem hT_coord {D : D7} (V : HSp D) (x : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm x) (V.frame.equivFun.symm x) =
      HeckeCharacterZeroLocus.SiegelWeilU.hE D.sp.cm.sig (HSpace.gram V) x x := by
  have hσ : ∀ a : D.host.E, ((D.sp.cm.sig : D.host.E →ₐ[D.host.F] D.host.E) : D.host.E →+* D.host.E) a = star a :=
    fun _ => rfl
  simp only [Module.Basis.equivFun_symm_apply, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, map_sum, LinearMap.sum_apply,
    map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hσ, HSpace.gram]
  simp only [starRingEnd_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem anisoOfRange : PositivityTheory.PfSWUS.AnisoOfRange := by
  rintro D n V ⟨h1, -, h3⟩
  by_cases h : n + 2 ≤ V.rank
  · exact Or.inl h
  refine Or.inr fun x hx => ?_
  by_contra hne
  have hv : V.frame.equivFun.symm x ≠ 0 := fun h0 => hne ((map_eq_zero_iff _ V.frame.equivFun.symm.injective).1 h0)
  have := one_le_wittIdx V hv ((hT_coord V x).trans hx)
  omega

end GlobalTheory.CompanionTheory.AnisoRange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveLocalUnitaryToGLStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_local_unitary_to_GL : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), Function.Bijective (thU D n v τ) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.thU_bijective | exact GlobalTheory.CompanionTheory.Jp.thU_bijective | (intros; apply GlobalTheory.CompanionTheory.Jp.thU_bijective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixInjective
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.EisCovar PositivityTheory.GramSchwartzFunctions.EC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTw

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

section Blocks

variable {R : Type} [CommRing R]

theorem block_mul₂ (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  simp only [bl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one (hn : ρ + p = n) : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (1 : Matrix (Fin p) (Fin p) R) = 1 := by
  simp only [bl, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrix_zero (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 (0 : Matrix (Fin p) (Fin p) R) = 0 := by
  simp only [bl, Matrix.fromBlocks_zero]
  rfl

theorem bl_add (hn : ρ + p = n) (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  simp only [bl]
  rw [← Matrix.fromBlocks_add]
  rfl

theorem blockMatrix_inj (hn : ρ + p = n) {a a' : Matrix (Fin ρ) (Fin ρ) R} {b b' : Matrix (Fin ρ) (Fin p) R}
    {c c' : Matrix (Fin p) (Fin ρ) R} {d d' : Matrix (Fin p) (Fin p) R}
    (h : bl hn a b c d = bl hn a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix (finSumFinEquiv.trans (finCongr hn)) (finSumFinEquiv.trans (finCongr hn))) h
  simp only [bl, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

theorem block_matrix_injective {a a' b b' c c' d d' : Matrix (Fin n) (Fin n) R}
    (h : blk4 a b c d = blk4 a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have h2 := congrArg (fun M => M.submatrix finSumFinEquiv finSumFinEquiv) h
  simp only [blk4, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] at h2
  exact Matrix.fromBlocks_inj.1 h2

end Blocks

theorem mat_nzx_sh (M : Maps D hn) (z : hermA D ρ) (x y : Mx D ρ p) :
    mat (M.nzx z x * M.sh y) = blk4 (bl hn 1 y 0 1) (bl hn (z.1 - x ⬝ adj y) x (adj x) 0) 0 (bl hn 1 0 (-adj y) 1) := by
  rw [mat_mul', M.nzx_mat, M.sh_mat, submatrix_fromBlocks_mul]
  congr 1
  · simp
  · rw [Matrix.mul_zero, zero_add, block_mul₂]
    simp [sub_eq_add_neg]
  · simp
  · simp

theorem nzx_sh_inj (M : Maps D hn) {z z' : hermA D ρ} {x x' y y' : Mx D ρ p}
    (h : M.nzx z x * M.sh y = M.nzx z' x' * M.sh y') : z = z' ∧ x = x' ∧ y = y' := by
  have h2 := congrArg mat h
  rw [mat_nzx_sh, mat_nzx_sh] at h2
  obtain ⟨h3, h4, -, -⟩ := block_matrix_injective h2
  obtain ⟨-, rfl, -, -⟩ := blockMatrix_inj hn h3
  obtain ⟨h5, rfl, -, -⟩ := blockMatrix_inj hn h4
  exact ⟨Subtype.ext (sub_left_injective h5), rfl, rfl⟩

set_option maxHeartbeats 1000000 in
theorem gl_levi (M : Maps D hn) (g : G D p) (a : GL (Fin p) (AE D)) (hg : mat g = blk4 a.1 0 0 (adj (a⁻¹).1))
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx z (x ⬝ adj a.1) * M.sh (y ⬝ (a⁻¹).1) * M.emb g := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D p p) from h1, adj_one] at this
    exact this.symm
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, blockMatrix_zero, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have h3 : ∀ w : Mx D p ρ, adj a.1 ⬝ (adj (a⁻¹).1 ⬝ w) = w := fun w => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h4 : ∀ w : Mx D ρ p, w ⬝ adj a.1 ⬝ adj (a⁻¹).1 = w := fun w => by
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have h5 : ∀ w : Mx D ρ p, w ⬝ (a⁻¹).1 ⬝ a.1 = w := fun w => by
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, adj_mul, adj_adj, Matrix.one_mul,
    Matrix.mul_one, h4, h5, Matrix.mul_assoc x, h3, Matrix.mul_neg, Matrix.neg_mul, neg_zero]

theorem adj_sub' {k l : ℕ} (u v : Mx D k l) : adj (u - v) = adj u - adj v := by
  rw [sub_eq_add_neg, adj_add, adj_neg, sub_eq_add_neg]

def zU (z : hermA D ρ) (y : Mx D ρ p) (b : Mx D p p) (hb : adj b = b) : hermA D ρ :=
  ⟨z.1 - y ⬝ (b ⬝ adj y), by
    show adj _ = _
    rw [adj_sub', adj_mul, adj_mul, adj_adj, hb, z.2, Matrix.mul_assoc]⟩

set_option maxHeartbeats 1000000 in
theorem gl_unip (M : Maps D hn) (g : G D p) (b : Mx D p p) (hb : adj b = b) (hg : mat g = blk4 1 b 0 1)
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx (zU z y b hb) (x - y ⬝ b) * M.sh y * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, blockMatrix_zero, blockRowSubstitution_one, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, block_mul₂, bl_add, adj_sub', adj_mul, hb]
  have e1 : (zU z y b hb).1 - (x - y ⬝ b) ⬝ adj y = z.1 - x ⬝ adj y := by
    simp only [zU, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have e2 : y ⬝ b + (x - y ⬝ b) = x := by abel
  have e3 : adj x + b ⬝ -adj y = adj x - b ⬝ adj y := by rw [Matrix.mul_neg, sub_eq_add_neg]
  rw [e1, e2, e3]

def zW (z : hermA D ρ) (x y : Mx D ρ p) : hermA D ρ :=
  ⟨z.1 - x ⬝ adj y - y ⬝ adj x, by
    show adj _ = _
    rw [adj_sub', adj_sub', adj_mul, adj_mul, adj_adj, adj_adj, z.2]
    abel⟩

set_option maxHeartbeats 1000000 in
theorem gl_weyl (M : Maps D hn) (g : G D p) (hg : mat g = blk4 0 1 (-1) 0)
    (z : hermA D ρ) (x y : Mx D ρ p) :
    M.emb g * (M.nzx z x * M.sh y) = M.nzx (zW z x y) (-y) * M.sh x * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective'
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  have e1 : (zW z x y).1 - -y ⬝ adj x = z.1 - x ⬝ adj y := by
    simp only [zW, Matrix.neg_mul]
    abel
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, bl_add, adj_neg, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, neg_neg, neg_zero]
  rw [show (zW z x y).1 - -(y ⬝ adj x) = z.1 - x ⬝ adj y by rw [← Matrix.neg_mul]; exact e1]

end GlobalTheory.CompanionTheory.ThTw
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterCommutator
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem adj_herm {D : D7} {ρ : ℕ} (b₀ : HermE D ρ) :
    adj (b₀.1.map (incA D) : Mx D ρ ρ) = b₀.1.map (incA D) := by
  have h := rat_conjTranspose b₀.1
  have e : b₀.1ᴴ = b₀.1 := b₀.2
  rw [e] at h
  exact h.symm

theorem chz_jc {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (y x : Mx D ρ p) :
    chz ψ b₀ (GlobalTheory.CompanionTheory.FJE.jc y x) = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y := by
  set B : Mx D ρ ρ := b₀.1.map (incA D) with hB
  have hadj : adj B = B := adj_herm b₀
  have e1 : Matrix.trace (B * (y * adj x)) = Matrix.trace (pr b₀ x y) := by
    show _ = Matrix.trace (adj x * (B * y))
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e2 : Matrix.trace (B * (x * adj y)) = cA D (Matrix.trace (pr b₀ x y)) := by
    rw [← GlobalTheory.CompanionTheory.FourierN.trace_adj]
    have h : adj (pr b₀ x y) = HMul.hMul (HMul.hMul (adj y) B : Mx D p ρ) x := by
      show adj (HMul.hMul (adj x) (HMul.hMul B y : Mx D ρ p) : Mx D p p) = _
      rw [adj_mul, adj_mul, adj_adj, hadj]
    rw [h, Matrix.trace_mul_comm, Matrix.mul_assoc x, Matrix.trace_mul_comm]
  have e3 : Matrix.trace (HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 : Mx D ρ ρ) =
      Matrix.trace (pr b₀ x y) + cA D (Matrix.trace (pr b₀ x y)) := by
    show Matrix.trace (B * (y * adj x + x * adj y)) = _
    rw [Matrix.mul_add, Matrix.trace_add, e1, e2]
  rw [chz, show HMul.hMul (b₀.1.map (incA D)) (GlobalTheory.CompanionTheory.FJE.jc y x).1 = HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 from rfl, e3,
    GlobalTheory.CompanionTheory.FourierN.halfTr_add_cA]
  rfl

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterProperties
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.CentralChar

theorem chz_facts : ∀ {D : D7} {ρ : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
    (∀ z z' : hermA D ρ, chz ψ b₀ (z + z') = chz ψ b₀ z * chz ψ b₀ z') ∧ (∀ z, ‖chz ψ b₀ z‖ = 1) ∧
      (∀ z ∈ ratHerm D ρ, chz ψ b₀ z = 1) ∧ Continuous (chz ψ b₀) := by
  intro D ρ ψ hψ b₀
  refine ⟨fun z z' => ?_, GlobalTheory.CompanionTheory.PcB.chz_norm hψ b₀, fun z hz => ?_, GlobalTheory.CompanionTheory.PcB.continuous_chz hψ b₀⟩
  · have e : (HMul.hMul (b₀.1.map (incA D)) (z + z').1 : Mx D ρ ρ) =
        (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ) + (HMul.hMul (b₀.1.map (incA D)) z'.1 : Mx D ρ ρ) :=
      Matrix.mul_add _ _ _
    have hadd : ∀ a c : AE D, halfTr (a + c) = halfTr a + halfTr c := fun a c => by
      simp only [halfTr, trA, map_add, mul_add]
    unfold chz
    rw [e, Matrix.trace_add, hadd, AddChar.map_add_eq_mul]
  · obtain ⟨Z, hZ⟩ := hz
    have hZ' : Z.map (incA D) = z.1 := hZ
    have e : Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ) = incA D (Matrix.trace (b₀.1 * Z)) := by
      rw [← hZ', ← Matrix.map_mul]
      simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
    unfold chz
    rw [e, GlobalTheory.CompanionTheory.ThetaInv.halfTr_incA]
    exact hψ.2.2.1 _

end GlobalTheory.CompanionTheory.FJE.CentralChar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantReductionRealStatement
section
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_reduction_real : PositivityTheory.RgBcC.RealD.LeviCommutantWordReduction := by
  first | exact @GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words | exact GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words | (intros; apply GlobalTheory.CompanionTheory.BlockCapelliWords.commutant_block_capelli_words <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableMatricesAndCosets
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem countable_mat_cosets : ∀ (D : D7) (a b : ℕ), Countable (Matrix (Fin a) (Fin b) D.host.E) ∧ Countable (GlobalTheory.Eis.Cosets (P D b) (GF D b)) := by
  intro D a b
  have hE : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  refine ⟨inferInstanceAs (Countable (Fin a → Fin b → D.host.E)), ?_⟩
  have hM : Countable (Matrix (Fin (b + b)) (Fin (b + b)) D.host.E) :=
    inferInstanceAs (Countable (Fin (b + b) → Fin (b + b) → D.host.E))
  have hGL : Countable (GL (Fin (b + b)) D.host.E) :=
    (Units.val_injective (α := Matrix (Fin (b + b)) (Fin (b + b)) D.host.E)).countable
  have hG : Countable (GF D b) := by
    have hR : Countable (GRat D.sp.cm.sig (Jst D b)) := by
      unfold GRat
      exact Subtype.val_injective.countable
    show Countable (ratPts D.sp.cm.sig (Jst D b))
    rw [← range_ratEmb]
    exact (Set.countable_range (ratEmb D.sp.cm.sig (Jst D b))).to_subtype
  exact Quotient.countable

end GlobalTheory.CompanionTheory.FJE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DictionaryMaximalCompactPartsStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_maximal_compact_parts : PositivityTheory.PfSWUS.DictKAOfParts := by
  first | exact @GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts | exact GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts | (intros; apply GlobalTheory.CompanionTheory.SWDict.dictKA_of_parts <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightTraceFormulaStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_weight_trace_formula : ∀ {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V), (∀ k, T * E.ρ k = E.ρ k * T) → ∀ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G → ∃ F : Finset (Fin n → ℤ), (∀ ν ∈ F, Antitone ν) ∧ (∀ ν : Fin n → ℤ, Antitone ν → ν ∉ F → hwOf G (wtR ν) = ⊥) ∧ ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = ∑ ν ∈ F, trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) * weylChar ν z := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.CharDec.main | exact GlobalTheory.CompanionTheory.RealCountG.CharDec.main | (intros; apply GlobalTheory.CompanionTheory.RealCountG.CharDec.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVanishingStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_vanishing : PositivityTheory.GramSchwartzFunctions.EC.Zero := by
  first | exact @GlobalTheory.CompanionTheory.EisZero.zero | exact GlobalTheory.CompanionTheory.EisZero.zero | (intros; apply GlobalTheory.CompanionTheory.EisZero.zero <;> assumption)
end

