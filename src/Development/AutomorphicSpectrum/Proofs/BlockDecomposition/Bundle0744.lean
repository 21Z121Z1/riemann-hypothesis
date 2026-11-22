import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0742
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0401
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0740
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0739
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0736
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMirabolicInvariantPairingScalar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixApplyInrInr
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EmbK

open GlobalTheory.CompanionTheory.JacobiMaps

section Entries

variable {R : Type} [CommRing R] {n r t : ℕ}

theorem block_matrix_apply_inl_inl (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem block_matrix_apply_inl_inr (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = b i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem block_matrix_apply_inr_inl (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]

theorem block_matrix_apply_inr_inr (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = d i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem entry (hn : r + t = n) (a b c d : Matrix (Fin t) (Fin t) R) (i j : Fin (n + n)) :
    blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) i j = (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) i j ∨
    ∃ i' j', blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) i j = blk4 a b c d i' j' ∧
      (1 : Matrix (Fin (t + t)) (Fin (t + t)) R) i' j' = (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) i j := by
  have h1 : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) =
      blk4 (bl hn 1 0 0 1) (bl hn 0 0 0 0) (bl hn 0 0 0 0) (bl hn 1 0 0 1) := by
    have z : bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 (0 : Matrix (Fin t) (Fin t) R) = 0 := blockMatrix_zero hn
    rw [blockRowSubstitution_one, z, GlobalTheory.StdUnn.Model.block_matrix_one]
  have h2 : (1 : Matrix (Fin (t + t)) (Fin (t + t)) R) = blk4 1 0 0 1 := GlobalTheory.StdUnn.Model.block_matrix_one.symm
  rw [h1, h2]
  have bll : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = a i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]
  have blr : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = b i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]
  have brl : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = c i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]
  have brr : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = d i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i <;>
    obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    simp only [block_matrix_apply_inl_inl, block_matrix_apply_inl_inr, block_matrix_apply_inr_inl, block_matrix_apply_inr_inr, bll, blr, brl, brr, true_or] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, (block_matrix_apply_inl_inl a b c d i j).symm, block_matrix_apply_inl_inl _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inl_inr a b c d i j).symm, block_matrix_apply_inl_inr _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inr_inl a b c d i j).symm, block_matrix_apply_inr_inl _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inr_inr a b c d i j).symm, block_matrix_apply_inr_inr _ _ _ _ i j⟩

theorem map_one_apply {T : Type} [CommRing T] {N : ℕ} (f : R →+* T) (i j : Fin N) :
    f ((1 : Matrix (Fin N) (Fin N) R) i j) = (1 : Matrix (Fin N) (Fin N) T) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

end Entries

variable {D : D7} {n r t : ℕ} {hn : r + t = n}

theorem emb_entries_one (M : Maps D hn) {T : Type} [CommRing T] (f : AE D →+* T) {u : G D t}
    (hu : ∀ i j, f (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) T) i j) (i j : Fin (n + n)) :
    f (mat (M.emb u) i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) T) i j := by
  rw [M.emb_mat u _ _ _ _ (block_matrix_of_blocks (mat u)).symm]
  rcases entry hn (b11 (mat u)) (b12 (mat u)) (b21 (mat u)) (b22 (mat u)) i j with h | ⟨i', j', h, h'⟩
  · rw [h, map_one_apply]
  · rw [h, block_matrix_of_blocks, hu i' j', ← map_one_apply f i' j', h', map_one_apply]

theorem emb_entries_mem (M : Maps D hn) {T : Type} [CommRing T] (f : AE D →+* T) (P : Subring T) {u : G D t}
    (hu : ∀ i j, f (mat u i j) ∈ P) (i j : Fin (n + n)) : f (mat (M.emb u) i j) ∈ P := by
  rw [M.emb_mat u _ _ _ _ (block_matrix_of_blocks (mat u)).symm]
  rcases entry hn (b11 (mat u)) (b12 (mat u)) (b21 (mat u)) (b22 (mat u)) i j with h | ⟨i', j', h, -⟩
  · rw [h, map_one_apply]
    by_cases e : i = j
    · subst e; simpa using P.one_mem
    · simpa [Matrix.one_apply_ne e] using P.zero_mem
  · rw [h, block_matrix_of_blocks]
    exact hu i' j'

theorem stab_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)}
    (h : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v)) (i j : Fin N) :
    m.1 i j ∈ intLoc F E v ∧ (m⁻¹).1 i j ∈ intLoc F E v := by
  have hs : (Pi.single j 1 : Fin N → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E N) v := by
    refine mem_latLoc_stdLattice.2 fun k => ?_
    by_cases e : k = j
    · subst e; simpa using (intLoc F E v).one_mem
    · simpa [Pi.single_eq_of_ne e] using (intLoc F E v).zero_mem
  constructor
  · have h1 := mem_latLoc_stdLattice.1 ((h _).1 hs) i
    simpa using h1
  · have e : m.1 *ᵥ ((m⁻¹).1 *ᵥ (Pi.single j 1 : Fin N → Fv F v ⊗[F] E)) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h2 : (m⁻¹).1 *ᵥ (Pi.single j 1 : Fin N → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E N) v :=
      (h _).2 (by rw [e]; exact hs)
    have h1 := mem_latLoc_stdLattice.1 h2 i
    simpa using h1

theorem emb_mem_KOff : ∀ {D : D7} {n r t : ℕ} {hn : r + t = n} (M : Maps D hn) (S : Finset (Pl D)) (u : G D t),
    u ∈ KOff D t S → M.emb u ∈ KOff D n S := by
  intro D n r t hn M S u hu
  obtain ⟨hf, h1, h2⟩ := mem_levelOff.1 hu
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · have hw := mem_finPts_iff_forall.1 hf w
    have ent : ∀ i j, compInf D.host.F D.host.E w (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) _) i j := fun i j => by
      have e := congrArg (fun g => (matHom _ D.sp.cm.sig (Jst D t) g).1 i j) hw
      simp only [map_one, Units.val_one] at e
      exact e
    apply matHom_injective
    apply Units.ext
    ext i j
    rw [matHom_projArch, map_one]
    exact emb_entries_one M _ ent i j
  · have ent : ∀ i j, cv D v (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) _) i j := fun i j => by
      have e := congrArg (fun g => (matHom _ D.sp.cm.sig (Jst D t) g).1 i j) (h1 v hv)
      simp only [map_one, Units.val_one] at e
      exact e
    apply matHom_injective
    apply Units.ext
    ext i j
    rw [matHom_proj, map_one]
    exact emb_entries_one M _ ent i j
  · have key : ∀ x : G D t, proj D.sp.cm.sig (Jst D t) v x ∈ stabLoc D.sp.cm.sig (Jst D t) (stdLattice D.host.E (t + t)) v →
        ∀ i j, (matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v (M.emb x))).1 i j ∈ intLoc D.host.F D.host.E v := by
      intro x hx i j
      exact emb_entries_mem M (cv D v) _ (fun i j => (stab_entries hx i j).1) i j
    refine GlobalTheory.StdUnn.StabFin.mem_stab_std (key u (h2 v hv)) fun i j => ?_
    rw [← map_inv, ← map_inv, ← map_inv]
    exact key u⁻¹ (by rw [map_inv]; exact inv_mem (h2 v hv)) i j

end GlobalTheory.CompanionTheory.EmbK
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterActsByScalarOnCyclic
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem eq_smul_of_commute_of_ev : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  intro n V _ _ F1 F2 hfin z hz ev c hev hS x
  set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
  set y : V := z x - c • x with hy
  obtain ⟨S₁, hfd, hyS₁, hst⟩ := hfin y
  have hpres : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      exact hst a b
    | algebraMap r =>
      intro w hw
      simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
    | add S T _ _ hS' hT' =>
      intro w hw
      exact S₁.add_mem (hS' w hw) (hT' w hw)
    | mul S T _ _ hS' hT' =>
      intro w hw
      exact hS' _ (hT' w hw)
  have hcomm : ∀ T ∈ A, z * T = T * z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      have h1 := (hz a b).1
      have h2 := (hz a b).2
      show z * (F1 a b + F2 a b) = (F1 a b + F2 a b) * z
      rw [mul_add, add_mul, h1, h2]
    | algebraMap r => exact (Algebra.commutes r z).symm
    | add S T _ _ hS' hT' => rw [mul_add, add_mul, hS', hT']
    | mul S T _ _ hS' hT' => rw [← mul_assoc, hS', mul_assoc, hT', mul_assoc]
  let S : Submodule ℂ V := (Subalgebra.toSubmodule A).map (LinearMap.applyₗ y)
  have hmem : ∀ w, w ∈ S ↔ ∃ T ∈ A, T y = w := by
    intro w
    simp [S, Submodule.mem_map]
  have hle : S ≤ S₁ := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    exact hpres T hT y hyS₁
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
  have hSst : ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
  have hSev : ∀ w ∈ S, ev w = 0 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    have hzT : T (z x) = z (T x) := (LinearMap.congr_fun (hcomm T hT) x).symm
    rw [hy, map_sub, map_smul, hzT, map_sub, map_smul, hev, smul_eq_mul, sub_self]
  have hyS : y ∈ S := (hmem y).2 ⟨1, A.one_mem, rfl⟩
  exact sub_eq_zero.1 (hS S hSfd hSst hSev y hyS)

end GlobalTheory.CompanionTheory.ModelS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExists
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SWCoef

theorem coefDataExists : PositivityTheory.PfSWUS.CoefDataExists := by
  intro D n
  have h : ∀ b : PositivityTheory.GramSchwartzFunctions.BC.hermA D n, ∃ g : GlobalTheory.StdUnn.G D n, GlobalTheory.StdUnn.mat g = GlobalTheory.StdUnn.blk4 1 b.1 0 1 :=
    fun b => (GlobalTheory.StdUnn.Model.exists_unip _).2 b.2
  choose nb hnb using h
  obtain ⟨lam, 𝓖, hl⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D n
  exact ⟨nb, lam, 𝓖, hnb, hl⟩

end GlobalTheory.CompanionTheory.SWCoef

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermCofiniteIdealTransfer
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.CTFin.Slice1

theorem slice_mem_genSpace : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (L : Subgroup (GL (Fin (r + s)) (Af E))), IsOpen (L : Set (GL (Fin (r + s)) (Af E))) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∀ J : Set (Module.End ℂ (Sm E (r + s))), Cofin J → ∀ J₁ : Set (Module.End ℂ (Sm E r)), Cofin J₁ → (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) → ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) → ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)), ∃ (L₁ : Subgroup (GL (Fin r) (Af E))) (ρ₁ : Representation ℂ (Kinf E r) W), IsOpen (L₁ : Set (GL (Fin r) (Af E))) ∧ GlobalTheory.Published.AutFin.IsContRep ρ₁ ∧ ∀ F ∈ goodCT L ρ J, ∀ m₂ : GA E s, ∃ G ∈ genSpace L₁ ρ₁ J₁, ∀ m₁ : GA E r, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
  intro E _ _ _ r s L hL W _ _ _ ρ hρ J hJ J₁ hJ₁ H3 t κ
  refine ⟨levelOne s L t, ρ.comp (levK E r s), isOpen_levelOne hL t,
    fun ℓ w => (hρ ℓ w).comp continuous_levK, ?_⟩
  intro F hF m₂
  obtain ⟨hN, hM, hLv, hC, hG, hZ⟩ := hF
  let h : GA E (r + s) := lev (Ad E) r s (1, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)
  let F' := rt E (r + s) h F
  let G : Sm E r := ⟨_, GlobalTheory.T.levi_restriction_smooth E r s F'.1 F'.2⟩
  have hGv : ∀ m₁, G.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) := by
    intro m₁
    change F.1 (lev (Ad E) r s (m₁, 1) * h) = _
    have e : (m₁, m₂) = ((m₁, 1) * (1, m₂) : GA E r × GA E s) := by simp
    rw [e, map_mul]
    simp only [h, mul_assoc]

  have hcoef : ∀ g : GA E r, (fun k : Kinf E r => (cptRep E r k G).1 g) ∈
      GlobalTheory.Published.AutFin.coeffSpan (ρ.comp (levK E r s)) := by
    intro g
    have key := coeff_comp ρ (levK E r s) κ (hC (lev (Ad E) r s (g, m₂) * finGL E (r + s) t))
    convert key using 1
    funext k
    change G.1 (g * infGL E r (Unitary.toUnits k)) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
      infGL E (r + s) (Unitary.toUnits (levK E r s k * κ)))
    rw [hGv, lev_infGL_right, ← toUnits_levK (s := s),
      ← map_mul (Unitary.toUnits : _ →* (Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E))ˣ)]

  have hle : (levelOne s L t : Set (GL (Fin r) (Af E))) ⊆ {k | finRep E r k G = G} := by
    intro k hk
    refine Subtype.ext (funext fun m => ?_)
    change G.1 (m * finGL E r k) = G.1 m
    rw [hGv, hGv]
    have hk' : F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ) *
        finGL E (r + s) (t⁻¹ * lev (Af E) r s (k, 1) * t)) =
        F.1 (lev (Ad E) r s (m, m₂) * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) :=
      congrFun (congrArg Subtype.val (hLv _ (mem_levelOne.1 hk))) _
    rw [← hk', lev_finGL_right]

  have hkill : ∀ z ∈ J₁, z G = 0 := by
    refine H3 F' (fun x g => ?_) (fun z hz => ?_) G (fun m => rfl)
    · change F.1 (unip x * g * h) = F.1 (g * h)
      rw [mul_assoc, hN]
    · change z (rt E (r + s) h F) = 0
      rw [← Module.End.mul_apply, (commute_rt_of_mem_Zalg (hJ.1 hz) h).eq, Module.End.mul_apply, hZ z hz, map_zero]
  refine ⟨G, ⟨⟨fun γ g => ?_, isOpen_stab_of_mem_nhds (finRep E r) G
      (Filter.mem_of_superset ((isOpen_levelOne hL t).mem_nhds (one_mem _)) hle),
    kfin_of_coeff _ G hcoef, zfin_of_cofin hJ₁ hkill, fun g => ?_⟩, fun k hk => hle hk, hcoef, hkill⟩, hGv⟩
  ·
    rw [hGv, hGv]
    have e : lev (Ad E) r s (ratGL E r γ * g, m₂) = lev (Ad E) r s (ratGL E r γ, ratGL E s 1) * lev (Ad E) r s (g, m₂) := by
      rw [← map_mul, Prod.mk_mul_mk, map_one, one_mul]
    simp only [e, mul_assoc]
    exact hM (γ, 1) _
  ·
    obtain ⟨C, N, hb⟩ := hG (lev (Ad E) r s (g, m₂) * finGL E (r + s) t)
    obtain ⟨B, hB0, hB⟩ := GlobalTheory.T.levi_embedding_height_bound E r s (Unitary.toUnits κ)
    refine ⟨|C| * B ^ N, N, fun y => ?_⟩
    have e1 : G.1 (g * infGL E r y) = F.1 (lev (Ad E) r s (g, m₂) * finGL E (r + s) t *
        infGL E (r + s) (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)) := by
      rw [hGv, lev_infGL_right]
    rw [e1]
    have h1 := hb (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ)
    have h2 := hB y
    have h0 : 0 ≤ height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) := zero_le_one.trans (one_le_height _)
    calc _ ≤ C * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N := h1
      _ ≤ |C| * height (lev (Cinf E) r s (y, 1) * Unitary.toUnits κ) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h0 N)
      _ ≤ |C| * (B * height y) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h2 N) (abs_nonneg C)
      _ = |C| * B ^ N * height y ^ N := by rw [mul_pow, mul_assoc]

end GlobalTheory.CompanionTheory.CTFin.Slice1
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerateStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_form_symmetric_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n : ℕ), (coordForm σ b n).IsSymm ∧ (coordForm σ b n).det ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.coordForm_isSymm_det_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn

namespace GlobalTheory.CompanionTheory.SwUnf

def lowerC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

variable {D : D7} {n : ℕ}

def cellKer (x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) : Submodule D.host.E (Fin n → D.host.E) :=
  LinearMap.ker (lowerC x).mulVecLin

def ratOf (γ : GF D n) : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E :=
  Classical.choose (GlobalTheory.StdUnn.LeftInvSect.rat_mat γ.2)

theorem mat_ratOf (γ : GF D n) : mat (γ : G D n) = (ratOf γ).map (incA D) :=
  Classical.choose_spec (GlobalTheory.StdUnn.LeftInvSect.rat_mat γ.2)

def cosetCell (q : GlobalTheory.Eis.Cosets (P D n) (GF D n)) : Submodule D.host.E (Fin n → D.host.E) :=
  cellKer (ratOf (q.out))

end GlobalTheory.CompanionTheory.SwUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovolumeOneInvariantUnderMatrixStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_one_invariant_under_matrix : ∀ (F : Type) [Field F] [NumberField F] (ν : Measure (AF F)), GlobalTheory.CompanionTheory.Hypotheses₂.OneV.IsCovolOne ν → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → (Measure.pi fun _ : ι => ν).map (fun x => (A.map (algebraMap F (AF F))).mulVec x) = Measure.pi fun _ : ι => ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix | exact GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix | (intros; apply GlobalTheory.CompanionTheory.SiegelND.piCovol_map_matrix <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalContragredientCentralCharacterStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_contragredient_central_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ),
    (contra σ.ρ).IsIrreducible ∧ IsCuspidal (contra σ.ρ) ∧
    ∃ (z : GL (Fin (m + 1)) k) (ϖ : k) (ω : ℂ), (z : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ϖ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∧
      ValuativeRel.valuation k ϖ < 1 ∧ ϖ ≠ 0 ∧ ω ≠ 0 ∧ (∀ a, σ.ρ z a = ω • a) ∧ ∀ l, contra σ.ρ z l = ω⁻¹ • l := by
  first | exact @GlobalTheory.CompanionTheory.ContraCusp.contra_facts | exact GlobalTheory.CompanionTheory.ContraCusp.contra_facts | (intros; apply GlobalTheory.CompanionTheory.ContraCusp.contra_facts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMirabolicInvariantPairingScalarStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_mirabolic_invariant_pairing_scalar : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (β : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ)
    (hβ : ∀ g : GL (Fin (m + 1)) k,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 →
      ∀ a l, β (σ.ρ g a) (contra σ.ρ g l) = β a l),
    ∃ c : ℂ, ∀ a l, β a l = c * (l : Module.Dual ℂ σ.V) a := by
  first | exact @GlobalTheory.CompanionTheory.StabForm.form_unique | exact GlobalTheory.CompanionTheory.StabForm.form_unique | (intros; apply GlobalTheory.CompanionTheory.StabForm.form_unique <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeUnitaryActionStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_unitary_action : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Matrix.unitaryGroup (Fin n) ℂ →* (H →L[ℂ] H)) (G : Fin n → Fin n → Module.End ℂ H), (∀ (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ), Xᴴ = -X → (∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) → ∀ w : H, HasDerivAt (fun t : ℝ => ρ (γ t) w) (∑ a, ∑ b, X a b • G a b w) 0) → ∀ (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf → (∀ a b (x y : V), ⟪Kf a b x, y⟫_ℂ = ⟪x, Kf b a y⟫_ℂ) → ∀ T : H →ₗ[ℂ] V, (∀ a b w, T (G a b w) = Kf a b (T w)) → ∀ k w, T (ρ k w) = σ k (T w) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.IntegrateK.intertwines_unitary | exact GlobalTheory.CompanionTheory.RealCount.IntegrateK.intertwines_unitary | (intros; apply GlobalTheory.CompanionTheory.RealCount.IntegrateK.intertwines_unitary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFamilyHeightBound
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FamMajorant

theorem fam_majorant : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  rintro D n H hH ⟨C, hC, hcov⟩ χ s₁ φ hφ hlaw
  have hHpos : ∀ g, 0 < (H g : ℝ) := fun g => NNReal.coe_pos.2 (hH.2.1 g)
  have hpos : ∀ g, 0 < (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := fun g => Real.rpow_pos_of_pos (hHpos g) _
  have hcont : Continuous fun g => ‖φ g‖ / (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
    hφ.norm.div ((NNReal.continuous_coe.comp hH.1).rpow_const fun g => Or.inl (hHpos g).ne') fun g => (hpos g).ne'
  obtain ⟨δ, hδ⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  have hB0 : 0 ≤ max δ 0 := le_max_right _ _
  have hon : ∀ c ∈ C, ‖φ c‖ ≤ max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro c hc
    have h1 := (hδ c hc).trans (le_max_left δ 0)
    rwa [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (hpos c).le), div_le_iff₀ (hpos c)] at h1
  have hall : ∀ g, ‖φ g‖ ≤ max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro g
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
    have hr : 0 < absA D (Matrix.GeneralLinearGroup.det a) := hom_pos _ _
    rw [hlaw q hq a ha c, hH.2.2 q hq a ha c]
    have e1 : ‖npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [norm_npow hr]; congr 1; simp
    have e2 : ((absA D (Matrix.GeneralLinearGroup.det a) * H c : ℝ≥0) : ℝ) ^ (s₁.re + (n : ℝ) / 2) =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [e2, norm_mul, norm_mul, e1]
    simp only [Circle.norm_coe, one_mul]
    have h0 : 0 ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
      Real.rpow_nonneg (NNReal.coe_nonneg _) _
    calc _ ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) *
          (max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2)) := mul_le_mul_of_nonneg_left (hon c hc) h0
      _ = _ := by ring
  refine ⟨max δ 0, hB0, fun z g => ?_⟩
  have e3 : ‖npow (H g) (z - s₁)‖ = (H g : ℝ) ^ (z.re - s₁.re) := by
    rw [norm_npow (hH.2.1 g)]; congr 1
  have e4 : (H g : ℝ) ^ (z.re + (n : ℝ) / 2) = (H g : ℝ) ^ (z.re - s₁.re) * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add (hHpos g)]; congr 1; ring
  have h0 : 0 ≤ (H g : ℝ) ^ (z.re - s₁.re) := (Real.rpow_pos_of_pos (hHpos g) _).le
  simp only [fam]
  rw [norm_mul, e3, e4]
  calc _ ≤ (H g : ℝ) ^ (z.re - s₁.re) * (max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (hall g) h0
    _ = _ := by ring

end GlobalTheory.CompanionTheory.FamMajorant

end
end

