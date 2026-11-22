import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetSplitPlaceLatticeIntersection
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0725
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0765
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0766
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemMaximalCompactIffIntegralImage
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

namespace GlobalTheory.CompanionTheory.Jp.SplitK

open Formalism.UG (GLint)

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {m : ℕ} {J : Matrix (Fin m) (Fin m) E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_stabLoc_std_iff (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {g : GLoc σ J v} :
    g ∈ stabLoc σ J (stdLattice E m) v ↔
      splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring ∧
        splitHom σ J (τ.comp σ) g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring := by
  have key : ∀ y : Fin m → Fv F v ⊗[F] E, y ∈ latLoc F (stdLattice E m) v ↔
      (∀ i, splitVec τ y i ∈ v.adicCompletionIntegers F) ∧
        ∀ i, splitVec (τ.comp σ) y i ∈ v.adicCompletionIntegers F := fun y => by
    rw [mem_latLoc_iff_split τ h, mem_splitLat_stdLattice h, mem_splitLat_stdLattice h]
  rw [mem_stabLoc]
  simp only [key, splitVec_matHom_mulVec, mem_GLint_iff_mulVec]
  constructor
  · intro H
    refine ⟨fun u => ?_, fun u => ?_⟩
    · simpa using H (splitIncl h τ u)
    · simpa using H (splitIncl h (τ.comp σ) u)
  · rintro ⟨H1, H2⟩ y
    exact and_congr (H1 _) (H2 _)

omit [NumberField E] in

theorem transpose_splitHom_comp (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1) (g : GLoc σ J v) :
    (splitHom σ J (τ.comp σ) g).1ᵀ = -(J.map τ * (splitHom σ J τ g⁻¹).1 * J.map τ) := by
  have e := splitHom_unitary τ g
  have i1 : (splitHom σ J τ g).1 * (splitHom σ J τ g⁻¹).1 = 1 := by
    rw [map_inv, Units.mul_inv]
  calc (splitHom σ J (τ.comp σ) g).1ᵀ
      = -((splitHom σ J (τ.comp σ) g).1ᵀ * (J.map τ * J.map τ)) := by rw [hJ]; simp
    _ = -(((splitHom σ J (τ.comp σ) g).1ᵀ * J.map τ * (splitHom σ J τ g).1) *
          (splitHom σ J τ g⁻¹).1 * J.map τ) := by
        congr 1
        rw [Matrix.mul_assoc _ (splitHom σ J τ g).1, i1]
        simp [Matrix.mul_assoc]
    _ = _ := by rw [e]

theorem mul_entry_mem {ι : Type} [Fintype ι] {X Y : Matrix ι ι (Fv F v)}
    (hX : ∀ i j, X i j ∈ v.adicCompletionIntegers F) (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers F) (i j : ι) :
    (X * Y) i j ∈ v.adicCompletionIntegers F := by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hX i l) (hY l j)

omit [NumberField E] in

theorem comp_mem_GLint (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1)
    (hint : ∀ i j, J.map τ i j ∈ v.adicCompletionIntegers F) {g : GLoc σ J v}
    (hg : splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring) :
    splitHom σ J (τ.comp σ) g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring := by
  rw [mem_GLint_iff] at hg ⊢
  obtain ⟨h1, h2⟩ := hg
  have h2' : ∀ i j, (splitHom σ J τ g⁻¹).1 i j ∈ v.adicCompletionIntegers F := by
    rw [map_inv]; exact h2
  have h1' : ∀ i j, (splitHom σ J τ g⁻¹⁻¹).1 i j ∈ v.adicCompletionIntegers F := by
    rw [inv_inv]; exact h1
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have e := congrFun₂ (transpose_splitHom_comp τ hJ g) j i
    rw [Matrix.transpose_apply] at e
    rw [e, Matrix.neg_apply]
    exact neg_mem (mul_entry_mem (mul_entry_mem hint h2') hint j i)
  · have e := congrFun₂ (transpose_splitHom_comp τ hJ g⁻¹) j i
    rw [Matrix.transpose_apply, map_inv] at e
    rw [e, Matrix.neg_apply]
    exact neg_mem (mul_entry_mem (mul_entry_mem hint h1') hint j i)

theorem mem_stabLoc_std_iff_GLint (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (hJ : J.map τ * J.map τ = -1)
    (hint : ∀ i j, J.map τ i j ∈ v.adicCompletionIntegers F) {g : GLoc σ J v} :
    g ∈ stabLoc σ J (stdLattice E m) v ↔
      splitHom σ J τ g ∈ GLint (Fin m) (v.adicCompletionIntegers F).toSubring :=
  (mem_stabLoc_std_iff h τ).trans ⟨fun H => H.1, fun H => ⟨H, comp_mem_GLint τ hJ hint H⟩⟩

end Gen

section Blocks

variable {D : D7} {n : ℕ} {v : Pl D}

theorem blkGL_val {R : Type} [CommRing R] (x : GL (Fin (n + n)) R) (i j : Ix n) :
    (blkGL n x).1 i j = x.1 (finSumFinEquiv i) (finSumFinEquiv j) := rfl

theorem mem_GLint_iff_blkGL {x : GL (Fin (n + n)) (Lv D v)} :
    x ∈ GLint (Fin (n + n)) (v.adicCompletionIntegers D.host.F).toSubring ↔
      blkGL n x ∈ GLint (Ix n) (v.adicCompletionIntegers D.host.F).toSubring := by
  rw [mem_GLint_iff, mem_GLint_iff, ← map_inv]
  simp only [blkGL_val]
  constructor
  · exact fun H => ⟨fun i j => H.1 _ _, fun i j => H.2 _ _⟩
  · refine fun H => ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using H.1 (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
    · simpa using H.2 (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

theorem Jst_map_sq (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    (Jst D n).map τ * (Jst D n).map τ = -1 := by
  have e : (Jst D n).map τ = blk4 0 1 (-1) 0 := by
    ext i j
    simp only [Matrix.map_apply, Jst, blk4, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
      simp [Matrix.one_apply]
  have e2 : (Matrix.fromBlocks (-1) 0 0 (-1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (Fv D.host.F v)) = -1 := by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp
  rw [e, blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, neg_zero]
  rw [e2]
  ext i j
  simp [Matrix.one_apply]

theorem Jst_map_int (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (i j : Fin (n + n)) :
    (Jst D n).map τ i j ∈ v.adicCompletionIntegers D.host.F := by
  simp only [Matrix.map_apply, Jst, blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply] <;> split_ifs <;> simp

end Blocks

theorem mem_KUpFin_iff (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (g : GLoc D.sp.cm.sig (Jst D n) v) :
    g ∈ GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v ↔
      thU D n v τ g ∈ (inL (O := Ov D v) (L := Lv D v) (n := n)).range :=
  (mem_stabLoc_std_iff_GLint (isCMExt_host D) τ (Jst_map_sq τ) (Jst_map_int τ)).trans
    mem_GLint_iff_blkGL

end GlobalTheory.CompanionTheory.Jp.SplitK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusUpperParabolicLocal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.UpTri

theorem transpose_block_matrix {A : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) A) :
    (GlobalTheory.StdUnn.blk4 a b c d)ᵀ = GlobalTheory.StdUnn.blk4 aᵀ cᵀ bᵀ dᵀ := by
  ext i j
  simp only [GlobalTheory.StdUnn.blk4, Matrix.transpose_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

theorem blocks_of_unitary {K : Type} [CommRing K] {n : ℕ} (a : GL (Fin n) K) (b d a' b' c' d' : Matrix (Fin n) (Fin n) K)
    (h : (GlobalTheory.StdUnn.blk4 a' b' c' d')ᵀ * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * GlobalTheory.StdUnn.blk4 a.1 b 0 d =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0) : c' = 0 ∧ a'ᵀ * d = 1 := by
  rw [transpose_block_matrix, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul, GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul] at h
  obtain ⟨h1, h2, -, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h
  have e1 : c'ᵀ * a.1 = 0 := by simpa using h1
  have e2 : c'ᵀ = 0 := by
    have := congrArg (· * (a⁻¹).1) e1
    simpa [Matrix.mul_assoc, -Matrix.coe_units_inv] using this
  have e3 : c' = 0 := by simpa using congrArg Matrix.transpose e2
  subst e3
  exact ⟨rfl, by simpa using h2⟩

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {v : HeightOneSpectrum (𝓞 F)}

theorem upperParabolic_height_of_split (h : IsCMExt F E σ) (hQ : Q = GlobalTheory.StdUnn.blk4 0 1 (-1) 0) (τ : E →ₐ[F] Fv F v)
    (y : GLoc σ Q v) (a d : GL (Fin n) (Fv F v)) (b : Matrix (Fin n) (Fin n) (Fv F v))
    (hy : (splitHom σ Q τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1) :
    ∃ hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q,
      absEv F E v (GlobalTheory.LocIntw.aUp (Fv F v) σ Q ⟨y, hm⟩) = ‖a.1.det‖₊ / ‖d.1.det‖₊ := by
  obtain ⟨A, B, C, D', e⟩ := GlobalTheory.LocIntw.exists_blockMatrixTwoByTwoFin_eq (GlobalTheory.LocIntw.matR (Fv F v) σ y)
  have key : ∀ ρ : E →ₐ[F] Fv F v, (splitHom σ Q ρ y).1 =
      GlobalTheory.StdUnn.blk4 (A.map (splitProj ρ)) (B.map (splitProj ρ)) (C.map (splitProj ρ)) (D'.map (splitProj ρ)) := by
    intro ρ
    rw [splitHom_val]
    change (GlobalTheory.LocIntw.matR (Fv F v) σ y).map (splitProj ρ : Fv F v ⊗[F] E →+* Fv F v) = _
    rw [e]
    exact GlobalTheory.LocIntw.blockMatrix_map _ _ _ _ _
  obtain ⟨ha, -, hc, -⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective ((key τ).symm.trans hy)
  have hQτ : Q.map τ = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    subst hQ
    have := GlobalTheory.LocIntw.blockMatrix_map (τ : E →+* Fv F v) (0 : Matrix (Fin n) (Fin n) E) 1 (-1) 0
    rw [Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  have u := splitHom_unitary τ y
  rw [key (τ.comp σ), hQτ, hy] at u
  obtain ⟨hc', hd'⟩ := blocks_of_unitary a b d.1 _ _ _ _ u
  have hC : C = 0 := splitMat_ext h τ
    (by rw [hc]; exact (Matrix.map_zero _ (map_zero _)).symm)
    (by rw [hc']; exact (Matrix.map_zero _ (map_zero _)).symm)
  have hm : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv F v) σ Q := (GlobalTheory.LocIntw.mem_siegelParabolic_iff_lowerLeft_eq_zero hQ).2 fun i j => by
    rw [e, hC, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    simp
  refine ⟨hm, ?_⟩
  have hA : GlobalTheory.StdUnn.blkA (GlobalTheory.LocIntw.matR (Fv F v) σ y) = A := by rw [e, GlobalTheory.LocIntw.upperLeft_blockMatrix]
  have d1 : splitProj τ A.det = a.1.det := by
    rw [← ha]
    exact RingHom.map_det (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) A
  have d2 : splitProj (τ.comp σ) A.det * d.1.det = 1 := by
    have : splitProj (τ.comp σ) A.det = (A.map (splitProj (τ.comp σ))).det :=
      RingHom.map_det (splitProj (τ.comp σ) : Fv F v ⊗[F] E →+* Fv F v) A
    rw [this, ← Matrix.det_transpose, ← Matrix.det_mul, hd', Matrix.det_one]
  rw [absEv_apply, GlobalTheory.LocIntw.coe_aUp, hA, GlobalTheory.SplitInterDet.norm_eq_split h τ, nnnorm_mul, d1,
    eq_inv_of_mul_eq_one_left d2, nnnorm_inv, div_eq_mul_inv]

end General

theorem upperParabolic_height (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (y : GLoc D.sp.cm.sig (Jst D n) v) (a d : GL (Fin n) (Fv D.host.F v))
    (b : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (H : thU D n v τ y = pM a d b) :
    ∃ hy : y ∈ GlobalTheory.LocIntw.upperParabolic (Fv D.host.F v) D.sp.cm.sig (Jst D n),
      absEv D.host.F D.host.E v (GlobalTheory.LocIntw.aUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) ⟨y, hy⟩) =
        nvL D v (Matrix.GeneralLinearGroup.det a) / nvL D v (Matrix.GeneralLinearGroup.det d) := by
  have hy : (splitHom D.sp.cm.sig (Jst D n) τ y).1 = GlobalTheory.StdUnn.blk4 a.1 b 0 d.1 := by
    have e : ((splitHom D.sp.cm.sig (Jst D n) τ y).1).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks a.1 b 0 d.1 := congrArg Units.val H
    rw [GlobalTheory.StdUnn.blk4, ← e]
    ext i j
    simp
  exact upperParabolic_height_of_split (isCMExt_host D) (GlobalTheory.LocIntw.Jst_eq D n) τ y a d b hy

end GlobalTheory.CompanionTheory.Jp.UpTri

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquet
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZNuPairAsm

section Lemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dualCl_degree (x : IrrGL k) : (dualCl x).1 = x.1 := by
  unfold dualCl
  split <;> rfl

theorem dual_shift (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (s q : IrrGL k) (j : ℕ) (h : q = (dualCl s).nu (j : ℂ)) :
    dualCl (q.nu (-(((j : ℂ) + 1) / 2))) = (s.nu (-(((j : ℂ) + 1) / 2))).nu 1 := by
  subst h
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA,
    IrrGL.nu_nu, IrrGL.nu_nu]
  congr 1
  ring

theorem nontrivial_of_irreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hi : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply hi.bot_ne_top
  ext v
  simp [Subsingleton.elim v 0]

theorem continuous_inv (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have e : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := by
    funext a
    exact AddChar.inv_apply ψ a
  rw [e]
  exact hc.comp continuous_neg

theorem jm_swap (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hJT : JmTheta k) {N : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ω : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth ω) (hi : ω.IsIrreducible)
    (a b c : IrrGL k) (hc : dualCl a = c) (hd : ∑ i, (![a, b] i).1 = N) (h : 1 ≤ jm ![a, b] hd (contra ω)) :
    ∃ hd' : ∑ i, (![dualCl b, c] i).1 = N, 1 ≤ jm ![dualCl b, c] hd' ω := by
  have hfl : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  have hd2 : ∑ i, (![dualCl b, dualCl a] i).1 = N := by
    simpa [Fin.sum_univ_two, dualCl_degree, add_comm] using hd
  have key := hJT N V ω hs hfl a b hd hd2
  have e := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra (GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA) N ω hs hi
  rw [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv ![a, b] hd _ _ e] at key
  subst hc
  exact ⟨hd2, key ▸ h⟩

end Lemmas

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k →
    GlobalTheory.BZSeg.NuPair k := by
  intro k _ _ _ _ hA hDJ hJT hDS N V _ _ ω hs hi hng
  obtain ⟨ψ, hc, h1⟩ := GlobalTheory.LocGL.exists_continuous_addChar_ne_one k
  have hn : Nontrivial V := nontrivial_of_irreducible ω hi
  have hg : ¬ IsGenericFor ψ ω := fun h => hng ((isGeneric_iff_isGenericFor hc h1 ω).2 h)
  obtain ⟨m, hm0, hmN, hnt, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc h1 N ω hs hn hg
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - n - 2, by omega⟩
  have hfl : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt
  obtain ⟨S, f, hf⟩ := hDS ψ n j V ω hs hfl hD
  have hsq : IsSubquotient S.ρ (GlobalTheory.BZMir.deriv k ψ j ω) := IsSubquotient.of_injective f hf
  obtain ⟨β, hdβ, hβ, hjm⟩ := hDJ ψ hc h1 n j V ω hs hfl S hsq
  have hv := GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc h1 n j ω hs hlow
  have hs' : IsSmooth (contra ω) := isSmooth_contra _
  have hi' : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  have hfl' : HasFiniteLength (contra ω) := hasFiniteLength_of_isIrreducible hi'
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := ((smoothPart ω.dual).subtype).flip
  have hB : ∀ g v v', B (ω g v) (contra ω g v') = B v v' := by
    intro g v v'
    change (ω.dual g (v' : Module.Dual ℂ V)) (ω g v) = (v' : Module.Dual ℂ V) v
    rw [Representation.dual_apply]
    show (v' : Module.Dual ℂ V) (ω g⁻¹ (ω g v)) = (v' : Module.Dual ℂ V) v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hBn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := by
    intro v hv0
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs
      (fun U a => GlobalTheory.ThetaLiftGL.compactOpen_basis k (n + 1 + j + 1) U a) hv0
    exact ⟨l, hl⟩
  obtain ⟨B', hB', hB'n⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc h1 n j ω (contra ω) hs hs' B hB hBn hv
  have hint : ∀ g w, f (S.ρ g w) = GlobalTheory.BZMir.deriv k ψ j ω g (f w) := fun g w =>
    Representation.IntertwiningMap.isIntertwining _ _ f g w
  have hSn : Nontrivial S.V := nontrivial_of_irreducible S.ρ S.irr
  obtain ⟨Q, hQ, hQeq⟩ := GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu k (n + 1) j _ S
    (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω)) (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j hs')
    (B'.comp f.toLinearMap)
    (by
      intro g w w'
      change B' (f (S.ρ g w)) _ = _ * B' (f w) w'
      rw [hint]
      exact hB' g (f w) w')
    (by
      intro h0
      obtain ⟨w, hw⟩ := exists_ne (0 : S.V)
      have hfw : f w ≠ 0 := fun e => hw (hf (e.trans (map_zero f).symm))
      obtain ⟨w', hw'⟩ := hB'n (f w) hfw
      apply hw'
      have := LinearMap.congr_fun (LinearMap.congr_fun h0 w) w'
      exact this)
  obtain ⟨β₂, hd₂, hβ₂, hjm₂⟩ := hDJ ψ⁻¹ (continuous_inv ψ hc) (inv_ne_one.mpr h1) n j _ (contra ω) hs' hfl' Q hQ
  obtain ⟨hd₃, hjm₃⟩ := jm_swap hA hJT ω hs hi _ β₂ _ rfl hd₂ hjm₂
  have hshift := dual_shift hA (IrrGL.of S.ρ S.smooth S.irr) (IrrGL.of Q.ρ Q.smooth Q.irr) j hQeq
  have hd' : ∑ a, (![dualCl β₂, ((IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2))).nu 1] a).1 =
      n + 1 + j + 1 := by
    rw [← hshift]
    exact hd₃
  refine ⟨(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), β, dualCl β₂, hdβ, hd', ?_, ?_, ?_, hjm, ?_⟩
  · rw [IrrGL.nu_fst]
    exact Nat.succ_pos n
  · rw [hβ]
    exact Nat.succ_pos j
  · rw [dualCl_degree, hβ₂, hβ]
  · rw [← GlobalTheory.CompanionTheory.SegFine.jm_congr (by rw [hshift]) hd₃ hd' ω]
    exact hjm₃

end GlobalTheory.CompanionTheory.BZNuPairAsm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodicPartialFourierMeanStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_partial_fourier_mean : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ), IsPer Φ → IsPer (pm hn m ψ b₀ Φ) := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.isPer_pm | exact GlobalTheory.CompanionTheory.PcFc.isPer_pm | (intros; apply GlobalTheory.CompanionTheory.PcFc.isPer_pm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankDirectSumHermitianLtStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_direct_sum_hermitian_lt : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (b₀ : HermE D ρ), b₀.1.det ≠ 0 → ∀ β' : HermE D p, β'.1 ≠ 0 → ρ + 1 ≤ (dsum hn b₀ β').1.rank := by
  first | exact @GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge | exact GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge | (intros; apply GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankResidueLeRankGeneric
section
namespace GlobalTheory.CompanionTheory.Jp

theorem rank_residue_map_le_rank_fraction_map :
    ∀ (O L : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field L] [Algebra O L]
      [IsFractionRing O L] (n : ℕ) (T : Matrix (Fin n) (Fin n) O),
      (T.map (IsLocalRing.residue O)).rank ≤ (T.map (algebraMap O L)).rank := by
  intro O L _ _ _ _ _ _ n T
  obtain ⟨S, τ, hdet⟩ := GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank (IsLocalRing.ResidueField O)
    (Fin n) (Fin n) _ (T.map (IsLocalRing.residue O)) le_rfl
  have hres : IsLocalRing.residue O (T.submatrix S τ).det =
      ((T.map (IsLocalRing.residue O)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hfrac : algebraMap O L (T.submatrix S τ).det =
      ((T.map (algebraMap O L)).submatrix S τ).det := by
    rw [RingHom.map_det]
    rfl
  have hO : (T.submatrix S τ).det ≠ 0 := by
    intro h
    apply hdet
    rw [← hres, h, map_zero]
  have hL : ((T.map (algebraMap O L)).submatrix S τ).det ≠ 0 := by
    rw [← hfrac]
    intro h
    exact hO (IsFractionRing.injective O L (h.trans (map_zero _).symm))
  calc (T.map (IsLocalRing.residue O)).rank
      = ((T.map (algebraMap O L)).submatrix S τ).rank := by
        rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)),
          Fintype.card_fin]
    _ ≤ (T.map (algebraMap O L)).rank := Matrix.rank_submatrix_le _ _ _

end GlobalTheory.CompanionTheory.Jp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatIntegrableAdelic
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem sb_integrable_selfDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, IsSchwartzBruhat Φ → Integrable Φ dx := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx Φ hΦ
  exact (GlobalTheory.CompanionTheory.SiegelND.CoefSum.continuous_integrable_tuple σ hCM M n dx hdx.1 Φ hΦ).2

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftCommutesLeviEmbeddingStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shift_commutes_levi_embedding : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (g₀ : G D p) (a : GL (Fin p) (AE D)),
  mat g₀ = blk4 a.1 0 0 (adj (a⁻¹).1) → ∀ y : Mx D ρ p, M.sh y * M.emb g₀ = M.emb g₀ * M.sh (HMul.hMul y a.1 : Mx D ρ p) := by
  first | exact @GlobalTheory.CompanionTheory.PcB.sh_emb_levi | exact GlobalTheory.CompanionTheory.PcB.sh_emb_levi | (intros; apply GlobalTheory.CompanionTheory.PcB.sh_emb_levi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormulaStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_orbital_integral_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (k : ℕ) (Φ : Fin k → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum | exact GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum | (intros; apply GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum <;> assumption)
end

