import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.ProdIotaRev
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import BuildAid.Bundle0001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0507
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0526

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductReverseContragredientHolds
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ProdIota

theorem typeTame_invTranspose (n : ℕ) (k : Type) [Field k] :
    GlobalTheory.TypeTame.invTranspose (R := k) n = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose n k :=
  MonoidHom.ext fun _ => Units.ext rfl

section Reverse

open GlobalTheory.TypeTame GlobalTheory.InvTransposeProd

theorem multiProd_comp_rev (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h n : ℕ) (d : Fin h → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (e' : (Σ a, Fin (d (Fin.rev a))) ≃ Fin n) (X : Fin h → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)) :
    Nonempty (Representation.Equiv ((multiProd e π).comp (invTranspose n))
      (multiProd e' fun a => ((π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) :
        Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a))))) := by
  set π' : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (X (Fin.rev a)) :=
    fun a => (π (Fin.rev a)).comp (invTranspose (d (Fin.rev a))) with hπ'
  have key : ∀ (q : parab k e) (hq : invTranspose n (q : GL (Fin n) k) ∈ parab k (revPlace e)),
      ((twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e))) ⟨invTranspose n q, hq⟩ =
        ((twist (piTensor π) (deltaHalf k _)).comp (leviProj k e)) q := by
    intro q hq
    refine LinearMap.ext fun v => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, twist_apply, twist_apply, deltaHalf_revPlace e q hq,
      hπ', revRep_leviProj e π q hq]
  obtain ⟨A⟩ : Nonempty ((parInd (revPlace e) (revRep π')).Equiv
      ((multiProd e π).comp (invTranspose n))) := by
    refine Relabel.smInd_equiv_comp (P := parab k (revPlace e)) (Q := parab k e)
      (σ := (twist (revRep π') (deltaHalf k _)).comp (leviProj k (revPlace e)))
      (τ := (twist (piTensor π) (deltaHalf k _)).comp (leviProj k e))
      (invTranspose n) (invTranspose n) (continuous_invTranspose n) (continuous_invTranspose n)
      (invTranspose_invTranspose n) (invTranspose_invTranspose n)
      (fun q => ⟨⟨_, mem_parab_revPlace e q.2⟩, rfl, key q _⟩) (fun p => ?_)
    have hp : invTranspose n (invTranspose n (p : GL (Fin n) k)) ∈ parab k (revPlace e) := by
      rw [invTranspose_invTranspose]
      exact p.2
    refine ⟨⟨_, mem_parab_of_revPlace e p.2⟩, rfl, ?_⟩
    refine (key ⟨_, mem_parab_of_revPlace e p.2⟩ hp).symm.trans ?_
    exact congrArg _ (Subtype.ext (invTranspose_invTranspose n (p : GL (Fin n) k)))
  obtain ⟨B⟩ := GlobalTheory.PlacingProd.multiProd_placing_equiv k h n (fun a => d (Fin.rev a)) (revPlace e) e'
    (fun a => X (Fin.rev a)) π'
  exact ⟨A.symm.trans ((parIndEquiv (revPlace e) (revRepEquiv π')).trans B)⟩

end Reverse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_gk (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (y : IrrGL k) :
    Nonempty (Representation.Equiv (y.rep.comp (GlobalTheory.TypeTame.invTranspose y.1)) (contra y.rep)) := by
  rw [typeTame_invTranspose]
  exact GlobalTheory.GelfandKazhdan.equiv_contra k _ _ _ (hA k _ _ _ y.2.rep.smooth y.2.rep.irr) y.2.rep.irr

theorem step_general {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hrev : ∑ a, d (Fin.rev a) = N)
    {X : Fin h → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {Y : Fin h → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (σ : ∀ a, Representation ℂ (GL (Fin (d (Fin.rev a))) k) (Y a))
    (φ : ∀ a, Nonempty (Representation.Equiv ((π (Fin.rev a)).comp (GlobalTheory.TypeTame.invTranspose (d (Fin.rev a)))) (σ a))) :
    Nonempty (Representation.Equiv ((multiProd (stdBlocks d hd) π).comp (GlobalTheory.TypeTame.invTranspose N))
      (multiProd (stdBlocks (fun a => d (Fin.rev a)) hrev) σ)) := by
  obtain ⟨A⟩ := multiProd_comp_rev k h N d (stdBlocks d hd)
    (stdBlocks (fun a => d (Fin.rev a)) hrev) X π
  exact ⟨A.trans (multiProdEquiv _ fun a => (φ a).some)⟩

theorem step_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (hrev : ∑ a, (x (Fin.rev a)).1 = N) :
    Nonempty (Representation.Equiv ((prodIrr x hd).comp (GlobalTheory.TypeTame.invTranspose N))
      (multiProd (stdBlocks (fun a => (x (Fin.rev a)).1) hrev) fun a => contra (x (Fin.rev a)).rep)) :=
  step_general (fun a => (x a).1) hd hrev (fun a => (x a).rep)
    (fun a => contra (x (Fin.rev a)).rep) fun a => step_gk hA (x (Fin.rev a))

theorem step_class {N h : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin N) k) V}
    (d : Fin h → ℕ) (hd : ∑ a, d a = N) {Y : Fin h → Type} [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (Y a)) (hs : ∀ a, IsSmooth (σ a)) (hi : ∀ a, (σ a).IsIrreducible)
    (A : Nonempty (ρ.Equiv (multiProd (stdBlocks d hd) σ))) :
    Nonempty (ρ.Equiv (prodIrr (fun a => IrrGL.of (σ a) (hs a) (hi a)) hd)) :=
  A.map fun A => A.trans (prodIrrEquiv hd σ hs hi)

theorem contragredient_product_reversed (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N)
    (hrev : ∑ a, (x (Fin.rev a)).1 = N) (hs : ∀ a, IsSmooth (contra (x (Fin.rev a)).rep))
    (hi : ∀ a, (contra (x (Fin.rev a)).rep).IsIrreducible) :
    Nonempty (Representation.Equiv ((prodIrr x hd).comp (GlobalTheory.TypeTame.invTranspose N))
      (prodIrr (fun a => IrrGL.of (contra (x (Fin.rev a)).rep) (hs a) (hi a)) hrev)) :=
  step_class (fun a => (x (Fin.rev a)).1) hrev (fun a => contra (x (Fin.rev a)).rep) hs hi (step_contra hA x hd hrev)

theorem comp_invTranspose_congr {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (A : Nonempty (Representation.Equiv (ρ.comp (GlobalTheory.TypeTame.invTranspose N)) τ)) :
    Nonempty (Representation.Equiv (ρ.comp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion.invTranspose N k)) τ) := by
  rw [← typeTame_invTranspose]
  exact A

theorem exists_prodIrr_of_eq {h N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin N) k) V} (y z : Fin h → IrrGL k) (hzy : z = y) (hy : ∑ a, (y a).1 = N)
    (E : Nonempty (ρ.Equiv (prodIrr y hy))) : ∃ hz : ∑ a, (z a).1 = N, Nonempty (ρ.Equiv (prodIrr z hz)) := by
  subst hzy
  exact ⟨hy, E⟩

theorem prodIotaRev : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.ProdIotaRev k := by
  intro k _ _ _ _ hA h N x hd
  have hrev : ∑ a, (x (Fin.rev a)).1 = N := by
    rw [← hd]
    exact Equiv.sum_comp Fin.revPerm fun a => (x a).1
  have hi : ∀ a, (contra (x (Fin.rev a)).rep).IsIrreducible := fun a =>
    GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ (x (Fin.rev a)).2.rep.smooth (x (Fin.rev a)).2.rep.irr
  have hs : ∀ a, IsSmooth (contra (x (Fin.rev a)).rep) := fun a => isSmooth_contra _
  exact exists_prodIrr_of_eq (fun a => IrrGL.of (contra (x (Fin.rev a)).rep) (hs a) (hi a))
    (fun a => Zc.dualCl (x (Fin.rev a))) (funext fun a => GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA _) hrev
    (comp_invTranspose_congr (contragredient_product_reversed hA x hd hrev hs hi))

end GlobalTheory.CompanionTheory.ProdIota
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Unique

theorem pullRatio_top_eq {N : ℕ} {x x' : Sp ℂ ⟶ PSpace ℤ N} (i j : Fin (N + 1))
    (h : ⊤ ≤ x ⁻¹ᵁ chart ℤ N i) (h' : ⊤ ≤ x' ⁻¹ᵁ chart ℤ N i)
    (e : valR x (chart ℤ N i) (ratio ℤ N i j) = valR x' (chart ℤ N i) (ratio ℤ N i j)) :
    pullRatio x ⊤ i h j = pullRatio x' ⊤ i h' j := by
  rw [valR, valR, dif_pos h, dif_pos h'] at e
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 e

theorem valR_comp_prB {m : ℕ} {n : Fin (m + 1) → ℕ} (x : Sp ℂ ⟶ MP ℤ m n) {k : Fin (m + 1)} (i j : Bk n k)
    (h : ⊤ ≤ x ⁻¹ᵁ blockChart n k i) :
    valR (x ≫ prB n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) =
      valR x (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) := by
  have h' : ⊤ ≤ (x ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) i := h
  rw [valR, valR, dif_pos h, dif_pos h', pullRatio,
    ← Scheme.Hom.appLE_comp_appLE x (prB n k) (chart ℤ (n k) i) (blockChart n k i) ⊤ le_rfl h]
  rfl

end GlobalTheory.CompanionTheory.MPDict.Unique

open GlobalTheory.CompanionTheory.MPDict.Unique in

theorem GlobalTheory.CompanionTheory.MPDict.isUnder_unique : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y' := by
  intro m n z y y' h h'
  refine Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_)
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k)) :=
    mem_ptsIn.2 (mem_ptChart _ k)
  obtain ⟨i, hi⟩ : ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ⟨_, hy⟩
  have hz : z ⟨k, i⟩ ≠ 0 := ((h k i).1).1 hi
  have hi' : y' ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((h' k i).1).2 hz
  refine GlobalTheory.ProjSpace.hom_ext ?_ fun t => ⟨⊤, trivial, i, hi, hi', fun j => ?_⟩
  · have s : pr ℤ m n k ≫ PSpace.str ℤ (n k) = mpStr ℤ m n := pr_toSpecBase ℤ m n k
    rw [Category.assoc, Category.assoc, s, y.2, y'.2]
  · have a : ⊤ ≤ y.1 ⁻¹ᵁ blockChart n k i := hi
    have a' : ⊤ ≤ y'.1 ⁻¹ᵁ blockChart n k i := hi'
    refine pullRatio_top_eq (x := y.1 ≫ prB n k) (x' := y'.1 ≫ prB n k) i j a a' ?_
    rw [valR_comp_prB y.1 i j a, valR_comp_prB y'.1 i j a']
    exact ((h k i).2 j hi).trans ((h' k i).2 j hi').symm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupInductionGenerators
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar.Transfer

section Field

variable {F₀ : Type} [Field F₀] {n : ℕ}

theorem block_matrix_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A B C E : Matrix (Fin n) (Fin n) R) :
    (blk4 A B C E).map f = blk4 (A.map f) (B.map f) (C.map f) (E.map f) := by
  rw [blk4, blk4, ← Matrix.fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_transpose {R : Type} (A B C E : Matrix (Fin n) (Fin n) R) :
    (blk4 A B C E)ᵀ = blk4 Aᵀ Cᵀ Bᵀ Eᵀ := by
  simp only [blk4, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]

theorem cT_mul (σ : F₀ →+* F₀) {N : ℕ} (g h : Matrix (Fin N) (Fin N) F₀) : cT σ (g * h) = cT σ h * cT σ g := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_blk4 (σ : F₀ →+* F₀) (A B C E : Matrix (Fin n) (Fin n) F₀) :
    cT σ (blk4 A B C E) = blk4 (cT σ A) (cT σ C) (cT σ B) (cT σ E) := by
  simp only [cT, block_matrix_map, blockMatrixTwoByTwoFin_transpose]

theorem cT_zero (σ : F₀ →+* F₀) : cT σ (0 : Matrix (Fin n) (Fin n) F₀) = 0 := by
  ext i j; simp [cT]

theorem cT_one (σ : F₀ →+* F₀) : cT σ (1 : Matrix (Fin n) (Fin n) F₀) = 1 := by
  ext i j; simp [cT, Matrix.one_apply, eq_comm]

theorem cT_neg (σ : F₀ →+* F₀) (x : Matrix (Fin n) (Fin n) F₀) : cT σ (-x) = -cT σ x := by
  ext i j; simp [cT]

theorem cT_cT {σ : F₀ →+* F₀} (hσ : ∀ x, σ (σ x) = x) (x : Matrix (Fin n) (Fin n) F₀) : cT σ (cT σ x) = x := by
  ext i j; simp [cT, hσ]

theorem isUnit_det_cT (σ : F₀ →+* F₀) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) : IsUnit (cT σ a).det := by
  have e : (cT σ a).det = σ a.det := by
    rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [e]; exact ha.map σ

theorem mA_isUnit_det (σ : F₀ →+* F₀) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) : IsUnit (mA σ a).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 a⁻¹ 0 0 (cT σ a)) ?_
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv _ ha
  have h2 : (cT σ a)⁻¹ * cT σ a = 1 := Matrix.nonsing_inv_mul _ (isUnit_det_cT σ ha)
  rw [mA, submatrix_fromBlocks_mul]
  simp [h1, h2, block_matrix_one]

theorem nB_isUnit_det (b : Matrix (Fin n) (Fin n) F₀) : IsUnit (nB b).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 1 (-b) 0 1) ?_
  rw [nB, submatrix_fromBlocks_mul]
  simp [block_matrix_one]

theorem Jm_isUnit_det : IsUnit (EC.Jm F₀ n).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := blk4 0 (-1) 1 0) ?_
  rw [EC.Jm, submatrix_fromBlocks_mul]
  simp [block_matrix_one]

theorem mA_isUnitary {σ : F₀ →+* F₀} (hσ : ∀ x, σ (σ x) = x) {a : Matrix (Fin n) (Fin n) F₀} (ha : IsUnit a.det) :
    IsUnitary σ (EC.Jm F₀ n) (mA σ a) := by
  have h1 : cT σ a * (cT σ a)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_cT σ ha)
  have h2 : cT σ (cT σ a)⁻¹ * a = 1 := by
    have h := congrArg (cT σ) h1
    rwa [cT_mul, cT_cT hσ, cT_one] at h
  unfold IsUnitary EC.Jm mA
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp [cT_zero, h1, h2]

theorem nB_isUnitary {σ : F₀ →+* F₀} {b : Matrix (Fin n) (Fin n) F₀} (hb : cT σ b = b) :
    IsUnitary σ (EC.Jm F₀ n) (nB b) := by
  unfold IsUnitary EC.Jm nB
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp [cT_zero, cT_one, hb]

theorem Jm_isUnitary (σ : F₀ →+* F₀) : IsUnitary σ (EC.Jm F₀ n) (EC.Jm F₀ n) := by
  unfold IsUnitary EC.Jm
  rw [cT_blk4, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp [cT_zero, cT_one, cT_neg]

theorem isUnitary_mul {σ : F₀ →+* F₀} {N : ℕ} {J g h : Matrix (Fin N) (Fin N) F₀} (hg : IsUnitary σ J g)
    (hh : IsUnitary σ J h) : IsUnitary σ J (g * h) := by
  unfold IsUnitary at *
  rw [cT_mul]
  calc cT σ h * cT σ g * J * (g * h) = cT σ h * (cT σ g * J * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hg, hh]

end Field

variable {D : D7} {n : ℕ}

theorem sig_sig (x : D.host.E) :
    (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x :=
  star_star x

theorem cT_sig_eq {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

theorem map_mA (a : Matrix (Fin n) (Fin n) D.host.E) :
    (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a).map (incA D) =
      blk4 (rat a) 0 0 (adj (rat a⁻¹)) := by
  rw [mA, block_matrix_map, cT_sig_eq, ← Matrix.conjTranspose_nonsing_inv, ← rat_conjTranspose]
  simp only [Matrix.map_zero _ (map_zero (incA D))]
  rfl

theorem map_nB (b : Matrix (Fin n) (Fin n) D.host.E) :
    (nB b).map (incA D) = blk4 1 (rat b) 0 1 := by
  rw [nB, block_matrix_map]
  show blk4 (rat 1) (rat b) (rat 0) (rat 1) = _
  rw [rat_one, rat_zero]

theorem map_Jm : (EC.Jm D.host.E n).map (incA D) = blk4 0 1 (-1) 0 := by
  rw [EC.Jm, block_matrix_map]
  show blk4 (rat 0) (rat 1) (rat (-1)) (rat 0) = _
  rw [rat_zero, rat_one, rat_neg, rat_one]

theorem ratPts_transfer : RatPts → ∀ (D : D7) (n : ℕ), FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n → ∀ S : G D n → Prop, (∀ g h, S g → S h → S (g * h)) → (∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → S g) → (∀ (g : G D n) (b : Mx D n n), adj b = b → mat g = blk4 1 b 0 1 → S g) → (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → S g) → ∀ γ ∈ GF D n, S γ := by
  intro hR D n hF S hmul hm hn hw γ hγ
  obtain ⟨h1, h2, -⟩ := hR D n
  obtain ⟨g, hgu, hgU, hg⟩ := h1 γ hγ
  let T : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E → Prop := fun M =>
    IsUnit M.det ∧ IsUnitary (D.sp.cm.sig : D.host.E →+* D.host.E) (EC.Jm D.host.E n) M ∧
      ∀ γ' : G D n, mat γ' = M.map (incA D) → S γ'
  have hprod : ∀ M₁ M₂, T M₁ → T M₂ → T (M₁ * M₂) := by
    rintro M₁ M₂ ⟨u₁, U₁, s₁⟩ ⟨u₂, U₂, s₂⟩
    refine ⟨by rw [Matrix.det_mul]; exact u₁.mul u₂, isUnitary_mul U₁ U₂, fun γ' e => ?_⟩
    obtain ⟨γ₁, -, e₁⟩ := h2 M₁ u₁ U₁
    obtain ⟨γ₂, -, e₂⟩ := h2 M₂ u₂ U₂
    have e' : γ' = γ₁ * γ₂ := mat_injective' (by rw [e, mat_mul', e₁, e₂, Matrix.map_mul])
    rw [e']
    exact hmul _ _ (s₁ _ e₁) (s₂ _ e₂)
  have hmA : ∀ a : Matrix (Fin n) (Fin n) D.host.E, IsUnit a.det →
      T (mA (D.sp.cm.sig : D.host.E →+* D.host.E) a) := by
    intro a ha
    refine ⟨mA_isUnit_det _ ha, mA_isUnitary sig_sig ha, fun γ' e => ?_⟩
    let a' : GL (Fin n) (AE D) := ⟨rat a, rat a⁻¹,
      by rw [← rat_mul, Matrix.mul_nonsing_inv _ ha, rat_one],
      by rw [← rat_mul, Matrix.nonsing_inv_mul _ ha, rat_one]⟩
    exact hm γ' a' (e.trans (map_mA a))
  have hnB : ∀ b : Matrix (Fin n) (Fin n) D.host.E, cT (D.sp.cm.sig : D.host.E →+* D.host.E) b = b → T (nB b) := by
    intro b hb
    refine ⟨nB_isUnit_det b, nB_isUnitary hb, fun γ' e => hn γ' (rat b) ?_ (e.trans (map_nB b))⟩
    rw [← rat_conjTranspose]
    exact congrArg rat hb
  have hJ : T (EC.Jm D.host.E n) :=
    ⟨Jm_isUnit_det, Jm_isUnitary _, fun γ' e => hw γ' (e.trans map_Jm)⟩
  exact (hF T hprod hmA hnB hJ g hgu hgU).2.2 γ hg

end GlobalTheory.CompanionTheory.EisCovar.Transfer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitarySendsIsotropicStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_sends_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ v : Fin n → E, v ≠ 0 → hE σ J v v = 0 → ∃ γ ∈ ratPts σ J, Sends σ J γ (Xᵀ 0) v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic | exact GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_ratPts_sends_isotropic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalUnitaryWittExtensionStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unitary_witt_extension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ γ ∈ ratPts σ J, ∀ w : Fin n → E, ∃ w' : Fin n → E, Sends σ J γ w w' ∧ hE σ J w' w' = hE σ J w w := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.exists_sends_hE | exact GlobalTheory.CompanionTheory.RedCov.exists_sends_hE | (intros; apply GlobalTheory.CompanionTheory.RedCov.exists_sends_hE <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslationLieConjugate
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem rt_infGL_mul_lie (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (g : GL (Fin a) (Cinf E)) (X : Lie E a) :
    rt E a (infGL E a g) * lie E a X =
      lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g) := by
  refine LinearMap.ext fun ψ => Subtype.ext <| funext fun x => ?_
  have hd : DifferentiableAt ℝ (chart ψ.1 x) (toL g.val) :=
    (contDiffAt_chart ψ.2 x (val_mem_invSet g)).differentiableAt (by simp)
  have e1 : lmul (toL g.val) (oneL E a) = toL g.val := mul_one g.val
  have e2 : rmul (toL g.val) (oneL E a) = toL g.val := one_mul g.val
  have e3 : lmul (toL g.val) X = rmul (toL g.val) (toL (g.val * Matrix.of X * (g⁻¹).val)) := by
    change g.val * Matrix.of X = g.val * Matrix.of X * (g⁻¹).val * g.val
    rw [mul_assoc (g.val * Matrix.of X), ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  change fderiv ℝ (chart ψ.1 (x * infGL E a g)) (oneL E a) X =
    fderiv ℝ (chart (fun y => ψ.1 (y * infGL E a g)) x) (oneL E a)
      (toL (g.val * Matrix.of X * (g⁻¹).val))
  rw [chart_mul, chart_rt_inf,
    fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL g.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL g.val)).differentiableAt,
    e1, e2, ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [e3]

end GlobalTheory.CompanionTheory.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootNumberEqDifferentCoeffStatement
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_number_eq_different_coeff : ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F), standardOpenSubgroup F ≤ χ.toIdele.ker → χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)) := by
  first | exact @GlobalTheory.CompanionTheory.PartialZeta.rootNumber_eq_coeff_different | exact GlobalTheory.CompanionTheory.PartialZeta.rootNumber_eq_coeff_different | (intros; apply GlobalTheory.CompanionTheory.PartialZeta.rootNumber_eq_coeff_different <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootsEqOfDistinctValuations
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.RootsDistinctVal

theorem roots_eq_of_distinct_ord : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (y : Fin n → ℤ),
    Function.Injective y → ∀ u u' : Fin n → L, (∀ i, ordL (u i) = y i) → (∀ i, ordL (u' i) = y i) →
      ∏ i, (X - C (u i)) = ∏ i, (X - C (u' i)) → u = u' := by
  intro L _ _ n y hy u u' hu hu' hprod
  funext i
  have h0 : (∏ j, (X - C (u' j))).eval (u i) = 0 := by
    rw [← hprod, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h0
  obtain ⟨j, -, hj⟩ := h0
  have hij : u i = u' j := by simpa [sub_eq_zero] using hj
  have : i = j := hy (by rw [← hu i, ← hu' j, hij])
  rw [hij, this]

end GlobalTheory.CompanionTheory.RootsDistinctVal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SameSpanTransferMatricesStatement
section
open scoped Matrix
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions.EC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_span_transfer_matrices : ∀ {K : Type} [Field K] {n r : ℕ} (C : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin r) (Fin n) K), LinearIndependent K c → Submodule.span K (Set.range c) = Submodule.span K (Set.range C) → ∃ (T : Matrix (Fin n) (Fin r) K) (L : Matrix (Fin r) (Fin n) K), C = T * c ∧ c = L * C ∧ L * T = 1 := by
  first | exact @GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq | exact GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq | (intros; apply GlobalTheory.CompanionTheory.BruhatCoeffs.exists_coeff_matrices_of_span_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingularHermitianCongruentBlockNormalFormStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.singular_hermitian_congruent_block_normal_form : ∀ (D : D7) (r : ℕ) (β : HermE D r), β.1.det = 0 → ∃ (a : Matrix (Fin r) (Fin r) D.host.E) (t : ℕ) (γ : HermE D r), a.det ≠ 0 ∧ GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t γ ∧ β = GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a γ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF | exact GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Deg.exists_congrH_isBlockNF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianLiePreservesStable
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock

theorem lie_skew_mem_of_cpt_stable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) →
    ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  intro E _ _ _ a F hf hK X hX φ hφ
  obtain ⟨c, -, h0, -, hc, hu⟩ := GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X
  let W' : Submodule ℂ (GA E a → ℂ) := F.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ W' := by
    have := hf
    exact inferInstance
  have hcl : IsClosed (W' : Set (GA E a → ℂ)) := W'.closed_of_finiteDimensional
  let G : ℝ → GA E a → ℂ := fun t g => φ.1 (g * infGL E a (c t))
  have hG : ∀ t, G t ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hX t⟩ φ, hK _ _ hφ, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hX t⟩ : Kinf E a) = c t := Units.ext rfl
      change φ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope G 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD X φ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve φ g c X h0 hc)
  have hm : lieD X φ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hG t) (hG 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E a X φ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.Dblock
end
end

