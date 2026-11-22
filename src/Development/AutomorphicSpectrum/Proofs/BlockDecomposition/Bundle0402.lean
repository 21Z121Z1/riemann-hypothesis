import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0389
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0361
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0367
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientHeckeDecay
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.CoeffBound

theorem exists_radius {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : Module.End ℂ W) (b : ℝ) (hb0 : 0 < b)
    (hb : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < b) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < b ∧ ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ < ρ := by
  classical
  have hfin : Set.Finite (T.HasEigenvalue : Set ℂ) := Module.End.finite_hasEigenvalue T
  let s : Finset ℝ := insert 0 (hfin.toFinset.image fun μ => ‖μ‖)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  have hM : s.max' hs < b := by
    rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hb0
    · obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.1 hy
      exact hb μ (hfin.mem_toFinset.1 hμ)
  have h0 : 0 ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  refine ⟨(s.max' hs + b) / 2, by linarith, by linarith, fun μ hμ => ?_⟩
  have h1 : ‖μ‖ ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (hfin.mem_toFinset.2 hμ)))
  linarith

theorem exists_coordinates (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] :
    ∃ (d : ℕ) (e : W ≃ₗ[ℂ] (Fin d → ℂ))
      (φ : Module.End ℂ W →ₐ[ℂ] ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))),
      (∀ (S : Module.End ℂ W) (x : W), φ S (e x) = e (S x)) ∧
      ∀ (S : Module.End ℂ W) (μ : ℂ),
        Module.End.HasEigenvalue ((φ S : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) : Module.End ℂ (Fin d → ℂ)) μ →
          S.HasEigenvalue μ := by
  let e : W ≃ₗ[ℂ] (Fin (Module.finrank ℂ W) → ℂ) := (Module.finBasis ℂ W).equivFun
  let φ : Module.End ℂ W →ₐ[ℂ] ((Fin (Module.finrank ℂ W) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)) :=
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) (Fin (Module.finrank ℂ W) → ℂ)).toAlgHom.comp
      (e.conjAlgEquiv ℂ).toAlgHom
  have hφ : ∀ (S : Module.End ℂ W) (x : Fin (Module.finrank ℂ W) → ℂ), φ S x = e (S (e.symm x)) := by
    intro S x
    simp [φ, LinearEquiv.conjAlgEquiv_apply]
    rfl
  refine ⟨_, e, φ, fun S x => by rw [hφ]; simp, fun S μ h => ?_⟩
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  have hx1 : φ S x = μ • x := Module.End.mem_eigenspace_iff.1 hx.1
  rw [hφ] at hx1
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm x)
    ⟨Module.End.mem_eigenspace_iff.2 ?_, fun h0 => hx.2 (by simpa using h0)⟩
  apply e.injective
  rw [hx1]
  simp

theorem diagPow_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) : Zls.diagPow k N 0 = 1 := by
  refine Units.ext ?_
  ext i j
  simp [Zls.diagPow, Matrix.one_apply, Matrix.diagonal_apply]

theorem lamOf_zero (N : ℕ) : Zls.lamOf (0 : Fin (N - 1) → ℕ) = 0 := by
  funext i
  simp [Zls.lamOf]

theorem hecke_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hsm : IsSmooth π) {m : ℕ} (hm : 1 ≤ m)
    (j : Fin (N - 1)) (T : Module.End ℂ (fixed π (Zls.Km k N m)))
    (hT : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1))) T) (n : ℕ) :
    Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf (Pi.single j n : Fin (N - 1) → ℕ))) (T ^ n) := by
  induction n with
  | zero =>
    rw [Pi.single_zero, lamOf_zero, diagPow_zero, pow_zero]
    intro v l _
    simp
  | succ n ih =>
    have hs : (Pi.single j (n + 1) : Fin (N - 1) → ℕ) = Pi.single j n + Pi.single j 1 := by
      rw [← Pi.single_add]
    rw [hs, ((GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1 _ _), pow_succ]
    refine GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _ ih ?_
    rw [(GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).2 j]
    exact hT

theorem radius_sq_lt {q ρ : ℝ} (hq : 0 < q) (a : ℕ) (h0 : 0 ≤ ρ)
    (h : ρ < q ^ (-((a : ℝ) / 2))) : q ^ a * ρ ^ 2 < 1 := by
  have h1 : ρ ^ 2 < (q ^ (-((a : ℝ) / 2))) ^ 2 := pow_lt_pow_left₀ h h0 (by norm_num)
  have h2 : (q ^ (-((a : ℝ) / 2))) ^ 2 = (q ^ a)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast q a, ← Real.rpow_neg hq.le]
    congr 1
    push_cast
    ring
  rw [h2] at h1
  have h3 : 0 < q ^ a := pow_pos hq a
  calc q ^ a * ρ ^ 2 < q ^ a * (q ^ a)⁻¹ := mul_lt_mul_of_pos_left h1 h3
    _ = 1 := mul_inv_cancel₀ h3.ne'

theorem coeff_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → IsAdmissible π → Zls.HeckeSpectral π → ∀ m : ℕ, 1 ≤ m → ∀ v ∈ fixed π (Zls.Km k N m), ∀ l : Module.Dual ℂ V, (∀ x ∈ Zls.Km k N m, l ∘ₗ π x = l) → ∃ (C : ℝ) (ρ : Fin (N - 1) → ℝ), (∀ j, 0 ≤ ρ j) ∧ (∀ j : Fin (N - 1), (Nat.card 𝓀[k] : ℝ) ^ (((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) * ρ j ^ 2 < 1) ∧ ∀ g : Fin (N - 1) → ℕ, ‖l (π (Zls.diagPow k N (Zls.lamOf g)) v)‖ ≤ C * ∏ j, ρ j ^ g j := by
  intro k _ _ _ _ N V _ _ π hsm hadm hsp m hm v hv l hl
  have hfd : FiniteDimensional ℂ (fixed π (Zls.Km k N m)) :=
    hadm.2 _ (GlobalTheory.CompanionTheory.KmTop.isOpen_Km N m) (GlobalTheory.CompanionTheory.KmTop.isCompact_Km N m)
  have hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ) := by
    exact_mod_cast Nat.card_pos
  obtain ⟨d, e, φ, hφ, hev⟩ := exists_coordinates (fixed π (Zls.Km k N m))
  choose T hT using fun j : Fin (N - 1) =>
    GlobalTheory.CompanionTheory.HeckeKm.exists_isHeckeOp k N V π hsm m (Zls.diagPow k N (Zls.omegaVec N ((j : ℕ) + 1)))
  have hrad := fun j : Fin (N - 1) => exists_radius (T j) _ (Real.rpow_pos_of_pos hq
      (-(((((((j : ℕ) + 1) * (N - ((j : ℕ) + 1))) : ℕ) : ℝ)) / 2)))
    (fun μ hμ => hsp m hm ((j : ℕ) + 1) (by omega) (by omega) (T j) (hT j) μ hμ)
  choose ρ hρ0 hρb hρe using hrad
  have hC := fun j : Fin (N - 1) => GlobalTheory.CompanionTheory.SpecBound.norm_pow_le_of_eigenvalues_lt (Fin d → ℂ) (φ (T j)) (ρ j)
    (fun μ hμ => hρe j μ (hev _ _ hμ))
  choose C hC using hC
  have hprod : ∀ (g : Fin (N - 1) → ℕ) (s : Finset (Fin (N - 1))),
      ∃ S : Module.End ℂ (fixed π (Zls.Km k N m)),
        Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.lamOf fun j => if j ∈ s then g j else 0)) S ∧
        ‖φ S‖ ≤ ∏ j ∈ s, C j * ρ j ^ g j := by
    classical
    intro g s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ?_, ?_⟩
      · have h0 : (fun j : Fin (N - 1) => if j ∈ (∅ : Finset (Fin (N - 1))) then g j else 0) = 0 := by
          funext j; simp
        rw [h0, lamOf_zero, diagPow_zero]
        intro v l _
        simp
      · rw [map_one, Finset.prod_empty]
        exact ContinuousLinearMap.norm_id_le
    | insert a s ha ih =>
      obtain ⟨S, hS, hn⟩ := ih
      refine ⟨T a ^ g a * S, ?_, ?_⟩
      · have hsplit : (fun j : Fin (N - 1) => if j ∈ insert a s then g j else 0) =
            (Pi.single a (g a) : Fin (N - 1) → ℕ) + fun j => if j ∈ s then g j else 0 := by
          funext j
          by_cases hj : j = a
          · subst hj
            simp [ha]
          · simp [hj]
        rw [hsplit, (GlobalTheory.CompanionTheory.LamOf.lamOf_add_and_single N).1]
        exact GlobalTheory.CompanionTheory.HeckeOpMul.isHeckeOp_mul k N V π hsm m hm _ _ ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) ((GlobalTheory.CompanionTheory.LamGap.lamOf_antitone_gap_sum N _).1) _ _
          (hecke_pow π hsm hm a (T a) (hT a) (g a)) hS
      · rw [map_mul, map_pow, Finset.prod_insert ha]
        exact (norm_mul_le _ _).trans (mul_le_mul (hC a (g a)) hn (norm_nonneg _)
          ((norm_nonneg _).trans (hC a (g a))))
  let L : (Fin d → ℂ) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    (l ∘ₗ (fixed π (Zls.Km k N m)).subtype ∘ₗ (e.symm : (Fin d → ℂ) →ₗ[ℂ] _))
  let w : Fin d → ℂ := e ⟨v, hv⟩
  refine ⟨‖L‖ * ‖w‖ * ∏ j, C j, ρ, hρ0, fun j => ?_, fun g => ?_⟩
  · exact radius_sq_lt hq _ (hρ0 j) (hρb j)
  · obtain ⟨S, hS, hn⟩ := hprod g Finset.univ
    have hg : (fun j : Fin (N - 1) => if j ∈ (Finset.univ : Finset (Fin (N - 1))) then g j else 0) = g := by
      funext j; simp
    rw [hg] at hS
    have h1 : l (π (Zls.diagPow k N (Zls.lamOf g)) v) = L (φ S w) := by
      rw [show π (Zls.diagPow k N (Zls.lamOf g)) v = π (Zls.diagPow k N (Zls.lamOf g)) ((⟨v, hv⟩ : fixed π (Zls.Km k N m)) : V) from rfl,
        hS ⟨v, hv⟩ l hl, hφ]
      simp [L]
    rw [h1, Finset.prod_mul_distrib] at *
    calc ‖L (φ S w)‖ ≤ ‖L‖ * ‖φ S w‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖φ S‖ * ‖w‖) := by gcongr; exact (φ S).le_opNorm _
      _ ≤ ‖L‖ * ((∏ j, C j) * (∏ j, ρ j ^ g j) * ‖w‖) := by gcongr
      _ = ‖L‖ * ‖w‖ * (∏ j, C j) * ∏ j, ρ j ^ g j := by ring

end GlobalTheory.CompanionTheory.CoeffBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirAdj

section Alg

variable (k : Type) [Field k]

theorem mirProj_levi (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j =
    (g : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]

theorem mirProj_eq_one_of_mem (n : ℕ) (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change GlobalTheory.BZMir.blockMat k n ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [GlobalTheory.BZMir.blockMat, ← hv]
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) +
    GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.castSucc i) (Fin.castSucc j) =
    (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one (n : ℕ) (y : Mir k n) (hy : mirabolicProjection k n y = 1) : y ∈ MirUin k n := by
  have hrow : ∀ j, ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      GlobalTheory.BZMir.eLast k n j :=
    fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (y : GL (Fin (n + 1)) k)).1 y.2) j
  have hblock : ∀ i j : Fin n,
      ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
        (1 : Matrix (Fin n) (Fin n) k) i j :=
    fun i j => congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hy
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
  apply Units.ext
  ext i j
  change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
    ((y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
  rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last]
  · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow,
      GlobalTheory.BZMir.eLast]
  · simp [hrow, GlobalTheory.BZMir.eLast]

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem psiMinus_mk {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (g : GL (Fin n) k) (v : V) :
    psiMinus k τ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (τ (levi k n g) v) := rfl

theorem mk_act_unip {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (u : Mir k n) (hu : u ∈ MirUin k n) (v : V) :
    (Submodule.Quotient.mk (τ u v) : TwJacquet τ (MirUin k n) 1) = Submodule.Quotient.mk v := by
  rw [Submodule.Quotient.eq]
  refine Submodule.subset_span ⟨⟨u, hu⟩, v, ?_⟩
  simp

theorem mk_act {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V)
    (x : Mir k n) (v : V) :
    (Submodule.Quotient.mk (τ x v) : TwJacquet τ (MirUin k n) 1) =
      psiMinus k τ (mirabolicProjection k n x) (Submodule.Quotient.mk v) := by
  have hu : (levi k n (mirabolicProjection k n x))⁻¹ * x ∈ MirUin k n :=
    mem_of_mirProj_eq_one k n _ (by rw [map_mul, map_inv, mirProj_levi, inv_mul_cancel])
  have hx : x = levi k n (mirabolicProjection k n x) * ((levi k n (mirabolicProjection k n x))⁻¹ * x) := by group
  calc (Submodule.Quotient.mk (τ x v) : TwJacquet τ (MirUin k n) 1)
      = Submodule.Quotient.mk (τ (levi k n (mirabolicProjection k n x)) (τ ((levi k n (mirabolicProjection k n x))⁻¹ * x) v)) := by
        rw [← Module.End.mul_apply, ← map_mul, ← hx]
    _ = psiMinus k τ (mirabolicProjection k n x) (Submodule.Quotient.mk (τ ((levi k n (mirabolicProjection k n x))⁻¹ * x) v)) := rfl
    _ = _ := by rw [mk_act_unip τ _ hu v]

theorem twKer_le_ker {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k n) V) (σ : Representation ℂ (GL (Fin n) k) W)
    (h : Representation.IntertwiningMap τ (psiPlus k σ)) :
    twKer τ (MirUin k n) 1 ≤ LinearMap.ker h.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul,
    Representation.IntertwiningMap.toLinearMap_apply, Representation.IntertwiningMap.isIntertwining]
  rw [show psiPlus k σ (u : Mir k n) = σ (mirabolicProjection k n u) from rfl, mirProj_eq_one_of_mem k n _ u.2, map_one,
    Module.End.one_apply, sub_self]

def adjPsiEquiv {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Mir k n) V) (σ : Representation ℂ (GL (Fin n) k) W) :
    Representation.IntertwiningMap (psiMinus k τ) σ ≃ Representation.IntertwiningMap τ (psiPlus k σ) where
  toFun f := LinearMap.intertwiningMap_of_isIntertwiningMap τ (psiPlus k σ)
    (f.toLinearMap ∘ₗ (twKer τ (MirUin k n) 1).mkQ) (fun x v => by
      show f (Submodule.Quotient.mk (τ x v)) = σ (mirabolicProjection k n x) (f (Submodule.Quotient.mk v))
      rw [mk_act, Representation.IntertwiningMap.isIntertwining])
  invFun h := LinearMap.intertwiningMap_of_isIntertwiningMap (psiMinus k τ) σ
    ((twKer τ (MirUin k n) 1).liftQ h.toLinearMap (twKer_le_ker τ σ h)) (fun g q => by
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        rw [psiMinus_mk]
        simp only [Submodule.liftQ_apply, Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining]
        rw [show psiPlus k σ (levi k n g) = σ (mirabolicProjection k n (levi k n g)) from rfl, mirProj_levi])
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    apply Submodule.linearMap_qext
    rfl
  right_inv h := by
    apply Representation.IntertwiningMap.ext
    rfl

end Rep

end GlobalTheory.CompanionTheory.BZMirAdj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive
section
noncomputable section

open Matrix ValuativeRel GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZMirExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' {a b} ha hb := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    have hb' : valuation k b ≤ valuation k (s : k) := hb
    exact (Valuation.map_add _ a b).trans (max_le ha' hb')
  neg_mem' {a} ha := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    show valuation k (-a) ≤ valuation k (s : k)
    rwa [Valuation.map_neg]

theorem exists_ball_of_finset (T : Finset k) : ∃ s : kˣ, ∀ x ∈ T, x ∈ cball s := by
  classical
  refine Finset.induction_on T ?_ ?_
  · exact ⟨1, by simp⟩
  · intro a T _ ih
    obtain ⟨s, hs⟩ := ih
    by_cases h : valuation k a ≤ valuation k (s : k)
    · refine ⟨s, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hs x hx
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact h (by simp)
      refine ⟨Units.mk0 a ha0, fun x hx => ?_⟩
      show valuation k x ≤ valuation k a
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · have hx' : valuation k x ≤ valuation k (s : k) := hs x hx
        exact le_trans hx' (le_of_lt (not_le.1 h))

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

theorem continuous_colMat (n : ℕ) : Continuous (colMat k n) := by
  refine continuous_matrix fun i j => ?_
  unfold GlobalTheory.BZMir.colMat
  by_cases hj : j = Fin.last n
  · simp only [if_pos hj]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simp only [Fin.lastCases_castSucc]
      exact continuous_apply i
    · simp only [Fin.lastCases_last]
      exact continuous_const
  · simp only [if_neg hj]
    exact continuous_const

theorem continuous_unipMir (n : ℕ) :
    Continuous (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) := by
  have hval : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n v :=
    continuous_const.add (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hinv : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - GlobalTheory.BZMir.colMat k n v :=
    continuous_const.sub (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hGL : Continuous fun v : Fin n → k =>
      GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

def ballGroup (n : ℕ) (s : kˣ) : Subgroup (Mir k n) :=
  (AddSubgroup.toSubgroup (AddSubgroup.pi Set.univ fun _ : Fin n => ballSub s)).map (unipMir n)

theorem ballGroup_le (n : ℕ) (s : kˣ) : ballGroup (k := k) n s ≤ MirUin k n := by
  rintro _ ⟨v, -, rfl⟩
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

theorem coe_ballGroup (n : ℕ) (s : kˣ) : (ballGroup (k := k) n s : Set (Mir k n)) =
    (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) '' Set.univ.pi fun _ => cball s := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.coe_map]
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.toAdd v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

theorem isCompact_ballGroup (n : ℕ) (s : kˣ) : IsCompact (ballGroup (k := k) n s : Set (Mir k n)) := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.coe_ballGroup]
  exact (isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s).image
    (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_unipMir n)

theorem exhaust (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.Exhaust k := by
  classical
  intro n S hS
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.BZMirExhaust.exists_ball_of_finset
    ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p =>
      ((p.1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc p.2) (Fin.last n))
  refine ⟨GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup n s, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup_le n s, ?_,
    GlobalTheory.CompanionTheory.BZMirExhaust.isCompact_ballGroup n s⟩
  intro g hg
  have hgU := hS hg
  rw [SetLike.mem_coe, GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hgU
  obtain ⟨v, hv⟩ := hgU
  rw [Finset.mem_coe] at hg
  rw [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.mem_map]
  refine ⟨v, ?_, Subtype.ext hv⟩
  show ∀ i ∈ Set.univ, Multiplicative.toAdd v i ∈ GlobalTheory.CompanionTheory.BZMirExhaust.ballSub s
  intro i _
  have hvi := GlobalTheory.BZMir.unip_apply_castSucc_last k n v i
  rw [hv] at hvi
  show Multiplicative.toAdd v i ∈ GlobalTheory.SplitWeil.cball s
  rw [← hvi]
  exact hs _ (Finset.mem_image.2 ⟨(g, i), Finset.mem_product.2 ⟨hg, Finset.mem_univ i⟩, rfl⟩)

end GlobalTheory.CompanionTheory.BZMirExhaust

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusContractingBlockLtOneStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_contracting_block_lt_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one | exact GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one | (intros; apply GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MoyPrasadJacquetIso
section
noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasadTop

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem moyPrasadJacquetIso : GlobalTheory.Published.MoyPrasadJacquetIso := by
  intro k _ _ _ _ n s d e V _ _ π hπ
  refine ⟨mapsTo_fixed_jacU e π _, ?_, ?_⟩
  · intro v hv w hw h
    have h0 : (Submodule.Quotient.mk (v - w) : Jacquet π (unipRad k e)) = 0 := by
      rw [Submodule.Quotient.mk_sub]
      exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.DepthZeroJac.fixed_inj_smooth k n s d e V π hπ.1 (v - w) (sub_mem hv hw) h0)
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := GlobalTheory.CompanionTheory.JacquetCentral.exists_fixed_mk_eq_of_commute π hπ (Gx k e) (unipRad k e) (GlobalTheory.CompanionTheory.MoyPrasad.isOpen_Gx k n s d e)
      (GlobalTheory.T.isCompact_parahoric_subgroup k n s d e) (leviEmb k e) (leviEmb_mem_normalizer k e) ((Gx k e).comap (leviEmb k e))
      (fun _ hm => hm) (lowC k e) (GlobalTheory.T.parahoric_levi_unipotent_lower k n s d e)
      (fun U hU => by
        obtain ⟨t, ht, hc⟩ := GlobalTheory.T.central_torus_contracts_lower k n s d e U hU
        exact ⟨t, fun m _ => ht m, hc⟩) y hy
    exact ⟨v, hv, hvy⟩

end GlobalTheory.CompanionTheory.MoyPrasadTop

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEqStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_forms_mutual_shuffle_eq : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)) (h h' : ℕ) (Δ : Fin h → Segment k) (Γ : Fin h' → Segment k), IsOrderedForm Δ 𝔪 → IsOrderedForm Γ 𝔫 → InShW 𝔫 (wtW Δ) → InShW 𝔪 (wtW Γ) → 𝔪 = 𝔫 := by
  first | exact @GlobalTheory.CompanionTheory.ZcWords.eq_of_inShW_wtW | exact GlobalTheory.CompanionTheory.ZcWords.eq_of_inShW_wtW | (intros; apply GlobalTheory.CompanionTheory.ZcWords.eq_of_inShW_wtW <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidalStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_word_letters_cuspidal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Δ : Fin h → Segment k), ∀ c ∈ wtW Δ, c.IsCusp := by
  first | exact @GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | exact GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp | (intros; apply GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp <;> assumption)
end

