import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0699
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelImpliesRegularClassFinite
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellInducingCharacter
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZRes

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hpg_wGL_conj_apply {i t : ℕ} (h : (i + 1) + t = i + t + 1) (G : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * G * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (G : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  have e' : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) =
      (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  rw [Units.val_mul, Units.val_mul, e, e']
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem hpg_wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (y : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) y) = ePG i t y := by
  simp [wPerm]

theorem hpg_leviProj_wGL_conj {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : HPG k i t)
    (hq : wGL k h * ((g : Mir k (i + t)) : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (x : Bool) :
    leviProj k (two (stdSum h)) ⟨_, hq⟩ x = leviProj k (ePG i t) (hpgIncl k i t g) x := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [leviProj_apply, leviProj_apply]
  show ((wGL k h * ((g : Mir k (i + t)) : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) _ _ = _
  rw [hpg_wGL_conj_apply, hpg_wPerm_two, hpg_wPerm_two]
  rfl

theorem open_orbit_twist : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {i j : ℕ} (h : (i + 1) + (j + 1) = i + (j + 1) + 1) (π₁ : Representation ℂ (GL (Fin (i + 1)) k) V) (π₂ : Representation ℂ (GL (Fin (j + 1)) k) W) (g : HPG k i (j + 1)) (hq : wGL k h * ((g : Mir k (i + (j + 1))) : GL (Fin (i + (j + 1) + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h))) (v : ⨂[ℂ] x, TwoT V W x), ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g (tE V W v) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ v) := by
  intro k _ _ _ _ V W _ _ _ _ i j h π₁ π₂ g hq v
  have hf : leviProj k (two (stdSum h)) ⟨_, hq⟩ false = ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k) :=
    hpg_leviProj_wGL_conj h g hq false
  have ht : leviProj k (two (stdSum h)) ⟨_, hq⟩ true = (pgProj k i (j + 1) g).2 :=
    hpg_leviProj_wGL_conj h g hq true
  have hδ : (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) =
      (absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k)) : ℂ) *
      (absPow k (((-((i + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det (pgProj k i (j + 1) g).2) : ℂ) := by
    have e := deltaHalf_two (k := k) (a := Fin (i + 1)) (b := Fin (j + 1))
      (leviProj k (two (stdSum h)) ⟨_, hq⟩ false, leviProj k (two (stdSum h)) ⟨_, hq⟩ true)
    have e2 : leviTwo k (Fin (i + 1)) (Fin (j + 1))
        (leviProj k (two (stdSum h)) ⟨_, hq⟩ false, leviProj k (two (stdSum h)) ⟨_, hq⟩ true) =
        leviProj k (two (stdSum h)) ⟨_, hq⟩ := by
      funext x
      cases x <;> rfl
    rw [e2, hf, ht] at e
    rw [e, Units.val_mul]
    simp only [Fintype.card_fin]
    push_cast
    rfl
  have key : ∀ x : ∀ b, TwoT V W b, ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
      (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g
        (tE V W (PiTensorProduct.tprod ℂ x)) = tE V W (sQ h π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) := by
    intro x
    have hr : tE V W (sQ h π₁ π₂ ⟨_, hq⟩ (PiTensorProduct.tprod ℂ x)) =
        (deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) •
          (π₁ (leviProj k (two (stdSum h)) ⟨_, hq⟩ false) (x false) ⊗ₜ[ℂ]
            π₂ (leviProj k (two (stdSum h)) ⟨_, hq⟩ true) (x true)) := by
      show tE V W ((deltaHalf k (Two (Fin (i + 1)) (Fin (j + 1))) (leviProj k (two (stdSum h)) ⟨_, hq⟩) : ℂ) •
        piTensor (twoRep π₁ π₂) (leviProj k (two (stdSum h)) ⟨_, hq⟩) (PiTensorProduct.tprod ℂ x)) = _
      rw [piTensor_tprod, map_smul, Exponents.boolTensorEquiv_tprod]
      rfl
    rw [hr, hf, ht, hδ, Exponents.boolTensorEquiv_tprod]
    refine (extTensor_tmul _ _ _ (x false) (x true)).trans ?_
    show ((absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k)) : ℂ) •
        π₁ ((pgProj k i (j + 1) g).1 : GL (Fin (i + 1)) k) (x false)) ⊗ₜ[ℂ]
      ((absPow k (((-((i + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) (GeneralLinearGroup.det (pgProj k i (j + 1) g).2) : ℂ) •
        π₂ (pgProj k i (j + 1) g).2 (x true)) = _
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm]
  let A : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W := ((extTensor (mtw (gres (⟨V, π₁⟩ : GRep k (i + 1))) (((j + 1 : ℕ) : ℝ) / 2)).ρ
      (GRep.tw (⟨W, π₂⟩ : GRep k (j + 1)) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (j + 1))) g
  have hlin : A ∘ₗ (tE V W).toLinearMap = (tE V W).toLinearMap ∘ₗ sQ h π₁ π₂ ⟨_, hq⟩ :=
    PiTensorProduct.ext (MultilinearMap.ext fun x => key x)
  exact LinearMap.congr_fun hlin v

end GlobalTheory.CompanionTheory.BZRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenDoubleCosetCriterion
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.OpenOrbit

section Perm

variable {k : Type} [Field k]

def permGL {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) k where
  val := (1 : Matrix _ _ k).submatrix σ id
  inv := (1 : Matrix _ _ k).submatrix id σ
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, mul_one]
    exact Matrix.submatrix_one_equiv σ
  inv_val := by
    rw [← Matrix.submatrix_mul _ _ _ σ _ σ.bijective, mul_one]
    exact Matrix.submatrix_one_equiv (Equiv.refl _)

theorem permGL_mul_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (B : Matrix (Fin N) (Fin N) k) (a c : Fin N) :
    (((permGL σ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) * B) a c = B (σ a) c := by
  show (((1 : Matrix (Fin N) (Fin N) k).submatrix σ id) * B) a c = _
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem vecMul_single_one {N : ℕ} (M : Matrix (Fin N) (Fin N) k) (a : Fin N) :
    vecMul (Pi.single a 1) M = M a := by
  ext c
  simp [vecMul, dotProduct, Pi.single_apply]

end Perm

section Orbit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdSum_inr_ne_inl {r t N : ℕ} (h : r + t = N) (j : Fin t) (l : Fin r) :
    stdSum h (Sum.inr j) ≠ stdSum h (Sum.inl l) := fun e => by
  simpa using (stdSum h).injective e

theorem wPerm_first {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    wPerm h (stdSum h (Sum.inl (Fin.last i))) = Fin.last (i + t) := by
  have e : (two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  show ePG i t ((two (stdSum h)).symm (stdSum h (Sum.inl (Fin.last i)))) = _
  rw [e]
  exact ePG_false_last i t

theorem lastRow_wInv {i t : ℕ} (h : (i + 1) + t = i + t + 1) :
    vecMul (eLast k (i + t)) (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) =
      Pi.single (stdSum h (Sum.inl (Fin.last i))) 1 := by
  rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one]
  ext c
  show (1 : Matrix _ _ k).submatrix id (wPerm h) (Fin.last (i + t)) c = _
  rw [← wPerm_first h]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem lastRow_inv {i t : ℕ} (h : (i + 1) + t = i + t + 1) (q p : GL (Fin (i + t + 1)) k)
    (hp : p ∈ Mir k (i + t)) :
    vecMul (eLast k (i + t)) (((q * wGL k h * p)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) =
      ((q⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (stdSum h (Sum.inl (Fin.last i))) := by
  have hp' : vecMul (eLast k (i + t)) ((p⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) = eLast k (i + t) :=
    (Mir k (i + t)).inv_mem hp
  rw [show (q * wGL k h * p)⁻¹ = p⁻¹ * (wGL k h)⁻¹ * q⁻¹ by simp [mul_assoc], Units.val_mul, Units.val_mul,
    ← vecMul_vecMul, ← vecMul_vecMul, hp', lastRow_wInv, vecMul_single_one]

theorem exists_ne_of_mem {i t : ℕ} (h : (i + 1) + t = i + t + 1) (q p : GL (Fin (i + t + 1)) k)
    (hq : q ∈ parab k (two (stdSum h))) (hp : p ∈ Mir k (i + t)) :
    ∃ a : Fin (i + 1), (((q * wGL k h * p)⁻¹ : GL (Fin (i + t + 1)) k) :
      Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  let r : parab k (two (stdSum h)) := ⟨q⁻¹, inv_mem hq⟩
  let M : GL (Fin (i + 1)) k := leviProj k (two (stdSum h)) r false
  have hrow : ∀ a, (M : Matrix (Fin (i + 1)) (Fin (i + 1)) k) (Fin.last i) a = 0 := fun a => by
    have e := congrFun (lastRow_inv h q p hp) (stdSum h (Sum.inl a))
    rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one, hc a] at e
    exact e.symm
  have h1 : ((M : Matrix (Fin (i + 1)) (Fin (i + 1)) k) *
      ((M⁻¹ : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k)) (Fin.last i) (Fin.last i) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel]
    simp
  rw [Matrix.mul_apply] at h1
  simp [hrow] at h1

theorem exists_parab_row {i t : ℕ} (h : (i + 1) + t = i + t + 1) (y : Fin (i + t + 1) → k) (a : Fin (i + 1))
    (ha : y (stdSum h (Sum.inl a)) ≠ 0) :
    ∃ b ∈ parab k (two (stdSum h)),
      (b : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (stdSum h (Sum.inl (Fin.last i))) = y := by
  obtain ⟨b, -, -, hb⟩ := exists_rowSec (k := k) (stdSum h (Sum.inl a))
  have hb0 := hb y ha
  have hbQ : b y ∈ parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) l j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · rw [hb0, two_true, two_false, Matrix.updateRow_ne (stdSum_inr_ne_inl h l a),
        Matrix.one_apply_ne (stdSum_inr_ne_inl h l j)]
    · exact absurd hlt (by decide)
  have hmQ : (permGL (Equiv.swap (stdSum h (Sum.inl a)) (stdSum h (Sum.inl (Fin.last i)))) : GL (Fin (i + t + 1)) k) ∈
      parab k (two (stdSum h)) := by
    refine mem_parab_iff.2 ?_
    rintro (_ | _) (_ | _) l j hlt
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · show (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Equiv.swap (stdSum h (Sum.inl a)) (stdSum h (Sum.inl (Fin.last i))) (stdSum h (Sum.inr l)))
        (stdSum h (Sum.inl j)) = 0
      rw [Equiv.swap_apply_of_ne_of_ne (stdSum_inr_ne_inl h l a) (stdSum_inr_ne_inl h l _),
        Matrix.one_apply_ne (stdSum_inr_ne_inl h l j)]
    · exact absurd hlt (by decide)
  refine ⟨_, mul_mem hmQ hbQ, ?_⟩
  funext c
  rw [Units.val_mul, permGL_mul_apply, Equiv.swap_apply_right, hb0, Matrix.updateRow_self]

theorem mem_of_ne {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a : Fin (i + 1))
    (ha : ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
      (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0) :
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) := by
  obtain ⟨b, hbQ, hrow⟩ := exists_parab_row h _ a ha
  refine ⟨b⁻¹, inv_mem hbQ, (wGL k h)⁻¹ * b * g, ?_, by group⟩
  show vecMul (eLast k (i + t)) (((wGL k h)⁻¹ * b * g : GL (Fin (i + t + 1)) k) : Matrix _ _ k) = eLast k (i + t)
  have e : ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
      vecMul (eLast k (i + t)) ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix _ _ k) := by
    rw [show eLast k (i + t) = Pi.single (Fin.last (i + t)) 1 from rfl, vecMul_single_one]
  rw [Units.val_mul, Units.val_mul, ← vecMul_vecMul, ← vecMul_vecMul, lastRow_wInv, vecMul_single_one, hrow, e,
    vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, vecMul_one]

end Orbit

end GlobalTheory.CompanionTheory.BZRes.OpenOrbit

namespace GlobalTheory.CompanionTheory.BZRes

theorem mem_dcos_wGL_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1), 0 < t → ∀ g : GL (Fin (i + t + 1)) k,
    g ∈ dcos (parab k (two (stdSum h))) (Mir k (i + t)) (wGL k h) ↔
      ∃ a : Fin (i + 1), ((g⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)
        (Fin.last (i + t)) (stdSum h (Sum.inl a)) ≠ 0 := by
  intro k _ _ _ _ i t h _ g
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩
    exact OpenOrbit.exists_ne_of_mem h q p hq hp
  · rintro ⟨a, ha⟩
    exact OpenOrbit.mem_of_ne h g a ha

end GlobalTheory.CompanionTheory.BZRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBound
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem orbFin_of_latBound : LatBound → OrbFin := by
  intro hL D θ hθ W m hm x₀ hx N hN
  obtain ⟨C, hC⟩ := hL D θ hθ W W.rank N hN
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨-, g2, g3, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hfd : IsFundamentalDomain (GQ W) (stdDom (GQ W)) m := isFundamentalDomain_stdDom _ m
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W m _ hm hfd
  have hcnt : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  have hNc : Continuous N :=
    (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ W.rank W.rank N
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ W.rank W.rank N hN)).1
  have hfm : Measurable fun h : GA D W => ‖N (ww W x₀ h)‖ₑ :=
    (hNc.comp (continuous_ww x₀)).enorm.measurable

  classical
  have hu : ∀ γ : GQ W, ∃ u : GL (Fin W.rank) D.host.E, mt W γ.1 = rat u.1 := fun γ => by
    obtain ⟨u, -, hu⟩ := γ.2
    exact ⟨u, (congrArg Units.val hu).symm⟩
  choose u hu using hu
  have hxu : IsUnit x₀.det := isUnit_iff_ne_zero.2 hx
  have hrk : ∀ γ : GQ W, ((u γ).1 * x₀).rank = W.rank := fun γ => by
    have h1 : IsUnit ((u γ).1 * x₀) := by
      refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (u γ).isUnit).mul hxu
    simpa using Matrix.rank_of_isUnit _ h1
  let e : GQ W → {x : Matrix (Fin W.rank) (Fin W.rank) D.host.E // x.rank = W.rank} :=
    fun γ => ⟨(u γ).1 * x₀, hrk γ⟩
  have he : Function.Injective e := fun γ γ' h => by
    have h1 : (u γ).1 * x₀ = (u γ').1 * x₀ := congrArg Subtype.val h
    have h2 : (u γ).1 = (u γ').1 := by
      have hxi : x₀ * x₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
      calc (u γ).1 = (u γ).1 * x₀ * x₀⁻¹ := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
        _ = (u γ').1 * x₀ * x₀⁻¹ := by rw [h1]
        _ = (u γ').1 := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
    exact Subtype.ext (GlobalTheory.MixModel.mt_injective W (by rw [hu, hu, h2]))
  have hterm : ∀ (γ : GQ W) (h : GA D W), ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ = ‖N (mm (mt W h⁻¹) (rat (e γ).1))‖ₑ := fun γ h => by
    have h1 : (γ⁻¹ • h)⁻¹ = h⁻¹ * γ.1 := by
      change ((γ.1)⁻¹ * h)⁻¹ = _
      rw [mul_inv_rev, inv_inv]
    have h2 : mt W (h⁻¹ * γ.1) = mt W h⁻¹ * mt W γ.1 := rfl
    have h3 : ww W x₀ (γ⁻¹ • h) = mm (mt W h⁻¹) (rat (e γ).1) := by
      simp only [ww, e]
      rw [h1, h2, hu, rat_mul]
      exact Matrix.mul_assoc _ _ _
    rw [h3]
  rw [hfd.lintegral_eq_tsum']
  rw [← lintegral_tsum fun γ => ?_]
  · calc ∫⁻ h in stdDom (GQ W), ∑' γ : GQ W, ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ ∂m
        ≤ ∫⁻ _ in stdDom (GQ W), (C : ℝ≥0∞) ∂m := lintegral_mono fun h => by
          simp only [hterm]
          exact (ENNReal.tsum_comp_le_tsum_of_injective he
            (fun x => ‖N (mm (mt W h⁻¹) (rat x.1))‖ₑ)).trans (hC h)
      _ = C * m (stdDom (GQ W)) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin
  · exact (hfm.comp (measurable_const_smul γ⁻¹)).aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIffFrameParabolic
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelFrame.ParStab

section Linear

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def firstCols (R : Type) [CommRing R] (ι : Type) [DecidableEq ι] : Matrix (ι ⊕ ι) ι R := Matrix.fromRows 1 0

theorem mul_firstCols (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) : g * firstCols R ι = g.toCols₁ := by
  ext r j
  simp [firstCols, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]

theorem firstCols_mul_apply_inl (m : Matrix ι ι R) (i j : ι) : (firstCols R ι * m) (Sum.inl i) j = m i j := by
  simp [firstCols, Matrix.mul_apply, Matrix.one_apply]

theorem firstCols_mul_apply_inr (m : Matrix ι ι R) (i j : ι) : (firstCols R ι * m) (Sum.inr i) j = 0 := by
  simp [firstCols, Matrix.mul_apply]

theorem firstCols_cancel {m m' : Matrix ι ι R} (h : firstCols R ι * m = firstCols R ι * m') : m = m' := by
  ext i j
  rw [← firstCols_mul_apply_inl m, h, firstCols_mul_apply_inl]

theorem low_zero_of_mul {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} {m : Matrix ι ι R} (h : g * firstCols R ι = firstCols R ι * m)
    (i j : ι) : g (Sum.inr i) (Sum.inl j) = 0 := by
  have := congrFun (congrFun h (Sum.inr i)) j
  rwa [mul_firstCols, firstCols_mul_apply_inr] at this

theorem mul_eq_of_low_zero {g : Matrix (ι ⊕ ι) (ι ⊕ ι) R} (h : ∀ i j, g (Sum.inr i) (Sum.inl j) = 0) :
    g * firstCols R ι = firstCols R ι * g.toBlocks₁₁ := by
  ext r j
  rcases r with i | i
  · rw [firstCols_mul_apply_inl, mul_firstCols]; rfl
  · rw [firstCols_mul_apply_inr, mul_firstCols]; exact h i j

theorem mem_stab_iff (g : GL (ι ⊕ ι) R) : g ∈ stab R (Sum.inl '' (Set.univ : Set ι)) ↔
    ∀ i j, (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl j) = 0 ∧
      ((g⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inr i) (Sum.inl j) = 0 := by
  constructor
  · intro h i j
    exact h (Sum.inr i) (by simp) (Sum.inl j) (by simp)
  · intro h r hr c hc
    obtain ⟨j, -, rfl⟩ := hc
    rcases r with i | i
    · exact absurd ⟨i, Set.mem_univ _, rfl⟩ hr
    · exact h i j

theorem exists_mul_eq_iff_mem_stab (B x : GL (ι ⊕ ι) R) (D : Matrix (ι ⊕ ι) ι R) (T : GL ι R)
    (hB : (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι = D * (T : Matrix ι ι R)) :
    (∃ t : GL ι R, (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * (t : Matrix ι ι R)) ↔
      B⁻¹ * x * B ∈ stab R (Sum.inl '' (Set.univ : Set ι)) := by
  have hBi : ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hTi : (T : Matrix ι ι R) * ((T⁻¹ : GL ι R) : Matrix ι ι R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hD : D = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
    rw [hB, Matrix.mul_assoc, hTi, Matrix.mul_one]
  have hC : ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (T : Matrix ι ι R) = firstCols R ι := by
    rw [Matrix.mul_assoc, ← hB, ← Matrix.mul_assoc, hBi, Matrix.one_mul]
  have hinv : (B⁻¹ * x * B)⁻¹ = B⁻¹ * x⁻¹ * B := by group
  have key : ∀ (g : GL (ι ⊕ ι) R) (s : Matrix ι ι R), (g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * s →
      ((B⁻¹ * g * B : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι =
        firstCols R ι * (((T⁻¹ : GL ι R) : Matrix ι ι R) * s * (T : Matrix ι ι R)) := by
    intro g s hg
    calc _ = ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D) * (T : Matrix ι ι R) := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rw [hB]
      _ = ((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (s * (T : Matrix ι ι R)) := by
          rw [hg]; simp only [Matrix.mul_assoc]
      _ = (((B⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D * (T : Matrix ι ι R)) *
            (((T⁻¹ : GL ι R) : Matrix ι ι R) * s * (T : Matrix ι ι R)) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (T : Matrix ι ι R) (((T⁻¹ : GL ι R) : Matrix ι ι R)), hTi, Matrix.one_mul]
      _ = _ := by rw [hC]
  constructor
  · rintro ⟨t, ht⟩
    have hx' : ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D = D * ((t⁻¹ : GL ι R) : Matrix ι ι R) := by
      have h1 : ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : (t : Matrix ι ι R) * ((t⁻¹ : GL ι R) : Matrix ι ι R) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc _ = ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (D * ((t : Matrix ι ι R) * ((t⁻¹ : GL ι R) : Matrix ι ι R))) := by
            rw [h2, Matrix.mul_one]
        _ = ((x⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * D) * ((t⁻¹ : GL ι R) : Matrix ι ι R) := by
            rw [ht]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [mem_stab_iff]
    intro i j
    refine ⟨low_zero_of_mul (key x _ ht) i j, ?_⟩
    rw [hinv]
    exact low_zero_of_mul (key x⁻¹ _ hx') i j
  · intro hy
    rw [mem_stab_iff] at hy
    set y : GL (ι ⊕ ι) R := B⁻¹ * x * B with hydef
    have e1 := mul_eq_of_low_zero fun i j => (hy i j).1
    have e2 := mul_eq_of_low_zero fun i j => (hy i j).2
    set m := (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ with hm
    set m' := ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R).toBlocks₁₁ with hm'
    have hyy : (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hyy' : ((y⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmm : m * m' = 1 := by
      apply firstCols_cancel
      rw [← Matrix.mul_assoc, ← e1, Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hyy, Matrix.one_mul, Matrix.mul_one]
    have hmm' : m' * m = 1 := by
      apply firstCols_cancel
      rw [← Matrix.mul_assoc, ← e2, Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, hyy', Matrix.one_mul, Matrix.mul_one]
    let u : GL ι R := ⟨m, m', hmm, hmm'⟩
    refine ⟨T * u * T⁻¹, ?_⟩
    have hx : (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) =
        (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [hydef]
      group
    calc _ = (x : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
          conv_lhs => rw [hD]
          simp only [Matrix.mul_assoc]
      _ = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * ((y : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι) * ((T⁻¹ : GL ι R) : Matrix ι ι R) := by
          rw [hx]; simp only [Matrix.mul_assoc]
      _ = (B : Matrix (ι ⊕ ι) (ι ⊕ ι) R) * firstCols R ι * (m * ((T⁻¹ : GL ι R) : Matrix ι ι R)) := by
          rw [e1]; simp only [Matrix.mul_assoc]
      _ = D * (T : Matrix ι ι R) * (m * ((T⁻¹ : GL ι R) : Matrix ι ι R)) := by rw [hB]
      _ = _ := by
          simp only [Units.val_mul, Matrix.mul_assoc]
          rfl

end Linear

theorem exists_isPar_iff_mem_uQ : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (t₀ : GL (Fin n) E), b.1.toCols₁ = diagCols (Fin n) * t₀.1 → ∀ x : G2 σ Y, (∃ t, IsPar x t) ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uQ ε (Set.univ : Set (Fin n)) := by
  intro F E _ _ _ _ _ σ n Y χ ε b hb t₀ ht x
  have hdiag : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map (inclR (F := F) (E := E) (AF F)) =
      diagCols (Fin n) := by
    ext r j
    rcases r with i | i <;> by_cases h : i = j <;> simp [diagCols, Matrix.one_apply, h]
  have hB : ((bA (F := F) b : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * firstCols (AE F E) (Fin n) =
      (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)) * ((Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) t₀ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [mul_firstCols, ← hdiag]
    have ht' : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E) * (t₀.1 : Matrix (Fin n) (Fin n) E) := ht
    have := congrArg (fun M : Matrix (Fin n ⊕ Fin n) (Fin n) E => M.map (inclR (F := F) (E := E) (AF F))) ht'
    simp only [Matrix.map_mul] at this
    exact this
  have h := exists_mul_eq_iff_mem_stab (bA (F := F) b) x.1 (diagCols (Fin n)) _ hB
  rw [PositivityTheory.RgEis.Ad.uQ, Subgroup.mem_subgroupOf, frameEquiv_val]
  exact h

end GlobalTheory.CompanionTheory.SiegelFrame.ParStab
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelImpliesRegularClassFiniteStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_implies_regular_class_finite : PositivityTheory.ThKR.SiegelCore → MainStatements.RegularCuspidalTrace.RegClassFin := by
  first | exact @GlobalTheory.CompanionTheory.CFin.regClassFin | exact GlobalTheory.CompanionTheory.CFin.regClassFin | (intros; apply GlobalTheory.CompanionTheory.CFin.regClassFin <;> assumption)
end

