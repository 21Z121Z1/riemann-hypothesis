import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0001
import Formalism.GelfandTransference.HadamardGelfand.Highest
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0438
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0430
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyLineUnit
section
noncomputable section

open Matrix Filter Topology
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.RmHol

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def XA (lam : Fin n → ℤ) (B : Mat n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  fun i j => fderiv ℂ (fun x : Mat n => Rm lam x i j) 1 B

def Xu (lam : Fin n → ℤ) (a b : Fin n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  XA lam (Matrix.single a b 1)

def HolRm (lam : Fin n → ℤ) : Prop :=
  ∀ (i j : Jd n lam), ∀ g ∈ GLs n, DifferentiableAt ℂ (fun x : Mat n => Rm lam x i j) g

theorem XA_add (lam : Fin n → ℤ) (B B' : Mat n) : XA lam (B + B') = XA lam B + XA lam B' := by
  ext i j; simp [XA]

theorem XA_smul (lam : Fin n → ℤ) (c : ℂ) (B : Mat n) : XA lam (c • B) = c • XA lam B := by
  ext i j; simp [XA]

theorem XA_sum (lam : Fin n → ℤ) {ι : Type} (s : Finset ι) (B : ι → Mat n) :
    XA lam (∑ r ∈ s, B r) = ∑ r ∈ s, XA lam (B r) := by
  ext i j; simp [XA, Matrix.sum_apply]

theorem Rm_of_unit (lam : Fin n → ℤ) {x : Mat n} (h : IsUnit x.det) :
    Rm lam x = LinearMap.toMatrix (wb lam) (wb lam) (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h)) := by
  rw [Rm, dif_pos h]

theorem Rm_one (lam : Fin n → ℤ) : Rm lam (1 : Mat n) = 1 := by
  have h : IsUnit (1 : Mat n).det := by simp
  rw [Rm_of_unit lam h]
  have e : Matrix.nonsingInvUnit (1 : Mat n) h = 1 := Units.ext rfl
  rw [e, map_one]
  exact LinearMap.toMatrix_one _

theorem Rm_mul (lam : Fin n → ℤ) {x y : Mat n} (hx : IsUnit x.det) (hy : IsUnit y.det) :
    Rm lam (x * y) = Rm lam x * Rm lam y := by
  have h : IsUnit (x * y).det := by rw [Matrix.det_mul]; exact hx.mul hy
  rw [Rm_of_unit lam h, Rm_of_unit lam hx, Rm_of_unit lam hy]
  have e : Matrix.nonsingInvUnit (x * y) h = Matrix.nonsingInvUnit x hx * Matrix.nonsingInvUnit y hy := Units.ext rfl
  rw [e, map_mul]
  exact LinearMap.toMatrix_mul _ _ _

theorem isUnit_det_of_mem {g : Mat n} (hg : g ∈ GLs n) : IsUnit g.det := isUnit_iff_ne_zero.2 hg

theorem mem_GLs_of_isUnit {g : Mat n} (hg : IsUnit g.det) : g ∈ GLs n := hg.ne_zero

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne_fun this continuous_const

theorem hasDerivAt_line {lam : Fin n → ℤ} (hD : HolRm lam) (B : Mat n) (i j : Jd n lam) :
    HasDerivAt (fun t : ℂ => Rm lam (1 + t • B) i j) (XA lam B i j) 0 := by
  have h1 : HasDerivAt (fun t : ℂ => (1 : Mat n) + t • B) B 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const B).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have h2 := (hD i j 1 one_mem_GLs).hasFDerivAt
  exact h2.comp_hasDerivAt_of_eq (0 : ℂ) h1 (by simp)

theorem eventually_line_unit (B : Mat n) : ∀ᶠ t : ℂ in 𝓝 0, IsUnit ((1 : Mat n) + t • B).det := by
  have hc : Continuous fun t : ℂ => (1 : Mat n) + t • B := continuous_const.add (continuous_id.smul continuous_const)
  have : ∀ᶠ t : ℂ in 𝓝 0, (1 : Mat n) + t • B ∈ GLs n :=
    hc.continuousAt.eventually_mem (isOpen_GLs.mem_nhds (by simpa using one_mem_GLs))
  exact this.mono fun t ht => isUnit_det_of_mem ht

theorem conj_XA {lam : Fin n → ℤ} (hD : HolRm lam) {x B B' : Mat n} (hx : IsUnit x.det) (h : x * B = B' * x) :
    Rm lam x * XA lam B = XA lam B' * Rm lam x := by
  ext i j
  have hev : ∀ᶠ t : ℂ in 𝓝 0, ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j = ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j := by
    filter_upwards [eventually_line_unit B, eventually_line_unit B'] with t h1 h2
    have e : x * (1 + t • B) = (1 + t • B') * x := by
      simp only [mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, h]
    have := Rm_mul lam hx h1
    rw [e, Rm_mul lam h2 hx] at this
    have := congrFun (congrFun this i) j
    simpa [Matrix.mul_apply] using this.symm
  have hL : HasDerivAt (fun t : ℂ => ∑ k, Rm lam x i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam x i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hR : HasDerivAt (fun t : ℂ => ∑ k, Rm lam (1 + t • B') i k * Rm lam x k j)
      (∑ k, XA lam B' i k * Rm lam x k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B' i k).mul_const _
  simpa [Matrix.mul_apply] using (hL.congr_of_eventuallyEq (hev.mono fun t ht => ht.symm)).unique hR |>.symm ▸ rfl

theorem fderiv_Rm {lam : Fin n → ℤ} (hD : HolRm lam) {g : Mat n} (hg : g ∈ GLs n) (B : Mat n) (i j : Jd n lam) :
    fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B) = (Rm lam g * XA lam B) i j := by
  have hu := isUnit_det_of_mem hg
  have hline : HasDerivAt (fun t : ℂ => g + t • (g * B)) (g * B) 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const (g * B)).const_add g
    rw [one_smul] at h
    exact h
  have h1 : HasDerivAt (fun t : ℂ => Rm lam (g + t • (g * B)) i j)
      (fderiv ℂ (fun x : Mat n => Rm lam x i j) g (g * B)) 0 :=
    (hD i j g hg).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  have h2 : HasDerivAt (fun t : ℂ => ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j)
      (∑ k, Rm lam g i k * XA lam B k j) 0 :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_line hD B k j).const_mul _
  have hev : ∀ᶠ t : ℂ in 𝓝 0, Rm lam (g + t • (g * B)) i j = ∑ k, Rm lam g i k * Rm lam (1 + t • B) k j := by
    filter_upwards [eventually_line_unit B] with t ht
    have e : g + t • (g * B) = g * (1 + t • B) := by
      simp only [mul_add, mul_one, Matrix.mul_smul]
    rw [e, Rm_mul lam hu ht, Matrix.mul_apply]
  simpa [Matrix.mul_apply] using h1.unique (h2.congr_of_eventuallyEq hev)

end GlobalTheory.CompanionTheory.RmHol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBlocksOfUpper
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwaBlock

theorem exists_blocks_of_upper {K : Type} [Field K] {n a b : ℕ} (h : a + b = n) (p : GL (Fin n) K)
    (hp : p.1.BlockTriangular id) :
    ∃ (m₁ : GL (Fin a) K) (m₂ : GL (Fin b) K) (Y : Matrix (Fin a) (Fin b) K),
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m₁.val (m₁.val * Y) 0 m₂.val) = p.val := by
  set e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he
  set M : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) K := p.val.submatrix e e with hM
  have h21 : M.toBlocks₂₁ = 0 := by
    refine Matrix.ext fun i j => hp ?_
    change (e (Sum.inl j) : ℕ) < e (Sum.inr i)
    simp [he]
    omega
  have hMb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21]; exact (Matrix.fromBlocks_toBlocks M).symm
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_submatrix_equiv_self]
    exact Matrix.GeneralLinearGroup.det_ne_zero p
  have hprod : M.toBlocks₁₁.det * M.toBlocks₂₂.det ≠ 0 := by
    rw [hMb, Matrix.det_fromBlocks_zero₂₁] at hdet
    simpa using hdet
  have hA : IsUnit M.toBlocks₁₁ :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (left_ne_zero_of_mul hprod))
  have hD : IsUnit M.toBlocks₂₂ :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hprod))
  refine ⟨hA.unit, hD.unit, (hA.unit⁻¹ : GL (Fin a) K).val * M.toBlocks₁₂, ?_⟩
  have hAB : hA.unit.val * ((hA.unit⁻¹ : GL (Fin a) K).val * M.toBlocks₁₂) = M.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rw [hAB]
  change Matrix.reindex e e (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂) = p.val
  rw [← hMb, hM]
  ext i j
  simp

theorem iwasawa_parabolic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (g : GLw n w), ∃ (m : GLw a w × GLw b w) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
      ∃ k ∈ GlobalTheory.LFun.KGL w n, g = blk h w m Y * k := by
  intro E _ _ _ n a b h w g
  obtain ⟨k, c, hc, hg⟩ := GlobalTheory.ValIwasawa.iwasawa (w.adicCompletionIntegers E) (w.adicCompletion E) n g⁻¹
  have hk : Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) k ∈
      GlobalTheory.LFun.KGL w n := ⟨k, rfl⟩
  have hc' : (c⁻¹).1.BlockTriangular id := by
    haveI : Invertible c.1 := Units.invertible c
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hc
  obtain ⟨m₁, m₂, Y, hY⟩ := exists_blocks_of_upper h c⁻¹ hc'
  have hblk : blk h w (m₁, m₂) Y = c⁻¹ := by
    have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m₁.val (m₁.val * Y) 0 m₂.val)) := by
      rw [hY]; exact (c⁻¹).isUnit
    apply Units.ext
    simp only [blk]
    rw [dif_pos hU, IsUnit.unit_spec]
    exact hY
  refine ⟨(m₁, m₂), Y, _, inv_mem hk, ?_⟩
  rw [hblk, ← inv_inv g, hg, _root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.IwaBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamily
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

theorem dualFam_exists : ∀ {n : ℕ} (E : KMod n), ∃ G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ), IsDualFam E G := by
  intro n E
  obtain ⟨e, ρ', hc, hiso, hint⟩ := GlobalTheory.T.unitary_euclidean_model E
  obtain ⟨F, hgl, -, hder⟩ := GlobalTheory.T.exists_compact_lie_action _ ρ' hc hiso
  refine ⟨fun a b => e.symm.toLinearMap ∘ₗ F a b ∘ₗ e.toLinearMap, ?_, ?_⟩
  · intro a b c d
    ext1 ξ
    have h := LinearMap.congr_fun (hgl a b c d) (e ξ)
    apply e.injective
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_sub] at h ⊢
    rw [h]
    split_ifs <;> simp
  · intro X γ hX hγ ξ
    let eL : EuclideanSpace ℂ (Fin (Module.finrank ℂ E.V)) →L[ℂ] (E.V →L[ℂ] ℂ) :=
      LinearMap.toContinuousLinearMap e.symm.toLinearMap
    have heL : ∀ w, eL w = e.symm w := fun _ => rfl
    have h := (eL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder X γ hX hγ (e ξ))
    have hf : (fun t : ℝ => ξ ∘L E.ρ (γ t)⁻¹) = (eL.restrictScalars ℝ) ∘ fun t : ℝ => ρ' (γ t) (e ξ) := by
      funext t
      simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', heL, ← hint,
        LinearEquiv.symm_apply_apply]
    rw [hf]
    refine h.congr_deriv ?_
    simp only [ContinuousLinearMap.coe_restrictScalars', map_sum, map_smul, heL, LinearMap.comp_apply,
      LinearEquiv.coe_coe]

end GlobalTheory.CompanionTheory.RealCountG
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinMapEq
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace GlobalTheory.CompanionTheory.RgCz

theorem exists_fin_map_eq {a : ℕ} (m : Multiset ℂ) (hm : Multiset.card m = a) :
    ∃ χ : Fin a → ℂ, Multiset.map χ Finset.univ.val = m := by
  subst hm
  induction m using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp

theorem charInt_at {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (hr : (CG.mk π).IsRegAlg) (τ : E →+* ℂ) :
    ∃ l : Fin a → ℤ, Function.Injective l ∧
      PositivityTheory.Rg.Cz.HasChar (cx τ (lieOp π)) fun k => (l k : ℂ) := by
  obtain ⟨hnd, hint⟩ := hr τ
  obtain ⟨χ, hχ⟩ := exists_fin_map_eq ((CG.mk π).infChar τ) (CG.card_infChar (CG.mk π) τ)
  have hinf : π.HasInfChar τ (Multiset.map χ Finset.univ.val) := by
    rw [hχ]
    exact GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ
  have hcap := (GlobalTheory.capelli_cuspSub E a π τ χ hinf).2
  rw [← hχ] at hnd hint
  have hχinj : Function.Injective χ := by
    have h := Multiset.inj_on_of_nodup_map hnd
    intro s t hst
    exact h s (by simp) t (by simp) hst
  have hn : ∀ s, ∃ n : ℤ, χ s = (n : ℂ) + ((a : ℂ) - 1) / 2 := fun s =>
    hint _ (Multiset.mem_map_of_mem χ (by simp))
  choose l hl using hn
  refine ⟨l, fun s t hst => hχinj (by rw [hl, hl, hst]), fun u => ?_⟩
  have h := hcap (u - ((a : ℂ) - 1) / 2)
  rw [sub_add_cancel] at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hl k]
  ring

theorem charInt : PositivityTheory.Rg.Cz.CharInt := by
  intro E _ _ _ a π hr
  choose l hl using charInt_at π hr
  exact ⟨l, fun τ => (hl τ).1, fun τ => (hl τ).2⟩

end GlobalTheory.CompanionTheory.RgCz

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightInInvariantSubmoduleStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highest_weight_in_invariant_submodule : ∀ {n : ℕ} (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (G : Fin n → Fin n → Module.End ℂ H), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ N : Submodule ℂ H, N ≠ ⊥ → (∀ a b, ∀ w ∈ N, G a b w ∈ N) → ∃ (μ : Fin n → ℝ) (v : H), v ∈ N ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) G μ v := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable | exact GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable | (intros; apply GlobalTheory.CompanionTheory.RealCountG.HwStable.exists_highest_of_stable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedBallIndicator
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirLevi.Bump

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

def IntM (m : GL (Fin n) k) : Prop :=
  ∀ i, Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i) ∈ polyBall (k := k) n 1

theorem intM_one : IntM (1 : GL (Fin n) k) := by
  intro i j
  show valuation k (((1 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j) ≤ valuation k ((1 : kˣ) : k)
  by_cases h : i = j
  · simp [h]
  · simp [one_apply, h]

theorem IntM.mulVec_mem {m : GL (Fin n) k} (hm : IntM m) {s : kˣ} {v : Fin n → k}
    (hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s) :
    Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k).mulVec v) ∈ polyBall (k := k) n s :=
  fun i => dotProduct_mem_cball (a := 1) (b := s) (c := s) (by simp) (hm i) hv

theorem isOpen_intM : IsOpen {m : GL (Fin n) k | IntM m} := by
  have h : {m : GL (Fin n) k | IntM m} = ⋂ i, (fun m : GL (Fin n) k =>
      Multiplicative.ofAdd ((m : Matrix (Fin n) (Fin n) k) i)) ⁻¹'
        (polyBall (k := k) n 1 : Set (Multiplicative (Fin n → k))) := by
    ext m
    simp [IntM]
  rw [h]
  refine isOpen_iInter_of_finite fun i => (isOpen_polyBall n 1).preimage ?_
  exact continuous_ofAdd.comp (continuous_pi fun j => Units.continuous_val.matrix_elem i j)

theorem continuous_colv : Continuous (colv : Mir k n → Fin n → k) :=
  continuous_pi fun i => (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)

theorem continuous_mvec : Continuous (mvec : Mir k n → Fin n → k) := by
  have h1 : Continuous fun x : Mir k n =>
      (((mirabolicProjection k n x)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) :=
    Units.continuous_val.comp (continuous_inv.comp (GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n))
  exact h1.matrix_mulVec continuous_colv

theorem continuous_lv : Continuous (lv k n) :=
  continuous_induced_rng.2 (GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n)

def bumpF (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E) (g : Mir k n) : E :=
  @ite _ (Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s) (Classical.propDecidable _)
    (ρ (lv k n (mirabolicProjection k n g)) e) 0

variable (ρ : Representation ℂ (LH k n) E) (s : kˣ) (e : E)

theorem bumpF_levi_mul (m : GL (Fin n) k) (g : Mir k n) :
    bumpF ρ s e (levi k n m * g) = ρ (lv k n m) (bumpF ρ s e g) := by
  unfold bumpF
  rw [mvec_levi_mul, map_mul, mirProj_levi, map_mul, map_mul, Module.End.mul_apply]
  split_ifs <;> simp

theorem bumpF_equi (h : LH k n) (g : Mir k n) :
    bumpF ρ s e ((h : Mir k n) * g) = ρ h (bumpF ρ s e g) := by
  obtain ⟨m, hm⟩ := h.2
  have e1 : h = lv k n m := Subtype.ext hm.symm
  rw [e1]
  exact bumpF_levi_mul ρ s e m g

theorem bumpF_levi_uv (q : GL (Fin n) k) (w : Fin n → k) :
    bumpF ρ s e (levi k n q * uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _)
        (ρ (lv k n q) e) 0 := by
  unfold bumpF
  rw [mvec_levi_mul_uv, map_mul, mirProj_levi, mirProj_uv, mul_one]

theorem bumpF_uv (w : Fin n → k) :
    bumpF ρ s e (uv n w) =
      @ite _ (Multiplicative.ofAdd w ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  have h := bumpF_levi_uv ρ s e 1 w
  rw [map_one (levi k n), one_mul, map_one (lv k n), map_one ρ] at h
  simpa using h

theorem mul_formula (p m : GL (Fin n) k) (v a : Fin n → k) :
    (levi k n p * uv n v) * (levi k n m * uv n a) = levi k n (p * m) *
      uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) := by
  rw [uv_add, map_mul, mul_assoc (levi k n p), ← mul_assoc (uv n v), uv_mul_levi]
  simp only [mul_assoc]

theorem bumpF_fix (p m : GL (Fin n) k) (v a : Fin n → k) (h1 : IntM m) (h2 : IntM m⁻¹)
    (hm : ρ (lv k n m) e = e) (ha : Multiplicative.ofAdd a ∈ polyBall (k := k) n s) :
    bumpF ρ s e ((levi k n p * uv n v) * (levi k n m * uv n a)) = bumpF ρ s e (levi k n p * uv n v) := by
  rw [mul_formula, bumpF_levi_uv, bumpF_levi_uv, map_mul, map_mul, Module.End.mul_apply, hm]
  have hiff : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v + a) ∈
      polyBall (k := k) n s ↔ Multiplicative.ofAdd v ∈ polyBall (k := k) n s := by
    constructor
    · intro h
      have h3 : Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) ∈
          polyBall (k := k) n s := by
        have h4 := mul_mem h (inv_mem ha)
        rwa [ofAdd_add, mul_inv_cancel_right] at h4
      have h5 := h1.mulVec_mem h3
      rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h5
    · intro h
      rw [ofAdd_add]
      exact mul_mem (h2.mulVec_mem h) ha
  by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) n s
  · rw [if_pos hv, if_pos (hiff.2 hv)]
  · rw [if_neg hv, if_neg (fun c => hv (hiff.1 c))]

def nbhd : Set (Mir k n) :=
  {x | IntM (mirabolicProjection k n x) ∧ IntM (mirabolicProjection k n x)⁻¹ ∧ ρ (lv k n (mirabolicProjection k n x)) e = e ∧
    Multiplicative.ofAdd (mvec x) ∈ polyBall (k := k) n s}

theorem isOpen_nbhd (hρ : IsSmooth ρ) : IsOpen (nbhd ρ s e) := by
  have hp := GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n
  refine (isOpen_intM.preimage hp).inter ((isOpen_intM.preimage (continuous_inv.comp hp)).inter
    (((hρ e).preimage (continuous_lv.comp hp)).inter ?_))
  exact (isOpen_polyBall n s).preimage (continuous_ofAdd.comp continuous_mvec)

theorem one_mem_nbhd : (1 : Mir k n) ∈ nbhd ρ s e := by
  have hm : mvec (1 : Mir k n) = 0 := by
    have h := mvec_uv (k := k) n 0
    rwa [uv_zero] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_one]; exact intM_one
  · rw [map_one, inv_one]; exact intM_one
  · simp
  · rw [hm]; exact one_mem _

theorem bumpF_mul_nbhd (g x : Mir k n) (hx : x ∈ nbhd ρ s e) :
    bumpF ρ s e (g * x) = bumpF ρ s e g := by
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have h := bumpF_fix ρ s e (mirabolicProjection k n g) (mirabolicProjection k n x) (mvec g) (mvec x) h1 h2 h3 h4
  rwa [← decomp g, ← decomp x] at h

theorem bumpF_mem : bumpF ρ s e ∈ indSpace (LH k n) ρ := fun h g => bumpF_equi ρ s e h g

theorem bumpF_smooth (hρ : IsSmooth ρ) :
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) ∈ smoothPart (ind (LH k n) ρ) := by
  have hfix : nbhd ρ s e ⊆ (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
      (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ) : Set (Mir k n)) := by
    intro x hx
    apply Subtype.ext
    funext g
    exact bumpF_mul_nbhd ρ s e g x hx
  exact (GlobalTheory.CompanionTheory.LeibPhi.stabSub (ind (LH k n) ρ)
    (⟨bumpF ρ s e, bumpF_mem ρ s e⟩ : indSpace (LH k n) ρ)).isOpen_of_mem_nhds (g := 1)
    (Filter.mem_of_superset ((isOpen_nbhd ρ s e hρ).mem_nhds (one_mem_nbhd ρ s e)) hfix)

theorem bumpF_support : ∃ C : Set (Mir k n), IsCompact C ∧ ∀ g, bumpF ρ s e g ≠ 0 →
    ∃ h ∈ LH k n, ∃ c ∈ C, g = h * c := by
  refine ⟨unipIn k n '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))),
    (isCompact_polyBall n s).image (continuous_unipIn n), fun g hg => ?_⟩
  have hL : Multiplicative.ofAdd (mvec g) ∈ polyBall (k := k) n s := by
    by_contra hc
    exact hg (if_neg hc)
  exact ⟨levi k n (mirabolicProjection k n g), ⟨_, rfl⟩, uv n (mvec g), ⟨_, hL, rfl⟩, decomp g⟩

theorem exists_bump_restr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E]
    (ρ : Representation ℂ (LH k n) E), IsSmooth ρ → ∀ (s : kˣ) (e : E),
    ∃ b : cIndSpace (LH k n) ρ, ∀ v : Fin n → k, restr ρ b v =
      @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) n s) (Classical.propDecidable _) e 0 := by
  intro k _ _ _ _ n E _ _ ρ hρ s e
  exact ⟨⟨⟨⟨bumpF ρ s e, bumpF_mem ρ s e⟩, bumpF_smooth ρ s e hρ⟩, bumpF_support ρ s e⟩,
    fun v => bumpF_uv ρ s e v⟩

end GlobalTheory.CompanionTheory.MirLevi.Bump

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDualStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_vector_zero_of_dual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J, (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed | exact GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed | (intros; apply GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed <;> assumption)
end

