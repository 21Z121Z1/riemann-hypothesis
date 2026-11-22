import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0449
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0462

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReversedMinorProductMemHarmonicRowHighest
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RenamedMinors

variable {D : D7} {S T : HSp D}

def phi (C : Ctx S T) : MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
  C.toH.comp (MvPolynomial.rename fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2))

theorem phi_varF_pos (C : Ctx S T) (τ : D.what₂.Tau) (b a : ℕ) (hb : b < C.X.p0) (ha : a < S.rank) :
    phi C (varF τ b a) = MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) *
      MvPolynomial.X (C.m.e τ, Sum.inr ⟨b, hb⟩, ⟨a, ha⟩) := by
  have hr := C.hr
  have hbm : b < T.rank := by omega
  rw [varF, dif_pos ⟨hbm, ha⟩, phi, AlgHom.comp_apply, MvPolynomial.rename_X, Ctx.toH, MvPolynomial.aeval_X]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [rowIdx_inr]
  simp only [revPos]
  rw [dif_pos ⟨hb, by omega⟩]

theorem phi_varF_neg (C : Ctx S T) (τ : D.what₂.Tau) (b a : ℕ) (hb : b < C.q0) (ha : a < S.rank) :
    phi C (varF τ (C.X.p0 + b) a) = MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) *
      MvPolynomial.X (C.m.e τ, Sum.inl ⟨b, hb⟩, ⟨a, ha⟩) := by
  have hr := C.hr
  have hbm : C.X.p0 + b < T.rank := by omega
  rw [varF, dif_pos ⟨hbm, ha⟩, phi, AlgHom.comp_apply, MvPolynomial.rename_X, Ctx.toH, MvPolynomial.aeval_X]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  dsimp only
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  rw [rowIdx_inl]
  simp only [revPos]
  rw [dif_neg (by simp)]

theorem phi_minorPlus (C : Ctx S T) (hle : C.X.p0 ≤ S.rank) (τ : D.what₂.Tau) (i : Fin C.X.p0) :
    phi C (minorPlus τ (i.val + 1)) = MvPolynomial.C ((((2 / fockScale D τ : ℝ) : ℂ)) ^ (i.val + 1)) *
      Harm.yMinor (C.m.e τ) i (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) := by
  rw [minorPlus, AlgHom.map_det, Harm.yMinor]
  have h : (phi C).mapMatrix (Matrix.of fun α β : Fin (i.val + 1) =>
      (varF τ β α : MvPolynomial (FVar D T.rank S.rank) ℂ)) =
      (MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) : Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) • (Matrix.of fun a b : Fin (i.val + 1) =>
        (Harm.yForm (C.m.e τ) (Harm.lead i a)
          ((fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) (Harm.lead i b)) :
            Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)))ᵀ := by
    ext α β
    have hβ : (β : ℕ) < C.X.p0 := by have := β.2; have := i.2; omega
    have hα : (α : ℕ) < S.rank := by have := α.2; have := i.2; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul]
    rw [phi_varF_pos C τ β α hβ hα, Harm.yForm_single]
    rfl
  rw [h, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, ← map_pow]

theorem phi_minorMinus (C : Ctx S T) (hn : T.rank ≤ S.rank) (τ : D.what₂.Tau) (i : Fin C.q0) : ∃ κ : ℂ,
    phi C (minorMinus τ C.X.p0 (i.val + 1)) = MvPolynomial.C κ *
      Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
        have := C.hr; have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) := by
  have hr := C.hr
  have hi := i.2
  rw [minorMinus, AlgHom.map_det, Harm.xMinor]
  have h : (phi C).mapMatrix (Matrix.of fun α β : Fin (i.val + 1) =>
      (varF τ (C.X.p0 + β) (S.rank - (i.val + 1) + α) : MvPolynomial (FVar D T.rank S.rank) ℂ)) =
      ((MvPolynomial.C (((2 / fockScale D τ : ℝ) : ℂ)) : Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)) • (Matrix.of fun a b : Fin (i.val + 1) =>
        (Harm.xForm (C.m.e τ) (Harm.lead i a)
          ((fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) (Harm.lead i b)) :
            Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank)))ᵀ).submatrix Fin.revPerm id := by
    ext α β : 1
    have hβ : (β : ℕ) < C.q0 := by have := β.2; omega
    have hα : S.rank - (i.val + 1) + (α : ℕ) < S.rank := by have := α.2; omega
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul, Matrix.submatrix_apply, id]
    rw [phi_varF_neg C τ β _ hβ hα, Harm.xForm_single]
    have := α.2
    congr 1
    exact congrArg _ (Prod.ext rfl (Prod.ext rfl (Fin.ext (by
      simp only [Harm.lead, Fin.coe_castLE, Fin.revPerm_apply, Fin.val_rev]
      omega))))
  refine ⟨((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i.val + 1))) : ℤ) : ℂ) *
    (((2 / fockScale D τ : ℝ) : ℂ)) ^ (i.val + 1), ?_⟩
  rw [h, Matrix.det_permute, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  simp only [map_mul, map_pow, map_intCast]
  ring

theorem prod_range_pow_eq {σ : Type} (N : ℕ) (g : ℕ → MvPolynomial σ ℂ) (h : Fin N → MvPolynomial σ ℂ) (d : ℕ → ℕ)
    (hg : ∀ i : Fin N, ∃ κ : ℂ, g i = MvPolynomial.C κ * h i) :
    ∃ κ : ℂ, ∏ i ∈ Finset.range N, g i ^ d i = MvPolynomial.C κ * ∏ i : Fin N, h i ^ d i := by
  choose κ hκ using hg
  refine ⟨∏ i : Fin N, κ i ^ d i, ?_⟩
  rw [← Fin.prod_univ_eq_prod_range (fun i => g i ^ d i), map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hκ i, mul_pow, map_pow]

theorem phi_delta (C : Ctx S T) (hn : T.rank ≤ S.rank) (ap am : D.what₂.Tau → ℕ → ℕ) : ∃ κ : ℂ,
    phi C (delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am) =
      MvPolynomial.C κ * Harm.minorProd
        (fun σ (i : Fin C.q0) => am (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.q0 then am (C.m.e.symm σ) (i + 1) else 0)
        (fun σ (i : Fin C.X.p0) => ap (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.X.p0 then ap (C.m.e.symm σ) (i + 1) else 0)
        (fun _ (a : Fin C.q0) => (Pi.single (⟨S.rank - 1 - a, by
          have := C.hr; have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ))
        (fun _ (b : Fin C.X.p0) => (Pi.single (Fin.castLE (by have := C.hr; omega) b) (1 : ℂ) : Fin S.rank → ℂ)) := by
  have hr := C.hr
  have hle : C.X.p0 ≤ S.rank := by omega
  have hτ : ∀ τ : D.what₂.Tau, ∃ κ : ℂ, phi C (deltaAt (m := T.rank) (n := S.rank) τ C.X.p0 (ap τ) C.q0 (am τ)) =
      MvPolynomial.C κ *
        ((∏ i : Fin C.q0, Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)) ^
            (am τ i - if (i : ℕ) + 1 < C.q0 then am τ (i + 1) else 0)) *
          ∏ i : Fin C.X.p0, Harm.yMinor (C.m.e τ) i
            (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)) ^
            (ap τ i - if (i : ℕ) + 1 < C.X.p0 then ap τ (i + 1) else 0)) := by
    intro τ
    rw [deltaAt, map_mul, map_prod, map_prod]
    simp only [map_pow]
    obtain ⟨κ1, h1⟩ := prod_range_pow_eq C.X.p0 (fun i => phi C (minorPlus τ (i + 1)))
      (fun i : Fin C.X.p0 => Harm.yMinor (C.m.e τ) i
        (fun b : Fin C.X.p0 => (Pi.single (Fin.castLE hle b) (1 : ℂ) : Fin S.rank → ℂ)))
      (fun i => ap τ i - if i + 1 < C.X.p0 then ap τ (i + 1) else 0)
      (fun i => ⟨_, phi_minorPlus C hle τ i⟩)
    obtain ⟨κ2, h2⟩ := prod_range_pow_eq C.q0 (fun i => phi C (minorMinus τ C.X.p0 (i + 1)))
      (fun i : Fin C.q0 => Harm.xMinor (C.m.e τ) i (fun a : Fin C.q0 => (Pi.single (⟨S.rank - 1 - a, by
            have := a.2; omega⟩ : Fin S.rank) (1 : ℂ) : Fin S.rank → ℂ)))
      (fun i => am τ i - if i + 1 < C.q0 then am τ (i + 1) else 0)
      (fun i => phi_minorMinus C hn τ i)
    refine ⟨κ1 * κ2, ?_⟩
    rw [h1, h2, map_mul]
    ring
  choose κ hκ using hτ
  refine ⟨∏ τ, κ τ, ?_⟩
  rw [delta, map_prod, Finset.prod_congr rfl (fun τ _ => hκ τ), Finset.prod_mul_distrib, ← map_prod, Harm.minorProd]
  congr 1
  exact Fintype.prod_equiv C.m.e _ _ (fun τ => by simp only [Equiv.symm_apply_apply])

end GlobalTheory.RenamedMinors

open GlobalTheory.RenamedMinors in

theorem GlobalTheory.RenamedMinors.renamed_delta_mem_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), T.rank ≤ S.rank → ∀ (ap am : D.what₂.Tau → ℕ → ℕ), ∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ∈ Harm.rowHighest ℂ c c' ∧ C.toH (MvPolynomial.rename (fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2)) (Formalism.IndefR.Datum.delta (m := T.rank) (n := S.rank) (fun _ => C.X.p0) (fun _ => C.q0) ap am)) ≠ 0 := by
  intro D S T C hn ap am
  have hr := C.hr
  obtain ⟨κ, hκ⟩ := phi_delta C hn ap am
  refine ⟨fun σ (i : Fin C.q0) => am (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.q0 then am (C.m.e.symm σ) (i + 1) else 0,
    fun σ (i : Fin C.X.p0) => ap (C.m.e.symm σ) i - if (i : ℕ) + 1 < C.X.p0 then ap (C.m.e.symm σ) (i + 1) else 0,
    ?_, ?_⟩
  · change phi C _ ∈ _
    rw [hκ, ← MvPolynomial.smul_eq_C_mul]
    refine Submodule.smul_mem _ κ (Harm.minorProd_mem_rowHighest _ _ fun t a b => ?_)
    rw [single_dotProduct, one_mul, Pi.single_apply, if_neg]
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.coe_castLE] at h'
    have := a.2
    have := b.2
    omega
  · change phi C _ ≠ 0
    have hf : Function.Injective fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2) :=
      Function.LeftInverse.injective (g := fun v : FVar D T.rank S.rank => (v.1, revPos C.X.p0 v.2.1, v.2.2))
        fun v => by simp only [revPos_revPos]
    have hinj : Function.Injective (phi C) := C.toH_bijective.1.comp (MvPolynomial.rename_injective _ hf)
    exact (map_ne_zero_iff (phi C) hinj).2 (GlobalTheory.FockDelta.delta_ne_zero _ _ _ _ (fun _ => by omega) hn)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignBlockDeterminantOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.ChainFr GlobalTheory.Chain.IoLift GlobalTheory.Chain.IoLift.FockOrbit GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec maxCpt)
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembers

theorem signBlockDeterminant_one {n : ℕ} (ε : Fin n → Bool) (e : Bool) : signBlockDeterminant ε e 1 = 1 := by
  unfold signBlockDeterminant
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Subtype.val : {a // ε a = e} → Fin n) Subtype.val = 1 from by
    ext x y; simp [Matrix.one_apply, Subtype.ext_iff]]
  exact Matrix.det_one

theorem fr_elt_one {D : D7} {V : HSp D} {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr V) (τ : D.what₂.Tau) :
    A.elt θ τ 1 = 1 := by
  rw [Fr.elt, Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)), GlobalTheory.PointAtPlaceHom.atTau_one hθ]

theorem frame_fock_orbit : ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (A : GlobalTheory.ChainFr.Fr V) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ), IsInfFam θ → GlobalTheory.ChainFr.CompactFockF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') ω f τ aS aT → ∀ φ : PolF D W.rank V.rank, ∃ (n : ℕ) (φs : Fin n → PolF D W.rank V.rank) (c : Fin n → Formalism.REAL.KG (M'.ε τ) → ℂ), GlobalTheory.Chain.IoLift.IsCoefFam c ∧ ∀ k, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (GlobalTheory.ChainFr.ptF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') f φ) = ∑ i, c i k • GlobalTheory.ChainFr.ptF ψ θ A (GlobalTheory.ChainFr.Fr.ofModel M') f (φs i) := by
  intro D V W S' A M' θ ψ ω f τ aS aT hθ hC φ
  obtain ⟨x, y, -, -, hc⟩ := hC
  let pt : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ) :=
    pureTensorO ψ θ V W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f
  have hp : ptF ψ θ A (Fr.ofModel M') f = pt := rfl
  let s : Formalism.REAL.KG (M'.ε τ) → ℂ := fun k =>
    signBlockDeterminant (M'.ε τ) true (Formalism.REAL.toMK k) ^ y true * signBlockDeterminant (M'.ε τ) false (Formalism.REAL.toMK k) ^ y false
  let ρ : Formalism.REAL.KG (M'.ε τ) → Module.End ℂ (PolF D W.rank V.rank) := fun k =>
    s k • (subst τ (A.ε τ) (M'.ε τ) 1 (Formalism.REAL.toMK k)).toLinearMap
  have key : ∀ k P, ω (1, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.elt θ M' τ (Formalism.REAL.toMK k)) (pt P) = pt (ρ k P) := fun k P => by
    have := hc 1 ⟨one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩ (Formalism.REAL.toMK k) k.2 P
    rw [fr_elt_one hθ, signBlockDeterminant_one, signBlockDeterminant_one, _root_.one_zpow, _root_.one_zpow, one_mul, one_mul,
      Matrix.map_one _ (map_zero _) (map_one _), hp, ← map_smul] at this
    exact this
  have hz : ∀ e, Continuous fun k : Formalism.REAL.KG (M'.ε τ) => signBlockDeterminant (M'.ε τ) e (Formalism.REAL.toMK k) ^ y e := fun e =>
    ((continuous_signBlockDeterminant _ e).comp (continuous_toMK _)).zpow₀ _ fun k => Or.inl (signBlockDeterminant_ne_zero_of_mem_maxCompact e k.2)
  have hs : Continuous s := (hz true).mul (hz false)
  obtain ⟨n, φs, c, h1, h2⟩ := exists_coefFam ρ (fun a b P => by
      have e : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
      simp only [ρ, s, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, e,
        subst_one_mul τ (A.ε τ) (M'.ε τ) a.2 b.2, signBlockDeterminant_mul_maximalCompact _ a.2 b.2, mul_zpow]
      congr 1
      ring)
    (fun a P => (MvPolynomial.totalDegree_smul_le _ _).trans
      (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _))
    (fun P => CoefCont.smul hs (coefCont_subst τ _ _ _ (continuous_toMK _) P)) φ
  refine ⟨n, φs, c, h1, fun k => ?_⟩
  rw [hp, key, h2, map_sum]
  simp only [map_smul]

set_option maxHeartbeats 1000000 in

theorem lowVanishFock (h1 : GlobalTheory.Published.DiscreteSeriesCover) (h2 : GlobalTheory.Published.HarishChandraModules)
    (h3 : GlobalTheory.Published.CuspRapidDecay) : ∀ D : D7, LowVanishFock D := by
  classical
  intro D
  obtain ⟨X, hX, -, h5, -, -, -, hAR⟩ := GlobalTheory.T.exists_provA_discreteSeries_archimedeanRallis h1 h2
  have hTB := (GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra h1 h2 D).2
  intro k i V' W M' θ ψ hθ hP hi hs ω' hω ν 𝓕 hν h𝓕 J χ F hF v A f₀ hf P
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  by_cases f0 : f₀ = 0
  · subst f0
    funext g
    simp [Lift.liftInt, thetaKO, ptF_zero]

  have tgt : ∀ τ, ∃ a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ),
      kFin M' τ ≤ M'.sm τ ∧ IsKAct M' τ a' := fun τ => by
    obtain ⟨al, be, ga, de, hd, -, -, e2⟩ := hP τ
    obtain ⟨-, -, p2, -⟩ := GlobalTheory.LowestTypes.lowest_types _ al be ga de hd.1
    have ht := hd.1.1
    obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W _ M' τ (al.length + de.length + D.R.t) (ga.length + be.length) _ _
      (expS D k τ) ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, congrArg dualPar e2⟩
    obtain ⟨U', hU'⟩ := hU' e' he'
    obtain ⟨hsm, a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W _ M' τ _ _ _ _ _ _ _ hU'
    exact ⟨a', hsm, ha'⟩
  choose a' hsm ha' using tgt
  have h' : KSm M' := hsm
  have hMF : IsMultMap θ M' J χ (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hF)
  have hM : ∀ F' : MultT θ M' J χ, IsMultMap θ M' J χ (PiTensorProduct.lift.symm (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ))) :=
    fun F' => (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F'.2)
  let pt : PolF D W.rank V'.rank →ₗ[ℂ] (WO V' W → ℂ) :=
    pureTensorO ψ θ V' W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f₀
  have hp : ptF ψ θ A (Fr.ofModel M') f₀ = pt := rfl
  have hpt : ∀ φ, IsThetaFunO ψ V' W (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hf.1 φ
  have L := GlobalTheory.T.thetaLift_cuspForm_automorphic_smooth_moderateGrowth h3 D V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hint : ∀ F' : MultT θ M' J χ, ∀ φ x g, IntegrableOn
      (fun h => thetaKO ω' g h (pt φ) * (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ)) x h) 𝓕 ν := fun F' φ x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (L.integ _ _ (hpt φ) ⟨(hM F').aut w, (hM F').cusp w⟩ g 1).const_mul r
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]
      rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, mul_add]; exact hx.add hy
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω' (g, h)) pt (MultT θ M' J χ) hint
  let G : PolF D W.rank V'.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V' → ℂ) :=
    B.compr₂ (LinearMap.applyₗ (⟨F, hF⟩ : MultT θ M' J χ))
  have hG : ∀ φ x, G φ x = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) (F x) := fun φ x => hB φ x ⟨F, hF⟩
  have hcl : ∀ w : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ w)) ∧
      IsCuspFun W (F (PiTensorProduct.tprod ℂ w)) := fun w => ⟨hMF.aut w, hMF.cusp w⟩

  have hT : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω' (1, oneP θ W τ Y t) (pt φ) z)
      (pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ) z) 0 :=
    fun τ Y hY φ z => (GlobalTheory.T.lieAction_fockOperators_scalars_trace D V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ (expS D k τ) (expT D k τ) hθ hW
      (hexp τ).1 (hexp τ).2 hf).2 Y hY φ z
  have hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (w : M'.Vec) (u : M'.sm τ), (u : M'.H τ) = dRep (M'.rep τ) Y (w τ) →
      G (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ)
        (PiTensorProduct.tprod ℂ w) + G φ (PiTensorProduct.tprod ℂ (Function.update w τ u)) = 0 := by
    intro τ Y hY φ w u hu
    have e1 := GlobalTheory.MultGelf.rder_apply hMF τ w hY (w τ) u hu
    rw [Function.update_eq_self] at e1
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω' τ Y (pt φ) =
        pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((expS D k τ : ℂ) * Y.trace) • φ) :=
      funext fun z => (hT τ Y hY φ z).deriv
    funext g
    have := L.derT_add (hpt φ) (hcl w) τ hY g
    rw [e2, add_comm] at this
    rw [Pi.add_apply, hG, hG]
    exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) A g) e1).symm.trans this

  have hav := mem_span_of_average G h' fun τ φ w => by
    obtain ⟨n, φs, c, hc, hφ⟩ := frame_fock_orbit D V' W _ A M' θ ψ ω' f₀ τ (expS D k τ) (expT D k τ) hθ
      (GlobalTheory.T.compact_subgroups_act_on_fock_vectors_all_signatures D V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ _ _ hθ hW (hexp τ).1 (hexp τ).2 hf f0) φ
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (w τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, ?_⟩
    funext g
    simp only [hG, Finset.sum_apply]
    exact GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V' W _ M' θ ψ χS χT ω' ν 𝓕 hθ hW hν h𝓕 τ n c _ _ _ _
      hc.1 (hpt φ) hφ (hcl w).1.toIsAutFun (fun i x => apply_kMean hMF τ (hc.1 i) w _ rfl x) g
      (hint ⟨F, hF⟩ _ _ g) fun i => hint ⟨F, hF⟩ _ _ g

  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨al, be, ga, de, hd, hbig, e1, e2⟩ := hP τ₀
  obtain ⟨p', q', hp', hq', hsig⟩ := hs τ₀
  have hnd : ((al ++ be) ++ (ga ++ de)).Nodup := by simpa only [List.append_assoc] using hd.1.2.2.2.2.2.2.1
  have hcard := signCard_signed (al ++ be) (ga ++ de) (expT D k τ₀) hnd.of_append_left hnd.of_append_right
  have e1' : parB (Ptw D) k τ₀ = dualPar (signed (al ++ be) (ga ++ de) (expT D k τ₀)) := congrArg dualPar e1
  rw [e1', GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.1, List.length_append] at hp'
  rw [e1', GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.2, List.length_append] at hq'
  obtain rfl : p' = al.length + be.length - i := by omega
  obtain rfl : q' = ga.length + de.length - i := by omega
  obtain ⟨e, he⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').2 A τ₀ _ _ hsig
  obtain ⟨-, -, p2, -⟩ := GlobalTheory.LowestTypes.lowest_types _ al be ga de hd.1
  have ht := hd.1.1
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W _ M' τ₀ (al.length + de.length + D.R.t) (ga.length + be.length) _ _
    (expS D k τ₀) ⟨by omega, by simp [block]; omega, by simp, p2, hX _ _ _ p2, congrArg dualPar e2⟩
  obtain ⟨U', hU'⟩ := hU' e' he'
  have kvan : ∀ φ (y : KT M'), G φ (inclK h' y) = 0 := by
    have hz := span_multi (G.compl₂ (inclK h')) fun p y => by
      funext g
      let b := slice (multi ((G.compl₂ (inclK h')).compr₂ (LinearMap.proj g))) τ₀ p y
      have hb0 := pairing_eq_zero X h5 hAR D.R.t al be ga de hd hbig i hi (by omega) (by omega) D V' W _ M' τ₀
        (A.ε τ₀) e e' m' (expS D k τ₀) U' (a' τ₀) b he he' hm' hU' (ha' τ₀) (fun Y hY Q z => by
          simp only [b, slice_apply, multi_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
            LinearMap.proj_apply]
          have eq1 : glue (Function.update p τ₀ (locT (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) Q +
              ((expS D k τ₀ : ℂ) * Y.trace) • Q)) =
              fockT τ₀ (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) (glue (Function.update p τ₀ Q)) +
                ((expS D k τ₀ : ℂ) * Y.trace) • glue (Function.update p τ₀ Q) := by
            rw [((GlobalTheory.T.gluing_law_holds D V'.rank W.rank).2 τ₀ _ _ _).2, Function.update_idem, Function.update_self]
            simp only [← glueM_apply, MultilinearMap.map_update_add, MultilinearMap.map_update_smul]
          have eq2 : Function.update y τ₀ (a' τ₀ Y z) = Function.update (Function.update y τ₀ z) τ₀
              (a' τ₀ Y (Function.update y τ₀ z τ₀)) := by
            rw [Function.update_idem, Function.update_self]
          rw [eq1, eq2, inclK_tprod h' (Function.update y τ₀ z), inclK_update h' (Function.update y τ₀ z) τ₀]
          refine congrFun (hBt τ₀ Y hY _ _ _ ?_) g
          exact ((ha' τ₀).der Y hY _).deriv.symm)
      have := LinearMap.congr_fun₂ hb0 (p τ₀) (y τ₀)
      simpa [b, slice_apply, multi_apply, Function.update_eq_self] using this
    exact fun φ y => LinearMap.congr_fun₂ hz φ y
  have h0 : G P v ∈ (⊥ : Submodule ℂ (GA D V' → ℂ)) :=
    Submodule.span_le.2 (by rintro _ ⟨φ, y, rfl⟩; simp [kvan φ y]) (hav P v)
  rw [Submodule.mem_bot, hG] at h0
  rw [hp]
  exact h0

end GlobalTheory.LowerMembers

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesOverNormAndCoverWithConjugates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjRead

theorem places_over_g : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ R.Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL
  have hPg := hL.Pg
  refine ⟨fun PP hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨k, hk⟩ := (hPg PP).1 hP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := R.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact PP.asIdeal.mul_mem_right _ h1
    · exact PP.asIdeal.mul_mem_left _ h1
  · rw [Nat.cast_mul] at hQ
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
      rcases Q.isPrime.mem_or_mem hQ with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hc : GlobalTheory.Mem.Chr.ConjPl D.host.conj.toRingEquiv Q (GlobalTheory.IdemSupport.cP Q) := by
      refine (GlobalTheory.Mem.Chr.conjPl_iff_mem _ _ _).2 fun x y hxy => ?_
      have h1 : y = GlobalTheory.IdemSupport.cO D x := by
        apply RingOfIntegers.ext
        rw [hxy, GlobalTheory.IdemSupport.cO_coe]
        exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
      rw [GlobalTheory.IdemSupport.mem_cP, h1, GlobalTheory.IdemSupport.cO_cO]
    have hsp := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) Q hk).2.2.2
      (R.C.P.pb k) (R.C.P.pb_over k) _ hc
    by_cases hu : Q.under (𝓞 D.host.K) = R.C.P.pb k
    · exact ⟨Q, (hPg Q).2 ⟨k, hu⟩, Or.inl rfl⟩
    · have hu' : (GlobalTheory.IdemSupport.cP Q).under (𝓞 D.host.K) = R.C.P.pb k := by
        by_contra hn
        exact hu (hsp.2.2 hn)
      exact ⟨GlobalTheory.IdemSupport.cP Q, (hPg _).2 ⟨k, hu'⟩, Or.inr (GlobalTheory.StdFrames.cP_cP Q).symm⟩

end GlobalTheory.SeeConjRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelCharStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_inf → R.thP_ωP → R.thP_vP → ∀ i t (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ → IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' → R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t := by
  first | exact @GlobalTheory.VecInv.omega_lifts_vP | exact GlobalTheory.VecInv.omega_lifts_vP | (intros; apply GlobalTheory.VecInv.omega_lifts_vP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelResidueCharacterPowStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_residue_character_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ X, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair_left | exact GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair_left | (intros; apply GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelResidueCharacterStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_residue_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ (μ : MeasureTheory.Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F)), μ.IsAddHaarMeasure →
        ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair | exact GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair | (intros; apply GlobalTheory.ArchimedeanUnitaryL2.integral_norm_sq_eq_pair <;> assumption)
end

