import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0531
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCoreVertexLatticeSplitsAlongOrthogonalDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.CoreSum

variable {D : D7}

theorem orthogonalSumAuxiliaryVectors_gramProjection_retraction {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (hiso : (frameMat B A d.ι)ᴴ * B.gram * frameMat B A d.ι = A.gram) (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    (A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram)) *ᵥ (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) = y := by
  have h1 : A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram) * frameMat B A d.ι = 1 := by
    rw [Matrix.mul_assoc, hiso, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]
  have h2 : A.gram⁻¹ * ((frameMat B A d.ι)ᴴ * B.gram) * d.a = 0 := by
    have := d.perp
    rw [cT_sig] at this
    rw [Matrix.mul_assoc, this, Matrix.mul_zero]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

theorem orthogonalSumAuxiliaryVectors_middleCoefficient_eq {A B : HSp D} {c : ℕ} {ε : D.host.E} (hε : ε ≠ 0) (d : HermitianOrthogonalExtensionData A B c ε) (p : Fin c)
    (hp : p.1 + p.1 + 1 = c) (u : Fin c → D.host.E) (t : D.host.E) (e : d.a *ᵥ u = d.a *ᵥ Pi.single p t) : u p = t := by
  have g := d.gram
  rw [cT_sig] at g
  have e2 := congrArg (fun w => ((d.a)ᴴ * B.gram) *ᵥ w) e
  simp only [Matrix.mulVec_mulVec, g] at e2
  have e3 := congrFun e2 p
  have key : ∀ w : Fin c → D.host.E, (antiDiagonalSignGramMatrix c ε *ᵥ w) p = ε * w p := by
    intro w
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single p]
    · simp only [antiDiagonalSignGramMatrix]
      rw [if_pos hp]
      simp
    · intro q _ hq
      have : ¬ (p.1 + q.1 + 1 = c) := fun h' => hq (Fin.ext (by omega))
      simp only [antiDiagonalSignGramMatrix]
      rw [if_neg this, zero_mul]
    · simp
  rw [key, key, Pi.single_eq_same] at e3
  exact mul_left_cancel₀ hε e3

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem besselCoreVertexLattice_eq_orthDecSumLattice (F : Frames G) (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) :
    lat0 F ρ h = GlobalTheory.Core.Rk.SumBox.sumLatO (F.oB ρ h) (G.Λ (.core (2 * ρ + 2)))
      (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  have lat2 : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat (2 * ρ + 2) (by omega) h
  have hstair : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) ⟨ρ, by omega⟩ =
      G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹ := by
    unfold stairId
    rw [show 2 * ρ + 2 - 1 - ρ = ρ + 1 by omega]
  have hM := hF.aB ρ h
  have hz := hF.zB' ρ h
  ext x
  simp only [lat0, Submodule.mem_comap, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
    GlobalTheory.Core.Rk.SumBox.mem_sumLatO]
  rw [lat2]
  constructor
  · rintro ⟨y, hy, u, hu, hx⟩
    have hiso2 : (frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι)ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram *
        frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι = (G.V (.core (2 * ρ + 2))).gram := by
      rw [← hM, Matrix.conjTranspose_mul, ← (F.oB ρ h).isoA, ← (F.dB ρ h).iso]
      simp only [Matrix.mul_assoc]
    have hQ : (G.V (.core (2 * ρ + 2))).gram⁻¹ * ((frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι)ᴴ *
        (G.V (.grid (2 * ρ + 2) 0)).gram) * (F.dB ρ h).i₀ = (F.oB ρ h).qA := by
      rw [← hM, Matrix.conjTranspose_mul, OrthDec.qA, ← (F.dB ρ h).iso]
      simp only [Matrix.mul_assoc]
    have hqA : (F.oB ρ h).qA *ᵥ x = y := by
      rw [← hQ, ← Matrix.mulVec_mulVec, hx, orthogonalSumAuxiliaryVectors_gramProjection_retraction _ hiso2]
    have hline := F.line 0
    have hr : (negSp F.Lz).rank = 1 := hline.1
    let i0 : Fin (negSp F.Lz).rank := ⟨0, by rw [hr]; omega⟩
    have hsub : ∀ j : Fin (negSp F.Lz).rank, j = i0 := fun j => Fin.ext (by have := j.isLt; show j.1 = 0; omega)
    have hζ0 : F.ζ 0 i0 ≠ 0 := by
      intro h0
      apply hline.2
      have : F.ζ 0 = 0 := funext fun j => by rw [hsub j]; exact h0
      rw [this]
      simp
    have hqB : (F.oB ρ h).qB *ᵥ x = (((F.oB ρ h).qB *ᵥ x) i0 / F.ζ 0 i0) • F.ζ 0 := by
      funext j
      rw [hsub j, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hζ0]
    have hsplit : (F.oB ρ h).iA *ᵥ ((F.oB ρ h).qA *ᵥ x) + (F.oB ρ h).iB *ᵥ ((F.oB ρ h).qB *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, (F.oB ρ h).iA_qA_add, Matrix.one_mulVec]
    have hx2 : (F.dB ρ h).i₀ *ᵥ x = frameMat _ _ (G.colDec (2 * ρ + 2) (by omega) h).ι *ᵥ y +
        (G.colDec (2 * ρ + 2) (by omega) h).a *ᵥ
          Pi.single ⟨ρ, by omega⟩ (((F.oB ρ h).qB *ᵥ x) i0 / F.ζ 0 i0) := by
      conv_lhs => rw [← hsplit, hqA, hqB]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, hz]
      congr 1
      funext i
      simp only [Matrix.mulVec_single, Matrix.col_apply, MulOpposite.smul_eq_mul_unop, Pi.smul_apply, smul_eq_mul,
        MulOpposite.unop_op]
      ring
    have ha := add_left_cancel (hx.symm.trans hx2)
    have hc := GlobalTheory.AscFin.CoreSum.orthogonalSumAuxiliaryVectors_middleCoefficient_eq (neg_ne_zero.2 one_ne_zero) _ ⟨ρ, by omega⟩ (by simp; omega) u _ ha
    have hcJ := hu ⟨ρ, by omega⟩
    rw [hc, hstair] at hcJ
    refine ⟨(F.oB ρ h).qA *ᵥ x, hqA ▸ hy, (F.oB ρ h).qB *ᵥ x, ?_, hsplit⟩
    rw [hqB]
    exact Submodule.subset_span ⟨_, hcJ, F.ζ 0, Submodule.mem_span_singleton_self _, rfl⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]
    refine Submodule.add_mem _ ⟨y, hy, 0, fun p => (stairId _ _ _ p).val.zero_mem, by simp⟩ ?_
    induction hb using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, w, hw, rfl⟩ := hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      refine ⟨0, Submodule.zero_mem _, Pi.single ⟨ρ, by omega⟩ (r • s), fun p => ?_, ?_⟩
      · by_cases hp : p = ⟨ρ, by omega⟩
        · subst hp
          rw [Pi.single_eq_same, hstair]
          exact Submodule.smul_mem _ r hs
        · rw [Pi.single_eq_of_ne hp]
          exact (stairId _ _ _ p).val.zero_mem
      · rw [Matrix.mulVec_zero, zero_add, ← algebraMap_smul D.host.E r (F.ζ 0), Matrix.mulVec_smul, Matrix.mulVec_smul, hz]
        funext i
        rw [Algebra.smul_def r s]
        simp only [Matrix.mulVec_single, Matrix.col_apply, MulOpposite.smul_eq_mul_unop, Pi.smul_apply, smul_eq_mul,
          MulOpposite.unop_op]
        ring
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hz hz'
    | smul r z _ hz =>
      rw [← algebraMap_smul D.host.E r z, Matrix.mulVec_smul, algebraMap_smul]
      exact Submodule.smul_mem _ r hz

theorem besselCoreVertexLattice_splitsAlongOrthDecomposition : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2)))
      (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v := by
  intro D T L sc G F hF ρ h v
  rw [besselCoreVertexLattice_eq_orthDecSumLattice F hF ρ h]
  exact GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v

end GlobalTheory.AscFin.CoreSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselHandedFunctionProductEqCoreLiftMulPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.HandProd

theorem handP_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B), ∀ (vL : VolM D B.L.rank J.W₀.rank) (χA χz : (AE D)ˣ →* Circle) (omb : Om J.W₀ B.A) (omz : Om J.W₀ B.L), s.χW = χA * χz → IsWeilDatumO ψ J.W₀ B.A s.χV χA omb → IsWeilDatumO ψ J.W₀ B.L s.χV χz omz → ∀ (φ : GA D J.W₀ → ℂ) Ξ₁ Φ' Φ₀, IsThetaFunO ψ J.W₀ B.A Ξ₁ → IsThetaFunO ψ J.W₀ B.L Φ' → IsThetaFunO ψ J.W₀ B.L Φ₀ → handP s vL omz φ Φ₀ (B.o.boxT J.W₀ Ξ₁ Φ') = thPair vL.μ vL.𝓕 Φ' Φ₀ • liftT omb J.v0.μ J.v0.𝓕 φ Ξ₁ := by
  intro D ψ σ J B s vL χA χz omb omz hχ hb hz φ Ξ₁ Φ' Φ₀ h1 h' h0
  have hW₀ : IsWeilDatumO ψ J.W₀ B.V₀ s.χV (χA * χz) s.om₀ := hχ ▸ s.weil₀
  have tt := GlobalTheory.TensorTargetRule.tensorTarget D ψ hb.std B.V₀ B.A B.L B.o J.W₀
  funext h₁
  have hpt : ∀ h₀, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (B.o.boxT J.W₀ Ξ₁ Φ')) (omz (h₀, 1) Φ₀) 0 =
      omb (h₀, h₁) Ξ₁ 0 * thPair vL.μ vL.𝓕 Φ' Φ₀ := by
    intro h₀
    rw [tt.om_box s.χV χA χz s.om₀ omb omz hW₀ hb hz h₀ h₁ 1 Ξ₁ Φ' h1 h',
      ← GlobalTheory.WeilPairing.thPair_om_eq D ψ J.W₀ B.L s.χV χz omz hz vL (h₀, 1) Φ' Φ₀ h' h0]
    have e : (fun v => B.o.boxT J.W₀ (omb (h₀, h₁) Ξ₁) (omz (h₀, 1) Φ') ((B.o.resT J.W₀).symm (0, v))) =
        fun v => omb (h₀, h₁) Ξ₁ 0 * omz (h₀, 1) Φ' v := by
      funext v
      simp only [OrthDec.boxT, AddEquiv.apply_symm_apply]
    simp only [contractT, e, thPair]
    rw [← integral_const_mul]
    congr 1; funext w
    have ew := congrFun e w
    rw [ew]; ring
  simp only [handP, hpt, Pi.smul_apply, smul_eq_mul, liftT_apply]
  rw [← integral_const_mul]
  congr 1; funext h₀; ring

end GlobalTheory.HandProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepBasePointScaledCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.FrameZero

theorem vecMul_row {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (q : Fin c) (m : ι) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = ((Formalism.UG.cT σ a * g).map φ * b) q m := by
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring
private theorem mulVec_col_eq_single_of_mul_eq_one {k m n : Type} [Field k] [Fintype m] [DecidableEq n] (b : Matrix m n k)
    (b' : Matrix n m k) (hb : b' * b = 1) (j : n) : (b' *ᵥ fun i => b i j) = Pi.single j 1 := by
  funext i
  show ∑ l, b' i l * b l j = _
  rw [← Matrix.mul_apply, hb, Matrix.one_apply, Pi.single_apply]
private theorem cA_incA_eq_incA_sig (D : D7) (x : D.host.E) :
    cA D (incA D x) = incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) x) := rfl
end GlobalTheory.FrameZero

theorem GlobalTheory.FrameZero.xclauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∃ s t : Fin (σ + 1) → k, (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (κ ⟨q.1, by omega⟩) 1) ∧
    (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) := by
  unfold GlobalTheory.AscFin.OnStd All
  intro D _ T L μ0 _ sc G _ M _ F hF σ h v _ k _ _ _ _ p β ϖ κ _ _ _ hirr hinj hb hperp
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hϖ : (ϖ : k) ≠ 0 := fun h0 => hirr.ne_zero (Subtype.ext h0)
  have hx0 : p.pr (incA D (-D.host.xi0)) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero)
  have hx1 : p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ≠ 0 :=
    (map_ne_zero (p.pr.comp (incA D))).mpr ((map_ne_zero _).mpr (neg_ne_zero.mpr cmHost_imaginaryGenerator_ne_zero))
  have hx : ∀ i (q : Fin (σ + 1)), xZero (F.dJ (σ + 1) h) i q = incA D ((-D.host.xi0) ^ (q.1 + 1) *
      (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩) := by
    intro i q
    show incA D ((F.dJ (σ + 1) h).e i q) = _
    rw [he]
    rfl
  refine ⟨fun q => (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) *
      ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹)⁻¹,
    fun q => (p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) *
      (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)))⁻¹, ?_, ?_⟩
  · intro q
    have hcol : (fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)))⁻¹) •
          fun i => β.b i (κ ⟨q.1, by omega⟩) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hb, hx, map_mul, map_mul, map_pow, map_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ)]
    dsimp only
    rw [hcol, Matrix.mulVec_smul, mulVec_col_eq_single_of_mul_eq_one _ _ β.b'b, smul_smul,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx0) (inv_ne_zero (pow_ne_zero _ hϖ))), one_smul]
  · intro q
    have hrow : (fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) =
        p.pr (incA D ((D.sp.cm.sig : D.host.E →+* D.host.E) (-D.host.xi0))) ^ (q.1 + 1) •
          fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
            ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩)) := by
      funext i
      rw [hx, cA_incA_eq_incA_sig]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, RingHom.comp_apply]
    have key : ∀ r : Fin (2 * (σ + 1) + 1 - 1), ∑ j, p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram)
            ⟨q.1, by omega⟩ j)) * ((ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) *
          p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a j r))) =
        (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram *
          (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a) ⟨q.1, by omega⟩ r)) := by
      intro r
      rw [Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul]
      ring
    have hN : ((fun i => (p.pr.comp (incA D)) ((D.sp.cm.sig : D.host.E →+* D.host.E)
          ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i ⟨q.1, by omega⟩))) ᵥ*
          ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) =
        (ϖ : k) ^ (G.pl.depth sc v * (2 * (σ + 1) - 1 - q.1 + 1)) •
          Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1 := by
      funext m
      refine (GlobalTheory.FrameZero.vecMul_row (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
        (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a (G.V (.grid (2 * (σ + 1) + 1) 0)).gram β.b
        ⟨q.1, by omega⟩ m).trans ?_
      by_cases hm : m ∈ Set.range κ
      · obtain ⟨r, rfl⟩ := hm
        rw [Matrix.mul_apply]
        simp only [hb, Matrix.map_apply, RingHom.comp_apply]
        rw [key, (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).gram, antiDiagonalSignGramMatrix]
        split_ifs with h1 h3
        · exfalso
          have h4 := congrArg Fin.val h3
          simp only at h1 h4
          omega
        · have hrv : r.1 = 2 * (σ + 1) - 1 - q.1 := by simp only at h1; omega
          rw [map_one, map_one, mul_one, Pi.smul_apply, Pi.single_apply,
            if_pos (congrArg κ (Fin.ext hrv)), smul_eq_mul, mul_one, hrv]
        · rw [map_zero, map_zero, mul_zero, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
          intro hk
          have h4 := congrArg Fin.val (hinj hk)
          simp only at h1 h4
          omega
      · rw [Pi.smul_apply, Pi.single_apply, if_neg (fun e => hm ⟨_, e.symm⟩), smul_zero]
        exact hperp m hm _
    dsimp only
    rw [hrow, Matrix.smul_vecMul, hN, smul_smul, smul_smul, mul_assoc,
      inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ hx1) (pow_ne_zero _ hϖ)), one_smul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)
open scoped ComplexOrder

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

open GlobalTheory.Grid (neg neg_gram sigOK_sgn isCartanInv_sgn)

theorem exists_stdRig (n : ℕ) : ∃ (V : HSp D) (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V), V.rank = n ∧ V.SigOK ∧ r.IsStd ∧ r.Is := by
  let V : HSp D := Formalism.BasicNotions.Examples₂.posSpace Formalism.BasicNotions.Examples₂.star_isIntegral n
  have hg : V.gram = 1 := Matrix.ext fun i j => by
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0 i j).trans ?_
    exact (Matrix.one_apply (i := i) (j := j)).symm
  let Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E)
  have hmem : ∀ y, y ∈ Λ ↔ ∀ i, IsIntegral ℤ (y i) := fun y => by
    simp only [Λ, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨y i, h⟩, rfl⟩⟩
  have hsingle : ∀ i, (Pi.single i 1 : Fin V.rank → D.host.E) ∈ Λ := fun i => (hmem _).2 fun k => by
    by_cases h : k = i
    · subst h; simpa using isIntegral_one
    · simpa [h] using isIntegral_zero
  have hsd : IsSelfDualC V Λ := by
    refine ⟨⟨Submodule.fg_pi fun _ => ?_, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => (hmem y).2 fun i => ?_⟩⟩
    · rw [Submodule.one_eq_span]
      exact Submodule.fg_span (Set.finite_singleton _)
    · rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      rw [Pi.basisFun_apply]
      exact hsingle i
    · have hs : IsIntegral ℤ (∑ a, ∑ b, star (x a) * V.gram a b * y b) := by
        rw [hg]
        refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
        by_cases hab : a = b
        · subst hab
          simpa using (Formalism.BasicNotions.Examples₂.star_isIntegral _ ((hmem x).1 hx a)).mul ((hmem y).1 hy a)
        · simpa [Matrix.one_apply, hab] using isIntegral_zero
      exact ⟨⟨_, hs⟩, rfl⟩
    · obtain ⟨b, hb⟩ := h _ (hsingle i)
      have e : ∑ a, ∑ c, star ((Pi.single i 1 : Fin V.rank → D.host.E) a) * V.gram a c * y c = y i := by
        rw [hg, Finset.sum_eq_single i]
        · simp [Matrix.one_apply]
        · intro a _ ha
          simp [ha]
        · simp
      rw [e] at hb
      exact hb ▸ b.isIntegral_coe
  obtain ⟨r, hr, hri⟩ := GlobalTheory.T.self_dual_lattice_has_rigidification D V Λ (Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n) hsd
  have hgt : ∀ τ, gramAt D V τ = 1 := fun τ => by rw [gramAt, hg]; simp
  refine ⟨V, ⟨Λ, r.β, fun _ => 1, fun _ => 1⟩, rfl, Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n,
    ⟨hg, fun y => (hmem y).trans (forall_congr' fun i => ⟨fun h => ⟨⟨y i, h⟩, rfl⟩, fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe⟩),
      fun _ => ⟨rfl, rfl⟩⟩, hsd, hr ▸ hri.2.1, fun τ => ⟨?_, V.rank, ?_⟩⟩
  · rw [hgt]
    exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩
  · rw [hgt]
    refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, ?_⟩ <;> simp

theorem bottom_chars {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i j : Fin D.R.m) (t : T) :
    IsHeckeChar D (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) ∧
      IsHeckeChar D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) ∧
      ResEta D (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2)) (SqNum.botSmall D i j) ∧
      ResEta D (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) (SqNum.botBig D i j) := by
  have hmul : ∀ {χ η : (AE D)ˣ →* Circle}, IsHeckeChar D χ → IsHeckeChar D η → IsHeckeChar D (χ * η) := fun h1 h2 =>
    ⟨h1.1.mul h2.1, fun x => by rw [MonoidHom.mul_apply, h1.2, h2.2, mul_one]⟩
  have heta : IsHeckeChar D L.eta := hL.eta.1
  have hpow : ∀ n, IsHeckeChar D (L.eta ^ n) := fun n =>
    ⟨heta.1.pow n, fun x => by rw [MonoidHom.pow_apply, heta.2, one_pow]⟩
  have hi := i.2
  have hchiE := G.ch.chi_eq (D.R.m - i) (by omega) (by omega)
  have rpow : ∀ n, ResEta D (L.eta ^ n) n := fun n => by
    induction n with
    | zero => exact ⟨(GlobalTheory.HeckeCharacterRestriction.resEta_eta hL).1, fun η _ a => by simp⟩
    | succ n ih => rw [pow_succ]; exact resEta_mul ih (GlobalTheory.HeckeCharacterRestriction.resEta_eta hL)
  have rchi : ResEta D (G.ch.chi (D.R.m - i)) 0 := ⟨(GlobalTheory.HeckeCharacterRestriction.resEta_eta hL).1, fun η _ a => by
    rw [pow_zero]; exact GlobalTheory.GridWeil.triv_base hchiE (G.ch.triv _ (by omega) (by omega)) a⟩
  obtain ⟨h1, h2, h3⟩ := SqNum.ranks_exact D i j
  refine ⟨hmul (GlobalTheory.HeckeCharacterRestriction.isHecke_mu hL t j) (hpow _), hmul hchiE.1 (hpow _),
    resEta_parity (resEta_mul (GlobalTheory.HeckeCharacterRestriction.resEta_mu hL t j) (rpow _)) ?_,
    resEta_parity (resEta_mul rchi (rpow _)) ?_⟩ <;> omega

theorem isSelfDualC_neg' {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (h : IsSelfDualC A Λ) :
    IsSelfDualC (neg A) Λ := by
  refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [neg_gram, hc]
  · simp [neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

theorem exists_bottomTri {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (W : G.Weil) (i j : Fin D.R.m) :
    ∃ (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X := by
  obtain ⟨A, rA, hA1, hA2, hA3, hA4⟩ := exists_stdRig (D := D) (SqNum.botBig D i j)
  obtain ⟨A', rA', hB1, hB2, hB3, hB4⟩ := exists_stdRig (D := D) (SqNum.botSmall D i j)
  obtain ⟨WW, rW, hW1, hW2, hW3, hW4⟩ := exists_stdRig (D := D) (SqNum.botBig D i j + SqNum.botSmall D i j)
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hc := fun t => bottom_chars hL G i j t
  have hd : ∀ {χ η : (AE D)ˣ →* Circle}, IsHeckeChar D χ → IsHeckeChar D η → IsHeckeChar D (χ / η) := fun h1 h2 =>
    ⟨h1.1.div' h2.1, fun x => by rw [MonoidHom.div_apply, h1.2, h2.2, div_one]⟩
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true A WW (hc t).2.1 (hd (hc t).2.1 (hc t).1)
    (hA1 ▸ (hc t).2.2.2) (by rw [hW1, div_eq_mul_inv]; exact resEta_mul (hc t).2.2.2 (resEta_inv (hc t).2.2.1))
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false A' WW (hc t).1 (hd (hc t).1 (hc t).2.1)
    (hB1 ▸ (hc t).2.2.1) (by rw [hW1, div_eq_mul_inv, Nat.add_comm (SqNum.botBig D i j)]; exact resEta_mul (hc t).2.2.1 (resEta_inv (hc t).2.2.2))
  have s1 : (neg A).SigOK := sigOK_sgn true hA2
  obtain ⟨vac, hv⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (neg A) WW (fun τ => -rA.s τ) rW.s
    s1 hW2 (fun τ => isCartanInv_sgn true _ τ (hA4.2.2 τ).1) (fun τ => (hW4.2.2 τ).1) rA.Λ rW.Λ (isSelfDualC_neg' hA4.1) hW4.1
  obtain ⟨vac', hv'⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ A' WW rA'.s rW.s
    hB2 hW2 (fun τ => (hB4.2.2 τ).1) (fun τ => (hW4.2.2 τ).1) rA'.Λ rW.Λ hB4.1 hW4.1
  choose e he using GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G
  choose c hc' using fun t w => GlobalTheory.ConstRatio.exists_expAt (SqNum.nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ A WW rA rW _ _ _ _ _ hA4 hW4 (hd (hc t).1 (hc t).2.1) (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ A' WW rA' rW _ _ _ _ A.rank _ hB4 hW4 (hd (hc t).1 (hc t).2.1) (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas A
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas A'
  exact ⟨A, A', WW, ⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩, hA1, hB1, hA3, hB3, hW3,
    ⟨by rw [hA1, hB1, hW1], hA4, hB4, hW4, hω, hω', hv, hv', he, fun t w _ => hc' t w, hf, hf', hm, hm'⟩⟩

theorem IsBottomTri.integrable {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) :
    (∀ P g, IntegrableOn (X.ker W.ψ W.θ t P g) X.fd X.m) ∧ ∀ P g, IntegrableOn (X.ker' W.ψ W.θ t P g) X.fd' X.m' := by
  have h := hX.is
  have hA := GlobalTheory.ConstRatio.posDef_of_std hX.std
  have hA' := GlobalTheory.ConstRatio.posDef_of_std hX.std'
  refine ⟨fun P g => ?_, fun P g => ?_⟩
  · exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ true A WW _ _ (X.ω t) X.m X.fd _ (h.weil t) hA h.meas.1 h.meas.2
      (GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) h.isVac.1 h.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f h t).1 P)).1 g
  · exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D W.ψ false A' WW _ _ (X.ω' t) X.m' X.fd' _ (h.weil' t) hA' h.meas'.1 h.meas'.2
      (GlobalTheory.Chain.InnerSteps.theta_pureTensorO h.isVac'.1 h.isVac'.2.inf X.rA'.s X.rA'.B X.rW.s X.rW.B
        (GlobalTheory.ConstRatio.theta_f h t).2 P)).1 g

end GlobalTheory.RowTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceLevelOfEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_level_of_embedding : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (𝔪 : Ideal (𝓞 D.host.E)) (h : GA D A), Lev.finE B (stabilizerEmbedding d h) ∈ congLev D.sp.cm B.gram (d.lat Λ 𝔟) 𝔪 → Lev.finE A h ∈ congLev D.sp.cm A.gram Λ 𝔪 := by
  first | exact @GlobalTheory.LevRestrict.finE_mem_congLev | exact GlobalTheory.LevRestrict.finE_mem_congLev | (intros; apply GlobalTheory.LevRestrict.finE_mem_congLev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalScalarPrimeToConjPolarisationLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_global_scalar_prime_to_conj_polarisationLattice' : ∀ (D : D7) (n : ℕ) (Λ ΛT : Lt D.host.E n), IsAA Λ ΛT → ∀ P : Finset (Formalism.L2.DIV.Pl D.host.E), ∃ γ : D.host.E, γ ≠ 0 ∧ ∃ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) ∧ (∀ v ∈ Λ, ((s : D.host.E) * γ⁻¹) • v ∈ ΛT) ∧ (∀ v ∈ ΛT, ((s : D.host.E) * γ) • v ∈ Λ) := by
  first | exact @GlobalTheory.GenChoice.exists_global_scalar_prime_to_conj_polarisationLattice | exact GlobalTheory.GenChoice.exists_global_scalar_prime_to_conj_polarisationLattice | (intros; apply GlobalTheory.GenChoice.exists_global_scalar_prime_to_conj_polarisationLattice <;> assumption)
end

