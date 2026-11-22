import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause resL resR)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.DoublingTheta

section Matrices

variable (R : Type) [CommRing R] (m n : ℕ)

def inL : Matrix (Fin (m + n)) (Fin m) R :=
  (Matrix.fromRows (1 : Matrix (Fin m) (Fin m) R) (0 : Matrix (Fin n) (Fin m) R)).submatrix finSumFinEquiv.symm id

def inR : Matrix (Fin (m + n)) (Fin n) R :=
  (Matrix.fromRows (0 : Matrix (Fin m) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)).submatrix finSumFinEquiv.symm id

variable {R m n}

theorem inL_map {R' : Type} [CommRing R'] (f : R →+* R') : (inL R m n).map f = inL R' m n := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i
  · simp only [inL, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl,
      Matrix.one_apply]
    split_ifs <;> simp
  · simp only [inL, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inr,
      Matrix.zero_apply, map_zero]

theorem inR_map {R' : Type} [CommRing R'] (f : R →+* R') : (inR R m n).map f = inR R' m n := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i
  · simp only [inR, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inl,
      Matrix.zero_apply, map_zero]
  · simp only [inR, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.fromRows_apply_inr,
      Matrix.one_apply]
    split_ifs <;> simp

theorem mul_inL {l : ℕ} (x : Matrix (Fin l) (Fin (m + n)) R) :
    x * inL R m n = Matrix.of fun i j => x i (finSumFinEquiv (Sum.inl j)) := by
  ext i j
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp]
  simp only [inL, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]

theorem mul_inR {l : ℕ} (x : Matrix (Fin l) (Fin (m + n)) R) :
    x * inR R m n = Matrix.of fun i j => x i (finSumFinEquiv (Sum.inr j)) := by
  ext i j
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp]
  simp only [inR, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr, Matrix.one_apply, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, mul_ite,
    mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.of_apply]

theorem blkMat_inL (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    blkMat finSumFinEquiv a b * inL R m n = inL R m n * a := by
  rw [blkMat, inL, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, Matrix.mul_apply, Matrix.one_apply]

theorem blkMat_inR (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    blkMat finSumFinEquiv a b * inR R m n = inR R m n * b := by
  rw [blkMat, inR, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_mul_fromRows]
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective i <;>
    simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, Matrix.mul_apply, Matrix.one_apply]

variable [StarRing R]

theorem inL_inL : (inL R m n)ᴴ * inL R m n = 1 := by
  rw [mul_inL]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inL, Matrix.one_apply, eq_comm, apply_ite star]

theorem inR_inR : (inR R m n)ᴴ * inR R m n = 1 := by
  rw [mul_inR]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inR, Matrix.one_apply, eq_comm, apply_ite star]

theorem inR_inL : (inR R m n)ᴴ * inL R m n = 0 := by
  rw [mul_inL]; ext i j
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, inR]

end Matrices

variable {D : D7}

def sumDec (V W : HSp D) : GlobalTheory.MixModel.OrthDec (sumSp V W) V W where
  iA := inL D.host.E V.rank W.rank
  iB := inR D.host.E V.rank W.rank
  isoA := by
    change (inL D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inL D.host.E V.rank W.rank = V.gram
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inL, ← Matrix.mul_assoc, inL_inL, Matrix.one_mul]
  isoB := by
    change (inR D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inR D.host.E V.rank W.rank = W.gram
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inR, ← Matrix.mul_assoc, inR_inR, Matrix.one_mul]
  orth := by
    change (inR D.host.E V.rank W.rank)ᴴ * (show Matrix (Fin (V.rank + W.rank)) (Fin (V.rank + W.rank)) D.host.E from
      (hsum V W).gram) * inL D.host.E V.rank W.rank = 0
    rw [gram_hsum, Matrix.mul_assoc, blkMat_inL, ← Matrix.mul_assoc, inR_inL, Matrix.zero_mul]
  rank_add := rfl

theorem sumDec_jA (V W : HSp D) : (sumDec V W).jA = inL (AE D) V.rank W.rank := inL_map (incA D)

theorem sumDec_jB (V W : HSp D) : (sumDec V W).jB = inR (AE D) V.rank W.rank := inR_map (incA D)

theorem sumDec_emb (V W : HSp D) (g : GA D V) (g' : GA D W) : (sumDec V W).emb (g, g') = ioSum V W (g, g') := by
  refine GlobalTheory.MixModel.mt_injective _ ?_
  have hA : HMul.hMul (mt (sumSp V W) (ioSum V W (g, g'))) (sumDec V W).jA = HMul.hMul (sumDec V W).jA (mt V g) := by
    rw [sumDec_jA]; exact blkMat_inL (mt V g) (mt W g')
  have hB : HMul.hMul (mt (sumSp V W) (ioSum V W (g, g'))) (sumDec V W).jB = HMul.hMul (sumDec V W).jB (mt W g') := by
    rw [sumDec_jB]; exact blkMat_inR (mt V g) (mt W g')
  rw [GlobalTheory.MixModel.OrthDec.mt_emb, ← hA, ← hB, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add,
    GlobalTheory.MixModel.OrthDec.sum_eq_one, Matrix.mul_one]

theorem boxS_apply (A B : HSp D) (f : WO A B → ℂ) (f' : WO (negSp A) B → ℂ) (x : WO (dblSp A) B) :
    (sumDec A (negSp A)).boxS B f f' x = f (resL A B x) * f' (resR A B x) := by
  rw [GlobalTheory.MixModel.OrthDec.boxS, GlobalTheory.MixModel.OrthDec.resS_apply, sumDec_jA, sumDec_jB]
  exact congrArg₂ (· * ·) (congrArg f (mul_inL x)) (congrArg f' (mul_inR x))

theorem thetaClause : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → IsWeilDatumO ψ (dblSp A) B 1 χB omh →
    ThetaClause ψ A B χB om omh := by
  intro D ψ A B χA χB om omh hom homh f₁ f₂ h₁ h₂
  refine ⟨GlobalTheory.T.isThetaFunction_doublingSeesaw_of_standard_char D ψ A B hom.std f₁ f₂ h₁ h₂, fun g₁ g₂ h => ?_⟩
  obtain ⟨hθ, om', hom', hact⟩ := GlobalTheory.T.exists_conjugate_weilDatum_hermitianSpaceNeg D ψ A B χA χB om hom
  have hT := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hom.std (sumSp A (negSp A)) A (negSp A) (sumDec A (negSp A)) B
  have hh : IsWeilDatumO ψ (sumSp A (negSp A)) B (χA * χA⁻¹) χB omh := by rw [mul_inv_cancel]; exact homh
  have key := hT.om_box χA χA⁻¹ χB omh om om' hh hom hom' g₁ ((negEquiv A).symm g₂) h f₁ _ h₁ (hθ f₂ h₂)
  rw [hact _ h f₂ h₂, sumDec_emb, io_eq_ioSum, MulEquiv.apply_symm_apply] at key
  have e : (sumDec A (negSp A)).boxS B f₁ (fun x => conj (f₂ (-x))) = delta A B f₁ f₂ :=
    funext fun x => boxS_apply A B _ _ x
  have main : omh (io A (g₁, g₂), h) (delta A B f₁ f₂) =
      (((χB (detA A g₂))⁻¹ : Circle) : ℂ) • delta A B (om (g₁, h) f₁) (om (g₂, h) f₂) := by
    rw [← e]
    refine key.trans (funext fun x => (boxS_apply A B _ _ x).trans ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨main, ?_⟩
  have zL : resL A B 0 = 0 := rfl
  have zR : resR A B 0 = 0 := rfl
  rw [thetaKO, main]
  simp only [thetaKO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.smul_apply, smul_eq_mul, zL, zR, neg_zero]
  ring

end GlobalTheory.DoublingTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingOpenOrbitUnfoldsToAdelicIntegral
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.OpenOrbit

open Set Filter GlobalTheory.Eis

variable {D : D7} {V : HSp D}

theorem io_one_mul (δ : GA D V) (x : GA D V × GA D V) : io V (δ, 1) * io V x = io V (δ * x.1, x.2) := by
  rw [← map_mul]; congr 1; ext <;> simp

section Terms

variable {μ : (AE D)ˣ →* Circle} {φ : GA D (dblSp V) → ℂ} {f₁ f₂ : GA D V → ℂ}

theorem term_eq (hf₁ : ∀ γ ∈ GQ V, ∀ g, f₁ (γ * g) = f₁ g) (δ : GQ V) (x : GA D V × GA D V) :
    dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ x =
      dblIntegrand V μ φ f₁ f₂ ((δ : GA D V) * x.1, x.2) := by
  simp only [dblIntegrand, io_one_mul, hf₁ _ δ.2]

theorem tsum_open_ne_top (hμ : IsHeckeChar D μ) {a : GL (Fin V.rank) (AE D)} {s : ℂ} (hφ : φ ∈ degPS V a μ s)
    {m : Measure (GA D V)} [SFinite m] {𝓕 : Set (GA D V)}
    (h : ∑' q : SiegelCosets V, ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m ≠ ⊤) :
    ∑' δ : GQ V, ∫⁻ x, ‖dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ x‖ₑ
      ∂(m.restrict 𝓕).prod (m.restrict 𝓕) ≠ ⊤ := by
  rw [Measure.prod_restrict]
  refine ne_top_of_le_ne_top h (le_trans (le_of_eq (tsum_congr fun δ => ?_))
    (ENNReal.tsum_comp_le_tsum_of_injective (injective_mk_io (V := V)) (fun q : SiegelCosets V => ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m)))
  set q : SiegelCosets V := mk _ ⟨io V (δ, 1), io_mem_GQ V δ.2 (one_mem _)⟩ with hq
  have e : (mk _ q.out : SiegelCosets V) = mk _ ⟨io V (δ, 1), io_mem_GQ V δ.2 (one_mem _)⟩ := Quotient.out_eq q
  obtain ⟨p, hp⟩ := mk_eq_iff.1 e
  have hE : (fun y => φ (io V (δ, 1) * y)) = fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x) := by
    funext y
    have h1 : io V (δ, 1) = ((p : GQ (dblSp V)) : GA D (dblSp V)) * ((q.out : GQ (dblSp V)) : GA D (dblSp V)) :=
      (congrArg Subtype.val hp).symm
    rw [h1, mul_assoc]
    exact apply_siegelQ_mul V a hμ hφ ⟨Subgroup.mem_subgroupOf.1 p.2, (p : GQ (dblSp V)).2⟩ _
  beta_reduce
  rw [hE]

theorem leftInv_open (hμ : IsHeckeChar D μ) {a : GL (Fin V.rank) (AE D)} {s : ℂ} (hφ : φ ∈ degPS V a μ s)
    (hf₁ : ∀ γ ∈ GQ V, ∀ g, f₁ (γ * g) = f₁ g) (hf₂ : ∀ γ ∈ GQ V, ∀ g, f₂ (γ * g) = f₂ g) :
    LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂) := by
  rintro ⟨γ₁, γ₂⟩ ⟨h1, h2⟩ ⟨x₁, x₂⟩
  have hs : ∑' δ : GQ V, φ (io V (δ, 1) * io V ((γ₁, γ₂) * (x₁, x₂))) =
      ∑' δ : GQ V, φ (io V (δ, 1) * io V (x₁, x₂)) := by
    let e : GQ V ≃ GQ V := (Equiv.mulLeft (⟨γ₂, h2⟩ : GQ V)⁻¹).trans (Equiv.mulRight ⟨γ₁, h1⟩)
    conv_rhs => rw [← e.tsum_eq]
    refine tsum_congr fun δ => ?_
    simp only [io_one_mul, Prod.mk_mul_mk]
    have := apply_io_mul V a hφ γ₂ ((e δ : GA D V) * x₁) x₂
    rw [apply_detA hμ h2, Circle.coe_one, one_mul] at this
    rw [← this]
    congr 3
    simp [e, mul_assoc]
  simp only [dblIntegrand]
  rw [hs]
  simp only [Prod.mk_mul_mk, hf₁ _ h1, hf₂ _ h2, map_mul, apply_detA hμ h2, one_mul]

end Terms

theorem open_orbit : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ZetaConvH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) ∧ ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = zetaH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  haveI := hm
  have hF : IsFundamentalDomain (GQ V) (stdDom (GQ V)) m := isFundamentalDomain_stdDom _ m
  set 𝓕 := stdDom (GQ V) with h𝓕
  have hφc : Continuous φ := hφ.2.1
  set E : GA D (dblSp V) → ℂ := fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y) with hEdef
  set H : GA D V × GA D V → ℂ := dblIntegrand V μ φ f₁ f₂ with hHdef
  set T : GQ V → GA D V × GA D V → ℂ := fun δ => dblIntegrand V μ (fun y => φ (io V (δ, 1) * y)) f₁ f₂ with hTdef
  set K : GA D V × GA D V → ℂ := fun p => H (p.1 * p.2, p.1) with hKdef
  have hHc : Continuous H := continuous_dblIntegrand hμ hφc h₁.continuous h₂.continuous
  have hT : ∀ (δ : GQ V) (x : GA D V × GA D V), T δ x = H ((δ : GA D V) * x.1, x.2) := fun δ x => term_eq h₁.1 δ x
  have hTc : ∀ δ : GQ V, Continuous (T δ) := fun δ => by
    rw [show T δ = fun x => H ((δ : GA D V) * x.1, x.2) from funext (hT δ)]
    exact hHc.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hTm : ∀ δ : GQ V, Measurable fun x => ‖T δ x‖ₑ := fun δ => (hTc δ).measurable.enorm
  have hKc : Continuous K := hHc.comp ((continuous_fst.mul continuous_snd).prodMk continuous_fst)

  have hbd : ∑' δ : GQ V, ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕) ≠ ⊤ :=
    tsum_open_ne_top hμ hφ ((GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂).1 𝓕 hF)
  have hTint : ∀ δ : GQ V, Integrable (T δ) ((m.restrict 𝓕).prod (m.restrict 𝓕)) := fun δ =>
    ⟨(hTc δ).aestronglyMeasurable, lt_of_le_of_lt
      (ENNReal.le_tsum (f := fun δ : GQ V => ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕)) δ)
      (lt_top_iff_ne_top.2 hbd)⟩

  have hlin : ∀ x₂, ∫⁻ x₁, ‖H (x₁, x₂)‖ₑ ∂m = ∑' δ : GQ V, ∫⁻ x₁ in 𝓕, ‖T δ (x₁, x₂)‖ₑ ∂m := fun x₂ => by
    rw [hF.lintegral_eq_tsum'' (fun x₁ => ‖H (x₁, x₂)‖ₑ)]
    refine tsum_congr fun δ => ?_
    simp only [hT, Subgroup.smul_def, smul_eq_mul]
  have hlK : ∫⁻ p, ‖K p‖ₑ ∂(m.restrict 𝓕).prod m =
      ∑' δ : GQ V, ∫⁻ x, ‖T δ x‖ₑ ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [lintegral_prod _ hKc.measurable.enorm.aemeasurable]
    have h1 : ∀ x₂, ∫⁻ g, ‖K (x₂, g)‖ₑ ∂m = ∫⁻ x₁, ‖H (x₁, x₂)‖ₑ ∂m := fun x₂ =>
      lintegral_mul_left_eq_self (fun x₁ => ‖H (x₁, x₂)‖ₑ) x₂
    simp_rw [h1, hlin]
    rw [lintegral_tsum (fun δ => ((hTm δ).lintegral_prod_left').aemeasurable)]
    refine tsum_congr fun δ => ?_
    rw [lintegral_prod_symm _ (hTm δ).aemeasurable]
  have hKint : Integrable K ((m.restrict 𝓕).prod m) :=
    ⟨hKc.aestronglyMeasurable, show ∫⁻ p, ‖K p‖ₑ ∂(m.restrict 𝓕).prod m < ⊤ by rw [hlK]; exact lt_top_iff_ne_top.2 hbd⟩
  have hHint : ∀ᵐ x₂ ∂(m.restrict 𝓕), Integrable (fun x₁ => H (x₁, x₂)) m := by
    filter_upwards [hKint.prod_right_ae] with x₂ hx
    have := hx.comp_mul_left x₂⁻¹
    simpa [hKdef, mul_inv_cancel_left] using this

  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_open hμ hφ h₁.1 h₂.1
  have hQ : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
    funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hli _ _)
  have hmp : MeasurePreserving (Prod.map (sec (GQ V)) (sec (GQ V))) ((autMeasure V m).prod (autMeasure V m))
      ((m.restrict 𝓕).prod (m.restrict 𝓕)) := measurePreserving_sec.prod measurePreserving_sec
  have S3 : ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m) =
      ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [hQ]; exact hmp.integral_comp (measurableEmbedding_sec.prodMap measurableEmbedding_sec) _
  have S4 : ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) =
      ∑' δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := by
    rw [← integral_tsum (fun δ => (hTc δ).aestronglyMeasurable) hbd]
    congr 1; funext x
    simp only [hTdef, hEdef, dblIntegrand, mul_assoc]
    exact tsum_mul_right.symm
  have S5 : ∀ δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) =
      ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := fun δ => integral_prod_symm _ (hTint δ)
  have S6 : ∑' δ : GQ V, ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m =
      ∫ x₂ in 𝓕, ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := by
    refine (integral_tsum (fun δ => ?_) ?_).symm
    · exact (((hTc δ).comp continuous_swap).aestronglyMeasurable
        (μ := (m.restrict 𝓕).prod (m.restrict 𝓕))).integral_prod_right'
    · refine ne_top_of_le_ne_top hbd (ENNReal.tsum_le_tsum fun δ => ?_)
      rw [lintegral_prod_symm _ (hTm δ).aemeasurable]
      exact lintegral_mono fun x₂ => enorm_integral_le_lintegral_enorm _
  have S7 : ∀ᵐ x₂ ∂(m.restrict 𝓕), ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m = ∫ x₁, H (x₁, x₂) ∂m := by
    filter_upwards [hHint] with x₂ hx
    rw [hF.integral_eq_tsum'' _ hx]
    refine tsum_congr fun δ => ?_
    simp only [hT, Subgroup.smul_def, smul_eq_mul]
  have S8 : ∀ x₂, ∫ x₁, H (x₁, x₂) ∂m = ∫ g, K (x₂, g) ∂m := fun x₂ =>
    (integral_mul_left_eq_self (fun x₁ => H (x₁, x₂)) x₂).symm
  have S9 : ∫ x₂ in 𝓕, ∫ g, K (x₂, g) ∂m ∂m = ∫ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m ∂m := by
    rw [← integral_prod _ hKint, integral_prod_symm _ hKint]
  have MirabolicColumnBlock : ∀ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m = φ (io V (g, 1)) * conj (petCoef V m f₁ f₂ g) := fun g => by
    have hl1 : LeftInv (GQ V) (rTr V g f₁) := fun γ hγ x => (h₁.mul_right g).1 γ hγ x
    have hl2 : LeftInv (GQ V) f₂ := h₂.1
    simp only [petCoef]
    rw [petersson_eq hF hl1 hl2, ← integral_conj, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x₂ => ?_)
    simp only [hKdef, hHdef, dblIntegrand_mul hφ, rTr, map_mul, Complex.conj_conj]
    ring
  refine ⟨?_, ?_⟩
  · rw [zetaConvH_iff]
    exact hKint.integral_prod_right.congr (Eventually.of_forall fun g => MirabolicColumnBlock g)
  · calc ∫ q, dblIntegrandQ V μ E f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m)
        = ∫ x, dblIntegrand V μ E f₁ f₂ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := S3
      _ = ∑' δ : GQ V, ∫ x, T δ x ∂(m.restrict 𝓕).prod (m.restrict 𝓕) := S4
      _ = ∑' δ : GQ V, ∫ x₂ in 𝓕, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := tsum_congr S5
      _ = ∫ x₂ in 𝓕, ∑' δ : GQ V, ∫ x₁ in 𝓕, T δ (x₁, x₂) ∂m ∂m := S6
      _ = ∫ x₂ in 𝓕, ∫ x₁, H (x₁, x₂) ∂m ∂m := integral_congr_ae S7
      _ = ∫ x₂ in 𝓕, ∫ g, K (x₂, g) ∂m ∂m := integral_congr_ae (Eventually.of_forall S8)
      _ = ∫ g, ∫ x₂ in 𝓕, K (x₂, g) ∂m ∂m := S9
      _ = ∫ g, φ (io V (g, 1)) * conj (petCoef V m f₁ f₂ g) ∂m := integral_congr_ae (Eventually.of_forall MirabolicColumnBlock)
      _ = zetaH D.sp.cm.sig (gram_hdbl V) m φ (petCoef V m f₁ f₂) := (zetaH_eq _ _ _ _).symm

end GlobalTheory.Core.Rk.OpenOrbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis

theorem zetaHolValueAt_of_heightBounds (l1 : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) (l2 : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q) : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) := by
  intro D V μ hμ m hm Φ hE ha hreg f₁ f₂ h₁ h₂ hZ s₀ E₀ hv
  obtain ⟨C', c, hio⟩ := l1 D V
  have key : ∀ (H : ℂ → GA D (dblSp V) → ℂ) (z : ℂ) (r : ℝ), 0 < r →
      (∀ s ∈ ball z r, LeftInv (GQ (dblSp V)) (H s)) →
      (∀ g, DifferentiableOn ℂ (H · g) (ball z r)) →
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball z r ×ˢ univ) →
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball z r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
      (∀ s ∈ ball z r, DblConv V μ m (H s) f₁ f₂) ∧
        DifferentiableOn ℂ (fun s => dblInt V μ m (H s) f₁ f₂) (ball z r) := by
    rintro H z r hr hinv hd hc ⟨C, N, hb⟩
    obtain ⟨bound, hbi, hbd⟩ := l2 D V μ m hm f₁ f₂ h₁ h₂ C' c hio C N
    have hcont : ∀ s ∈ ball z r, Continuous (H s) := fun s hs =>
      hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    have hli : ∀ s ∈ ball z r, LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (H s) f₁ f₂) := fun s hs =>
      leftInv_dblIntegrand hμ (hinv s hs) h₁.1 h₂.1
    have hmeas : ∀ s ∈ ball z r, AEStronglyMeasurable (dblIntegrandQ V μ (H s) f₁ f₂)
        ((autMeasure V m).prod (autMeasure V m)) := by
      intro s hs
      have e' : dblIntegrandQ V μ (H s) f₁ f₂ =
          dblIntegrand V μ (H s) f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
        funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk (hli s hs) _ _)
      rw [e']
      exact ((continuous_dblIntegrand hμ (hcont s hs) h₁.continuous h₂.continuous).measurable.comp
        (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
    refine ⟨fun s hs => ⟨hli s hs, hbi.mono' (hmeas s hs) (ae_of_all _ fun q => hbd (H s) (hinv s hs) (hb s hs) q)⟩, ?_⟩
    have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
      (μ := (autMeasure V m).prod (autMeasure V m)) (F := fun q s => dblIntegrandQ V μ (H s) f₁ f₂ q)
      (isOpen_ball (x := z) (ε := r)) hmeas
      (ae_of_all _ fun q => by
        simp only [dblIntegrandQ, dblIntegrand]
        exact (((hd _).mul_const _).mul_const _).mul_const _)
      fun x hx => ⟨ball z r, isOpen_ball.mem_nhds hx, bound, hbi,
        ae_of_all _ fun q y hy => hbd (H y) (hinv y hy) (hb y hy) q⟩
    exact this.1
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  set Z : ℂ → ℂ := fun s => dblInt V μ m (eisCont V Φ s) f₁ f₂ with hZdef
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, r, H, hr, e, hd, hc, C, N, hb⟩ := hreg s₁
    have hinvH : ∀ s ∈ ball s₁ r, LeftInv (GQ (dblSp V)) (H s) := by
      intro s hs γ hγ g
      rcases eq_or_ne s s₁ with rfl | h0
      · have t1 := ((hd (γ * g)).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        have t2 := ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        refine tendsto_nhds_unique t1 (t2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with w h1 h2
        rw [e w h2 h1, e w h2 h1, hinvE w γ hγ g]
      · rw [e s hs h0, e s hs h0, hinvE s γ hγ g]
    have han : AnalyticAt ℂ (fun s => dblInt V μ m (H s) f₁ f₂) s₁ :=
      (key H s₁ r hr hinvH hd hc ⟨C, N, hb⟩).2.analyticAt (ball_mem_nhds _ hr)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * dblInt V μ m (H s) f₁ f₂) s₁ := by
      have : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
      exact (this.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr)] with w h1 h2
    have e1 : eisCont V Φ w = ((w - s₁) ^ k)⁻¹ • H w := by
      funext g
      rw [Pi.smul_apply, e w h2 h1 g, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H w) (f₁ := f₁) (f₂ := f₂) ((w - s₁) ^ k)⁻¹ 1 1
    simp only [one_smul, map_one, mul_one] at e2
    simp only [Z, e1, e2]
  have hext : IsMerExt (zeta V μ m Φ f₁ f₂) univ Z := by
    refine ⟨isRightDomain_univ, fun s _ => hmer s, (V.rank : ℝ) / 2, fun s hs => ?_⟩
    have : eisCont V Φ s = eis V (Φ s) := funext fun g => eqOn_cont (ha g) hs
    simp only [Z, zeta, this]
  obtain ⟨k, hk⟩ := hreg s₀
  obtain ⟨r, hr, hd, hc, C, N, hb⟩ := hk.of_eisValueAt hv
  obtain ⟨hconv, hdiff⟩ := key (eisCont V Φ) s₀ r hr (fun s _ => hinvE s) hd hc ⟨C, N, hb⟩
  have e0 := hv.eisCont_eq
  refine ⟨e0 ▸ hconv s₀ (mem_ball_self hr), hZ, Z, hext.isExtAt trivial, hdiff.analyticAt (ball_mem_nhds _ hr), ?_⟩
  simp only [Z, e0]

theorem zetaHolValueAt_of_eisValueAt : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) :=
  zetaHolValueAt_of_heightBounds GlobalTheory.T.exists_height_doublingEmbedding_le_pow_mul_heights GlobalTheory.T.exists_integrable_bound_doubling_integrand_quotient

end GlobalTheory.Eis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBadPrimeOverChartBadPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over_sub : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) := by
  intro B X I hOk _ l Z a v hv
  obtain ⟨P, hP, hPv⟩ := exists_SBof_over I hOk l Z a v hv
  exact ⟨⟨P, hP⟩, hPv⟩

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenominatorAvoidingGivenPrimesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_avoiding_given_primes : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)) (G : HeightOneSpectrum (𝓞 E) → Prop) (c : ℕ), 0 < c → ∀ x : Formalism.L2.Col.HomE E a b, (c : E) • x ∈ M → (∀ Q : HeightOneSpectrum (𝓞 E), ¬ G Q → x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M) → ∃ d : 𝓞 E, d ≠ 0 ∧ (d : E) • x ∈ M ∧ ∀ Q : HeightOneSpectrum (𝓞 E), (c : 𝓞 E) ∈ Q.asIdeal → d ∈ Q.asIdeal → G Q := by
  first | exact @GlobalTheory.OffDen.exists_den_avoid | exact GlobalTheory.OffDen.exists_den_avoid | (intros; apply GlobalTheory.OffDen.exists_den_avoid <;> assumption)
end

