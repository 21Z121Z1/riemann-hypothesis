import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0355
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0354
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0314
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem kernelSite_seriesData_below_lastStep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hP hPos hSc
  refine ⟨?_, ?_, ?_, hSc, J.rho std, ?_, ?_, ?_⟩
  · intro j hj L0 hL0 La' hLa'
    exact (hP j hj L0 La' (repOf_lat _ _ j L0 hL0) hLa').1
  · obtain ⟨hpos, hS⟩ := GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors t std J
    exact ⟨hpos, fun hd => GlobalTheory.T.site_residue_char_not_mem_bad_primes t std J (hS _ Fact.out hd)⟩
  · exact ⟨(t.O u μ).S, GlobalTheory.T.site_residue_char_not_mem_bad_primes t std J, fun j _ L0 _ La' _ y => GlobalTheory.T.intOff_xi0_of_joint t std J S j L0 La' y⟩
  · exact GlobalTheory.TwU.lamPosG_of_lamPos _ S.E D _ _ _ hPos
  · exact fun j La v => GlobalTheory.isUnit_det_frameMatrix_ofCharts _ _ _ j La v
  · refine GlobalTheory.T.orthonormal_local_bases_carry_witt_lattices _ S.hfin D (J.fd std) (J.rho std) (halfDiffInv_integral_at_split D _ _ hg) ?_
    intro j hj La La' h1 h2
    have q := hP j hj La La' h1 h2
    exact ⟨q.1, fun v => ⟨(q.2.2.2.2.2.2.2 v).2.2.1, (q.2.2.2.2.2.2.2 v).2.2.2⟩⟩

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteValuesAtPointIffRealisesInStdCoords
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem realAt_iff_realises : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) (e : D.what₂.Tau → ℤ) (φ : (D.chTw u μ).cls j → (D.chTw u μ).Y j → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), (∀ y, φ (clsAt X H j La.1 La.2) y = (∏ τ, (D.chTw u μ).de j y τ ^ e τ)⁻¹ * frPoly (t.O u μ) j P y) → ∀ V, RealAt d j hj h La φ V ↔ Realises (sysS H X std) D (hT.gat_pos u w hg) j h (fun τ => e τ - cTw D j) (sPt d j hj La • P) (actC (sysS H X std) D (hT.gat_pos u w hg) j h (mM d j hj La) V)) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj h La e φ P hφ V
  have hp := J.pins.frm j hj
  have hde := (t.O u μ).frm_de j hj

  have hdetU : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, IsUnit ((A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ)).det := by
    intro A τ
    have e1 := RingHom.map_det (embT D τ) (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)
    rw [RingHom.mapMatrix_apply] at e1
    rw [← e1]
    exact (Matrix.isUnits_det_units A).map _
  have hmul : ∀ (A A' : GL (Fin (D.R.N j)) D.host.E) τ, ((A * A' : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) =
      (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * (A' : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) := by
    intro A A' τ
    rw [Units.val_mul, Matrix.map_mul]
  have hinv : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, ((A⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
      (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) = 1 := by
    intro A τ
    rw [← hmul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinv' : ∀ (A : GL (Fin (D.R.N j)) D.host.E) τ, (A : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
      ((A⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) = 1 := by
    intro A τ
    rw [← hmul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMB : mM d j hj La * (bAt J j hj La.1)⁻¹ = J.A.crd j hj * (d.gam j hj La)⁻¹ := by
    unfold mM
    exact mul_inv_cancel_right _ _
  have hat : ∀ τ, (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) =
      (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) *
        ((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ) := by
    intro τ
    rw [hMB, ← hmul]
    rfl

  have alg : ∀ (z' : Fr D j hj) (f : Fr1 D (D.R.N j)),
      (∀ τ, f.1 τ = (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ) →
      d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j *
          dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' *
          φ (clsAt X H j La.1 La.2) ((J.St j hj).eY.symm z') =
        (∏ τ, (f.1 τ).det ^ (-(e τ - cTw D j))) * GL3Theta.evFr D (sPt d j hj La • P) f.1 := by
    intro z' f hf
    have hfr : (t.O u μ).frm j ((J.St j hj).eY.symm z') = f.1 := by
      funext τ
      rw [hp, Equiv.apply_symm_apply, hf]
      rfl
    have hfp : frPoly (t.O u μ) j P ((J.St j hj).eY.symm z') = GL3Theta.evFr D P f.1 := by
      rw [← hfr]
      rfl
    have hdef : ∀ τ, (D.chTw u μ).de j ((J.St j hj).eY.symm z') τ = (f.1 τ).det := fun τ => by rw [hde, hfr]
    have hsm : GL3Theta.evFr D (sPt d j hj La • P) f.1 = sPt d j hj La * GL3Theta.evFr D P f.1 := by
      unfold GL3Theta.evFr
      rw [MvPolynomial.smul_eval]
    rw [hφ, hfp, hsm]
    simp only [hdef]
    have ha : ∀ τ, embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det ≠ 0 := fun τ =>
      ((Matrix.isUnits_det_units (J.A.crd j hj)).map (embT D τ)).ne_zero
    have hw : ∀ τ, (z'.1 τ).det ≠ 0 := fun τ => (z'.2 τ).ne_zero
    have hdf : ∀ τ, (f.1 τ).det = embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det * (z'.1 τ).det := by
      intro τ
      rw [hf, Matrix.det_mul, RingHom.map_det, RingHom.mapMatrix_apply]
    have huB : dPow (uB J j hj La.1).1 (fun _ => -(cTw D j)) =
        ∏ τ, (embT D τ (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det *
          embT D τ (bAt J j hj La.1 : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).det) ^ (-(cTw D j)) := by
      unfold dPow uB
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [Units.val_mul, Matrix.det_mul, map_mul]
    have hprod : dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' * (∏ τ, (f.1 τ).det ^ e τ)⁻¹ =
        (∏ τ, (f.1 τ).det ^ (-(e τ - cTw D j))) * dPow (uB J j hj La.1).1 (fun _ => -(cTw D j)) := by
      rw [huB]
      unfold dPow detF
      rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [hdf τ]
      have h1 := ha τ
      have h2 := hw τ
      rw [mul_zpow, mul_zpow, mul_zpow, neg_sub, zpow_sub₀ h1, zpow_sub₀ h2, zpow_neg, zpow_neg]
      field_simp
    unfold sPt
    linear_combination (d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j * GL3Theta.evFr D P f.1) * hprod
  unfold RealAt Realises
  constructor
  · intro hR f
    let z' : Fr D j hj := ⟨fun τ => ((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ) * f.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (f.2 τ)⟩
    let z : Fr D j hj := ⟨fun τ => (d.gam j hj La : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (z'.2 τ)⟩
    have hzz : IsTr (atInf (embT D) (d.gam j hj La).1) z' z := fun τ => rfl
    have hf' : ∀ τ, f.1 τ = (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ := by
      intro τ
      show _ = _ * (_ * _)
      rw [← Matrix.mul_assoc, hinv', Matrix.one_mul]
    have hfz : ∀ τ, f.1 τ = (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) * z.1 τ := by
      intro τ
      rw [hat]
      show _ = _ * _ * (_ * _)
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ)), hinv, Matrix.one_mul, hf']
    have key := (GlobalTheory.T.evalBasisCoords_against_blockAction (sysS H X std) D (hT.gat_pos u w hg) j h (gramC (gramN D j hj) (embT D)) (bAt J j hj La.1)
      (mM d j hj La) V z f hfz).1
    rw [← key, hR z z' hzz, alg z' f hf']
  · intro hR z z' hzz
    let f : Fr1 D (D.R.N j) := ⟨fun τ => (J.A.crd j hj : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * z'.1 τ,
      fun τ => by rw [Matrix.det_mul]; exact (hdetU _ τ).mul (z'.2 τ)⟩
    have hfz : ∀ τ, f.1 τ = (atR D (mM d j hj La * (bAt J j hj La.1)⁻¹) τ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) ℂ) * z.1 τ := by
      intro τ
      rw [hat, hzz τ]
      show _ = _ * _ * ((d.gam j hj La : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ) * _)
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (((d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E).1.map (embT D τ)), hinv, Matrix.one_mul]
    have key := (GlobalTheory.T.evalBasisCoords_against_blockAction (sysS H X std) D (hT.gat_pos u w hg) j h (gramC (gramN D j hj) (embT D)) (bAt J j hj La.1)
      (mM d j hj La) V z f hfz).1
    rw [key, hR f, alg z' f (fun τ => rfl)]

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepCharacterAtLevelDetMulLocalCharacters
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopMuDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := intAtA_mul
  one_mem' := by simpa using intAtA_int (F := F) (P := P) 1
  add_mem' := intAtA_add
  zero_mem' := by simpa using intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := intAtA_mul (intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add, e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add, Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

end Frame

end GlobalTheory.TopMuDet

end

theorem GlobalTheory.TwTop.muOf_det_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))) (z : SB t μ → t.X.K)
    (g' : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1)))) (z' : SB t μ → t.X.K),
    (∀ P, A.cplRel β P (g P) (z P) ∧ InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 (g P)) →
    (∀ P, TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P (g' P) (z' P) ∧
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 (g' P)) →
    muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hMu hi β β' κ κ' g z g' z' hg hg'
  have hlt : t.m2 + 1 < D.R.m := by omega
  have hok := (t.idx_ok μ).cst_ok
  obtain ⟨h1, -⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu (t.m2 + 1) hlt (t.m2 + 1) (Nat.le_of_succ_le hi) β κ
    (fun P => ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.TopMuDet.det_inFrame t.seam _ _ (hok.D_pos P) (hg P).2)
  have hdep : ∀ P : SB t μ, 1 ≤ topDep t.sel (t.tup μ) (t.cst μ) P := by
    intro P
    unfold topDep
    split_ifs
    · exact le_rfl
    · have := hok.M_pos
      omega
  obtain ⟨-, h2⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu (t.m2 + 1) hlt (t.m2 + 1 + 1) hi β' κ'
    (fun P => ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.TopMuDet.det_inFrame t.seam _ _ (hdep P) (hg' P).2)
  rw [Finset.prod_mul_distrib, map_mul, ← mul_assoc, h1, one_mul, h2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatAdLocOf
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem latAdLoc_of : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), SplAlg A → LocInt A → Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ → LatAdLoc A Lb := by
  intro F E _ _ _ _ _ n p G A Lb hS hI hfin hspan y v
  letI : StarRing E := starRingOfComm
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F) :=
    Units.val (bc (prV (E := E) (A.pl v).1) y : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) with hY
  set f : E ⊗[F] (A.pl v).1.adicCompletion F →+* G.P.Qq v :=
    ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp (A.ph v) with hf
  have hfac : ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) = Y.map f := by
    rw [hY]; ext i j; rfl
  have hmv : ∀ u : Fin n → E ⊗[F] (A.pl v).1.adicCompletion F,
      (fun k => (A.eQ v).symm (A.ph v ((Y *ᵥ u) k))) =
        ((facQ A v y : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ
          (fun k => (A.eQ v).symm (A.ph v (u k))) := by
    intro u
    rw [hfac]
    funext k
    exact RingHom.map_mulVec f Y u k
  ext z'
  rw [locSp_eq_image A hS hI v, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, hzz⟩
    rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan] at hz
    set u := Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ z with hu
    refine ⟨fun k => (A.eQ v).symm (A.ph v (u k)), (locSp_eq_image A hS hI v Lb _).2 ⟨u, hz, fun k => rfl⟩, ?_⟩
    have hzu : z = Y *ᵥ u := by
      rw [hu, hY, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    show (facQ A v y : Matrix (Fin n) (Fin n) (G.P.Qq v)) *ᵥ _ = z'
    rw [← hmv, ← hzu]
    funext k
    exact hzz k
  · rintro ⟨w, hw, hwz⟩
    obtain ⟨u, hu, huw⟩ := (locSp_eq_image A hS hI v Lb w).1 hw
    refine ⟨Y *ᵥ u, ?_, ?_⟩
    · have hback : Units.val ((bc (prV (E := E) (A.pl v).1) y)⁻¹ : GL (Fin n) (E ⊗[F] (A.pl v).1.adicCompletion F)) *ᵥ
          (Y *ᵥ u) = u := by
        rw [hY, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [GlobalTheory.LocCarry.mem_latS_latAd_iff y Lb hfin hspan]
      rw [hback]
      exact hu
    · intro k
      have hw' : w = fun k => (A.eQ v).symm (A.ph v (u k)) := funext fun k => (huw k).symm
      subst hwz
      subst hw'
      exact congrFun (hmv u) k

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleLevelZeroPointIsComponentPoint
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem latticeTupleLevelZero_point_isComponentPoint : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin (((sysS H X std).Pj 0).m + 1)) (((sysS H X std).Pj 0).Qq v), (∀ v, La.2 v = colSpan (((sysS H X std).Pj 0).W v) (g v).1) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 g (J.pt std 0 (Nat.zero_le _) La).1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD La hLa
  obtain ⟨⟨hr, he⟩, -⟩ := hD 0 (Nat.zero_le _) La hLa
  simp only [Joint.cp, cpAt, chAt] at he
  refine ⟨basesAt (chainAt H hT) std _ _ _ _ _ _ _ 0 La.2, fun v => ?_, ?_⟩
  · unfold basesAt
    obtain ⟨g0, hg0⟩ := Formalism.MainNotions.G.KAat.exists_bases1 La.2 hLa
    exact Classical.epsilon_spec (⟨g0 v, hg0 v⟩ : ∃ g : GL (Fin (((sysS H X std).Pj 0).m + 1)) (((sysS H X std).Pj 0).Qq v),
      La.2 v = colSpan (((sysS H X std).Pj 0).W v) (g : Matrix _ _ _))
  · rw [he]
    convert (Classical.epsilon_spec (GlobalTheory.TwU.exists_unitary_pt J.one.good La.1
      (basesAt (chainAt H hT) std _ _ _ _ _ _ _ 0 La.2))).1 using 1
    ext i j
    rfl

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleSuccLevelPointIsComponentPointInChar
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

theorem reGL_finCongr_twice {R : Type} [CommRing R] {a b : ℕ} (h1 : a = b) (h2 : b = a) (x : GL (Fin a) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h2) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h1) x) = x := by
  subst h1
  apply Units.ext
  ext r s
  rfl

set_option maxHeartbeats 1000000 in

theorem ptS_isPt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v), (∀ v, La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g v).1) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g (J.pt std (j + 1) hj La).1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD j hj La hLa
  obtain ⟨⟨hr, hx⟩, -⟩ := hD (j + 1) hj La hLa
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  refine ⟨Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2, fun v => ?_, ?_⟩
  · obtain ⟨g, hg'⟩ := (Formalism.L2.G.Cmp.isLattice_iff _ (La.2 v)).1 (hLa v)
    exact Classical.epsilon_spec (p := fun g0 : GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v) =>
      La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g0 : Matrix _ _ _)) ⟨g, by rw [hg', Formalism.L2.G.Cmp.colSpan_eq]⟩
  · have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
      show (dite (j + 1 ≤ D.R.m) _ _ : PtCh _ _).y = _
      rw [dif_pos hj]
    rw [hx, hy, reGL_finCongr_twice]
    exact (Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
          (Formalism.L2.PairingIndexBounds.F.basesAt (chainAt H hT) std _ _ _ _ _ _ _ (j + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
      ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩).1

end GlobalTheory.TwV.DelA
end
end

