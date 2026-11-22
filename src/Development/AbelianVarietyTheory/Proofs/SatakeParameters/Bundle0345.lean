import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0004
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Formalism.LocalToGlobal.HermitianForms.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1766
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemUnderSBOfGIdx
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem not_mem_underSB_of_gIdx : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∀ v, GlobalTheory.TwU.UnderSB t μ v → ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ hQ v hv hmem
  classical
  obtain ⟨P, hP, hvP⟩ := hv
  have h1 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P).asIdeal := by
    have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈
        (seamP t.seam P).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hvP ▸ hmem
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have h2 : ((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
    rw [← mem_seamP t.seam P, map_natCast]
    exact h1
  rcases Finset.mem_union.1 hP with hG | hQE
  · obtain ⟨k, hk⟩ : ∃ k, P ∈ t.Pr.vG k := by
      rcases Finset.mem_union.1 hG with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    have hgk : ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.pr_ok.vG_norm k P hk]
      exact Ideal.absNorm_mem P.asIdeal
    have hnd : ¬ D.what₂.places.resChar w ∣ t.Pr.g k := by
      rw [t.g_rec]
      intro hd
      exact hg.2.2.2.2.1 (((Nat.prime_dvd_prime_iff_eq hg.1 (D.host.g_prime k)).1 hd) ▸ D.host.g_level k)
    have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) ((t.Pr.g k : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hg.1).2 hnd)
    obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 t.X.E))
    have hone : (1 : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← hab]
      refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
      · simpa using h2
      · simpa using hgk
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)
  · exact hQ ((t.Q_rec μ _).2 ⟨hg.1, P, hQE, h2⟩)

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorMatricesAtComplexPoint
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

open Matrix

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
  (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) {j : ℕ} (hN : RankTie X D j)
  (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
  (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ)

theorem evD_yMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (yMat X Kc j v s).map (evD X D pos ι hN d f') =
      ((zT X D pos f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) := by
  ext b t
  simp only [Matrix.map_apply, yMat, evD, MvPolynomial.eval₂Hom_C, RingHom.coe_comp, Function.comp_apply,
    MvPolynomial.eval_X, Matrix.submatrix_apply]
  rfl

theorem evD_dMat (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    (dMat X Kc j v s).map (evD X D pos ι hN d f') =
      ((d (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) := by
  ext a b
  simp only [Matrix.map_apply, dMat, evD, MvPolynomial.eval₂Hom_X', Matrix.submatrix_apply]

theorem zT_even (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : ¬ IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos g (pos ⟨v, s⟩) = g (pos ⟨v, s⟩) := by
  rw [zT, Equiv.symm_apply_apply, if_neg hs]

theorem zT_odd (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos g (pos ⟨v, s⟩) = ((g (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev := by
  rw [zT, Equiv.symm_apply_apply, if_pos hs]

theorem adj_zT_odd (v : X.Pl) (s : Fin (X.G.P.n' v)) (hs : IsOddPos s) {n : ℕ} (g : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ)
    (hg : (g (pos ⟨v, s⟩)).det ≠ 0) :
    (zT X D pos g (pos ⟨v, s⟩)).adjugate =
      (zT X D pos g (pos ⟨v, s⟩)).det • (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id := by
  set z := zT X D pos g (pos ⟨v, s⟩) with hz
  have hmul : z * (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id = 1 := by
    rw [hz, zT_odd X D pos v s hs g]
    have h1 : ((g (pos ⟨v, s⟩))⁻¹).transpose.submatrix id Fin.rev * (g (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id =
        (((g (pos ⟨v, s⟩))⁻¹).transpose * (g (pos ⟨v, s⟩)).transpose).submatrix id id :=
      Matrix.submatrix_mul_equiv _ _ _ Fin.revPerm _
    rw [h1, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hg)]
    simp
  have hdet : z.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [← Matrix.inv_eq_right_inv hmul, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hdet, one_smul]

theorem evD_blockMats {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j)
    (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ)
    (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ) :
    (∀ τ, (f' τ).det ≠ 0) → (∀ τ, (dfr X D hN d f' τ).det ≠ 0) → ∀ (v : X.Pl) (s : Fin (X.G.P.n' v)),
      evD X D pos ι hN d f' (yMat X Kc j v s).det = ι (zT X D pos f' (pos ⟨v, s⟩)).det ∧
      (¬ IsOddPos s → (dyMat X Kc j v s).map (evD X D pos ι hN d f') =
        ((dfr X D hN d f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) ∧
      (IsOddPos s → (YtMat X Kc j v s).map (evD X D pos ι hN d f') =
        ι (zT X D pos f' (pos ⟨v, s⟩)).det • (((dfr X D hN d f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix
          (Fin.cast hN.1.symm) (Fin.cast hN.1.symm)) := by
  intro hf _ v s
  refine ⟨?_, ?_, ?_⟩
  · rw [RingHom.map_det, RingHom.mapMatrix_apply, evD_yMat, ι.map_det]
    exact Matrix.det_submatrix_equiv_self (finCongr hN.2.symm) _
  · intro hs
    rw [dyMat, ← Matrix.submatrix_map, Matrix.map_mul, evD_yMat, evD_dMat, zT_even X D pos v s hs]
    rw [show ((d (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) *
        ((f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) =
        ((d (pos ⟨v, s⟩)).map ι * (f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.1.symm) (Fin.cast hN.2.symm) from
      Matrix.submatrix_mul_equiv _ _ _ (finCongr hN.2.symm) _]
    rw [← Matrix.map_mul, Matrix.submatrix_submatrix, dfr, ← Matrix.submatrix_map, Matrix.submatrix_submatrix]
    ext a t
    rfl
  · intro hs
    have hz := hf (pos ⟨v, s⟩)
    have hY : (yMat X Kc j v s).adjugate.map (evD X D pos ι hN d f') =
        (((zT X D pos f' (pos ⟨v, s⟩)).det • (f' (pos ⟨v, s⟩)).transpose.submatrix Fin.rev id).map ι).submatrix
          (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) := by
      have h1 : (yMat X Kc j v s).adjugate.map (evD X D pos ι hN d f') =
          ((yMat X Kc j v s).map (evD X D pos ι hN d f')).adjugate := RingHom.map_adjugate _ _
      rw [h1, evD_yMat, ← adj_zT_odd X D pos v s hs f' hz]
      rw [show (((zT X D pos f' (pos ⟨v, s⟩)).map ι).submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm)).adjugate =
          ((zT X D pos f' (pos ⟨v, s⟩)).map ι).adjugate.submatrix (Fin.cast hN.2.symm) (Fin.cast hN.2.symm) from
        Matrix.adjugate_submatrix_equiv_self (finCongr hN.2.symm) _]
      congr 1
      exact (RingHom.map_adjugate ι _).symm
    rw [YtMat, Matrix.map_mul, ← Matrix.submatrix_map, hY, Matrix.transpose_map, evD_dMat, Matrix.transpose_submatrix,
      Matrix.submatrix_submatrix]
    have hrev : ∀ t : Fin (NN X.G.P.m X.t j),
        Fin.rev (Fin.cast hN.2.symm (shiftI X j t)) = Fin.castLE (rk_le X D hN) (Fin.rev (Fin.cast hN.1.symm t)) := by
      intro t
      have h1 := hN.1
      have h2 := hN.2
      have h3 := rk_le X D hN
      have := t.isLt
      ext
      simp only [Fin.val_rev, Fin.coe_cast, Fin.coe_castLE, shiftI]
      omega
    ext t a
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.transpose_apply,
      Function.comp_apply, id, smul_eq_mul, dfr, map_mul, map_sum]
    rw [hrev, Finset.mul_sum]
    refine Fintype.sum_equiv (finCongr hN.2.symm) _ _ (fun b => ?_)
    simp only [finCongr_apply]
    ring

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorOnFrameAndClassSummandPolynomial
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem polD_eq_map_polDY (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    GL3Theta.polD D s Q y' =
      MvPolynomial.map (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q) := by
  set v : GL3Theta.FrV D N' → ℂ := fun k => y' k.1 k.2.1 k.2.2
  have hmap : ∀ P : MvPolynomial (GL3Theta.Idx D N N') (MvPolynomial (GL3Theta.FrV D N') ℂ),
      MvPolynomial.map (MvPolynomial.eval v) P = MvPolynomial.mapAlgHom (MvPolynomial.aeval v) P := fun P => rfl
  rw [hmap]
  unfold GL3Theta.polD polDY
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun k => ?_
  rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [MvPolynomial.mapAlgHom_apply]
  split_ifs with h
  · simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.C_mul]
    simp [v]
  · simp

theorem applyFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame := by
  intro D N N' s Q G y'
  rw [polD_eq_map_polDY]
  unfold GL3Theta.applyAt0 framePol GL3Theta.evFr
  rw [map_sum]
  symm
  rw [← Finset.sum_subset (MvPolynomial.support_map_subset
    (MvPolynomial.eval fun k : GL3Theta.FrV D N' => y' k.1 k.2.1 k.2.2) (polDY D s Q))]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.eval_C, mul_assoc]
  · intro α _ hα
    rw [MvPolynomial.notMem_support_iff] at hα
    rw [MvPolynomial.coeff_map] at hα
    rw [map_mul, hα, zero_mul]

theorem entQFrame : Formalism.L2.KerInert.SecondKernelDifference.EntQFrame := by
  intro D L hT Gi Gl Kc0 Dx cX ex t u μ i c Q c' y'
  unfold Formalism.L2.KerInert.SecondKernelDifference.entQ
  rw [applyFrame]
  rfl

theorem applyFrame_and_entQFrame : Formalism.L2.KerInert.SecondKernelDifference.ApplyFrame ∧ Formalism.L2.KerInert.SecondKernelDifference.EntQFrame :=
  ⟨applyFrame, entQFrame⟩

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorPolynomialCoeffsWeightExtendedByZero
section
noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MvPolynomial

theorem sum_castLE_of_vanish {M : Type} [AddCommMonoid M] {a b : ℕ} (h : a ≤ b) (F : Fin b → M)
    (hF : ∀ r : Fin b, a ≤ r.1 → F r = 0) : ∑ r, F r = ∑ r : Fin a, F (Fin.castLE h r) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)
  intro r hr
  apply hF
  by_contra hlt
  exact hr ⟨⟨r.1, by omega⟩, rfl⟩

theorem polDY_colSub (D : D7) {N N' : ℕ} (hN : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (β : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) (hβ : ∀ τ r c, c < r → β τ r c = 0) :
    MvPolynomial.map (colSub β : MvPolynomial (GL3Theta.FrV D N') ℂ →+* MvPolynomial (GL3Theta.FrV D N') ℂ) (polDY D s Q (N' := N')) =
      polDY D s (colSub (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN)) Q) (N' := N') := by
  have e : (MvPolynomial.mapAlgHom (colSub β : MvPolynomial (GL3Theta.FrV D N') ℂ →ₐ[ℂ] MvPolynomial (GL3Theta.FrV D N') ℂ)).comp
      (aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
        C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
          X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))) =
      (aeval (fun k : GL3Theta.FrV D N => ∑ b : Fin N',
        C (C (s k.1) * (if h : (k.2.2 : ℕ) < N' then (X (k.1, b, ⟨k.2.2, h⟩) : MvPolynomial (GL3Theta.FrV D N') ℂ) else 0)) *
          X ((k.1, b, k.2.1) : GL3Theta.Idx D N N'))).comp (colSub (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, i, c⟩
    have hc : (c : ℕ) < N' := lt_of_lt_of_le c.2 hN
    have h1 : ∀ r : Fin N, (r : ℕ) < N' := fun r => lt_of_lt_of_le r.2 hN
    simp only [AlgHom.comp_apply, aeval_X, colSub, dif_pos hc, dif_pos (h1 _), map_sum, map_mul, MvPolynomial.mapAlgHom_apply,
      map_X, map_C, algHom_C, algebraMap_eq, Matrix.submatrix_apply]
    simp only [RingHom.coe_coe, aeval_C, aeval_X, map_sum, map_mul, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [sum_castLE_of_vanish hN]
    · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.castLE, MvPolynomial.algebraMap_apply, algebraMap_eq]
      ring
    · intro r hr
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [hβ τ r ⟨c, hc⟩ (Fin.lt_def.2 (lt_of_lt_of_le c.2 hr))]
      simp
  exact DFunLike.congr_fun e Q

theorem wt_polDY_framePol : ∀ (D : D7) {N N' : ℕ}, N ≤ N' → ∀ (s : D.what₂.Tau → ℂ) (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ), Q ∈ WtPol ℂ ν → (∀ α, MvPolynomial.coeff α (polDY D s Q (N' := N')) ∈ WtPol ℂ (extNu N' ν)) ∧ ∀ Θ : TaylorLogMetric.VC D N N' → ℂ, framePol D s Q Θ ∈ WtPol ℂ (extNu N' ν) := by
  intro D N N' hN s ν Q hQ
  have hc : ∀ α, MvPolynomial.coeff α (polDY D s Q (N' := N')) ∈ WtPol ℂ (extNu N' ν) := by
    intro α β hβ
    have hβ0 : ∀ τ r c, c < r → β τ r c = 0 := fun τ r c h => (hβ τ).1 r c h
    have hB : IsBor (fun τ => (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN)) :=
      fun τ => ⟨fun r c h => (hβ τ).1 _ _ h, fun r => (hβ τ).2 _⟩
    have e1 := congrArg (MvPolynomial.coeff α) (polDY_colSub D hN s Q β hβ0)
    have e2 : ∀ (c : ℂ) (P : MvPolynomial (GL3Theta.FrV D N) ℂ), polDY D s (c • P) (N' := N') = c • polDY D s P (N' := N') :=
      fun c P => by unfold polDY; exact map_smul _ c P
    rw [MvPolynomial.coeff_map, hQ _ hB, e2, MvPolynomial.coeff_smul] at e1
    have e3 : (∏ τ, ∏ r, β τ r r ^ extNu N' ν τ r) = ∏ τ, ∏ r, (β τ).submatrix (Fin.castLE hN) (Fin.castLE hN) r r ^ ν τ r := by
      refine Finset.prod_congr rfl fun τ _ => ?_
      symm
      refine Fintype.prod_of_injective (Fin.castLE hN) (Fin.castLE_injective hN) _ _ ?_ ?_
      · intro r hr
        have hr' : ¬ (r : ℕ) < N := fun h => hr ⟨⟨r, h⟩, rfl⟩
        simp only [extNu, dif_neg hr', pow_zero]
      · intro r
        simp only [extNu, Matrix.submatrix_apply, Fin.coe_castLE, dif_pos r.2]
    rw [e3]
    exact e1
  refine ⟨hc, fun Θ => ?_⟩
  unfold framePol
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [mul_comm, ← MvPolynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (hc α)

end GlobalTheory.TwV.DelA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevels
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA.LastEnt

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem succ_mul_succ_sub_one_div_succ (l t : ℕ) : ((l + 1) * (t + 1) - 1) / (t + 1) = l := by
  have h : (l + 1) * (t + 1) - 1 = t + (t + 1) * l := by rw [Nat.succ_mul]; ring_nf; omega
  rw [h, Nat.add_mul_div_left _ _ (Nat.succ_pos t), Nat.div_eq_of_lt (Nat.lt_succ_self t), zero_add]

theorem eT_zero (τ : D.what₂.Tau) : eT X D pos 0 τ =
    lamAt (X.G.P.lam0 (pos.symm τ).1) (pos.symm τ).2 (Fin.last X.G.P.m) := rfl

theorem eT_succ (l : ℕ) (τ : D.what₂.Tau) : eT X D pos (l + 1) τ =
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 (pos.symm τ).1 s) (fun i => X.Fl.w (pos.symm τ).1 i s) (l + 1))
      (pos.symm τ).2 (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) := rfl

theorem lamAt_last0 (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (X.G.P.lam0 v) s (Fin.last X.G.P.m) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else X.G.P.lam0 v s (Fin.last X.G.P.m) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [if_pos h, if_neg (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
  · rw [if_neg h, if_pos (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]

theorem lamAt_lastS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    lamAt (fun s => liftWt X.Fl.t X.G.P.m (X.G.P.lam0 v s) (fun i => X.Fl.w v i s) (l + 1)) s
        (Fin.last (X.G.P.m + (l + 1) * (X.Fl.t + 1))) =
      if IsOddPos s then -(X.G.P.lam0 v s 0) else -(X.Fl.w v (l + 1) s) := by
  unfold lamAt
  by_cases h : Even s.val
  · rw [if_pos h, if_neg (fun ho : IsOddPos s => by unfold IsOddPos at ho; rw [Nat.even_iff] at h; omega)]
    unfold liftWt
    beta_reduce
    have h1 : 1 ≤ (l + 1) * (X.Fl.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    rw [dif_neg (by simp only [Fin.val_last]; omega)]
    simp only [Fin.val_last]
    have h2 : X.G.P.m + (l + 1) * (X.Fl.t + 1) - (X.G.P.m + 1) = (l + 1) * (X.Fl.t + 1) - 1 := by omega
    rw [h2, succ_mul_succ_sub_one_div_succ]
  · rw [if_neg h, if_pos (show IsOddPos s by unfold IsOddPos; rw [Nat.even_iff] at h; omega), Fin.rev_last]
    unfold liftWt
    beta_reduce
    rw [dif_pos (by simp)]
    rfl

theorem nuv_one (j : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (j + 1) s 1 = X.G.P.lam0 v s 0 + X.w v (j + 1) s := by
  unfold Sys.nuv nu
  rw [if_pos ⟨le_refl 1, by omega⟩]
  unfold lamI
  rw [dif_pos ⟨le_refl 1, by omega⟩]
  rfl

theorem nuv_one_at_firstLevelIndex (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v 1 s (NN X.G.P.m X.t 0) = X.G.P.lam0 v s (Fin.last X.G.P.m) + X.w v 1 s := by
  unfold Sys.nuv nu NN
  rw [if_pos ⟨by omega, by omega⟩]
  unfold lamI
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 2
  ext
  simp

theorem nuv_NNS (l : ℕ) (v : X.Pl) (s : Fin (X.G.P.n' v)) :
    X.nuv v (l + 1 + 1) s (NN X.G.P.m X.t (l + 1)) = -X.w v (l + 1) s + X.w v (l + 1 + 1) s := by
  have h1 : 1 ≤ (l + 1) * (X.t + 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have h3 : (l + 1) * (X.t + 1) + (X.t + 1) = (l + 1 + 1) * (X.t + 1) := by ring
  unfold Sys.nuv nu
  rw [if_neg (by unfold NN; omega), if_pos ⟨by unfold NN; omega, by unfold NN; omega⟩]
  have h2 : NN X.G.P.m X.t (l + 1) - (X.G.P.m + 2) = (l + 1) * (X.t + 1) - 1 := by unfold NN; omega
  rw [h2, succ_mul_succ_sub_one_div_succ]

end GlobalTheory.TwV.DelA.LastEnt

open GlobalTheory.TwV.DelA.LastEnt in

theorem GlobalTheory.TwV.DelA.eT_last_pair : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (τ : D.what₂.Tau), (eT X D pos j τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) - wT X D pos j τ) ∧ (eT X D pos (j + 1) τ = if IsOddPos (pos.symm τ).2 then wT X D pos j τ - cT1 X D pos j τ else -wT X D pos j τ) := by
  intro p _ X D pos j τ
  have hc1 : cT1 X D pos j τ = X.G.P.lam0 (pos.symm τ).1 (pos.symm τ).2 0 + wT X D pos j τ :=
    nuv_one X j (pos.symm τ).1 (pos.symm τ).2
  have hw : wT X D pos j τ = X.w (pos.symm τ).1 (j + 1) (pos.symm τ).2 := rfl
  rw [hc1, eT_succ X D pos j τ, lamAt_lastS X j]
  cases j with
  | zero =>
    rw [eT_zero, lamAt_last0, nuv_one_at_firstLevelIndex, hw]
    constructor <;> split_ifs <;> ring
  | succ l =>
    rw [eT_succ X D pos l τ, lamAt_lastS X l, nuv_NNS, hw]
    constructor <;> split_ifs <;> ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReindexRenamePointDetLatK
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem reindex_rename_point_det_latK : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N n : ℕ} (h : N = n) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (y : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb : Submodule (𝓞 E) (Fin N → E)), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y ∧ Matrix.GeneralLinearGroup.det (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = Matrix.GeneralLinearGroup.det y ∧ HEq ((latK sp (J.reindex (finCongr h) (finCongr h)) a (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) (Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E)))).map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a y Lb) := by
  intro R F E _ _ _ _ _ _ sp N n h J a y Lb
  subst h
  have hr : ∀ {A : Type} [CommRing A] (g : GL (Fin N) A), Formalism.L2.PairingIndexBounds.F.reGL (finCongr (rfl : N = N)) g = g := by
    intro A _ g
    ext i j
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have hJ : J.reindex (finCongr (rfl : N = N)) (finCongr (rfl : N = N)) = J := by
    ext i j
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hr, hr]
  · rw [hr]
  · apply heq_of_eq
    rw [hJ, hr, map_reE_rfl, map_reE_rfl]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SgRevNeZero
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

def twF {n : ℕ} (c : D.what₂.Tau → ℤ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos y τ).det ^ (-(c τ)) else 1) * GL3Theta.evFr D Q (zT X D pos y)

theorem zT_zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) :
    zT X D pos (zT X D pos f) = f := by
  funext τ
  unfold zT
  split_ifs with h
  · have hu : IsUnit (f τ).det := isUnit_iff_ne_zero.2 (hf τ)
    rw [show ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix (Equiv.refl (Fin n)) (Fin.revPerm : Equiv.Perm (Fin n)) from rfl,
      Matrix.inv_submatrix_equiv, ← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu]
    ext i j
    simp
  · rfl

theorem det_zT {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det = if IsOddPos (pos.symm τ).2 then sgRev n * ((f τ).det)⁻¹ else (f τ).det := by
  unfold zT
  split_ifs with h
  · rw [show ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) from rfl,
      Matrix.det_permute', Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    simp [sgRev]
  · rfl

theorem sgRev_ne_zero (n : ℕ) : sgRev n ≠ 0 := by
  unfold sgRev
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> simp [h]

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateEntireAlgebraic
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.translate_entire_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ → ∀ (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), TaylorLogMetric.admitted D a b N N' → ∀ s : TaylorLogMetric.VC D a b, (∃ m : ℕ, 0 < m ∧ m • s ∈ TaylorLogMetric.La D B.tor N N') → Differentiable ℂ (TaylorLogMetric.U D B.tor s (B.eNat χ a b N N')) ∧ TaylorLogMetric.CoefIn D (TaylorLogMetric.U D B.tor s (B.eNat χ a b N N')) TaylorLogMetric.Qbar := by
  intro D cc δ B χ hc hδ hχ a b N N' hA s hs
  obtain ⟨h1, -⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.vector_bound_link D cc hc δ hδ B χ hχ a b N N' hA
  exact ⟨Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_diff _ s h1.1, fun α => GlobalTheory.ThLoc.algTAll D cc δ B χ hc hδ hχ a b N N' hA s hs α⟩
end

