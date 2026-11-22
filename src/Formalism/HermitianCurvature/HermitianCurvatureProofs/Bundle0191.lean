import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0185
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVrad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormZeroEqSlotPairingOfLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0044
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevAInv
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

def psiInt {ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B1 : B.RealPlaceData k (ρ + 1) Wp Wq) (f1 : B.Mat k (ρ + 1) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (γ : B.Mat k ρ) (b b' : B.Mat k (1 + ρ)) : Wq →L[ℂ] Wp :=
  (psi k (ρ + 1) B1.z cStd (D.castM (Nat.add_comm 1 ρ) b) *
      star (psi k (ρ + 1) B1.z' cStd (D.castM (Nat.add_comm 1 ρ) b'))) •
    f1 ((D.castM (Nat.add_comm 1 ρ) b)⁻¹ * D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) *
      D.castM (Nat.add_comm 1 ρ) b')

theorem levA_inv (ρ : ℕ) {h : B.Mat k ρ} (hh : IsUnit h.det) :
    (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ h))⁻¹ = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ h⁻¹) := by
  rw [← castM_inv', LongWeylElement.lev_inv _ hh]

theorem pt_eq {ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B1 : B.RealPlaceData k (ρ + 1) Wp Wq) (B0 : B.RealPlaceData k ρ Wp Wq)
    (hz : B1.z = D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z))
    (hz' : B1.z' = D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z'))
    (hπ : ∀ y : B.Mat k ρ, B0.π y = B1.π (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y)))
    (hπ' : ∀ y : B.Mat k ρ, B0.π' y = B1.π' (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y)))
    (f1 : B.Mat k (ρ + 1) → (Wq →L[ℂ] Wp)) (c : ℂ) (γ : B.Mat k ρ)
    (h0 y h0' y' : Mt k ρ) (a a' : Mt k (1 + ρ))
    (hh0 : Matrix.of h0 ∈ UWset k ρ B0.z) (hy : Matrix.of y ∈ Nset k ρ)
    (hh0' : Matrix.of h0' ∈ UWset k ρ B0.z') (hy' : Matrix.of y' ∈ Nset k ρ)
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (ha' : Matrix.of a' ∈ Nset k (1 + ρ)) :
    JF.integrand B1 f1 (D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ))
        ((levA ρ h0, Qm ρ (a, y)), (levA ρ h0', Qm ρ (a', y'))) =
      (psi k ρ B0.z cStd (Matrix.of y) * star (psi k ρ B0.z' cStd (Matrix.of y'))) •
        (B0.π (Matrix.of h0)).comp
          ((psiInt B1 f1 c ((Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0'))
              (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a))
              (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a'))).comp
            (B0.π' (Matrix.of h0')⁻¹)) := by
  set κ : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ with hκ
  have hH := Ux3.hpk_det k ρ
  have hu0 : IsUnit (Matrix.of h0).det := HermitianFormFactor.UH_unit hH hh0.1
  have hu0' : IsUnit (Matrix.of h0').det := HermitianFormFactor.UH_unit hH hh0'.1
  have huy : IsUnit (Matrix.of y).det := HermitianFormFactor.UH_unit hH hy.1
  have huy' : IsUnit (Matrix.of y').det := HermitianFormFactor.UH_unit hH hy'.1
  have hg : IsUnit (ιLev k 1 ρ (Matrix.of y * Matrix.of h0)).det :=
    LongWeylElement.lev_unit _ (by rw [Matrix.det_mul]; exact huy.mul hu0)
  have hg' : IsUnit (ιLev k 1 ρ (Matrix.of y' * Matrix.of h0')).det :=
    LongWeylElement.lev_unit _ (by rw [Matrix.det_mul]; exact huy'.mul hu0')

  have hconj : ∀ (g : B.Mat k (1 + ρ)) (hg : IsUnit g.det) (x : Mt k (1 + ρ)),
      (Matrix.of (conjM g⁻¹ x) : B.Mat k (1 + ρ)) = g⁻¹ * Matrix.of x * g := by
    intro g hg x
    show g⁻¹ * Matrix.of x * g⁻¹⁻¹ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ hg]

  have hψ1 : psi k (ρ + 1) B1.z cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) B1.z cStd (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a))) *
        psi k ρ B0.z cStd (Matrix.of y) := by
    rw [hz, psi_Qm ρ B0.z_mem ha hy, psi_castM, psi_castM, hconj _ hg, psi_conjLev ρ B0.z_mem ha hy hh0]
  have hψ2 : psi k (ρ + 1) B1.z' cStd (Matrix.of (Qm ρ (a', y'))) =
      psi k (ρ + 1) B1.z' cStd (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a'))) *
        psi k ρ B0.z' cStd (Matrix.of y') := by
    rw [hz', psi_Qm ρ B0.z'_mem ha' hy', psi_castM, psi_castM, hconj _ hg', psi_conjLev ρ B0.z'_mem ha' hy' hh0']

  have hπa : B1.π (Matrix.of (levA ρ h0)) = B0.π (Matrix.of h0) := (hπ _).symm
  have hπb : B1.π' (Matrix.of (levA ρ h0'))⁻¹ = B0.π' (Matrix.of h0')⁻¹ := by
    rw [levA_apply, levA_inv ρ hu0', ← hπ']

  have hpt : (Matrix.of (levA ρ h0))⁻¹ * (Matrix.of (Qm ρ (a, y)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) * Matrix.of (Qm ρ (a', y')) * Matrix.of (levA ρ h0') =
      (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c)
          ((Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0'))) *
        D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a')) := by
    rw [hconj _ hg, hconj _ hg']
    show (D.castM κ (ιLev k 1 ρ (Matrix.of h0)))⁻¹ * (D.castM κ (Matrix.of a * ιLev k 1 ρ (Matrix.of y)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) * D.castM κ (Matrix.of a' * ιLev k 1 ρ (Matrix.of y')) *
        D.castM κ (ιLev k 1 ρ (Matrix.of h0')) = _
    rw [← castM_inv', ← castM_inv', ← castM_inv', ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul,
      ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul,
      sgs_alg ρ _ _ _ _ hu0 huy hu0' huy']
  unfold JF.integrand JF.xiP B.rho B.sgs psiInt
  rw [hψ1, hψ2, hπa, hπb, hpt]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  congr 1
  rw [star_mul']
  ring

end Formalism.FourierDecayAlt.P.PBH
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVpic
section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

section Pic

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem JF_mul_inv (Bs : B.RealPlaceData k r Wp Wq) (m : B.Mat k r → ℂ)
    (hm : ∀ p : B.SS k r, Bs.inSS p → ∀ g, m (B.sgs p g) = m g) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h : B.Mat k r) : B.JF Bs (fun g => m g • F g) h = m h • B.JF Bs F h := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun g => m g • F g) h ∂Bs.μSS = m h • ∫ p, JF.xiP Bs p • B.rho Bs p F h ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hm p hp h]
  exact smul_comm _ _ _

theorem JF_uInv (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) {h : B.Mat k r} (hh : h ∈ JF.Om k r Bs.z Bs.z') :
    ∀ (w : List C.Letter) (x : Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)), (∀ e, JC.NiceCoef Bs ε (x e)) →
      ∀ e, B.JF Bs (KB.uInv s w x e) h = KB.uInv s w (fun e => B.JF Bs (x e) h) e
  | [], x, _, e => rfl
  | l :: w, x, hx, e => by
    rw [uInv_cons, uInv_cons]
    by_cases h0 : e 0 = 0
    · rw [if_pos h0, if_pos h0]
      exact JF_uInv Bs ε s hh w _ (fun e' => hx _) _
    · rw [if_neg h0, if_neg h0]
      generalize (if l.1 = true then s else (starRingEnd ℂ) s) = c
      have h1 := uInv_nice Bs ε s w (fun e' => x (Fin.cons 1 e')) (fun e' => hx _) (fun a => e a.succ)
      have h2 := uInv_nice Bs ε s w (fun e' => x (Fin.cons 0 e')) (fun e' => hx _) (fun a => e a.succ)
      have e1 := JCx2.bc_JF_add h1 (JCx2.mn_nice_smul c h2) hh
      calc B.JF Bs ((KB.uInv s w (fun e' => x (Fin.cons 1 e')) fun a => e a.succ) +
            c • (KB.uInv s w (fun e' => x (Fin.cons 0 e')) fun a => e a.succ)) h
          = B.JF Bs (fun g => (KB.uInv s w (fun e' => x (Fin.cons 1 e')) fun a => e a.succ) g +
            (fun g => c • (KB.uInv s w (fun e' => x (Fin.cons 0 e')) fun a => e a.succ) g) g) h := rfl
        _ = _ := e1
        _ = _ := by
          rw [JCx2.bc_JF_smul, JF_uInv Bs ε s hh w _ (fun e' => hx _), JF_uInv Bs ε s hh w _ (fun e' => hx _)]

end Pic

section Minor

variable {k r : ℕ}

theorem first_minor_cell_eq_coord {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hr : 0 < r)
    (c : Fin r → ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (h1 : 1 < r + 2) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, h1⟩ = c ⟨0, hr⟩ := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ := by
    rw [Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  rw [e]
  have hmin := (big_cell_minors_holds k r z z' c μ hz hz').1 ⟨1, by omega⟩
  have hl : (⟨(⟨1, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = ⟨1, h1⟩ := Fin.ext rfl
  rw [hl] at hmin
  rw [hmin]
  have hs : (Finset.univ.filter fun a : Fin r => a.val < (⟨1, by omega⟩ : Fin (r + 1)).val) = {⟨0, hr⟩} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ha; exact Fin.ext (by simp at ha; omega)
    · rintro rfl; simp
  rw [Finset.prod_filter, ← Finset.prod_filter, hs, Finset.prod_singleton]

theorem first_minor_top_eq_zeta {z z' : Fin (2 * r + k + 1) → ℂ} (hr : r = 0) (c : Fin r → ℂ) (g : Mx k r) (h1 : 1 < r + 2) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, h1⟩ = P5.zeta k r z z' g := by
  subst hr
  have hw : wCell k 0 (Fin.last 0) c = 1 := Formalism.FourierDecayAlt.P.Qx6.wCell_zero c
  rw [hw, one_mul, dmin_one]
  simp [P5.zeta, zetaL, fvec]

end Minor

section Rad

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem radPic_wave (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (w : List C.Letter)
    (x : Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e))
    (Φ : Ix (Fin w.length) → RadSp k r Bs.z Bs.z' Bs.π Bs.π')
    (hΦ : ∀ e, ∀ y ∈ DomR k r Bs.z Bs.z',
      (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF Bs (x e)) y.1 y.2)
    (m : (Fin r → ℂ) → Mx k r → ℂ) (h1 : 1 < r + 2)
    (hm : ∀ y ∈ DomR k r Bs.z Bs.z', m y.1 y.2 = fsv s (Dmin k r Bs.z Bs.z' (wCell k r (Fin.last r) y.1 * y.2) ⟨1, h1⟩))
    (Wv Wv' : Module.End ℂ (RadSp k r Bs.z Bs.z' Bs.π Bs.π')) (hW : multiplicationOperator Wv m) :
    ∀ e, ∀ y ∈ DomR k r Bs.z Bs.z', (act (Vw (mkP Wv Wv') s (D.positionted w)) Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG k r (Fin.last r) (B.JF Bs (KB.waveG Bs s w x e)) y.1 y.2 := by
  intro e y hy
  have hGV : wCell k r (Fin.last r) y.1 * y.2 ∈ B.GV k r := by
    rw [Rad.wCell_last_eq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
  have hh : wCell k r (Fin.last r) y.1 * y.2 ∈ JF.Om k r Bs.z Bs.z' :=
    ⟨hGV, Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hy.1 hy.2.1 hy.2.2⟩
  set h := wCell k r (Fin.last r) y.1 * y.2 with hhdef
  rw [Vw, act_mul, act_io]
  change (Wv (act (UUiw s (D.positionted w)) Φ e) : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = _
  rw [hW, act_UUiw]
  let ev : RadSp k r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
    { toFun := fun Ψ => (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ((KB.uInv s w Φ e : RadSp k r Bs.z Bs.z' Bs.π Bs.π') : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      KB.uInv s w (fun e => (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) e := uInv_map ev s w Φ e
  rw [hev]
  have hfun : (fun e => (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) = fun e => resG k r (Fin.last r) (B.JF Bs (x e)) y.1 y.2 :=
    funext fun e => hΦ e y hy
  rw [hfun]
  simp only [resG]
  set gau : ℂ := ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖y.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ)
    with hgau
  have hsm := uInv_map ((gau • LinearMap.id : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))) s w (fun e => B.JF Bs (x e) h) e
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hsm
  rw [← hsm]
  unfold KB.waveG
  rw [JF_mul_inv Bs (fun g => P5.fsv s (Dmin k r Bs.z Bs.z' g ⟨1, h1⟩))
    (fun p hp g => by rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g]),
    JF_uInv Bs ε s hh w x hx e, hm y hy, smul_comm]

end Rad

end Formalism.FourierDecayAlt.P.PBFV
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PbFormPos
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexOrder

theorem pb_formPos : P5.ThmPActual → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter), KB.CutWord P p.l0 w →
    ∀ (x : Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε →
      (∀ e, JC.NiceCoef (p.T.bs j) ε (x e)) → 0 ≤ p.form j hj w x x := by
  intro hP Wp Wq _ _ _ _ _ _ P p j hj w hc x ε hε hx
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hlk, -⟩ := p.hl
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ0, hμ0⟩ := Formalism.FourierDecayAlt.P.JCTx5.exists_haar_level_zero (Nat.sub_self P.r) (p.T.bs P.r)
  set μ := μ0.map (Formalism.FourierDecayAlt.P.JCTx5.embL P.k (P.r - j)) with hμ
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, Formalism.FourierDecayAlt.P.JCTx5.haar_glev μ0 hμ0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Cst, hC, hform⟩ := Formalism.FourierDecayAlt.P.radial_module_form Wp Wq P p.T jF X μ L st p.l0 hD
  choose Φ hΦK hΦ using fun a => hJ (x a) ε hε (hx a).2.1 (hx a).2.2
  have hW := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hc.1 hc.2
  have hpos := ((hThm (D.positionted w) hW).2.2 0 (fun _ => 1) (fun _ => one_ne_zero)).2 Φ (fun a _ => hΦK a)
  have hpos' : 0 ≤ P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ 0 :=
    hpos.trans_eq (Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ _)
  have e := hform w x x Φ Φ ε hε hx hx hΦ hΦ
  show 0 ≤ D.formLev p.T (M.sgn P p.l0) jF w x x
  rw [e]
  exact mul_nonneg (by exact_mod_cast hC.le) hpos'

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfStepParts2
section
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

def DecayData (n : ℕ) (C : ℝ) (D : ℂ → ℂ) : Prop :=
  Integrable D ∧ Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) ∧ (∀ t, t ≠ 0 → ContinuousAt D t) ∧
    (∀ s, ‖∫ t, fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))) ∧
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def DerivComb (f : ℂ → ℂ) : Prop :=
  ∃ (n K : ℕ) (C : ℝ) (Dd : Fin K → ℂ → ℂ) (j : Fin K → ℕ) (v : ∀ i, Fin (j i) → ℂ) (a : Fin K → ℂ),
    (∀ i, j i ≤ n) ∧ (∀ i, DecayData n C (Dd i)) ∧
    ∀ t, t ≠ 0 → f t = ∑ i, a i * iteratedFDeriv ℝ (j i) (Dd i) t (v i)

section Gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Gen

def StepPartsCpt2 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r,
      form μ l.castSucc (act (star (bTl L l w) * (RRi L st l.succ w * bTl L l w)) x) y c =
        form μ l.castSucc (act (RRi L st l.succ w * bTl L l w) x) (act (bTl L l w) y) c ∧
      Integrable (fun c' : Cf P.r l.castSucc => ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (act (RRi L st l.succ w * bTl L l w) x a) (act (bTl L l w) y a) (glue l.castSucc c c')) ∧
      DerivComb (ph L st μ l w x y c)

end Formalism.FourierDecayAlt.P5.HerC
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSquareIntegrableHolds
section
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lintegral_base_measure_le {r : ℕ} {TT : ℝ} (H : MA.E r → ENNReal) :
    ∫⁻ q : MA.Qp r TT, H q.1 ∂MA.mu0 r TT ≤ ∫⁻ x in MA.Qset r TT, MA.dens0 x * H x := by
  have hQ : MeasurableSet (MA.Qset r TT) := (MA.Qset_open r TT).measurableSet
  rw [MA.mu0, lintegral_subtype_comap hQ (fun x => H x), restrict_withDensity hQ]
  exact lintegral_withDensity_le_lintegral_mul _ Formalism.FourierDecayAlt.P.MAx2.Adj.density_measurable H

theorem jd_AB_le (k r : ℕ) : B.AB k r ≤ 3 * ((r : ℝ) + 1) ^ 2 * nDim k r := by
  have ha : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  unfold B.AB
  rw [hn]
  nlinarith [sq_nonneg (r : ℝ), mul_nonneg ha hb, mul_nonneg (mul_nonneg ha ha) ha, mul_nonneg (mul_nonneg ha ha) hb,
    mul_nonneg (mul_nonneg ha hb) ha]

theorem transfer_square_integrable_holds : TransferSquareIntegrable := by
  refine ⟨3, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr A hA F hCk hCC hFF π
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  have hQm : MeasurableSet (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := (MA.Qset_open _ _).measurableSet

  have hAB : B.AB S.G.k S.G.r ≤ A := (jd_AB_le S.G.k S.G.r).trans hA
  obtain ⟨c0, -, -, hB1, -⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db A hAB
  obtain ⟨C, hC⟩ := hB1
  obtain ⟨c4, hc4⟩ := hCC 4
  have hN : B.normSq Db F ≠ ⊤ := (hC F F c4 c4 (hCC 5) (hCC 5) hc4 hc4).1
  unfold B.normSq jNormSq at hN

  have hsm := Formalism.FourierDecayAlt.P.CutMP.En.trace_smoothness E Wp Wq S T v hPl e hFr (B.JF Db F) hFF π
  have hval := Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem (D.parOf S v) hsm
  refine ⟨((jd_evQ_meas _ _).norm).pow 2, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun q => by positivity)).2 ?_
  set H : MA.E S.G.r → ENNReal := fun x =>
    ENNReal.ofReal (MA.wq S.G.k x (D.parOf S v).TT * ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) with hH
  have p1 : ∀ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT,
      ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2) ≤ H q.1 := by
    intro q
    refine ENNReal.ofReal_le_ofReal ?_
    have hq : MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q =
        ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1))) := congrFun hval q
    rw [hq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hw := Formalism.FourierDecayAlt.P.CutMP.En.wq_pos (k := S.G.k) q.2
    rw [Real.sq_sqrt hw.le]
    refine mul_le_mul_of_nonneg_left ?_ hw.le
    have he1 : ‖B.hsVec (e π q.1.2)‖ ≤ 1 := by
      have h1 : inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (e π q.1.2)) = (1 : ℂ) := by
        simpa using (hFr.2 q.1.2 q.2.2).2.1 π π
      rw [inner_self_eq_norm_sq_to_K] at h1
      have h2' : ((‖B.hsVec (e π q.1.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
      have h2 : ‖B.hsVec (e π q.1.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
      nlinarith [norm_nonneg (B.hsVec (e π q.1.2))]
    have hi : ‖inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (B.JF Db F (B.gq Db q.1)))‖ ≤
        ‖B.hsVec (B.JF Db F (B.gq Db q.1))‖ :=
      (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (B.JF Db F (B.gq Db q.1)))])
    exact pow_le_pow_left₀ (norm_nonneg _) hi 2
  have p2 : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x ≤
      ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
        ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := by
    intro x hx
    have hd : MA.dens0 x = ENNReal.ofReal (Formalism.FourierDecayAlt.P.MAx2.Adj.dR x) := by
      unfold MA.dens0 Formalism.FourierDecayAlt.P.MAx2.Adj.dR
      rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _))]
    have hd0 : 0 ≤ Formalism.FourierDecayAlt.P.MAx2.Adj.dR x :=
      Finset.prod_nonneg fun l _ => inv_nonneg.2 (Complex.normSq_nonneg _)
    have hW : bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x =
        Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
      have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
        rw [hTT]; exact le_of_lt hx.2
      unfold bcWeight
      rw [if_pos hle]
      unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
      rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl fun l _ => ?_
      have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
        have := l.isLt
        simp only [MA.Mdim]; omega
      have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
      have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
      rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
        pow_succ]
      field_simp
    rw [hd, hH, ← ENNReal.ofReal_mul hd0, hW, mul_assoc]
  calc ∫⁻ q, ENNReal.ofReal (‖MA.evQ (D.parOf S v) (trJ S T v e (B.JF Db F) π) q‖ ^ 2)
          ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT
        ≤ ∫⁻ q : MA.Qp (D.parOf S v).r (D.parOf S v).TT, H q.1 ∂MA.mu0 (D.parOf S v).r (D.parOf S v).TT :=
          lintegral_mono p1
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.dens0 x * H x := lintegral_base_measure_le H
      _ ≤ ∫⁻ x in MA.Qset (D.parOf S v).r (D.parOf S v).TT,
            ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_mono' hQm p2
      _ ≤ ∫⁻ x, ENNReal.ofReal (bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') x *
              ‖B.hsVec (B.JF Db F (B.gq Db x))‖ ^ 2) := setLIntegral_le_lintegral _ _
      _ < ⊤ := lt_top_iff_ne_top.2 hN

end

end Formalism.FourierDecayAlt.P.CutMP
end

