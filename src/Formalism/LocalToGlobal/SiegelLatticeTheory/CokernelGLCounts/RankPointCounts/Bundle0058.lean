import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0047
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepNormOneOfLeaves
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0056
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0025
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0057

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerShOfKind
section
noncomputable section

open scoped Classical
open Matrix
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cornerSh_of_kind (δ : ∀ p : PlF D, (D.s.atP p).Fp) (T T' : ℕ) (p : PlF D)
    {w w' : Point D.host.E (D.R.rS + 1)} (h : kind w = kind w') : cornerSh δ T T' p w = cornerSh δ T T' p w' := by
  unfold kind at h
  unfold cornerSh
  by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0
  · simp [h1, h2]
  · simp [h1, h2] at h
  · simp [h1, h2] at h
  · simp only [h1, h2, if_false] at h ⊢
    rw [Option.some.inj h]

theorem sgn_sq (q : ℕ) :
    (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem lead_at {w : Point D.host.E (D.R.rS + 1)} {Z : PairVal.MatR D} (hZ : AtMat w Z) (q : ℕ) (hq : q ≤ D.R.rS + 1) :
    leadMinorE Z q = (∏ b : Fin q, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * Dmin w q := by
  have h1 := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_cell (ZhatOM Z) w hZ q
  rw [Formalism.L2.SG.NGCut.LeadingMinorIntegrality.lead_ZhatOM Z q hq, Formalism.L2.SG.NGCut.NormalVectorPairings.leadingMinor_eq_pointMinor w q hq] at h1
  rw [h1, ← mul_assoc, sgn_sq, one_mul]

theorem cross_of_kind {w w' : Point D.host.E (D.R.rS + 1)} {Z Z' : PairVal.MatR D} (hk : kind w = kind w')
    (hZ : AtMat w Z) (hZ' : AtMat w' Z') :
    leadMinorE Z D.R.rS * leadMinorE Z' (D.R.rS + 1) = leadMinorE Z' D.R.rS * leadMinorE Z (D.R.rS + 1) := by
  rw [lead_at hZ _ (Nat.le_succ _), lead_at hZ' _ le_rfl, lead_at hZ' _ (Nat.le_succ _), lead_at hZ _ le_rfl]
  have key : Dmin w D.R.rS * Dmin w' (D.R.rS + 1) = Dmin w' D.R.rS * Dmin w (D.R.rS + 1) := by
    unfold kind at hk
    by_cases h1 : Dmin w D.R.rS = 0 <;> by_cases h2 : Dmin w' D.R.rS = 0
    · rw [h1, h2]; ring
    · simp [h1, h2] at hk
    · simp [h1, h2] at hk
    · simp only [h1, h2, if_false, Option.some.injEq] at hk
      unfold zetaOf at hk
      field_simp at hk
      linear_combination -hk
  linear_combination (∏ b : Fin D.R.rS, (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) *
    (∏ b : Fin (D.R.rS + 1), (-1 : D.host.E) ^ (D.R.rS - (b : ℕ))) * key

theorem inv_last_mul_det {K : Type*} [CommRing K] {m : ℕ} (Y : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hY : IsUnit Y.det) :
    Y⁻¹ (Fin.last m) (Fin.last m) * Y.det = (Y.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, smul_eq_mul]
  simp only [Fin.succAbove_last, Fin.val_last]
  rw [show ((-1 : K) ^ (m + m)) = 1 by rw [← two_mul, pow_mul]; simp, one_mul, mul_comm, ← mul_assoc,
    Ring.mul_inverse_cancel _ hY, one_mul]

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaK
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open BwdCut BwdBetaCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

namespace BwdBetaCut

variable (u u' F0 what₂) in

def BHyp (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) : Prop :=
  CtxP u u' F0 what₂ ∧ Ctx γ Z ∧ StarHyp Zd γ Z F'₂ φ φ' ∧ Λ₂ ∈ GlobSet Zd γ F'₂ φ φ' ∧
    (∃ n ∈ unipotentFrameFixers F0, (n : (VS D).V → (VS D).V) '' (Λ₂ : Set (VS D).V) = (γ.lam : Set (VS D).V)) ∧
    TermHyp (F0 := F0) Λ₂ F'₂ ∧ PD D γ.lam (lf D F0) u' (repF γ) ∧ Gval (lf D F0) (repF γ) ≠ 0

def OmB {T : D.host.E} (F : LFlag (VS D) D.R.rS T) {T' : D.host.E} (F' F₂ : LFlag (VS D) D.R.rS T')
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  star (GDl (frame F) (frame F₂) (D.R.rS + 1)) • β (Gom (frame F) (frame F')) -
      star (GDl (frame F) (frame F') (D.R.rS + 1)) • Gom (frame F) (frame F₂) ∈ Xsp F₂

end BwdBetaCut

variable (u u' F0 what₂)

def BetaRat : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∃ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) ∧
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ ∧ OmB (lf D F0) (repF γ) (liftF F'₂) β₀

def ScalarOf : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β (frame (repF γ) b) = frame (liftF F'₂) b) → OmB (lf D F0) (repF γ) (liftF F'₂) β →
      Scalar₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β

def BetaInt : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂))
    (Λ₂ : Submodule (𝓞 D.host.E) (VS D).V), BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ →
    ∀ β₀ : (VS D).V ≃ₗ[D.host.E] (VS D).V, β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT →
      (∀ b, β₀ (frame (repF γ) b) = frame (liftF F'₂) b) →
      W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) β₀ → OmB (lf D F0) (repF γ) (liftF F'₂) β₀ →
      ∃ v : (VS D).V ≃ₗ[D.host.E] (VS D).V, v ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
        (∀ b, v (frame (liftF F'₂) b) = frame (liftF F'₂) b) ∧
        (∀ y ∈ orth (VS D) (Xsp (liftF F'₂)), v y - y ∈ Xsp (liftF F'₂)) ∧
        Formalism.HermitianLatticesTheory.gmap (v * β₀) γ.lam = Λ₂ ∧ IotaC₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀)

variable {u u' F0 what₂}

namespace BwdBetaCut

variable {T T' : D.host.E}

theorem fvec_cs' (F : LFlag (VS D) D.R.rS T) (i : Fin D.R.rS) : frame F i.castSucc = F.fl.e i := by
  first
  | exact PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_castSucc F.fl i
  | simp [frame]
  | rfl

theorem fvec_last' (F : LFlag (VS D) D.R.rS T) : frame F (Fin.last _) = F.fl.z := by
  first
  | exact PI.UnitaryGroupMassFormula.BetaLUniq.GN.fvec_last F.fl
  | simp [frame]
  | rfl

theorem e_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (VS D) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) (i : Fin D.R.rS) : β (F.fl.e i) = F₂.fl.e i := by
  have hi := h i.castSucc
  rwa [fvec_cs', fvec_cs'] at hi

theorem Xflag_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (VS D) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) (j : ℕ) :
    (Xflag F j).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xflag F₂ j := by
  ext x
  rw [Submodule.mem_map_equiv]
  exact (Formalism.L2.SG.Pf.mem_xflag_of_frame (fun a => (h a).symm) j x).symm

theorem Xsp_of_frame (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (F F₂ : LFlag (VS D) D.R.rS T')
    (h : ∀ b, β (frame F b) = frame F₂ b) :
    (Xsp F).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) = Xsp F₂ := by
  rw [← Formalism.L2.SG.FourParts.Xflag_r, ← Formalism.L2.SG.FourParts.Xflag_r]
  exact Xflag_of_frame β F F₂ h D.R.rS

theorem Gom_orth (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') :
    Gom (frame F) (frame F') ∈ orth (VS D) (Xsp F') := by
  unfold orth Xsp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  unfold Formalism.MainNotions.S.FlagG.X at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    rw [← fvec_cs' F' i, PI.NRL.herm_eq, Formalism.L2.SG.Pf.ScalarFramePf.om_pair,
      if_neg (Fin.castSucc_lt_last i).ne, star_zero]
  | zero => simp
  | add y z _ _ hy hz => simp [map_add, hy, hz]
  | smul a y _ hy => simp [hy]

end BwdBetaCut

namespace BwdBetaCut

theorem comb_mem {V : Type*} [AddCommGroup V] [Module D.host.E V] {X : Submodule D.host.E V}
    (v : V ≃ₗ[D.host.E] V) (a c : D.host.E) (p q : V) (h : a • p - c • q ∈ X) (hvX : ∀ y ∈ X, v y ∈ X)
    (hq : v q - q ∈ X) : a • v p - c • q ∈ X := by
  have h1 := hvX _ h
  rw [map_sub, map_smul, map_smul] at h1
  have h2 := X.add_mem h1 (X.smul_mem c hq)
  convert h2 using 1
  rw [smul_sub]
  abel

private theorem Hp_le_orth_Xsp (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ)
    {T₁ T₂ : D.host.E} (F : LFlag (VS D) D.R.rS T₁) (F' : LFlag (VS D) D.R.rS T₂) :
    Hp Λ F F' ≤ orth (VS D) (Xsp F') := by
  have hle : XLam Λ F' ≤ UU Λ F F' := by
    unfold UU
    exact le_sup_right.trans le_sup_left
  have hX : Xsp F' ≤ spanE (VS D) (UU Λ F F') := by
    refine le_trans ?_ (Submodule.span_mono (SetLike.coe_subset_coe.mpr hle))
    intro x hx
    have hxs : x ∈ Submodule.span D.host.E (Λ : Set (VS D).V) := by
      rw [hΛ.span_eq_top]
      exact Submodule.mem_top
    obtain ⟨d, hd0, hd⟩ := Formalism.MainNotions.LatticeGluingRadicals.m_exists_smul_mem Λ hxs
    have hdx : (algebraMap (𝓞 D.host.E) D.host.E d) • x ∈ Xsp F' := (Xsp F').smul_mem _ hx
    rw [algebraMap_smul] at hdx
    have hdX : d • x ∈ XLam Λ F' := by
      unfold XLam
      exact Submodule.mem_inf.mpr ⟨hd, by unfold toO; first | exact hdx | simpa using hdx⟩
    have hd' : algebraMap (𝓞 D.host.E) D.host.E d ≠ 0 := by
      first
      | exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 D.host.E) D.host.E)).mpr hd0
      | simpa using hd0
    have hx' : x = (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul D.host.E d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hdX)
  unfold Hp UUE
  intro y hy
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy ⊢
  intro x hx
  exact hy x (hX hx)

theorem h_le_orth_second_frame (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsLattice D.host.E Λ) {T' : D.host.E}
    (F' : LFlag (VS D) D.R.rS T') (hL : IsLift Λ (lf D F0)) (hL' : IsLift Λ F') :
    Hp Λ (lf D F0) F' ≤ orth (VS D) (Xsp F') := by
  exact Hp_le_orth_Xsp Λ hΛ _ F'

end BwdBetaCut

theorem betaCore₂_of (h1 : BetaRat Zd u u' F0 what₂) (h2 : ScalarOf Zd u u' F0 what₂) (h3 : BetaInt Zd u u' F0 what₂) :
    BetaCore₂ Zd u u' F0 what₂ := by
  unfold BetaRat at h1
  unfold ScalarOf at h2
  unfold BetaInt at h3
  unfold BetaCore₂
  intro hP γ Z hC F'₂ φ φ' hS Λ₂ hG hn hT hPD hv0
  have hB : BwdBetaCut.BHyp Zd u u' F0 what₂ γ Z F'₂ φ φ' Λ₂ := by
    unfold BwdBetaCut.BHyp
    exact ⟨hP, hC, hS, hG, hn, hT, hPD, hv0⟩
  obtain ⟨β₀, hi₀, hf₀, hW₀, hO₀⟩ := h1 γ Z F'₂ φ φ' Λ₂ hB
  obtain ⟨v, hiv, hfv, hov, hgm, hio⟩ := h3 γ Z F'₂ φ φ' Λ₂ hB β₀ hi₀ hf₀ hW₀ hO₀
  have hfr : ∀ b, (v * β₀) (frame (repF γ) b) = frame (liftF F'₂) b := by
    intro b
    rw [LinearEquiv.mul_apply, hf₀, hfv]
  have hXv : ∀ y ∈ Xsp (liftF F'₂), v y ∈ Xsp (liftF F'₂) := by
    intro y hy
    rw [← BwdBetaCut.Xsp_of_frame v (liftF F'₂) (liftF F'₂) hfv]
    exact Submodule.mem_map_of_mem hy
  have hO : BwdBetaCut.OmB (lf D F0) (repF γ) (liftF F'₂) (v * β₀) := by
    unfold BwdBetaCut.OmB at hO₀ ⊢
    rw [LinearEquiv.mul_apply]
    exact BwdBetaCut.comb_mem v _ _ _ _ hO₀ hXv (hov _ (BwdBetaCut.Gom_orth _ _))
  have hi : v * β₀ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hiv hi₀
  have hW : BwdBetaCut.W0₂ γ.lam Λ₂ (lf D F0) (repF γ) (liftF F'₂) (v * β₀) := by
    unfold BwdBetaCut.W0₂ at hW₀ ⊢
    intro w hw
    obtain ⟨w₂, hw₂, hd1, hd2⟩ := hW₀ w hw
    refine ⟨w₂, hw₂, hd1, ?_⟩
    have hw₂o := BwdBetaCut.Hp_le_orth_Xsp Λ₂ hG.1 _ _ hw₂
    have hs := (Xsp (liftF F'₂)).add_mem (hXv _ hd2) (hov _ hw₂o)
    rw [LinearEquiv.mul_apply]
    convert hs using 1
    rw [map_sub]
    abel
  refine ⟨v * β₀, ?_⟩
  unfold BwdBetaCut.IsPair₂
  refine ⟨hi, hgm, fun j => BwdBetaCut.Xflag_of_frame _ _ _ hfr j, ?_, hio, hW,
    h2 γ Z F'₂ φ φ' Λ₂ hB _ hi hfr hO⟩
  rw [← BwdBetaCut.fvec_last' (repF γ), ← BwdBetaCut.fvec_last' (liftF F'₂)]
  exact hfr _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgBwdSub
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG6

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem rg_bwd_sub (g : SplitG M.L) {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V}
    {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')} {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂}
    {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'} (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    (hG : (fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' GamR H t₁ (algebraMap F E (g.q : F)) =
      GamR H t₂ (algebraMap F E (g.q : F))) :
    Prod.map φ' φ '' H.iotaGraph g t₁ ⊆ H.iotaGraph g ⟨Λ₂, t₂.f, t₂.f', t₂.T, t₂.T'⟩ := by
  rintro _ ⟨⟨y', y⟩, ⟨x₁', x₁, hx₁'L, hx₁L, hd₁, hpe⟩, rfl⟩
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  have hcO : algebraMap F E (g.q : F) ∈ M.L.O := by
    rw [M.L.O_def]
    have := isIntegral_algebraMap (R := ↥𝒪[F]) (A := E) (x := g.q)
    convert this using 1
    rw [IsScalarTower.algebraMap_apply (↥𝒪[F]) F E]
    rfl
  set c := algebraMap F E (g.q : F) with hc
  have hcx : ∀ x ∈ Λ₂, c • x ∈ Λ₂ := fun x hx => Λ₂.smul_mem (⟨c, hcO⟩ : M.L.O) hx
  obtain ⟨l, hl, hle⟩ := exists_of_mem_smulLat H hd₁
  obtain ⟨a, ha, b, hb, hab⟩ := dec_of D.hU₁ (x₁ : V)
  obtain ⟨a', ha', b', hb', hab'⟩ := dec_of D.hU₁ (x₁' : V)
  obtain ⟨a'', ha'', b'', hb'', hab''⟩ := dec_of D.hU₁ l
  obtain ⟨hda, hdb⟩ := dec_diff D.hU₁ c ha ha' ha'' hb hb' hb'' hab hab' hab'' hle
  have hap : a ∈ H.perp (H.X t₁.f) := by
    have : a = (x₁ : V) - b := by rw [← hab]; abel
    rw [this]
    exact (H.perp _).sub_mem x₁.2 (mem_perp_isotropicSpan_of_mem_framePerp H hb)
  have hap' : a' ∈ H.perp (H.X t₁.f') := by
    have : a' = (x₁' : V) - b' := by rw [← hab']; abel
    rw [this]
    exact (H.perp _).sub_mem x₁'.2 (mem_perp_isotropicSpan_of_mem_framePerp' H hb')
  have haS : a ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha hb (by rw [hab]; exact hx₁L)
  have haS' : a' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha' hb' (by rw [hab']; exact hx₁'L)
  have haS'' : a'' ∈ MMsharp H t₁ :=
    part_MMsharp H t₁ t₁.abelian₂ D.hsd₁ D.hMM₁ ha'' hb'' (by rw [hab'']; exact hl)
  have hmemG : (θ (ddMk H t₁ ⟨a, haS⟩), θ (ddMk H t₁ ⟨a'', haS''⟩), φ (H.mkW t₁.f ⟨a, hap⟩),
      φ' (H.mkW t₁.f' ⟨a', hap'⟩)) ∈ GamR H t₂ c := by
    rw [← hG]
    exact ⟨_, ⟨⟨a, haS⟩, ⟨a', haS'⟩, ⟨a'', haS''⟩, hap, hap', hda, rfl⟩, rfl⟩
  obtain ⟨u, u', u'', hu, hu', huu, hpe2⟩ := hmemG
  simp only [Prod.mk.injEq] at hpe2
  obtain ⟨e1, e2, e3, e4⟩ := hpe2
  have key : ∀ (m : MMsharp H t₁) (n : MMsharp H t₂) (v : H.W0 t₁.f t₁.f'),
      θ (ddMk H t₁ m) = ddMk H t₂ n → (m : V) + v ∈ t₁.abelian₂ → (n : V) + ↑(ψ v) ∈ Λ₂ := by
    intro m n v hmn hv
    obtain ⟨w, hw1, hw2⟩ := (D.hθ m n).1 hmn
    have h1 : ((v - w : H.W0 t₁.f t₁.f') : V) ∈ t₁.abelian₂ := by
      have : ((v - w : H.W0 t₁.f t₁.f') : V) = ((m : V) + v) - ((m : V) + w) := by
        rw [Submodule.coe_sub]
        abel
      rw [this]
      exact t₁.abelian₂.sub_mem hv hw1
    have h2 := (D.hth (v - w)).1 h1
    have : (n : V) + ↑(ψ v) = ((n : V) + ↑(ψ w)) + ↑(ψ (v - w)) := by
      rw [map_sub, Submodule.coe_sub]
      abel
    rw [this]
    exact Λ₂.add_mem hw2 h2
  have hx₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ Λ₂ :=
    key ⟨a, haS⟩ u ⟨b, hb⟩ e1 (by
      show a + b ∈ _
      rw [hab]
      exact hx₁L)
  have hx₂'' : (u'' : V) + ↑(ψ ⟨b'', hb''⟩) ∈ Λ₂ :=
    key ⟨a'', haS''⟩ u'' ⟨b'', hb''⟩ e2 (by
      show a'' + b'' ∈ _
      rw [hab'']
      exact hl)
  have hbb : (⟨b', hb'⟩ : H.W0 t₁.f t₁.f') = ⟨b, hb⟩ - c • ⟨b'', hb''⟩ :=
    Subtype.ext (by
      show b' = b - c • b''
      rw [← hdb]
      abel)
  have hx₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ Λ₂ := by
    have e : (u' : V) + ↑(ψ ⟨b', hb'⟩) =
        ((u : V) + ↑(ψ ⟨b, hb⟩)) - c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Λ₂.sub_mem hx₂ (hcx _ hx₂'')
  have hp₂ : (u : V) + ↑(ψ ⟨b, hb⟩) ∈ H.perp (H.X t₂.f) :=
    (H.perp _).add_mem hu (mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2)
  have hp₂' : (u' : V) + ↑(ψ ⟨b', hb'⟩) ∈ H.perp (H.X t₂.f') :=
    (H.perp _).add_mem hu' (mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2)
  have hd₂ : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) ∈ H.smulLat c Λ₂ := by
    have e : ((u : V) + ↑(ψ ⟨b, hb⟩)) - ((u' : V) + ↑(ψ ⟨b', hb'⟩)) =
        c • ((u'' : V) + ↑(ψ ⟨b'', hb''⟩)) := by
      rw [hbb, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul, smul_add, ← huu]
      abel
    rw [e]
    exact Submodule.subset_span ⟨_, hx₂'', rfl⟩
  have hy : a + b ∈ H.perp (H.X t₁.f) := by
    rw [hab]
    exact x₁.2
  have hy' : a' + b' ∈ H.perp (H.X t₁.f') := by
    rw [hab']
    exact x₁'.2
  have hC : φ (H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩) =
      H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := D.hC1 ⟨b, hb⟩
  have hC' : φ' (H.mkW t₁.f' ⟨b', mem_perp_isotropicSpan_of_mem_framePerp' H hb'⟩) =
      H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := D.hC1' ⟨b', hb'⟩
  have hφ : φ (H.mkW t₁.f x₁) = H.mkW t₂.f ⟨_, hp₂⟩ := by
    calc φ (H.mkW t₁.f x₁) = φ (H.mkW t₁.f ⟨a + b, hy⟩) :=
          congrArg φ (mkW_congr H x₁.2 hy hab.symm)
      _ = H.mkW t₂.f ⟨u, hu⟩ + H.mkW t₂.f ⟨↑(ψ ⟨b, hb⟩), mem_perp_isotropicSpan_of_mem_framePerp H (ψ _).2⟩ := by
          rw [mkW_add H a b hap (mem_perp_isotropicSpan_of_mem_framePerp H hb), map_add, e3, hC]
      _ = H.mkW t₂.f ⟨_, hp₂⟩ := (mkW_add H _ _ hu _).symm
  have hφ' : φ' (H.mkW t₁.f' x₁') = H.mkW t₂.f' ⟨_, hp₂'⟩ := by
    calc φ' (H.mkW t₁.f' x₁') = φ' (H.mkW t₁.f' ⟨a' + b', hy'⟩) :=
          congrArg φ' (mkW_congr H x₁'.2 hy' hab'.symm)
      _ = H.mkW t₂.f' ⟨u', hu'⟩ + H.mkW t₂.f' ⟨↑(ψ ⟨b', hb'⟩), mem_perp_isotropicSpan_of_mem_framePerp' H (ψ _).2⟩ := by
          rw [mkW_add H a' b' hap' (mem_perp_isotropicSpan_of_mem_framePerp' H hb'), map_add, e4, hC']
      _ = H.mkW t₂.f' ⟨_, hp₂'⟩ := (mkW_add H _ _ hu' _).symm
  exact ⟨⟨_, hp₂'⟩, ⟨_, hp₂⟩, hx₂', hx₂, hd₂, Prod.ext hφ' hφ⟩

end RG6

end Formalism.L2.SG.LsDatumA
end
end

