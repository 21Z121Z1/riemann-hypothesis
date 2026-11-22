import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0023
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0042
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0041
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0004
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0025
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0047

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HsNormSqEqHilbertSchmidtSq
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.OOCoreHilbertSchmidt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hsNormSq_eq_hilbertSchmidt_sq {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  first
    | exact inner_self_eq_norm_sq _
    | (rw [inner_self_eq_norm_sq_to_K]; norm_cast)
    | (rw [inner_self_eq_norm_sq_to_K]; simp [sq])

variable {D : D7} {X : HidaSetting D} (u u' : D.what₂.Word)

theorem hsNormSq_OOP_quot (ν : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : Formalism.L2.SG.Pf.Carrier.JointPf.OOQuot X u u' ν νl) (w : Point D.host.E (D.R.rS + 1))
    (hw : ∃ γ, IsPtRep X u u' w γ) (hG : ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) :
    Formalism.MainNotions.S.hsNormSq (Formalism.L2.SG.Pf.OOCore.OOP u u' ν w) =
      ∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  have hF := hQ w hw hG
  rw [hsNormSq_eq_hilbertSchmidt_sq]
  simp only [hsNormSq_eq_hilbertSchmidt_sq]
  unfold Formalism.L2.SG.Pf.OOCore.OOP hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

def GXPos : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ γ, IsPtRep X u u' w γ) → ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v

variable (Y : Formalism.L2.SG.Full.Full X) {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

def LocNormP (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), Formalism.L2.SG.ThmBUse.IsRowPt D (D.mem u).A.T (D.mem u').A.T w →
    (∃ g, IsPtRep X u u' w g) →
    Complex.normSq ((Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
        (∏ v, Formalism.MainNotions.S.hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
          Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))) *
      (Formalism.L2.SG.LoopTerm.covN (Y := Y) C u * Formalism.L2.SG.LoopTerm.covN (Y := Y) C u') =
      Formalism.L2.SG.Pf.JointAmplitudePoints.localAmplitudeProduct u u' hB w

section GX

variable {D : D7} {X : HidaSetting D}

theorem frm_sc (u : D.what₂.Word) (sc : ℝ) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    frm X u sc v a = (((sc ^ (D.R.rS - a.val))⁻¹ : ℝ) : ℂ) • frm X u 1 v a := by
  unfold frm famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Complex.ofReal_inv, Complex.ofReal_pow]

theorem zx_rd (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) (a b : Fin (D.R.rS + 1)) :
    ZX X u u' D.host.rdE γ v a b = ((rhoF D a * rhoF D b : ℝ) : ℂ) * ZX X u u' 1 γ v a b := by
  have hρ : ∀ c : Fin (D.R.rS + 1), rhoF D c = (D.host.rdE ^ (D.R.rS - (c : ℕ)))⁻¹ := by
    intro c
    have hc := c.isLt
    unfold rhoF
    have h1 := Real.rpow_intCast D.host.rdE (-((D.R.rS - (c : ℕ) : ℕ) : ℤ))
    rw [zpow_neg, zpow_natCast] at h1
    rw [← h1]
    congr 1
    push_cast [Nat.cast_sub (Nat.lt_succ_iff.mp hc)]
    ring
  rw [hρ a, hρ b]
  unfold ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_sc u D.host.rdE v a, frm_sc u' D.host.rdE v b, Matrix.mulVec_smul]
  unfold hJ
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  clear hρ
  push_cast
  ring

theorem gx_eq (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (hw : ∃ γ, IsPtRep X u u' w γ)
    (τ : D.what₂.Tau) :
    GX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) =
      Formalism.MainNotions.S.ThB.Gpt (Tw (D := D) u) (Tw (D := D) u') (Formalism.MainNotions.S.ThB.ptLoc D τ w) := by
  have hrep : IsPtRep X u u' w (gamW X u u' w) := by
    unfold gamW
    rw [dif_pos hw]
    exact hw.choose_spec
  have hZ : ∀ a b, ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ) a b =
      (-1 : ℂ) ^ (D.R.rS - b.val) * ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w) a b := by
    intro a b
    have h1 := congrFun (congrFun (hrep (vOf X τ)) a) b
    unfold Formalism.L2.SG.RealObj.ZhatO Formalism.L2.SG.RealObj.ptC at h1
    simp only [Matrix.map_apply] at h1
    rw [X.φ_eq, X.ιE.apply_symm_apply, show X.pl (vOf X τ) = τ from X.pl.apply_symm_apply τ] at h1
    have hs : ((-1 : ℂ) ^ (D.R.rS - b.val)) * (-1 : ℂ) ^ (D.R.rS - b.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [zx_rd, Formalism.L2.SG.Pf.RelPtR.ptMat_ptLoc τ w a b]
    have h2 : ZX X u u' 1 (gamW X u u' w) (vOf X τ) a b = (-1 : ℂ) ^ (D.R.rS - b.val) * embS D τ (ptMat w a b) := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2]
    ring
  have hD : ∀ l (hl : l ≤ D.R.rS + 1), Complex.normSq (Formalism.L2.SG.RealObj.Dl (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)) l) =
      Complex.normSq (leadMinor (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)) l hl) := by
    intro l hl
    unfold Formalism.L2.SG.RealObj.Dl leadMinor
    rw [dif_pos hl]
    have hM : (ZX X u u' D.host.rdE (gamW X u u' w) (vOf X τ)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
        (ptMat (Formalism.MainNotions.S.ThB.ptLoc D τ w)).submatrix (Fin.castLE hl) (Fin.castLE hl) *
          Matrix.diagonal (fun b : Fin l => (-1 : ℂ) ^ (D.R.rS - (Fin.castLE hl b).val)) := by
      ext i j
      simp [Matrix.mul_diagonal, hZ, mul_comm]
    rw [hM, Matrix.det_mul, Matrix.det_diagonal, map_mul, map_prod]
    simp [Complex.normSq_neg]
  unfold GX Gv Formalism.MainNotions.S.ThB.Gpt
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hD (D.R.rS + 1) le_rfl, hD D.R.rS (Nat.le_succ _)]

theorem gxPos_holds (u u' : D.what₂.Word) : GXPos (X := X) u u' := by
  intro w hb hw v
  have hv : v = vOf X (X.pl v) := (X.pl.symm_apply_apply v).symm
  rw [hv, gx_eq u u' w hw (X.pl v)]
  exact hb.2 (X.pl v)

end GX

end Formalism.L2.SG.Pf.OOCoreHilbertSchmidt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RhoSurjPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.RhoSurjW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.AllRowsOf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i
  simp [PI.FinKW.vecV, map_sub]

theorem vecV_nsmul (v : HeightOneSpectrum (𝓞 X.B.I.F)) (c : ℕ)
    (a : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (c • a) = c • PI.FinKW.vecV X.B.I v a := by
  funext i
  simp [PI.FinKW.vecV]

theorem exists_cofactor (p : TypX X) : ∃ c : ℕ, (X.B.g : ℕ) = gOf p * c := by
  rw [X.g_eq]
  unfold gOf
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨D.host.g 0, mul_comm _ _⟩

theorem piV_mem_KgX (x : X.B.I.Gf) (hx : x ∈ X.B.I.Kg X.B.g) (p : TypX X) :
    piV X.B.I p.1 (tf X.B.I hb x) ∈ MassDataIdxSteps.KgX X p := by
  have hKf := (Bridge_mem_Kf_iff X.B.I hb x).2 hx.1
  rw [Kf, Subgroup.mem_iInf] at hKf
  refine ⟨hKf p.1, ?_⟩
  intro y hy
  obtain ⟨c, hc⟩ := exists_cofactor X p
  obtain ⟨u, huv, huw⟩ := PI.FinKW.local_vector_lift X.B.I p.1 y
  have huL : u ∈ X.B.I.Lf := PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective X.B.I u fun w => by
    by_cases hw : w = p.1
    · subst hw
      rw [huv]
      exact hy
    · rw [huw w hw]
      exact zero_mem _
  obtain ⟨z, hzL, hz⟩ := hx.2 u huL
  have hfx : X.B.I.fmat x = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := (toHA_isBridge X.B.I hb (1, x)).2
  refine ⟨c • PI.FinKW.vecV X.B.I p.1 z, nsmul_mem (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I z hzL p.1) c, ?_⟩
  have e := congrArg (PI.FinKW.vecV X.B.I p.1) hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecV_sub, hfx, PI.FinKW.vecV_mulVec, huv, Nat.cast_smul_eq_nsmul,
    vecV_nsmul] at e
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_smul, ← hc]
  exact e

end Loc

section Count

variable {D : D7} (X : HidaSetting D)

theorem card_target :
    Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = Nat.card (G0g D.nd) := by
  classical
  have hT : (Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod]
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.prod_typ X (fun g => (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod g)) : ℝ))]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.ggC_eq D.R (gOf p)]
    rfl
  have hG : (Nat.card (G0g D.nd) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sigma, Fin.prod_univ_two]
    have e : ∀ k : Fin 2, ∏ _v : D.nd.PlG k, (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) =
        (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g k))) : ℝ) ^ D.R.f := fun k => by
      rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
      rfl
    exact congrArg₂ (· * ·) (e 0) (e 1)
  exact_mod_cast hT.trans hG.symm

end Count

theorem reduction_map_surjective : RhoSurj := by
  intro D X
  classical
  let hb : AdBridgeIso X.B.I := (Formalism.L2.SG.Closed.adelic_isomorphism_statement X.B.I).1
  have hK : ∀ p : TypX X, ((KvS X p : Subgroup _) : Set (MassDataIdxSteps.HAp X p)) = MassDataIdxSteps.KvX X p := by
    intro p
    obtain ⟨K, hKs, -, -, -⟩ := Formalism.L2.SG.Pf.MassDataX.stK_holds X p
    have e : KvS X p = K := by
      have e : (K : Set _) = Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1 := hKs
      rw [KvS, ← e, Subgroup.closure_eq]
    rw [e]
    exact hKs
  choose ρ hρ hker using fun p : TypX X => Formalism.L2.SG.Pf.MassDataX.stRed_holds X p (KvS X p) (hK p)
  let ψ : KsetSub X.B.I →* ∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MonoidHom.pi fun p => (ρ p).comp (Pi.evalMonoidHom (fun p => KvS X p) p)).comp (phiK X hb)
  have hψ : Function.Surjective ψ := by
    intro t
    choose a ha using fun p => hρ p (t p)
    obtain ⟨k, hk⟩ := phiK_surjective X hb single_component_surjective a
    refine ⟨k, funext fun p => ?_⟩
    show ρ p (phiK X hb k p) = t p
    rw [hk]
    exact ha p
  let ι : KSub X.B.I → KsetSub X.B.I := fun x => ⟨x.1, x.2⟩
  have hψι : ∀ x y : KSub X.B.I, rhoX X x = rhoX X y → ψ (ι x) = ψ (ι y) := by
    intro x y hxy
    have h1 : rhoX X (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hg := (rhoX_eq_one_iff X _).1 h1
    have h2 : ψ (ι (x⁻¹ * y)) = 1 := by
      funext p
      show ρ p (phiK X hb (ι (x⁻¹ * y)) p) = 1
      exact (hker p _).2 (RhoSurjW.piV_mem_KgX X hb _ hg p)
    have h3 : ι (x⁻¹ * y) = (ι x)⁻¹ * ι y := rfl
    rw [h3, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let f : (rhoX X).range → (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) :=
    fun r => ψ (ι (MonoidHom.mem_range.1 r.2).choose)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨k, hk⟩ := hψ t
    let x : KSub X.B.I := ⟨k.1, k.2⟩
    let r : (rhoX X).range := ⟨rhoX X x, x, rfl⟩
    exact ⟨r, (hψι _ x (MonoidHom.mem_range.1 r.2).choose_spec).trans hk⟩
  have hle : Nat.card (G0g D.nd) ≤ Nat.card (rhoX X).range := by
    rw [← RhoSurjW.card_target X]
    exact Nat.card_le_card_of_surjective f hf
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_le_card _ hle)

end Formalism.L2.SG.Pf.RhoSurjW
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.StandardCoordinates
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.StandardCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (v : InfinitePlace X.B.I.F) {lam : ℂ} (hl : lam ≠ 0)
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}
  (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi) (u' : D.what₂.Word)

include hT in

theorem fam_eq (hl : lam ≠ 0) (b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.RealObj.frm X u' 1 v b =
      (lam ^ (D.R.rS - b.val))⁻¹ • (Q *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun c => ?_) b
  · rw [Fin.snoc_last]
    unfold Formalism.QuantumDeterminants.fvec
    rw [dif_neg (by simp), Matrix.mulVec_mulVec, hT.2.1, Matrix.one_mulVec, Fin.val_last, Nat.sub_self, pow_zero,
      inv_one, one_smul]
  · rw [Fin.snoc_castSucc]
    have h1 := (hT.2.2.2 c c rfl).1
    unfold Formalism.QuantumDeterminants.fvec Formalism.QuantumDeterminants.bvec
    simp only [Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.eta]
    rw [h1, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]

include hT hl in

theorem stCoordV_gen (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε v))
    (p : Formalism.L2.SG.RealObj.FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v y p =
      ((D.host.rdE : ℂ) * lam) ^ (D.R.rS - p.1.1.1) / ((D.host.rdE : ℂ) * lam) ^ (D.R.rS - p.1.2.1) *
      ((Qi * uMat ((γ v)⁻¹ * y * γ v) * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) p.1.2)
        (Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨p.1.1.1, by have := p.2.1; have := p.1.2.isLt; omega⟩) := by
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  have ha : p.1.1.1 < D.R.rS := by have := p.2.1; have := p.1.2.isLt; omega
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have := Formalism.L2.SG.RealFrameCoordinates.frS_mul_rd D
    intro h; rw [h, mul_zero] at this; exact zero_ne_one this
  set z' := Qi *ᵥ rv X.B.I v (X.zR u') with hz'
  set f := Formalism.QuantumDeterminants.fvec D.R.k D.R.rS z' p.1.2 with hf
  have hfrm : Formalism.L2.SG.RealObj.frm X u' D.host.rdE v p.1.2 =
      ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.val))⁻¹ • ((lam ^ (D.R.rS - p.1.2.val))⁻¹ • (Q *ᵥ f)) := by
    rw [← fam_eq v hT u' hl p.1.2]
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
  have hfR : rv X.B.I v (X.fR ⟨p.1.1.1, ha⟩) =
      star (lam ^ (D.R.rS - p.1.1.1)) • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨p.1.1.1, ha⟩) 1) := by
    rw [(hT.2.2.2 ⟨p.1.1.1, ha⟩ ⟨p.1.1.1, ha⟩ rfl).2, smul_smul, mul_inv_cancel₀, one_smul]
    exact star_ne_zero.2 (pow_ne_zero _ hl)
  have hM : uMat ((γ v)⁻¹ * y * γ v) *ᵥ (Q *ᵥ f) = Q *ᵥ ((Qi * uMat ((γ v)⁻¹ * y * γ v) * Q) *ᵥ f) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc Q, ← Matrix.mul_assoc Q, hQQi, Matrix.one_mul]
  have hQ : ∀ x v' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ,
      star (Q *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ (Q *ᵥ v')) = star x ⬝ᵥ (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS *ᵥ v') := by
    intro x v'
    rw [← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH]
  unfold Formalism.L2.SG.NGPin.stCoordV
  rw [hfrm, hfR, Matrix.mulVec_smul, Matrix.mulVec_smul, hM]
  unfold hJ
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, star_smul, smul_dotProduct, hQ,
    Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RealFrameCoordinates.hpk_esI]
  simp only [smul_eq_mul, star_star]
  have h1 : (lam ^ (D.R.rS - p.1.2.val)) ≠ 0 := pow_ne_zero _ hl
  have h2 : ((D.host.rdE : ℂ) ^ (D.R.rS - p.1.2.val)) ≠ 0 := pow_ne_zero _ hrd
  rw [mul_pow, mul_pow]
  field_simp

include hT hl in

theorem coord_conj (M H : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)
    (hHU : Hᴴ * Formalism.REAL.Jm (X.B.I.ε v) * H = Formalism.REAL.Jm (X.B.I.ε v)) (hHu : IsUnit H.det)
    (he : ∀ b, H *ᵥ rv X.B.I v (X.eR b) = rv X.B.I v (X.eR b)) (hz : H *ᵥ rv X.B.I v (X.zR u') = rv X.B.I v (X.zR u'))
    (hfa : ∀ a, H *ᵥ rv X.B.I v (X.fR a) = rv X.B.I v (X.fR a)) (a : Fin D.R.rS) (b : Fin (D.R.rS + 1)) :
    ((Qi * (H⁻¹ * M * H) * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) =
      ((Qi * M * Q) *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) := by
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  set f := Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (Qi *ᵥ rv X.B.I v (X.zR u')) b with hf

  have hHf : H *ᵥ (Q *ᵥ f) = Q *ᵥ f := by
    have := fam_eq v hT u' hl b
    have e : Q *ᵥ f = lam ^ (D.R.rS - b.val) • Formalism.L2.SG.RealObj.frm X u' 1 v b := by
      rw [this, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hl), one_smul]
    rw [e, Matrix.mulVec_smul]
    congr 1
    unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
    simp only [Complex.ofReal_one, one_pow, inv_one, one_smul]
    refine Fin.lastCases ?_ (fun c => ?_) b
    · rw [Fin.snoc_last]; exact hz
    · rw [Fin.snoc_castSucc]; exact he c

  have hread : ∀ x : Fin X.B.I.n → ℂ, (Qi *ᵥ x) (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) =
      (lam ^ (D.R.rS - a.val))⁻¹ * hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) x := by
    intro x
    have hfR : rv X.B.I v (X.fR a) = star (lam ^ (D.R.rS - a.val)) • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) 1) := by
      rw [(hT.2.2.2 a a rfl).2, smul_smul, mul_inv_cancel₀, one_smul]
      exact star_ne_zero.2 (pow_ne_zero _ hl)
    have hx : x = Q *ᵥ (Qi *ᵥ x) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
    rw [hfR]
    conv_rhs => rw [hx]
    unfold hJ
    rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
      Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RealFrameCoordinates.hpk_esI, smul_eq_mul, star_star,
      ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl), one_mul]
  have hisom : ∀ x y : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (H *ᵥ x) (H *ᵥ y) = hJ (X.B.I.ε v) x y := by
    intro x y
    unfold hJ
    rw [← Formalism.L2.SG.HermitianMatrixIdentities.star_dot_conjT' H x (Formalism.REAL.Jm (X.B.I.ε v) *ᵥ (H *ᵥ y)), Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hHU]
  have hinvJ : ∀ x : Fin X.B.I.n → ℂ, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (H⁻¹ *ᵥ x) =
      hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) x := by
    intro x
    have hx : H *ᵥ (H⁻¹ *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hHu, Matrix.one_mulVec]
    rw [← hisom, hfa a, hx]
  have e1 : (Qi * (H⁻¹ * M * H) * Q) *ᵥ f = Qi *ᵥ (H⁻¹ *ᵥ (M *ᵥ (Q *ᵥ f))) := by
    simp only [← Matrix.mulVec_mulVec, hHf]
  have e2 : (Qi * M * Q) *ᵥ f = Qi *ᵥ (M *ᵥ (Q *ᵥ f)) := by
    simp only [← Matrix.mulVec_mulVec]
  rw [e1, e2, hread, hread, hinvJ]

end Formalism.L2.SG.StandardCoordinates

end
end

