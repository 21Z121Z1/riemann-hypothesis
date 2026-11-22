import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0031
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0045
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0016
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0026
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.UniPart

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensCut
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocSelfDual : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (p : PlF D), (L.H p).IsSelfDual (lattice₂ L p (VS D).L0)

def GaPlusDiag : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∀ p : PlF D,
          ∃ (A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep)
            (a : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → 𝒪[(D.s.atP p).Fp]),
            (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
            GaPlus M δ p (Tn u) (Tn u') Z = (A.map (M p).L.cj).transpose *
              Matrix.diagonal (fun i => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a i : (D.s.atP p).Fp)) * A ∧
            (Finset.univ.filter fun i => ϖ p ∣ a i).card =
              cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal

def NotIntDens : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ¬ Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∃ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = 0

def DensProdVal : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (p : PlF D) (c : ℕ), c ≤ 2 * (D.R.rS + 1) →
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[(D.s.atP p).Fp])
                (if ∀ x : (D.s.atP p).Ep, x ≠ 0 → IsUnit x then -1 else 1) D.R.r (2 * (D.R.rS + 1)) c =
        alphaStd D.host.E p.asIdeal D.R.r / alphaStd D.host.E p.asIdeal (D.R.k - 1 - c)

def DensMultInt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)

theorem densAll_of (h1 : LocSelfDual) (h2 : GaPlusDiag) (h3 : NotIntDens) (h5 : DensProdVal)
    (h6 : DensMultInt) : DensAll := by
  intro D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP
  refine ⟨fun hI => ⟨fun p => ?_, h6 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI⟩,
    h3 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP⟩
  obtain ⟨A, a, hAO, hAdet, hG, hc⟩ := h2 D δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hz hZ hP hI p
  have hSD := h1 D δ M hA L p
  obtain ⟨-, -, hUr, -⟩ := perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hz hZ hP
  have hm := Formalism.L2.SG.Pf.NcArithG.rm_eq D
  have hk5 : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hcard : Fintype.card (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) ≤ Module.finrank (D.s.atP p).Ep (L.V p) := by
    rw [L.rank p, Fintype.card_sum, Fintype.card_fin]
    omega
  have hcle : cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal ≤ 2 * (D.R.rS + 1) := by
    have := Formalism.L2.SG.Pf.Asm.cJ_le (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal
    rw [hUr, hm] at this
    exact this
  unfold densP
  rw [hG, local_density_corank (D.s.atP p).Fp (D.s.atP p).Ep (M p) (D.s.atP p).lf (D.s.atP p).char0 (L.V p)
    (L.H p) (lattice₂ L p (VS D).L0) hSD (ϖ p) (hϖ p) _ A a hAO hAdet hcard, L.rank p, Fintype.card_sum,
    Fintype.card_fin, hc, show D.R.rS + 1 + (D.R.rS + 1) = 2 * (D.R.rS + 1) by ring]
  exact h5 D δ M hA p _ hcle

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetNeOfTotPos
section
noncomputable section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section D7

variable (D : Formalism.BasicNotions.D7)

theorem emb_G {T T' : ℕ} (Z : MatZ D) (φ : D.host.E →+* ℂ) :
    φ (GZ (T : D.host.E) (T' : D.host.E) Z) =
      ((Complex.normSq (φ Z.det) - (T : ℝ) * T' * Complex.normSq (φ (leadMinorE Z D.R.rS)) : ℝ) : ℂ) := by
  have hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1 φ
  rw [GZ, PI.UnitaryGroupMassFormula.CntFormula.DetGa.leadMinorE_full D Z]
  simp only [map_sub, map_mul, map_natCast, hφ, Complex.mul_conj]
  push_cast
  ring

theorem det_ne_of_totPos {T T' : ℕ} (Z : MatZ D) (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (T : D.host.E) (T' : D.host.E) Z)) :
    Z.det ≠ 0 := by
  intro h0
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n; positivity)
  obtain ⟨τ⟩ := this
  have h1 := hP τ
  rw [emb_G D Z, Complex.ofReal_re, h0, map_zero, Complex.normSq_zero, zero_sub] at h1
  have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) T) (Nat.cast_nonneg (α := ℝ) T'))
    (Complex.normSq_nonneg (D.host.emb (D.eTau τ) (leadMinorE Z D.R.rS)))
  linarith

theorem inv_last (Z : MatZ D) (hdet : Z.det ≠ 0) :
    Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) = leadMinorE Z D.R.rS / Z.det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply,
    PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_updateRow_last_single, ← PI.UnitaryGroupMassFormula.CntFormula.DetGa.leadMinorE_prev D Z,
    Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]

theorem gam'_last (N' : ℕ) (Z : MatZ D) :
    Gam' N' Z (Fin.last D.R.rS) (Fin.last D.R.rS) =
      -(N' : D.host.E) * (star (Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)) * Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)) := by
  simp only [Gam', Gam, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, ite_and]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, mul_ite, ite_mul]
  ring

theorem tv_star (N N' : ℕ) (Z : MatZ D) : star (tv N N' Z) = tv N N' Z := by
  rw [tv, star_add, gam'_herm, star_inv₀, star_natCast]

theorem tv_pos (hD : TotPosAll) {N N' : ℕ} (hN : 0 < N) (Z : MatZ D)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (N : D.host.E) (N' : D.host.E) Z)) :
    Formalism.HermitianLattices.Ext.L3.TotPos (tv N N' Z) := by
  have hdet := det_ne_of_totPos D Z hP
  have hGs : star (GZ (N : D.host.E) (N' : D.host.E) Z) = GZ (N : D.host.E) (N' : D.host.E) Z := by
    simp only [GZ, star_sub, star_mul, star_star, star_natCast]
    ring
  have hG := hD D _ hGs hP
  intro φ
  have hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1 φ
  have h1 := hG φ
  rw [emb_G D Z, Complex.ofReal_re] at h1
  have hA : 0 < Complex.normSq (φ Z.det) := Complex.normSq_pos.2 ((map_ne_zero φ).2 hdet)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : φ (tv N N' Z) = (((N : ℝ)⁻¹ - N' * (Complex.normSq (φ (leadMinorE Z D.R.rS)) /
      Complex.normSq (φ Z.det)) : ℝ) : ℂ) := by
    rw [tv, gam'_last, inv_last D Z hdet]
    simp only [map_add, map_mul, map_neg, map_natCast, map_inv₀, hφ, map_div₀, star_div₀]
    rw [div_mul_div_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  rw [ht, Complex.ofReal_re]
  have e : (N : ℝ)⁻¹ - N' * (Complex.normSq (φ (leadMinorE Z D.R.rS)) / Complex.normSq (φ Z.det)) =
      (Complex.normSq (φ Z.det) - N * N' * Complex.normSq (φ (leadMinorE Z D.R.rS))) /
        (N * Complex.normSq (φ Z.det)) := by
    field_simp
  rw [e]
  exact div_pos h1 (mul_pos hNr hA)

end D7

end Formalism.L2.SG.Pf.Cnt.R1

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in

theorem ratPair_of (hD : TotPosAll) : RatPair := by
  intro D u u' _ F0 what₂ _ Z hP
  have hN : 0 < (D.mem u).A.T := (D.mem u).A.T_prime.pos
  obtain ⟨y, hy⟩ := dual_of_flag D hN F0
  have hdet := det_ne_of_totPos D Z hP
  obtain ⟨w0, hw0, hwt⟩ := exists_W_vec D hN hy (tv (D.mem u).A.T (D.mem u').A.T Z)
    (tv_star D _ _ Z) (tv_pos D hD hN Z hP)
  set p := pv F0.e y F0.z (D.mem u).A.T (D.mem u').A.T Z w0 with hp
  set f' : Fin (D.R.rS + 1) → (VS D).V := fun b => ∑ a, Z a b • p a with hf'
  have hfp : ∀ a a', (VS D).hT (F0.fvec a) (p a') = if a = a' then 1 else 0 :=
    fun a a' => hf_pv hy hN hw0 a a'
  have hpp : ∀ a a', (VS D).hT (p a) (p a') = Gam' (D.mem u').A.T Z a a' := hpv_pv hy hN hw0 hwt
  have hzh : ∀ a b, (VS D).hT (F0.fvec a) (f' b) = Z a b := by
    intro a b
    simp only [hf', map_sum, map_smul, smul_eq_mul, hfp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hgr : ∀ b c, (VS D).hT (f' b) (f' c) = Gam D.host.E D.R.rS (D.mem u').A.T b c := by
    intro b c
    rw [hf', gram_comb' p Z b c]
    have h1 : Matrix.of (fun a a' => (VS D).hT (p a) (p a')) = Gam' (D.mem u').A.T Z := by
      ext a a'; simp [hpp]
    have hinv : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z (isUnit_iff_ne_zero.2 hdet)
    rw [h1, Gam']
    simp only [Matrix.mul_assoc]
    rw [hinv, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hne : ∀ d : Fin D.R.rS, Fin.castSucc d ≠ Fin.last D.R.rS := fun d => (Fin.castSucc_lt_last d).ne
  have hind : LinearIndependent D.host.E (fun d : Fin D.R.rS => f' (Fin.castSucc d)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc d
    have hv : Z.mulVec (Fin.snoc (α := fun _ => D.host.E) c 0) = 0 := by
      funext a
      have h1 := congrArg ((VS D).hT (F0.fvec a)) hc
      rw [map_sum, map_zero] at h1
      simp only [map_smul, smul_eq_mul, hzh] at h1
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
    simpa using congrFun this (Fin.castSucc d)
  let Fl : FlagG (VS D) D.R.rS (Tn u') :=
    { e := fun d => f' (Fin.castSucc d)
      z := f' (Fin.last D.R.rS)
      e_indep := hind
      e_iso := fun a b => by rw [hgr]; simp [Gam, hne]
      z_orth := fun a => by rw [hgr]; simp [Gam, hne]
      z_norm := by rw [hgr]; simp [Gam, Tn] }
  refine ⟨⟨Fl, f' (Fin.last D.R.rS)⟩, rfl, ?_⟩
  funext a b
  have hfv : Fl.fvec b = f' b := by
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, Fl]
    | cast b => simp [FlagG.fvec, Fl]
  show brS (VS D) (Fl.fvec b) (F0.fvec a) = Z a b
  rw [brS, hfv, hzh]

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FamilyMeetHolds
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.FamilyMeetLattice

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases

theorem alg_eq {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    (t : 𝓞 F) : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  first
    | rfl
    | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K t).symm.trans (IsScalarTower.algebraMap_apply (𝓞 F) F K t)
    | simp

theorem family_meet_holds : FamMeet := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  classical
  obtain ⟨hbU, hspan, -, -, -⟩ := hba
  obtain ⟨hwW, hworth, hwc, hτ, ⟨s₀, hu⟩, -, -⟩ := hg
  have hπ0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    intro e0
    exact hu.notMem (by rw [show π = 0 from RingOfIntegers.ext e0]; exact Ideal.zero_mem _)
  set p := algebraMap F K (π : F) with hp
  set G := glueFam K 𝔭 b a π w τ with hG
  have hGl : ∀ i, G (Sum.inl i) = if vF 𝔭 (a i) = 0 then b i else
      ((p)⁻¹ ^ vF 𝔭 (a i)) • (b i + w (τ i)) := fun i => rfl
  have hGr : ∀ j, G (Sum.inr j) = w j := fun j => rfl
  have hUloc : locF 𝔭 (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) :=
    Formalism.L2.SG.Pf.G7.locF_subspace U h𝔭.isPrime
  apply le_antisymm
  ·
    rintro x ⟨hx, hxU⟩
    rw [← hspan]
    obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff h𝔭.isPrime _ x).1 hx
    refine (LocF.mem_locF_iff h𝔭.isPrime _ x).2 ⟨t, ht, ?_⟩
    set y := algebraMap (𝓞 F) (𝓞 K) t • x with hy
    have hyU : y ∈ U := Submodule.smul_of_tower_mem U _ hxU
    obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hty
    let cf : Fin (finrank K U) → K := fun i =>
      if vF 𝔭 (a i) = 0 then algebraMap (𝓞 K) K (γ (Sum.inl i)) else algebraMap (𝓞 K) K (γ (Sum.inl i)) * p⁻¹ ^ vF 𝔭 (a i)
    let co : Fin (finrank K U) → K := fun i =>
      if vF 𝔭 (a i) = 0 then 0 else algebraMap (𝓞 K) K (γ (Sum.inl i)) * p⁻¹ ^ vF 𝔭 (a i)
    have hz : y - ∑ i, cf i • b i = ∑ i, co i • w (τ i) + ∑ j, algebraMap (𝓞 K) K (γ (Sum.inr j)) • w j := by
      rw [← hγ, Fintype.sum_sum_type, add_sub_right_comm, ← Finset.sum_sub_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [hGl, ← algebraMap_smul K (γ (Sum.inl i))]
        simp only [cf, co]
        split_ifs with he
        · rw [zero_smul, sub_self]
        · rw [smul_smul, smul_add]
          abel
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [hGr, ← algebraMap_smul K (γ (Sum.inr j))]
    have hzW : ∑ i, co i • w (τ i) + ∑ j, algebraMap (𝓞 K) K (γ (Sum.inr j)) • w j ∈ orthK h U :=
      Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hwW _))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hwW _))
    have hzU : y - ∑ i, cf i • b i ∈ U :=
      Submodule.sub_mem _ hyU (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbU i))
    have hz0 : y - ∑ i, cf i • b i = 0 :=
      (Submodule.disjoint_def.1 hUc.disjoint) _ hzU (hz ▸ hzW)
    have hint : ∀ i, vF 𝔭 (a i) ≠ 0 → ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = cf i := by
      intro i hi
      have h0 := congrArg (h (w (τ i))) (hz.symm.trans hz0)
      rw [map_zero, map_add, map_sum, map_sum] at h0
      simp only [LinearMap.map_smul, smul_eq_mul] at h0
      rw [Finset.sum_eq_single i, Finset.sum_eq_single (τ i)] at h0
      · have hc := hwc (τ i)
        rw [hc.1, ← add_mul] at h0
        have hc0 : algebraMap F K (c (τ i)) ≠ 0 := by rw [map_ne_zero]; exact hc.2
        have h1 := (mul_eq_zero.1 h0).resolve_right hc0
        refine ⟨-γ (Sum.inr (τ i)), ?_⟩
        simp only [cf, co, if_neg hi] at h1 ⊢
        rw [map_neg]
        linear_combination -h1
      · intro j _ hj
        rw [hworth _ _ (Ne.symm hj), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro i' _ hi'
        simp only [co]
        split_ifs with he
        · rw [zero_mul]
        · rw [hworth _ _ (fun e => hi' (hτ i' i he hi e.symm)), mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [sub_eq_zero.1 hz0]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases he : vF 𝔭 (a i) = 0
    · have : cf i = algebraMap (𝓞 K) K (γ (Sum.inl i)) := if_pos he
      rw [this, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · obtain ⟨r, hr⟩ := hint i he
      rw [← hr, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  ·
    rw [← hspan]
    refine le_inf (LocF.locF_mono 𝔭 ?_) ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases he : vF 𝔭 (a i) = 0
      · have : G (Sum.inl i) = b i := by rw [hGl, if_pos he]
        exact Submodule.subset_span ⟨Sum.inl i, this⟩
      · have e1 : b i = algebraMap (𝓞 F) (𝓞 K) π ^ vF 𝔭 (a i) • G (Sum.inl i) - G (Sum.inr (τ i)) := by
          rw [hGl, if_neg he, hGr, ← algebraMap_smul K, map_pow, alg_eq, smul_smul, ← mul_pow,
            mul_inv_cancel₀ hπ0, one_pow, one_smul, add_sub_cancel_right]
        rw [e1]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
          (Submodule.subset_span ⟨_, rfl⟩)
    · calc locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) ≤ locF 𝔭 (U.restrictScalars (𝓞 K)) :=
            LocF.locF_mono 𝔭 (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbU i))
        _ = U.restrictScalars (𝓞 K) := hUloc

end Formalism.L2.SG.Pf.FamilyMeetLattice
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormMemOfDual
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem h_UW {x y : V} (hx : x ∈ U) (hy : y ∈ orthK h U) : h x y = 0 := by
  simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  exact hy x hx

theorem h_WU (hs : h.IsSymm) {x y : V} (hx : x ∈ orthK h U) (hy : y ∈ U) : h x y = 0 := by
  rw [← LinearMap.isSymm_def.1 hs y x, h_UW hy hx, map_zero]

theorem prO_of_mem_U {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ U) : prO hc' x = x := by
  have e := prO_add hc' x
  rw [prO_symm_of_mem_U (hc' := hc') hx, add_zero] at e
  exact e

theorem split (hs : h.IsSymm) (hc' : IsCompl U (orthK h U)) (x y : V) :
    h x y = h (prO hc' x) (prO hc' y) + h (prO hc'.symm x) (prO hc'.symm y) := by
  conv_lhs => rw [← prO_add hc' x, ← prO_add hc' y]
  simp only [map_add, LinearMap.add_apply]
  rw [h_UW (prO_mem hc' x) (prO_symm_mem hc' y), h_WU hs (prO_symm_mem hc' x) (prO_mem hc' y)]
  ring

theorem form_mem_of_dual (hd : dualF h 𝔭 Λ = Λ) {a b : V} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    h a b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have hb' : b ∈ dualF h 𝔭 Λ := by rw [hd]; exact hb
  exact hb' a ha

theorem mem_T_of (hG : Good hc M T 𝔭 Λ) (hd : dualF h 𝔭 Λ = Λ) {b : V} (hb : b ∈ orthK h U)
    (H : ∀ b' ∈ locF 𝔭 (dualIn h (orthK h U) T), h b' b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    b ∈ locF 𝔭 T := by
  have hbΛ : b ∈ Λ := by
    rw [← hd]
    intro y hy
    rw [← prO_add hc y, map_add, LinearMap.add_apply, h_UW (prO_mem hc y) hb, zero_add]
    exact H _ (hG.iW y hy)
  rw [← hG.cW]
  exact Submodule.mem_inf.2 ⟨hbΛ, hb⟩

def FP (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)) : Prop :=
  ∀ x y x' y' : ↥(locF 𝔭 (dualIn h (orthK h U) T)),
    Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
    Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
    h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)

theorem FP.injective (hG : Good hc M T 𝔭 Λ) (hd : dualF h 𝔭 Λ = Λ)
    {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)} (hP : FP P) : Function.Injective P := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨z, -, hz⟩ := hG.oW (x : V) x.2
  have hxW : (x : V) ∈ orthK h U := hz ▸ prO_symm_mem hc z
  have H : ∀ b' ∈ locF 𝔭 (dualIn h (orthK h U) T), h b' x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro b' hb'
    obtain ⟨b'', hb''⟩ := Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk ⟨b', hb'⟩))
    have e := hP ⟨b', hb'⟩ x b'' 0 hb'' (by rw [hq, Submodule.Quotient.mk_zero])
    simpa using e
  have hxT := mem_T_of hG hd hxW H
  rw [← Submodule.Quotient.mk_zero, mk_eq_iff]
  simpa using hxT

theorem fp_of (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hd : dualF h 𝔭 Λ = Λ)
    (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭))
    (H : ∀ b x' : ↥(locF 𝔭 (dualIn h (orthK h U) T)),
      Submodule.Quotient.mk x' = P (Submodule.Quotient.mk b) →
      ∃ z ∈ Λ₀, ∃ w ∈ Λ, prO hc.symm z = b ∧ prO hc.symm w = x' ∧ prO hc z = prO hc w) : FP P := by
  intro x y x' y' hx hy
  obtain ⟨z₁, hz₁, w₁, hw₁, hq₁, hq₁', hp₁⟩ := H x x' hx
  obtain ⟨z₂, hz₂, w₂, hw₂, hq₂, hq₂', hp₂⟩ := H y y' hy
  have e₁ := split hs hc w₁ w₂
  have e₂ := split hs hc z₁ z₂
  rw [hq₁', hq₂', ← hp₁, ← hp₂] at e₁
  rw [hq₁, hq₂] at e₂
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) = h w₁ w₂ - h z₁ z₂ := by
    rw [e₁, e₂]
    ring
  rw [e]
  exact sub_mem (form_mem_of_dual hd hw₁ hw₂) (form_mem_of_dual hd₀ hz₁ hz₂)

def glue (hc' : IsCompl U (orthK h U)) (T : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (Λ₀ : Submodule (𝓞 K) V) (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)) :
    Submodule (𝓞 K) V where
  carrier := {x | ∃ b : ↥(locF 𝔭 (dualIn h (orthK h U) T)), (b : V) = prO hc'.symm x ∧
    ∃ y ∈ Λ₀, ∃ c : ↥(locF 𝔭 (dualIn h (orthK h U) T)), (c : V) = prO hc'.symm y ∧
      prO hc' y = prO hc' x ∧ Submodule.Quotient.mk b = P (Submodule.Quotient.mk c)}
  zero_mem' := ⟨0, by simp, 0, Λ₀.zero_mem, 0, by simp, by simp, by simp⟩
  add_mem' := by
    rintro x x' ⟨b, hb, y, hy, c, hcy, hU, hP⟩ ⟨b', hb', y', hy', c', hcy', hU', hP'⟩
    refine ⟨b + b', by simp [hb, hb'], y + y', Λ₀.add_mem hy hy', c + c', by simp [hcy, hcy'],
      by simp [hU, hU'], ?_⟩
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, map_add, hP, hP']
  smul_mem' := by
    rintro r x ⟨b, hb, y, hy, c, hcy, hU, hP⟩
    refine ⟨r • b, by simp [hb], r • y, Λ₀.smul_mem r hy, r • c, by simp [hcy], by simp [hU], ?_⟩
    rw [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul, hP]

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RebasingHolds
section
open Module

noncomputable section

namespace Formalism.L2.SG.Pf.TemperedBoundGL3

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

theorem rebasing_holds : G3.Rebase := by
  intro K V _ _ _ _ _ S π h hS hπ hs hd
  exact rebaseAt_of hS hπ
    (fun J _ _ b e i₀ ho hu x hx hX => G3.uni_part hS hπ hs hd ho hu x hx hX)
    (fun J _ _ e i₀ x hx T hT hlt b ho hu => G3.absorb hS hπ hs x hx T hT hlt b ho hu)

end Formalism.L2.SG.Pf.TemperedBoundGL3
end
end

