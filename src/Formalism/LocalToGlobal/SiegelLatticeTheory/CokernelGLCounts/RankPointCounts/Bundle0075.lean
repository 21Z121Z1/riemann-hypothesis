import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0073
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LocOpenHolds
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0047
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0072
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0035
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0029

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMapFlag
section
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem omp_congr {F G : FlagG S r T} {F' G' : FlagG S r T'} (h : ∀ a, F.fvec a = G.fvec a)
    (h' : ∀ a, F'.fvec a = G'.fvec a) : omp F F' = omp G G' ∧ Zhat F F' = Zhat G G' := by
  have hF : F.fvec = G.fvec := funext h
  have hF' : F'.fvec = G'.fvec := funext h'
  have hZ : Zhat F F' = Zhat G G' := by
    unfold Zhat
    first
      | rw [hF, hF']
      | (simp only [hF, hF']; rfl)
  refine ⟨?_, hZ⟩
  unfold omp
  rw [hZ, hF']

theorem fvec_mapFlag (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (b : Fin (r + 1)) :
    (mapFlag g hg F).fvec b = g (F.fvec b) := by
  unfold FlagG.fvec
  induction b using Fin.lastCases with
  | last => simp [mapFlag]
  | cast i => simp [mapFlag]

theorem coef_mat (F : FlagG S r T) (s : S.V →ₗ[E] S.V) (hs : ∀ j, ∀ x ∈ F.Xa (j + 1), s x - x ∈ F.Xa j)
    (hz : s F.z - F.z ∈ F.X) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c) ∧ M.det = 1 ∧
      ∀ c, M (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  have hcolE : ∀ b' : Fin r, ∃ l : Fin r →₀ E, (∀ i : Fin r, ¬ i.1 < b'.1 → l i = 0) ∧
      s (F.e b') = F.e b' + ∑ i, l i • F.e i := by
    intro b'
    have hmem : F.e b' ∈ F.Xa (b'.1 + 1) := Submodule.subset_span ⟨b', Nat.lt_succ_self _, rfl⟩
    have h1 := hs b'.1 (F.e b') hmem
    obtain ⟨l, hl, hl2⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 h1
    refine ⟨l, fun i hi => (Finsupp.mem_supported' E l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hl2
    rw [hl2]
    abel
  choose l hl0 hl using hcolE
  obtain ⟨cz, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hz
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun c b =>
    Fin.lastCases (motive := fun _ => E)
      (Fin.lastCases (motive := fun _ => E) 1 (fun i => cz i) c)
      (fun b' => Fin.lastCases (motive := fun _ => E) 0 (fun i => (if i = b' then 1 else 0) + l b' i) c) b
  have hMcol : ∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, one_smul]
      have h2 : s F.z = F.z + ∑ i, cz i • F.e i := by
        rw [hcz]
        abel
      rw [h2, add_comm]
    | cast b' =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, zero_smul, add_zero, add_smul, Finset.sum_add_distrib, ite_smul,
        one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hl b'
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [M]
    | cast i => simp [M, hl0 i i (lt_irrefl _)]
  have htri : M.BlockTriangular id := by
    intro i j hij
    induction j using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last i))
    | cast j =>
      induction i using Fin.lastCases with
      | last => simp [M]
      | cast i =>
        have hji : j < i := by simpa using hij
        have hne : i ≠ j := (ne_of_lt hji).symm
        simp [M, hne, hl0 j i (not_lt.2 (le_of_lt hji))]
  refine ⟨M, hMcol, ?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  · intro c
    induction c using Fin.lastCases with
    | last => simp [M]
    | cast c => simp [M, Fin.castSucc_ne_last]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed
section
namespace Formalism.L2.SG.Pf.MassDataX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

theorem stK_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StK X p :=
  MassDataIdxSteps.stK_holds X p

theorem stRed_holds {D : D7} (X : HidaSetting D) (p : TypX X) : MassDataIdxSteps.StRed X p :=
  MassDataIdxSteps.stRed_of_embP X p (MassDataIdxSteps.embP_holds X p)

theorem stImA_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : TypX X) :
    MassDataIdxSteps.StImA X hb p :=
  MassDataIdxSteps.stImA_of X hb p (MassDataIdxSteps.reduction_image_every_place X hb p)

theorem stImB_holds {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) :
    MassDataIdxSteps.StImB X u p :=
  MassDataIdxSteps.stImB_of_adaptQ X u p (MassDataIdxSteps.stAdaptQ_holds X hb u p)

theorem inIndicesAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : LocIn (TypX X)) (A : AnIn),
      InIndicesAt X hb hK FdN FdN' u u' X0 L A :=
  local_indices_at_instance

end Formalism.L2.SG.Pf.MassDataX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowMulSelf
section
noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Conj

variable (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (hA : ∀ q, Agree δ M q)

include hA in
theorem dd_conj {h : ℕ} (hk : h ≤ D.R.rS) {x : D.host.E} (hx : x ∈ ddPow D h) : D.conjF x ∈ ddPow D h := by
  rw [← locGlob _ (shapeNZ.1 h)] at hx ⊢
  exact fun p => locMem_conj δ M hA p hk (hx p)

include hA in
theorem qd_conj {h : ℕ} (hk : h ≤ D.R.rS) {x : D.host.E} (hx : x ∈ qdPow D h) : D.conjF x ∈ qdPow D h := by
  rw [qdPow_mem_iff] at hx ⊢
  have := dd_conj δ M hA hk hx
  rwa [map_div₀, map_natCast] at this

end Conj

theorem neg_one_pow_mul_self (k : ℕ) : ((-1 : D.host.E) ^ k) * (-1) ^ k = 1 := by
  rw [← pow_add]; exact Even.neg_one_pow ⟨k, rfl⟩

variable (w : Point D.host.E (D.R.rS + 1))

def sgm (a c : Fin (D.R.rS + 1)) : D.host.E := (-1) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val)

omit w in
theorem sgm_mul (a d c : Fin (D.R.rS + 1)) : sgm a d * sgm d c = sgm a c := by
  unfold sgm
  have := neg_one_pow_mul_self (D := D) (D.R.rS - d.val)
  linear_combination ((-1 : D.host.E) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val)) * this

omit w in
theorem sgm_self (a : Fin (D.R.rS + 1)) : sgm a a = (1 : D.host.E) := neg_one_pow_mul_self _

omit w in
theorem sgm_conj (a c : Fin (D.R.rS + 1)) : D.conjF (sgm a c) = sgm a c := by
  simp [sgm, map_pow, map_neg, map_one]

omit w in
theorem sgm_cases (a c : Fin (D.R.rS + 1)) : sgm a c = (1 : D.host.E) ∨ sgm a c = -1 := by
  unfold sgm
  rw [← pow_add]
  exact neg_one_pow_eq_or _ _

theorem sgm_pinv (a c : Fin (D.R.rS + 1)) (hs : blkOf w.1 a.val = blkOf w.1 c.val) :
    sgm a c * sgm (pinv w c) (pinv w a) = (1 : D.host.E) := by
  unfold sgm
  have h1 := pinv_add w a c hs
  have ha := a.isLt; have hc := c.isLt; have ha' := (pinv w a).isLt; have hc' := (pinv w c).isLt
  rw [show ((-1 : D.host.E)) ^ (D.R.rS - a.val) * (-1) ^ (D.R.rS - c.val) *
      ((-1) ^ (D.R.rS - (pinv w c).val) * (-1) ^ (D.R.rS - (pinv w a).val)) =
      (-1) ^ ((D.R.rS - a.val) + (D.R.rS - c.val) + (D.R.rS - (pinv w c).val) + (D.R.rS - (pinv w a).val)) by ring]
  exact Even.neg_one_pow ⟨2 * D.R.rS - (pinv w a).val - a.val, by omega⟩

def Psi (Mt : MatR D) : MatR D := fun a c => sgm a c * D.conjF (Mt (pinv w c) (pinv w a))

def piPerm : Equiv.Perm (Fin (D.R.rS + 1)) := ⟨pinv w, pinv w, pinv_pinv w, pinv_pinv w⟩

theorem Psi_sub (A B : MatR D) : Psi w (A - B) = Psi w A - Psi w B := by
  funext a c; simp [Psi, map_sub, mul_sub]

theorem Psi_mul (A B : MatR D) : Psi w (A * B) = Psi w B * Psi w A := by
  funext a c
  simp only [Psi, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (piPerm w) _ _ (fun e => ?_)
  simp only [piPerm, Equiv.coe_fn_mk, pinv_pinv]
  rw [← sgm_mul a (pinv w e) c]; ring

theorem Psi_one : Psi w (1 : MatR D) = 1 := by
  funext a c
  simp only [Psi, Matrix.one_apply]
  by_cases h : a = c
  · subst h; simp [sgm_self]
  · have : pinv w c ≠ pinv w a := fun e => h (pinv_inj w e).symm
    simp [this, h]

theorem Psi_inv {A : MatR D} (hA : IsUnit A.det) : Psi w A⁻¹ = (Psi w A)⁻¹ := by
  have : Psi w A⁻¹ * Psi w A = 1 := by rw [← Psi_mul, Matrix.mul_nonsing_inv _ hA, Psi_one]
  exact (Matrix.inv_eq_left_inv this).symm

theorem Psi_Psi {A : MatR D} (hB : IsBlockDiagonalMatrix w A) : Psi w (Psi w A) = A := by
  funext a c
  simp only [Psi, pinv_pinv, map_mul, Formalism.MainNotions.BridgeLemma.conjF_inv, sgm_conj]
  by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
  · rw [← mul_assoc, sgm_pinv w a c hs, one_mul]
  · rw [hB a c hs, mul_zero, mul_zero]

theorem Psi_blk {A : MatR D} (hB : IsBlockDiagonalMatrix w A) : IsBlockDiagonalMatrix w (Psi w A) := by
  intro a c hne
  have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
    rw [blkOf_pinv, blkOf_pinv]; exact fun e => hne e.symm
  simp only [Psi, hB _ _ this, map_zero, mul_zero]

theorem Psi_upU {A : MatR D} (hU : UpU A) (hB : IsBlockDiagonalMatrix w A) : UpU (Psi w A) := by
  intro a c
  refine ⟨fun hca => ?_, fun hac => ?_⟩
  · simp only [Psi]
    by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
    · have := (pinv_lt_iff w c a hs.symm).1 hca
      rw [(hU _ _).1 this, map_zero, mul_zero]
    · have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
        rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
      rw [hB _ _ this, map_zero, mul_zero]
  · subst hac; simp [Psi, sgm_self, (hU _ _).2 rfl]

theorem Psi_grD (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {A : MatR D} (hB : IsBlockDiagonalMatrix w A) (hG : GrD A) : GrD (Psi w A) := by
  intro a c hac
  simp only [Psi]
  by_cases hs : blkOf w.1 a.val = blkOf w.1 c.val
  · have hle : pinv w c ≤ pinv w a := by
      rcases eq_or_lt_of_le hac with h | h
      · rw [h]
      · exact le_of_lt ((pinv_lt_iff w a c hs).1 h)
    have hh : (pinv w a).val - (pinv w c).val = c.val - a.val := by
      have := pinv_add w a c hs; omega
    have h1 := hG _ _ hle
    rw [hh] at h1
    have h2 := dd_conj δ M hA (by have := c.isLt; omega) h1
    rcases sgm_cases a c with e | e
    · rw [e, one_mul]; exact h2
    · rw [e, neg_one_mul]; exact (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem h2
  · have : blkOf w.1 (pinv w c).val ≠ blkOf w.1 (pinv w a).val := by
      rw [blkOf_pinv, blkOf_pinv]; exact fun e => hs e.symm
    rw [hB _ _ this, map_zero, mul_zero]; exact FractionalIdeal.zero_mem _

theorem blk_inv {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) : IsBlockDiagonalMatrix w X⁻¹ := by
  obtain ⟨hlo, hXi, hW, -⟩ := st_of_X w hU hB
  set β := ptMat w * X * (ptMat w)⁻¹
  have hu := ptMat_isUnit w
  have hβd : IsUnit β.det := by rw [loU_det (show LoU β from hlo)]; exact isUnit_one
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hW' : β⁻¹ * ptMat w * X = ptMat w := by
    have : ptMat w * X⁻¹ = β⁻¹ * ptMat w := by
      calc ptMat w * X⁻¹ = β⁻¹ * (β * ptMat w * X⁻¹) := by
            rw [Matrix.mul_assoc β]; exact (Matrix.nonsing_inv_mul_cancel_left β _ hβd).symm
        _ = β⁻¹ * ptMat w := by rw [hW]
    rw [← this, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hXd, Matrix.mul_one]
  obtain ⟨h1, -, h3⟩ := X_of_st w (loU_inv (show LoU β from hlo)) hU hW'
  rw [h1] at h3
  exact h3

end Formalism.L2.SG.Pf.StabIntLat
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NofibOf
section
namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting NumberField

def NOfibLat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    ∃ τ : ∀ p : CBlk D.R.rS, (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → CSpc (InfinitePlace X.B.I.F) D.R.k p,
      (∀ p (x x' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), (∀ q, cHgt q < cHgt p → x q = x' q) → τ p x = τ p x') ∧
      ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
        x ∈ blk X u '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ ∀ p, x p - τ p x ∈ cLat X u p

theorem nofib_of (hL : NOfibLat) : NOfib := by
  intro D X u
  obtain ⟨h1, h2, h3⟩ := nOinf_closed_under_mul_inv X u
  exact ⟨h1, h2, h3, hL X u⟩

end Formalism.L2.SG.Pf.NcReal.JX
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnramifiedFactorEqOne
section
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem absV_prod {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v) : absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact absV_one v
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, absV_mul, ih]

theorem absV_alp_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (h1 : absV v (dV v) = 1)
    (r : ℕ) (i : Fin (r + 1)) : absV v (alp v r i) = 1 := by
  rw [absV_alp, h1, Real.one_rpow]

section Vols

variable {X} {ψ}

theorem zz_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : ZZX X u u' ψ v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH1, -, hO1⟩ := hN v hv (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  have := hH1
  have hsetZ : ZZOrd (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
        {c | sc (E := X.B.I.E) v (alp v D.R.rS p.1 * alp v D.R.rS p.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [ZZOrd, locZ, Set.mem_pi, Prod.forall]
  unfold ZZX volS
  rw [if_neg hv, hsetZ, SdW.boxScaleL_holds v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) hfin
    (sdE (E := X.B.I.E) ψ v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => alp v D.R.rS p.1 * alp v D.R.rS p.2)
    (fun p => mul_ne_zero (alp_ne_zero v D.R.rS p.1) (alp_ne_zero v D.R.rS p.2)), hO1, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [absV_mul, absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem uo_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) :
    (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS) (UO (E := X.B.I.E) v D.R.rS)).toReal = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH2, -, hO2⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have hsetU : UO (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun q : UIdx D.R.rS =>
        {c | sc (E := X.B.I.E) v ((alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [UO, Set.mem_pi]
  rw [hsetU, SdW.boxScaleL_holds v (UIdx D.R.rS) hfin (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS))
    (fun q : UIdx D.R.rS => (alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2)
    (fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v D.R.rS q.1.1)) (alp_ne_zero v D.R.rS q.1.2)), hO2, h1,
    one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_mul, absV_inv v (alp_ne_zero v D.R.rS q.1.1), absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem unramified_factor_eq_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : localVolumeUnit X ψ v = 1 := by
  obtain ⟨hH2, hS2, -⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have := hS2
  unfold localVolumeUnit volU
  rw [if_neg hv, localVolumeOrdinary, Measure.prod_prod, ENNReal.toReal_mul, uo_one hN hv h1, one_mul]

theorem pp_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) (l : Fin (D.R.rS + 1)) :
    PPX X u u' ψ l v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_pow, absV_alp_one v h1]
  norm_num

theorem jac_one {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : jacX X v = 1 := by
  unfold jacX jacS
  refine Finset.prod_eq_one fun l _ => ?_
  rw [if_neg hv, mul_one, absV_prod]
  rw [Finset.prod_eq_one fun i _ => by rw [absV_pow, absV_alp_one v h1, one_pow]]
  norm_num

end Vols

theorem VolOneAEC_holds (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : VolOneAEC X u u' ψ := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hT : Set.Finite {v : PlX X | TypAt X v} := (typSet X.B.I.F (D.host.g 0) (D.host.g 1)).finite_toSet
  have hI := differentIdeal_ne_zero' X.B.I.F
  have hD := Ideal.hasFiniteMulSupport hI
  refine (hT.union hD).subset fun v hv => ?_
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Function.mem_mulSupport, not_or, not_not] at hnot
  obtain ⟨htyp, hmax⟩ := hnot
  have h1 : absV v (dV v) = 1 := by rw [absV_dV, hmax, map_one, Nat.cast_one, inv_one]
  exact hv ⟨unramified_factor_eq_one hN htyp h1, zz_one u u' hN htyp h1, fun l => pp_one u u' hN htyp h1 l, jac_one htyp h1⟩

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

