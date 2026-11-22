import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0088
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0067
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0047
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ReHermitianCombinationNonpos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0075
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0018
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0089

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameMemUUE
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Saturated Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open BwdCut BwdBetaCut BwdNP BetaI

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem localSign_sq (p : PlF D) (a : Fin (D.R.rS + 1)) : TermLoc.sgnP D p a * TermLoc.sgnP D p a = 1 := by
  unfold TermLoc.sgnP
  split
  · rename_i sg _
    rw [← map_mul, Prod.mk_mul_mk, Formalism.L2.SG.Pf.FibD.neg_one_pow_sq, one_mul]
    exact map_one sg.e.symm
  · exact one_mul 1

theorem hu_all (p : PlF D) (a : Fin (D.R.rS + 1)) : IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a) :=
  IsUnit.mul ⟨Units.mkOfMulEqOne _ _ (localSign_sq p a), rfl⟩
    (Formalism.L2.SG.Pf.StabShape.frFac_unit Zd.δ Zd.M (Zd.agree p) a)

theorem frame_mem_UUE {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (G : LFlag (VS D) D.R.rS T') (b : Fin (D.R.rS + 1)) :
    frame G b ∈ UUE Λ F (liftF G) := by
  induction b using Fin.lastCases with
  | last =>
    rw [frame_lastG]
    apply Submodule.subset_span
    show G.fl.z ∈ (UU Λ F (liftF G) : Set (VS D).V)
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  | cast i =>
    rw [frame_csG]
    haveI := hΛ
    obtain ⟨s, hs, hsv⟩ := Formalism.L2.SG.Pf.exists_smul_mem Λ (G.fl.e i)
    have hX : s • G.fl.e i ∈ UU Λ F (liftF G) := by
      refine Submodule.mem_sup_left (Submodule.mem_sup_right ⟨hsv, ?_⟩)
      show s • G.fl.e i ∈ (Xsp (liftF G) : Set (VS D).V)
      exact Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨i, rfl⟩)
    have hs' : ((s : D.host.E)) ≠ 0 := by exact_mod_cast hs
    have e : G.fl.e i = ((s : D.host.E))⁻¹ • (s • G.fl.e i) := by
      rw [← algebraMap_smul (R := 𝓞 D.host.E) D.host.E s (G.fl.e i), smul_smul]
      show G.fl.e i = (((s : D.host.E))⁻¹ * algebraMap (𝓞 D.host.E) D.host.E s) • G.fl.e i
      rw [show algebraMap (𝓞 D.host.E) D.host.E s = (s : D.host.E) from rfl, inv_mul_cancel₀ hs', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hX)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.OrthogonalLocalComplement
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalPositivity
section
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.LocalPositivity

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem pos_of_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a / b) : 0 < a ∧ 0 < b := by
  rcases div_pos_iff.1 h with h' | h'
  · exact h'
  · exact absurd ha (not_le.2 h'.1)

theorem localVolumeUnit_pos_and_ZZX_pos (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hTT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) :
    0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v := by
  have hU : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  have hZ : 0 ≤ ZZX X u u' ψ v := ENNReal.toReal_nonneg
  by_cases hv : TypAt X v
  · have e := volTypV_holds X u u' ψ hψ hs hTT v hv
    exact pos_of_div hU hZ (by rw [e]; exact pow_pos (by exact_mod_cast hg v hv) _)
  · have e := volOrdV_holds X u u' ψ hψ hs v hv
    exact pos_of_div hU hZ (by rw [e]; exact Real.rpow_pos_of_pos (absV_pos v (dV_ne_zero v)) _)

theorem pp_pos_ord (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) {v : PlX X} (hv : ¬ TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
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
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO]
  refine mul_pos (pow_pos (absV_pos v (dV_ne_zero v)) _) (Finset.prod_pos fun q _ => ?_)
  exact inv_pos.2 (pow_pos (absV_pos v (pow_ne_zero _ (alp_ne_zero v D.R.rS l))) 2)

theorem jac_pos (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) : 0 < jacX X v := by
  unfold jacX jacS
  refine Finset.prod_pos fun l _ => ?_
  have hx : (∏ i ∈ Finset.univ.filter (fun i : Fin (D.R.rS + 1) => (i : ℕ) ≤ (l : ℕ)), alp v D.R.rS i ^ 2) *
      (if TypAt X v then ((gAt X v : Fv X.B.I.F v)⁻¹) ^ ((l : ℕ) + 1) else 1) ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (alp_ne_zero v D.R.rS i)) ?_
    split_ifs with ht
    · refine pow_ne_zero _ (inv_ne_zero ?_)
      exact_mod_cast (hg v ht).ne'
    · exact one_ne_zero
  exact pow_pos (pow_pos (absV_pos v hx) 2) 2

end Formalism.L2.SG.Pf.LocalPositivity
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxCong
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem one_mem_R {p : PlF D} (a b : Fin (D.R.rS + 1)) :
    (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (M p).R := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (M p).R.one_mem
  · exact (M p).R.zero_mem

theorem mem_R_of_sub_one {p : PlF D} (hA : Agree δ M p) {X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (h : EntIn (latS (D.s.atP p) (ellP p)) (X - 1)) (a b : Fin (D.R.rS + 1)) : X a b ∈ (M p).R := by
  have e : X a b = (X - 1) a b + (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b := by
    rw [Matrix.sub_apply]; ring
  rw [e]
  exact (M p).R.add_mem (latS_R hA (h a b)) (one_mem_R M a b)

theorem cong_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ c : (D.s.atP p).Fp, c ≠ 0 ∧ c ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ k : ProdE.StP M δ u u' w p,
      EntIn (latS (D.s.atP p) c) ((k.1.1 : ProdE.MP p) - 1) → EntIn (latS (D.s.atP p) c) ((k.1.2.unop : ProdE.MP p) - 1) →
        k ∈ ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w hA L U hL hU := by
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by
    rw [← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hUU : Upi * Up = 1 := by
    rw [← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  have hLp := ProdE.lOf_loUni M δ hA L U hL hU
  have hLpi := ProdE.lOf_loUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  have hUp := ProdE.ρOf_upUni M δ hA L U hL hU
  have hUpi := ProdE.ρOf_upUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  refine ⟨ellP p * (s1 * s2 * s3 * s4),
    mul_ne_zero (ellP_ne p) (mul_ne_zero (mul_ne_zero (mul_ne_zero hs10 hs20) hs30) hs40),
    Subring.mul_mem _ (ellP_mem p) (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O),
    fun k h1 h2 => ?_⟩
  obtain ⟨hk1, hk2, -⟩ := k.2
  have hO12 : s1 * s2 * s3 * s4 ∈ 𝒪[(D.s.atP p).Fp] :=
    Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O
  have h1l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.1 : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h1
  have h2l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.2.unop : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h2
  have h1c : EntIn (latS (D.s.atP p) (ellP p)) (Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi) :=
    entIn_sandwich hs1 hs2 (entIn_latS_of_eq (t := s3 * s4) (by ring) (Subring.mul_mem _ hs3O hs4O) h1)
  have h2c : EntIn (latS (D.s.atP p) (ellP p)) (Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up) :=
    entIn_sandwich hs4 hs3 (entIn_latS_of_eq (t := s1 * s2) (by ring) (Subring.mul_mem _ hs1O hs2O) h2)
  have e1 : Lp * (k.1.1 : ProdE.MP p) * Lpi - 1 = Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLL]
  have e2 : Upi * (k.1.2.unop : ProdE.MP p) * Up - 1 = Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
  have hc1 := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLp hk1) hLpi
  have hc2 := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUpi hk2) hUp
  refine Subgroup.mem_inf.2 ⟨⟨⟨fun a => (hk1 a a).2 rfl, fun a b h => (hk1 a b).1 h,
    mem_R_of_sub_one M δ hA h1l⟩, ⟨fun a => (hk2 a a).2 rfl, fun a b h => (hk2 a b).1 h, mem_R_of_sub_one M δ hA h2l⟩⟩,
    ⟨⟨fun a => (hc1 a a).2 rfl, fun a b h => (hc1 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e1]; exact h1c)⟩,
    ⟨fun a => (hc2 a a).2 rfl, fun a b h => (hc2 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e2]; exact h2c)⟩⟩⟩

end Cong

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolLat
section
noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolLat

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

theorem mem_of_mul (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hI : I ≠ 0) (m n : ℤ) (y : D.host.E)
    (h : ∀ x ∈ I ^ n, x * y ∈ I ^ m) : y ∈ I ^ (m - n) := by
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n ≤ I ^ m := by
    refine FractionalIdeal.mul_le.2 fun a ha b hb => ?_
    obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 ha
    rw [smul_mul_assoc, mul_comm]
    exact (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h b hb)))
  have h2 : I ^ (-n) * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y * I ^ n) ≤ I ^ (-n) * I ^ m :=
    mul_right_mono hle
  rw [mul_comm (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) y), ← mul_assoc, ← zpow_add₀ hI,
    neg_add_cancel, zpow_zero, one_mul, ← zpow_add₀ hI, neg_add_eq_sub] at h2
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ y)

theorem coef_XS {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {v : (VS D).V} (hv : v ∈ XS D F0)
    (y : Fin D.R.rS → D.host.E) (hy : v = ∑ a, y a • F0.e a) (a : Fin D.R.rS) :
    y a ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have key : ∃ y' : Fin D.R.rS → D.host.E, (∀ a : Fin D.R.rS, y' a ∈ (ddS D ^ (-((D.R.rS : ℤ) - ((a : Fin D.R.rS) : ℕ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧ v = ∑ a, y' a • F0.e a := by
    clear hy
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, x, hx, rfl⟩ := hx
      refine ⟨Pi.single a x, fun b => ?_, ?_⟩
      · by_cases h : b = a
        · subst h
          simpa using hx
        · rw [Pi.single_eq_of_ne h]
          exact FractionalIdeal.zero_mem _
      · rw [Finset.sum_eq_single a (fun b _ hb => by rw [Pi.single_eq_of_ne hb, zero_smul]) (by simp),
          Pi.single_eq_same]
    | zero => exact ⟨0, fun _ => FractionalIdeal.zero_mem _, by simp⟩
    | add x w _ _ hx hw =>
      obtain ⟨y1, h1, rfl⟩ := hx
      obtain ⟨y2, h2, rfl⟩ := hw
      exact ⟨y1 + y2, fun a => (FractionalIdeal.mem_coe).1 (Submodule.add_mem _ ((FractionalIdeal.mem_coe).2 (h1 a))
        ((FractionalIdeal.mem_coe).2 (h2 a))), by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul c x _ hx =>
      obtain ⟨y1, h1, rfl⟩ := hx
      refine ⟨fun a => (c : D.host.E) * y1 a, fun a => ?_, ?_⟩
      · have := (FractionalIdeal.mem_coe).1 (Submodule.smul_mem _ c ((FractionalIdeal.mem_coe).2 (h1 a)))
        rwa [Algebra.smul_def] at this
      · rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← smul_assoc, Algebra.smul_def]
  obtain ⟨y', hy', hv'⟩ := key
  have hyy : y = y' := by
    have h := F0.e_indep
    rw [Fintype.linearIndependent_iff] at h
    funext b
    have := h (y - y') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, ← hy, ← hv', sub_self]) b
    exact sub_eq_zero.1 this
  rw [hyy]
  exact hy' a

end Formalism.L2.SG.Pf.ZsVolLat

end
end

