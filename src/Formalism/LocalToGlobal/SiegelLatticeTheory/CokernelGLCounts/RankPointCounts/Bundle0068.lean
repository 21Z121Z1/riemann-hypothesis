import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0064
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DataCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalUnimodularHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.PerpendicularDefinitionHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountPositivity.TotPosOfFlags

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BcPFrame
section
noncomputable section

open scoped Classical
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  ValuativeRel

namespace Formalism.L2.SG.Pf.LocalDenominators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem denF (x : D.host.E) : ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ IsIntegral ℤ (algebraMap D.host.F D.host.E (d : D.host.F) * x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have : (b : 𝓞 D.host.E) ≠ 0 := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have hbi : IsIntegral ℤ (b : D.host.E) := (b : 𝓞 D.host.E).2
  have hbc : IsIntegral ℤ (D.conjF (b : D.host.E)) := hbi.map (D.conjF.toRingHom.toIntAlgHom)
  obtain ⟨t0, ht0⟩ := conjF_fix ((b : D.host.E) * D.conjF (b : D.host.E)) (by rw [map_mul, conjF_invol, mul_comm])
  have ht0i : IsIntegral ℤ t0 := (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1
    (by rw [ht0]; exact hbi.mul hbc)
  refine ⟨⟨t0, ht0i⟩, ?_, ?_⟩
  · intro h
    have h1 : t0 = 0 := congrArg Subtype.val h
    rw [h1, map_zero] at ht0
    have hc0 : D.conjF (b : D.host.E) ≠ 0 := by
      intro hc; apply hb0
      have := congrArg D.conjF hc
      rwa [conjF_invol, map_zero] at this
    exact mul_ne_zero hb0 hc0 ht0.symm
  · show IsIntegral ℤ (algebraMap D.host.F D.host.E t0 *
      (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)))
    have e : algebraMap D.host.F D.host.E t0 *
        (algebraMap (𝓞 D.host.E) D.host.E a / algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E)) =
        D.conjF (b : D.host.E) * (a : D.host.E) := by
      rw [ht0]
      have hb0' : algebraMap (𝓞 D.host.E) D.host.E (b : 𝓞 D.host.E) ≠ 0 := hb0
      field_simp
    rw [e]; exact hbc.mul (a : 𝓞 D.host.E).2

theorem denE (p : PlF D) (a : (D.s.atP p).Ep) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) * a ∈ (D.s.atP p).O := by
  obtain ⟨x, hx, -⟩ := Formalism.L2.SG.Pf.PCountEx.approxE D.s.atP {p} 1 one_ne_zero
    (Function.update (fun q => (0 : (D.s.atP q).Ep)) p a)
  obtain ⟨o, ho, hxo⟩ := hx p (Finset.mem_singleton_self p)
  simp only [Function.update_self, map_one, one_mul] at hxo
  obtain ⟨d, hd0, hdx⟩ := denF x
  refine ⟨d, hd0, ?_⟩
  have hxeq : a = (D.s.atP p).ιE x - o := by rw [← hxo]; ring
  have hd : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) ∈ (D.s.atP p).O := by
    rw [← iE_alg]; exact iE_int (D.s.atP p) ((d : 𝓞 D.host.F).2.map (algebraMap D.host.F D.host.E).toIntAlgHom)
  rw [hxeq, mul_sub]
  refine (D.s.atP p).O.sub_mem ?_ ((D.s.atP p).O.mul_mem hd ho)
  have h2 := iE_int (D.s.atP p) hdx
  rw [map_mul, iE_alg] at h2
  exact h2

theorem baseChangeAt_frame (p : PlF D) (j : Fin (nV D)) : baseChange₂ D p ((VS D).frame j) = Pi.single j 1 := by
  funext i
  simp only [baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

set_option maxHeartbeats 1000000 in

theorem exists_isLattice_eq_localLattice (Zd : LocDat D) (p : PlF D) (M : Submodule (Zd.M p).L.O (Vp D p)) (hfg : M.FG)
    (hsp : Submodule.span (D.s.atP p).Ep (M : Set (Vp D p)) = ⊤) :
    ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsLattice D.host.E Λ' ∧ M = lattice₂ D Zd.M p Λ' := by
  let u : 𝓞 D.host.F → (D.s.atP p).Ep := fun d => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F))
  have u_mem : ∀ d, u d ∈ (D.s.atP p).O := fun d => by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (d : D.host.F)) ∈ (D.s.atP p).O
    rw [← iE_alg]; exact iE_int (D.s.atP p) ((d : 𝓞 D.host.F).2.map (algebraMap D.host.F D.host.E).toIntAlgHom)
  have u_mul : ∀ a b, u (a * b) = u a * u b := fun a b => by
    show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((a * b : 𝓞 D.host.F) : D.host.F)) = _
    push_cast; rw [map_mul, map_mul]
  have smulM : ∀ {z : (D.s.atP p).Ep}, z ∈ (D.s.atP p).O → ∀ {v : Vp D p}, v ∈ M → z • v ∈ M := fun {z} hz {v} hv => by
    have hz' : z ∈ (Zd.M p).L.O := by rw [hO Zd p]; exact hz
    exact M.smul_mem ⟨z, hz'⟩ hv
  obtain ⟨s, hs⟩ := hfg

  have hall : ∀ j : Fin (nV D), (Pi.single j 1 : Vp D p) ∈ Submodule.span (D.s.atP p).Ep ((s : Set (Vp D p))) := by
    intro j
    have h1 : Submodule.span (D.s.atP p).Ep (s : Set (Vp D p)) = ⊤ := by
      rw [← Submodule.span_span_of_tower (Zd.M p).L.O (D.s.atP p).Ep, hs, hsp]
    rw [h1]; exact Submodule.mem_top
  choose ε _ hε using fun j => Submodule.mem_span_finset.1 (hall j)
  choose d hd0 hdm using fun (j : Fin (nV D)) (m : Vp D p) => denE p (ε j m)
  set c : 𝓞 D.host.F := ∏ j, ∏ m ∈ s, d j m with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro j _
    rw [Finset.prod_ne_zero_iff]
    exact fun m _ => hd0 j m
  have hkey : ∀ j, ∀ m ∈ s, u c * ε j m ∈ (D.s.atP p).O := by
    intro j m hm
    have hdv : d j m ∣ c := (Finset.dvd_prod_of_mem _ hm).trans (Finset.dvd_prod_of_mem (fun j => ∏ m ∈ s, d j m)
      (Finset.mem_univ j))
    obtain ⟨r, hr⟩ := hdv
    rw [hr, mul_comm (d j m) r, u_mul, mul_assoc]
    exact (D.s.atP p).O.mul_mem (u_mem r) (hdm j m)
  have hsM : ∀ m ∈ s, m ∈ M := fun m hm => by rw [← hs]; exact Submodule.subset_span hm
  have hce : ∀ j, u c • (Pi.single j 1 : Vp D p) ∈ M := by
    intro j
    rw [← hε j, Finset.smul_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [smul_smul]
    exact smulM (hkey j m hm) (hsM m hm)
  have hdec : ∀ w : Vp D p, u c • w = ∑ i, w i • (u c • (Pi.single i 1 : Vp D p)) := by
    intro w
    funext j
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j), mul_comm]
  have hcv : ∀ v : Vp D p, (∀ i, v i ∈ (D.s.atP p).O) → u c • v ∈ M := by
    intro v hv
    rw [hdec v]
    exact Submodule.sum_mem _ fun i _ => smulM (hv i) (hce i)

  have happ : ∀ m : Vp D p, ∃ xm : (VS D).V, ∃ ov : Vp D p, (∀ i, ov i ∈ (D.s.atP p).O) ∧ baseChange₂ D p xm - m = u c • ov := by
    intro m
    have h1 : ∀ i, ∃ x : D.host.E, ∃ o ∈ (D.s.atP p).O, (D.s.atP p).ιE x - m i = u c * o := by
      intro i
      obtain ⟨x, hx, -⟩ := Formalism.L2.SG.Pf.PCountEx.approxE D.s.atP {p} c hc0
        (Function.update (fun q => (0 : (D.s.atP q).Ep)) p (m i))
      obtain ⟨o, ho, hxo⟩ := hx p (Finset.mem_singleton_self p)
      simp only [Function.update_self] at hxo
      exact ⟨x, o, ho, hxo⟩
    choose x o ho hxo using h1
    refine ⟨(VS D).frame.equivFun.symm x, o, ho, ?_⟩
    funext i
    have hr : (VS D).frame.repr ((VS D).frame.equivFun.symm x) i = x i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    show (D.s.atP p).ιE ((VS D).frame.repr ((VS D).frame.equivFun.symm x) i) - m i = u c * o i
    rw [hr, hxo i]
  choose xs ov hov hxs using happ
  obtain ⟨G, hG⟩ : ∃ G : Set (VS D).V, G = xs '' (s : Set (Vp D p)) ∪
      Set.range (fun i : Fin (nV D) => algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i) := ⟨_, rfl⟩
  have hGx : ∀ m ∈ s, xs m ∈ G := fun m hm => by rw [hG]; exact Or.inl ⟨m, hm, rfl⟩
  have hGc : ∀ i, algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i ∈ G := fun i => by
    rw [hG]; exact Or.inr ⟨i, rfl⟩
  have hGfin : G.Finite := by rw [hG]; exact (s.finite_toSet.image xs).union (Set.finite_range _)
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Λ' = Submodule.span (𝓞 D.host.E) G := ⟨_, rfl⟩
  have hbcf : ∀ i, baseChange₂ D p (algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i) = u c • (Pi.single i 1 : Vp D p) := by
    intro i
    rw [baseChange_smul₂, baseChangeAt_frame, iE_alg]
  have hlat : Submodule.IsLattice D.host.E Λ' := by
    refine ⟨by rw [hΛ']; exact Submodule.fg_span hGfin, ?_⟩
    rw [eq_top_iff, ← (VS D).frame.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hcE : algebraMap D.host.F D.host.E (c : D.host.F) ≠ 0 := by
      rw [ne_eq, map_eq_zero]; exact_mod_cast hc0
    have hmem : algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i ∈ Submodule.span D.host.E (Λ' : Set (VS D).V) :=
      Submodule.subset_span (by rw [hΛ']; exact Submodule.subset_span (hGc i))
    have e : (VS D).frame i = (algebraMap D.host.F D.host.E (c : D.host.F))⁻¹ •
        (algebraMap D.host.F D.host.E (c : D.host.F) • (VS D).frame i) := by
      rw [smul_smul, inv_mul_cancel₀ hcE, one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ hmem
  refine ⟨Λ', hlat, le_antisymm ?_ ?_⟩
  · rw [← hs, Submodule.span_le]
    intro m hm
    have e : m = baseChange₂ D p (xs m) - u c • ov m := by rw [← hxs m]; abel
    rw [SetLike.mem_coe, e]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨xs m, by rw [hΛ']; exact Submodule.subset_span (hGx m hm), rfl⟩) ?_
    rw [hdec (ov m)]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hbcf i]
    exact smul_mem_localLattice Zd p (hov m i) (Submodule.subset_span ⟨_, by rw [hΛ']; exact Submodule.subset_span (hGc i), rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, hΛ'] at hy
    rw [SetLike.mem_coe]
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rw [hG] at hy
      rcases hy with ⟨m, hm, rfl⟩ | ⟨i, rfl⟩
      · have e : baseChange₂ D p (xs m) = m + u c • ov m := by rw [← hxs m]; abel
        rw [e]
        exact M.add_mem (hsM m hm) (hcv _ (hov m))
      · rw [hbcf]; exact hce i
    | zero => rw [map_zero]; exact M.zero_mem
    | add a b _ _ ha hb => rw [map_add]; exact M.add_mem ha hb
    | smul a y _ hy =>
      rw [oE_smul, baseChange_smul₂]
      exact smulM (iE_int (D.s.atP p) (a : 𝓞 D.host.E).2) hy

end Formalism.L2.SG.Pf.LocalDenominators
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DensLoc
section
noncomputable section

namespace Formalism.L2.SG.Pf.DensLoc

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.DataCut Formalism.L2.SG.DataInst
open Formalism.HermitianLattices.Ext.L3
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem prod_lower_third {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 3) {η : ℝ} (hη : η = 1 ∨ η = -1) (a b : ℕ)
    (ha : 1 ≤ a) : Real.exp (-(3 * x ^ a)) ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i * x ^ i) := by
  have habs : ∀ i, |η ^ i| = 1 := fun i => by rcases hη with rfl | rfl <;> simp
  have hxi : ∀ i ∈ Finset.Icc a b, x ^ i ≤ 1 / 2 := fun i hi => by
    have hi1 : 1 ≤ i := le_trans ha (Finset.mem_Icc.1 hi).1
    calc x ^ i ≤ x ^ 1 := pow_le_pow_of_le_one hx0 (by linarith) hi1
      _ ≤ 1 / 2 := by rw [pow_one]; linarith
  have hlow : ∀ i ∈ Finset.Icc a b, 1 - x ^ i ≤ 1 - η ^ i * x ^ i := fun i _ => by
    have : η ^ i * x ^ i ≤ x ^ i := by
      have h1 := le_abs_self (η ^ i * x ^ i)
      rw [abs_mul, habs, one_mul, abs_of_nonneg (pow_nonneg hx0 _)] at h1
      exact h1
    linarith
  have hS : ∑ i ∈ Finset.Icc a b, x ^ i ≤ 3 / 2 * x ^ a := by
    have hI : Finset.Icc a b = Finset.Ico a (b + 1) := by
      ext i; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hI]
    refine (geom_sum_Ico_le_of_lt_one hx0 (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg hx0 a]
  calc Real.exp (-(3 * x ^ a)) ≤ Real.exp (-(2 * ∑ i ∈ Finset.Icc a b, x ^ i)) := by
        apply Real.exp_le_exp.2; linarith
    _ = ∏ i ∈ Finset.Icc a b, Real.exp (-(2 * x ^ i)) := by
        rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ ≤ ∏ i ∈ Finset.Icc a b, (1 - η ^ i * x ^ i) := by
        refine Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i hi => ?_
        exact (LocModel.exp_neg_two_le (pow_nonneg hx0 _) (hxi i hi)).trans (hlow i hi)

section Alpha

variable {K F : Type} [Field K] [Field F] [NumberField F] [Algebra F K]

theorem etaF_pm (𝔭 : Ideal (𝓞 F)) : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
  unfold etaF
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem alphaStd_eq (𝔭 : Ideal (𝓞 F)) (n : ℕ) :
    alphaStd K 𝔭 n = ∏ i ∈ Finset.Icc 1 n, (1 - etaF K F 𝔭 ^ i * ((Ideal.absNorm 𝔭 : ℝ))⁻¹ ^ i) := by
  unfold alphaStd
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem alphaStd_split (𝔭 : Ideal (𝓞 F)) {j n : ℕ} (h : j ≤ n) :
    alphaStd K 𝔭 n = alphaStd K 𝔭 j *
      ∏ i ∈ Finset.Icc (j + 1) n, (1 - etaF K F 𝔭 ^ i * ((Ideal.absNorm 𝔭 : ℝ))⁻¹ ^ i) := by
  rw [alphaStd_eq, alphaStd_eq]
  have hU : Finset.Icc 1 n = Finset.Icc 1 j ∪ Finset.Icc (j + 1) n := by
    ext i; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hD : Disjoint (Finset.Icc 1 j) (Finset.Icc (j + 1) n) :=
    Finset.disjoint_left.2 fun i h1 h2 => by
      simp only [Finset.mem_Icc] at h1 h2; omega
  rw [hU, Finset.prod_union hD]

theorem ratio_bounds (𝔭 : Ideal (𝓞 F)) (hN : (2 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ)) {j n s : ℕ} (hjn : j ≤ n)
    (hs : s ≤ j + 1) (_hs1 : 1 ≤ s) :
    0 < alphaStd K 𝔭 n / alphaStd K 𝔭 j ∧
      alphaStd K 𝔭 n / alphaStd K 𝔭 j ≤ Real.exp (2 * ((Ideal.absNorm 𝔭 : ℝ))⁻¹ ^ s) ∧
      ((3 : ℝ) ≤ (Ideal.absNorm 𝔭 : ℝ) →
        Real.exp (-(3 * ((Ideal.absNorm 𝔭 : ℝ))⁻¹ ^ s)) ≤ alphaStd K 𝔭 n / alphaStd K 𝔭 j) := by
  set x : ℝ := ((Ideal.absNorm 𝔭 : ℝ))⁻¹ with hxdef
  have hx0 : 0 ≤ x := inv_nonneg.2 (by linarith)
  have hx : x ≤ 1 / 2 := by rw [hxdef, one_div]; exact inv_anti₀ (by norm_num) hN
  have hη := etaF_pm (K := K) 𝔭
  have hj0 : 0 < alphaStd K 𝔭 j := by
    rw [alphaStd_eq]
    exact lt_of_lt_of_le (Real.exp_pos _) (LocModel.prod_bounds hx0 hx hη 1 j le_rfl).1
  have hsp := alphaStd_split (K := K) 𝔭 hjn
  set P := ∏ i ∈ Finset.Icc (j + 1) n, (1 - etaF K F 𝔭 ^ i * x ^ i) with hP
  have hq : alphaStd K 𝔭 n / alphaStd K 𝔭 j = P := by
    rw [hsp, mul_div_cancel_left₀ _ hj0.ne']
  rw [hq]
  obtain ⟨hlo, hup⟩ := LocModel.prod_bounds hx0 hx hη (j + 1) n (by omega)
  have hxs : x ^ (j + 1) ≤ x ^ s := pow_le_pow_of_le_one hx0 (by linarith) hs
  refine ⟨lt_of_lt_of_le (Real.exp_pos _) hlo, hup.trans (Real.exp_le_exp.2 (by linarith)), fun h3 => ?_⟩
  have hx3 : x ≤ 1 / 3 := by rw [hxdef, one_div]; exact inv_anti₀ (by norm_num) h3
  exact (Real.exp_le_exp.2 (by linarith)).trans (prod_lower_third hx0 hx3 hη (j + 1) n (by omega))

end Alpha

theorem qP_lt_three_finite (D : Formalism.BasicNotions.D7) : {p : PlF D | qP p < 3}.Finite := by
  obtain ⟨hl, hc⟩ := placesOver_holds D
  have hfin : ∀ m : ℕ, {p : PlF D | Loc.resChar p = m}.Finite := by
    intro m
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (D.R.f + 1)
    have := hc m t fun p hp => ht hp
    omega
  refine ((Set.finite_le_nat 2).biUnion fun m _ => hfin m).subset fun p hp => ?_
  simp only [Set.mem_setOf_eq] at hp
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  refine ⟨Loc.resChar p, ?_, rfl⟩
  have h1 := hl p
  have h2 : ((Loc.resChar p : ℕ) : ℝ) < 3 := lt_of_le_of_lt h1 hp
  have h3 : Loc.resChar p < 3 := by exact_mod_cast h2
  omega

def DensAllAt (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Formalism.MainNotions.S.Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) → ∀ (Z : MatZ D) (F' : LFlag (VS D) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        (Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (Cnt.MMof D F0 F') →
          (∀ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = Formalism.HermitianLattices.Ext.L3.alphaStd D.host.E p.asIdeal D.R.r /
            Formalism.HermitianLattices.Ext.L3.alphaStd D.host.E p.asIdeal (D.R.k - 1 - Cnt.cJ (VS D).hT (Cnt.UPair D F0 F') (Cnt.MMof D F0 F') p.asIdeal)) ∧
          Multipliable (densP L δ ϖ (Tn u) (Tn u') Z)) ∧
        (¬ Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (Cnt.MMof D F0 F') → ∃ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = 0)

theorem densAllAt_of (h5 : Cnt.DensAll) (D : Formalism.BasicNotions.D7) : DensAllAt D := h5 D

theorem densLocBound_at {D : Formalism.BasicNotions.D7} (h5 : DensAllAt D) : DensLocBound D := by
  intro hk δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z hEx
  obtain ⟨Λ, hΛ, F', hF'⟩ := hEx
  have hF'2 := hF'
  obtain ⟨⟨⟨-, hzt⟩, -, hG⟩, -, -, -, hZ⟩ := hF'2
  have hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) := by
    have h1 : GZ (Tn u) (Tn u') Z = Gflag F0 F'.fl := by rw [← hZ]; rfl
    rw [h1]
    exact PI.CntNotPosW.totPos_of_flags D F0 F'.fl hG
  obtain ⟨-, hiff⟩ := Cnt.mmChar_of Cnt.local_unimodular_holds D u u' hT F0 what₂ hR Z F' hzt hZ hP
  have hGl := (hiff Λ).1 ⟨hR.1 Λ hΛ, hF'⟩
  have hI : Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (Cnt.MMof D F0 F') := by
    by_contra hI
    rw [Asm.glueSet_eq_empty hI] at hGl
    exact hGl
  obtain ⟨h5i, -⟩ := h5 δ M hA L u u' hT F0 what₂ hR ϖ hϖ Z F' hzt hZ hP
  obtain ⟨hd, -⟩ := h5i hI
  obtain ⟨-, -, hUr, -⟩ := Cnt.perpendicular_definition_holds D u u' hT F0 what₂ hR Z F' hzt hZ hP
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    have h1 : D.R.rS = D.R.m / 2 - 1 := rfl
    obtain ⟨t, ht⟩ := D.R.m_even
    have := D.R.two_le_m
    omega
  have hkm := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hα := alpBound_holds D hk u u'

  have key : ∀ p : PlF D,
      0 < densP L δ ϖ (Tn u) (Tn u') Z p ∧
      densP L δ ϖ (Tn u) (Tn u') Z p ≤ Real.exp (2 * (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹) ∧
      ((3 : ℝ) ≤ qP p → Real.exp (-(3 * (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹)) ≤
        densP L δ ϖ (Tn u) (Tn u') Z p) := by
    intro p
    have hc : Cnt.cJ (VS D).hT (Cnt.UPair D F0 F') (Cnt.MMof D F0 F') p.asIdeal ≤ D.R.m :=
      (Asm.cJ_le (F := D.host.F) _ _ _ _).trans hUr.le
    have hqe : qP p = ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := LocModel.qPl_eq p
    have hq2 : (2 : ℝ) ≤ ((Ideal.absNorm p.asIdeal : ℕ) : ℝ) := hqe ▸ LocModel.two_le_qPl p
    have hinv : (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹ =
        ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹ ^ (D.R.k - 2 * D.R.rS - 2) := by
      rw [hqe, inv_pow]
    obtain ⟨h1, h2, h3⟩ := ratio_bounds (K := D.host.E) p.asIdeal hq2
      (j := D.R.k - 1 - Cnt.cJ (VS D).hT (Cnt.UPair D F0 F') (Cnt.MMof D F0 F') p.asIdeal) (n := D.R.r)
      (s := D.R.k - 2 * D.R.rS - 2) (by omega) (by omega) (by omega)
    rw [hd p, hinv]
    exact ⟨h1, h2, fun h => h3 (hqe ▸ h)⟩
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨h0, hup, -⟩ := key p
    obtain ⟨hαl, -⟩ := hα p
    have hαpos : 0 < alpD u u' p := lt_of_lt_of_le (Real.exp_pos _) hαl
    refine ⟨h0, ?_⟩
    rw [div_le_iff₀ hαpos]
    set y := (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹
    calc densP L δ ϖ (Tn u) (Tn u') Z p ≤ Real.exp (2 * y) := hup
      _ = Real.exp (4 * y) * Real.exp (-(2 * y)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (4 * y) * alpD u u' p := mul_le_mul_of_nonneg_left hαl (Real.exp_pos _).le
  · refine (qP_lt_three_finite D).subset fun p hp => ?_
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra h3
    push_neg at h3
    obtain ⟨-, -, hlo⟩ := key p
    obtain ⟨hαl, hαu⟩ := hα p
    have hαpos : 0 < alpD u u' p := lt_of_lt_of_le (Real.exp_pos _) hαl
    set y := (qP p ^ (D.R.k - 2 * D.R.rS - 2))⁻¹
    refine absurd hp (not_lt.2 ?_)
    rw [le_div_iff₀ hαpos]
    calc Real.exp (-(5 * y)) * alpD u u' p ≤ Real.exp (-(5 * y)) * Real.exp (2 * y) :=
          mul_le_mul_of_nonneg_left hαu (Real.exp_pos _).le
      _ = Real.exp (-(3 * y)) := by rw [← Real.exp_add]; ring_nf
      _ ≤ densP L δ ϖ (Tn u) (Tn u') Z p := hlo h3

theorem densLocBound_of (h5 : Cnt.DensAll) (D : Formalism.BasicNotions.D7) : DensLocBound D :=
  densLocBound_at (densAllAt_of h5 D)

end Formalism.L2.SG.Pf.DensLoc
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNH
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coef_int (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (c : Fin (D.R.rS + 1) → D.host.E)
    (hc : ∑ a, c a • frame (lf D F0) a ∈ Λ₂) : IsIntegral ℤ (c (Fin.last D.R.rS)) := by
  refine int_of_loc Zd fun p => ?_
  set m := ∑ a, c a • frame (lf D F0) a with hm
  have hbm : baseChange₂ D p m = ∑ a, ((D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) •
      (tLoc Zd p γ).f a := by
    rw [hm, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂, baseChangeAt_frame_eq Zd p γ (hu p), Units.smul_def, smul_smul]
  have hspan : baseChange₂ D p m ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) := by
    rw [hbm]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h2 := (hprim p).2.2 _ (baseChange_mem_localLattice Zd hc p) hspan
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h2
  have hli := (hprim p).2.1
  have hz : ∑ a, (((o a : (Zd.M p).L.O) : (D.s.atP p).Ep) -
      (D.s.atP p).ιE (c a) * (((hu p a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) : (D.s.atP p).Ep)) • (tLoc Zd p γ).f a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← hbm, ← ho]
    simp only [sub_eq_zero]
    rfl
  have h3 := Fintype.linearIndependent_iff.1 hli _ hz (Fin.last D.R.rS)
  have key : ∀ {a : (D.s.atP p).Ep} (h : IsUnit a), a = 1 →
      (((h.unit⁻¹ : ((D.s.atP p).Ep)ˣ)) : (D.s.atP p).Ep) = 1 := by
    intro a h ha
    subst ha
    have : h.unit = 1 := Units.ext (IsUnit.unit_spec h)
    rw [this, inv_one, Units.val_one]
  have hone := key (hu p (Fin.last D.R.rS)) (by rw [sgnP_last, frFac_last', mul_one])
  rw [hone, mul_one, sub_eq_zero] at h3
  rw [← h3]
  exact (o (Fin.last D.R.rS)).2

theorem exists_y (γ : TermDef.Term D u u' F0 what₂) {Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ₂ : Submodule.IsLattice D.host.E Λ₂) (hSD₂ : BwdNA.SD (VS D) Λ₂)
    (hprim : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) (hzX : F0.z ∉ Xsp (lf D F0)) :
    ∃ y ∈ Λ₂, y ∈ orth (VS D) (Xsp (lf D F0)) ∧ (VS D).hT y F0.z = 1 := by
  obtain ⟨f, hfz, hfX⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hzX inferInstance
  let ρ : Module.Dual D.host.E (VS D).V := (f F0.z)⁻¹ • f
  have hρz : ρ F0.z = 1 := by
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hfz
  have hρX : ∀ x ∈ Xsp (lf D F0), ρ x = 0 := fun x hx => by
    have h1 : f x ∈ (Xsp (lf D F0)).map f := ⟨x, hx, rfl⟩
    rw [hfX, Submodule.mem_bot] at h1
    simp only [ρ, LinearMap.smul_apply, smul_eq_mul, h1, mul_zero]
  have hρe : ∀ i : Fin D.R.rS, ρ (frame (lf D F0) i.castSucc) = 0 := fun i => by
    rw [frame_cs]; exact hρX _ (Submodule.subset_span ⟨i, rfl⟩)
  have hρl : ρ (frame (lf D F0) (Fin.last D.R.rS)) = 1 := by
    have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [this, hρz]
  obtain ⟨v, hv⟩ := BwdNA.riesz (VS D) ρ
  let U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range (frame (lf D F0)))
  have hint : ∀ m ∈ Λ₂, m ∈ U → IsIntegral ℤ ((VS D).hT m v) := fun m hm hmU => by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hmU
    have hρm : ρ m = c (Fin.last D.R.rS) := by
      rw [← hc, map_sum, Fin.sum_univ_castSucc]
      simp only [map_smul, smul_eq_mul, hρe, mul_zero, Finset.sum_const_zero, zero_add, hρl, mul_one]
    rw [BwdNA.hsw (VS D) v m, hv, hρm]
    exact BwdNA.isInt_star (coef_int Zd γ hprim hu c (by rw [hc]; exact hm))
  obtain ⟨w, hwΛ, hvw⟩ := BwdNA.dual_sum (VS D) Λ₂ hΛ₂ hSD₂ U v hint
  have hw : ∀ a, (VS D).hT w (frame (lf D F0) a) = ρ (frame (lf D F0) a) := fun a => by
    have h0 := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hvw _ (Submodule.subset_span ⟨a, rfl⟩)
    rw [map_sub, sub_eq_zero] at h0
    rw [BwdNA.hsw (VS D) (frame (lf D F0) a) w, ← h0, ← BwdNA.hsw (VS D) (frame (lf D F0) a) v, hv]
  refine ⟨w, hwΛ, (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).2 fun x hx => ?_, ?_⟩
  · change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [BwdNA.hsw (VS D) w (F0.e i), ← frame_cs, hw, hρe, star_zero]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
    | smul c x _ hx => rw [BwdNA.hT_smulL, hx, mul_zero]
  · have : frame (lf D F0) (Fin.last D.R.rS) = F0.z := by simp [frame, FlagG.fvec]
    rw [← this, hw, hρl]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

