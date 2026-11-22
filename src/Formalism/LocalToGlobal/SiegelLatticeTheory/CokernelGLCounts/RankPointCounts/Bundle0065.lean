import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0047
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0009
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDenominatorSecond
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0061
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0056
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaRatA
section
noncomputable section

open scoped Classical
open Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BRat

open FsLA BwdBetaS OmP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}

def projL {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := lin u (pc u v)
  map_add' x y := by rw [pc_add, lin_add]
  map_smul' t x := by rw [pc_smul, lin_smul, RingHom.id_apply]

def moveL {ι : Type*} [Fintype ι] [DecidableEq ι] (u u' : ι → S.V) : S.V →ₗ[E] S.V where
  toFun v := lin u' (pc u v)
  map_add' x y := by rw [pc_add, lin_add]
  map_smul' t x := by rw [pc_smul, lin_smul, RingHom.id_apply]

theorem pc_of_orth {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → S.V) {y : S.V} (hy : ∀ k, S.hT (u k) y = 0) :
    pc u y = 0 := by
  have h0 : (fun k => S.hT (u k) y) = 0 := funext fun k => hy k
  rw [pc, h0, Matrix.mulVec_zero]

theorem lin_zero {ι : Type*} [Fintype ι] (u : ι → S.V) : lin u 0 = 0 := by simp [lin]

theorem isometry_extension_two {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (u u' : ι → S.V) (w : κ → S.V) (hG : gram S u' u' = gram S u u) (hdet : (gram S u u).det ≠ 0)
    (hdetw : (gram S w w).det ≠ 0) (hsp : ∀ i, u' i ∈ Submodule.span E (Set.range w))
    (hkey : ∀ y y', (∀ k, S.hT (u k) y = 0) → (∀ k, S.hT (u k) y' = 0) →
      S.hT (lin w (pc w y)) (lin w (pc w y')) = 0) :
    ∃ g : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (g x) (g y) = S.hT x y) ∧ (∀ i, g (u i) = u' i) ∧
      (∀ y, (∀ k, S.hT (u k) y = 0) → g y = y - lin w (pc w y)) := by
  let P : S.V →ₗ[E] S.V := LinearMap.id - projL u
  let β : S.V →ₗ[E] S.V := (LinearMap.id - projL w) ∘ₗ P + moveL u u'
  have hβ : ∀ v, β v = ((v - lin u (pc u v)) - lin w (pc w (v - lin u (pc u v)))) + lin u' (pc u v) :=
    fun v => rfl
  have hsp' : ∀ c, lin u' c ∈ Submodule.span E (Set.range w) := fun c =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hsp i)
  have hGe : ∀ i j, S.hT (u' i) (u' j) = S.hT (u i) (u j) := fun i j => congrFun (congrFun hG i) j
  have hiso : ∀ x y, S.hT (β x) (β y) = S.hT x y := by
    intro x y
    set x' := x - lin u (pc u x) with hx'
    set y' := y - lin u (pc u y) with hy'
    have hx'u : ∀ k, S.hT (u k) x' = 0 := fun k => hT_u_rem u hdet x k
    have hy'u : ∀ k, S.hT (u k) y' = 0 := fun k => hT_u_rem u hdet y k
    have hk := hkey x' y' hx'u hy'u
    rw [hβ, hβ]

    have t1 : S.hT (x' - lin w (pc w x')) (lin u' (pc u y)) = 0 := (hT_span_rem w hdetw x' _ (hsp' _)).2
    have t2 : S.hT (lin u' (pc u x)) (y' - lin w (pc w y')) = 0 := (hT_span_rem w hdetw y' _ (hsp' _)).1
    have t3 : S.hT (lin u' (pc u x)) (lin u' (pc u y)) = S.hT (lin u (pc u x)) (lin u (pc u y)) := by
      rw [hT_lin_lin, hT_lin_lin]; simp only [hGe]
    have t4 : S.hT (x' - lin w (pc w x')) (lin w (pc w y')) = 0 :=
      (hT_span_rem w hdetw x' _ (lin_sub w _)).2
    have t5 : S.hT (lin w (pc w x')) (y' - lin w (pc w y')) = 0 :=
      (hT_span_rem w hdetw y' _ (lin_sub w _)).1
    have t6 : S.hT (x' - lin w (pc w x')) (y' - lin w (pc w y')) = S.hT x' y' := by
      have e1 : S.hT (x' - lin w (pc w x')) (y' - lin w (pc w y')) =
          S.hT (x' - lin w (pc w x')) y' := by
        rw [map_sub, t4, sub_zero]
      have e2 : S.hT (lin w (pc w x')) y' = 0 := by
        have := t5
        rw [map_sub, hk, sub_zero] at this
        exact this
      rw [e1, map_sub S.hT x' (lin w (pc w x')), LinearMap.sub_apply, e2, sub_zero]
    have hxy : S.hT x y = S.hT x' y' + S.hT (lin u (pc u x)) (lin u (pc u y)) := by
      have dx : x = x' + lin u (pc u x) := by rw [hx']; abel
      have dy : y = y' + lin u (pc u y) := by rw [hy']; abel
      conv_lhs => rw [dx, dy]
      simp only [map_add, LinearMap.add_apply]
      rw [(hT_span_rem u hdet x _ (lin_sub u _)).2, (hT_span_rem u hdet y _ (lin_sub u _)).1]
      ring
    rw [← hx', ← hy']
    simp only [map_add, LinearMap.add_apply]
    rw [t1, t2, t3, t6, hxy]
    ring
  have hinj : Function.Injective β := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    refine (Submodule.mem_bot E).2 (S.nondeg.1 v fun y => ?_)
    rw [← hiso v y, hv, map_zero, LinearMap.zero_apply]
  have hbij : Function.Bijective β := ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  refine ⟨LinearEquiv.ofBijective β hbij, hiso, fun i => ?_, fun y hy => ?_⟩
  · show β (u i) = u' i
    rw [hβ, pc_self u hdet, lin_single, lin_single, sub_self]
    have : pc w (0 : S.V) = 0 := by
      have := pc_smul w 0 0
      simpa using this
    rw [this, lin_zero, sub_zero, zero_add]
  · show β y = y - lin w (pc w y)
    rw [hβ, pc_of_orth u hy, lin_zero, lin_zero, sub_zero, add_zero]

variable {r : ℕ}

theorem norm_om_ne {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) (hG : Gflag A B ≠ 0) : 1 + TA * S.hT Ω Ω ≠ 0 := by
  have hx := om_zcoef A B hdet hΩ
  set c := (Zhat A B)⁻¹ (Fin.last r) (Fin.last r) with hc
  set x := Ω - c • B.z with hxd
  have hΩe : Ω = x + c • B.z := by rw [hxd]; abel
  have hxx : S.hT x x = 0 := NMoveP.hT_X_X B hx hx
  have hxz : S.hT x B.z = 0 := by
    have h := NMoveP.hT_f_X B (Fin.last r) hx
    rw [NMoveP.fvecL] at h
    rw [BwdNA.hsw S B.z x, h, star_zero]
  have hzx : S.hT B.z x = 0 := by
    have h := NMoveP.hT_f_X B (Fin.last r) hx
    rwa [NMoveP.fvecL] at h
  have hnorm : S.hT Ω Ω = star c * c * (-TB) := by
    rw [hΩe]
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, hxx, hxz, hzx,
      B.z_norm, smul_eq_mul, starRingEnd_apply, mul_zero, zero_add, add_zero]
    ring
  have hcl : c = leadMinorE (Zhat A B) r / (Zhat A B).det := inv_last _
  intro h0
  apply hG
  unfold Gflag Dl
  rw [FsLA.leadMinorE_full]
  rw [hnorm, hcl, star_div₀] at h0
  have hs : star (Zhat A B).det ≠ 0 := star_ne_zero.2 hdet
  field_simp at h0
  linear_combination h0

theorem key_X {TA TB : E} (A : FlagG S r TA) (B : FlagG S r TB) (hdet : (Zhat A B).det ≠ 0) {Ω : S.V}
    (hΩ : OmV A B Ω) (hG : Gflag A B ≠ 0) {q : S.V}
    (hq : q ∈ Submodule.span E (Set.range (Sum.elim A.fvec B.fvec))) (hqA : ∀ a, S.hT (A.fvec a) q = 0)
    (hqΩ : S.hT Ω q = 0) : q ∈ A.X := by
  obtain ⟨x, hx, c, rfl⟩ := dec A B hdet hΩ hq hqA
  have hΩx : S.hT Ω x = 0 := by
    rw [BwdNA.hsw S x Ω]
    have : x ∈ A.X := hx
    have h := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).1 (show Ω ∈ orth S A.X from ?_) x this
    · rw [h, star_zero]
    · refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun y hy => ?_
      change y ∈ Submodule.span E (Set.range A.e) at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        rw [← fvec_cs, hΩ.2]
        simp [Fin.castSucc_ne_last]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul t y _ hy => rw [BwdNA.hT_smulL, hy, mul_zero]
  have hΩz : S.hT Ω A.z = 1 := by
    rw [BwdNA.hsw S A.z Ω, ← fvec_last, hΩ.2]
    simp
  have h1 : S.hT Ω (x + c • (A.z + TA • Ω)) = c * (1 + TA * S.hT Ω Ω) := by
    rw [map_add, hΩx, zero_add, map_smul, map_add, map_smul, hΩz, smul_eq_mul, smul_eq_mul]
  rw [h1] at hqΩ
  have hc : c = 0 := (mul_eq_zero.1 hqΩ).resolve_right (norm_om_ne A B hdet hΩ hG)
  rw [hc, zero_smul, add_zero]
  exact hx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BRat
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfE
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching IsDedekindDomain ValuativeRel

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

namespace CohIntPf

variable {D : Formalism.BasicNotions.D7}

theorem denF' (x : D.host.E) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ IsIntegral ℤ (algebraMap D.host.F D.host.E (d : D.host.F) * x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 D.host.E) x
  have hb0 : (b : D.host.E) ≠ 0 := by
    have : (b : 𝓞 D.host.E) ≠ 0 := nonZeroDivisors.ne_zero hb
    exact_mod_cast this
  have hbi : IsIntegral ℤ (b : D.host.E) := (b : 𝓞 D.host.E).2
  have hbc : IsIntegral ℤ (D.conjF (b : D.host.E)) := hbi.map (D.conjF.toRingHom.toIntAlgHom)
  obtain ⟨t0, ht0⟩ := Formalism.L2.SG.Pf.LocalDenominators.conjF_fix ((b : D.host.E) * D.conjF (b : D.host.E))
    (by rw [map_mul, Formalism.L2.SG.Pf.LocalDenominators.conjF_invol, mul_comm])
  have ht0i : IsIntegral ℤ t0 := (isIntegral_algebraMap_iff (algebraMap D.host.F D.host.E).injective).1
    (by rw [ht0]; exact hbi.mul hbc)
  refine ⟨⟨t0, ht0i⟩, ?_, ?_⟩
  · intro h
    have h1 : t0 = 0 := congrArg Subtype.val h
    rw [h1, map_zero] at ht0
    have hc0 : D.conjF (b : D.host.E) ≠ 0 := by
      intro hc; apply hb0
      have := congrArg D.conjF hc
      rwa [Formalism.L2.SG.Pf.LocalDenominators.conjF_invol, map_zero] at this
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

theorem coe_alg (s : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) s : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (s : D.host.F) :=
  rfl

theorem exists_den {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V) :
    ∃ d : 𝓞 D.host.F, d ≠ 0 ∧ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.ExistsBaseFieldIntegerDenominator.exists_den hΛ x

variable (Zd : LocDat D)

theorem bcP_mem_cof {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V) :
    {p : PlF D | baseChange₂ D p x ∉ lattice₂ D Zd.M p Λ}.Finite := by
  obtain ⟨d, hd, hdx⟩ := exists_den hΛ x
  have hI : Ideal.span {d} ≠ (0 : Ideal (𝓞 D.host.F)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hd
  refine (Ideal.finite_factors hI).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  by_contra hnd
  apply hp
  have := p.isPrime
  rw [Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hΛ]
  exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).2 ⟨d, hnd, hdx⟩

theorem scal_mem {p : PlF D} (hs : (Zd.M p).split = none)
    (hδ : Zd.δ p ∈ 𝒪[(D.s.atP p).Fp] ∧ (Zd.δ p)⁻¹ ∈ 𝒪[(D.s.atP p).Fp])
    (hu : (D.s.atP p).ιE (uP p : D.host.E) ∈ (D.s.atP p).O ∧ (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) ∈ (D.s.atP p).O)
    (b : Fin (D.R.rS + 1)) : TermLoc.sgnP' D p b * frFac Zd.δ p b ∈ (D.s.atP p).O := by
  have hs' : (D.s.atP p).split = none := by
    have hA := (Zd.agree p).2.2.2.2.2
    rw [hs] at hA
    cases h2 : (D.s.atP p).split with
    | none => rfl
    | some sg =>
      rw [h2] at hA
      exact (hA : False).elim
  refine Subring.mul_mem _ ?_ ?_
  · unfold TermLoc.sgnP'
    rw [hs']
    exact Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _
  · rw [Formalism.L2.SG.Pf.BBTie.bt_frFac_eq Zd p b]
    set w : (D.s.atP p).Ep := algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ *
      (D.s.atP p).ιE ((uP p : D.host.E)⁻¹) with hw
    have hwO : w ∈ (D.s.atP p).O :=
      Subring.mul_mem _ (Formalism.L2.SG.Pf.LocalDenominators.alg_mem_O (D.s.atP p) hδ.2) hu.2
    have hinv : (((Formalism.L2.SG.Pf.BBTie.bt_T_unit Zd p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = w := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [IsUnit.unit_spec]
      show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) * w = 1
      rw [hw]
      have hδ0 : Zd.δ p ≠ 0 := (Zd.agree p).2.1
      have hu0 := Formalism.L2.SG.Pf.BBTie.uP_ne (D := D) p
      calc algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p) * (D.s.atP p).ιE (uP p : D.host.E) *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p)⁻¹ * (D.s.atP p).ιE ((uP p : D.host.E)⁻¹))
          = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Zd.δ p * (Zd.δ p)⁻¹) *
            (D.s.atP p).ιE ((uP p : D.host.E) * (uP p : D.host.E)⁻¹) := by rw [map_mul, map_mul]; ring
        _ = 1 := by rw [mul_inv_cancel₀ hδ0, mul_inv_cancel₀ hu0, map_one, map_one, mul_one]
    rw [Units.val_pow_eq_pow_val, hinv]
    exact Subring.pow_mem _ hwO _

end CohIntPf

open CohIntPf

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem cohInt_holds : CohInt Zd u u' F0 what₂ := by
  intro hP γ Z F'₂ φ' _
  have hΛ : Submodule.IsLattice D.host.E γ.lam := (hP.2.1.1 γ.lam γ.mem).1.1
  have hgood := Formalism.L2.SG.Pf.LocModel.good_cofinite Zd.δ Zd.M Zd.agree ∅
  rw [Filter.eventually_cofinite] at hgood
  refine (hgood.union (Set.finite_iUnion fun b => bcP_mem_cof Zd hΛ (frame F'₂ b))).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists, not_not] at hn
  obtain ⟨hg, hb⟩ := hn
  apply hp
  intro b
  exact Formalism.L2.SG.Pf.LocalDenominators.smul_mem_localLattice Zd p (scal_mem Zd hg.1 hg.2.1 hg.2.2.1 b) (hb b)

theorem star_coherence_of_three (hDG : CohDG Zd u u' F0 what₂) (hLp : CohLp Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  star_coherence_of_four Zd (cohInt_holds Zd) hDG hLp hGood

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FramesMem
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Term

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem frames_mem (t : TauC Y u u') :
    (∀ b, (X.Fu u).fvec b ∈ t.lam) ∧ (∀ b, t.frame.fl.fvec b ∈ t.lam) := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hP := t.rep.2.2.2.2
  exact ⟨Formalism.L2.SG.NGCut.PtPf.frame_mem (lf D (X.Fu u)) hrow.2.1.2.2.1.1 hrow.2.2,
    Formalism.L2.SG.NGCut.PtPf.frame_mem t.frame hP.1.1 hP.2.2.2⟩

theorem yT_mem (t : TauC Y u u') : NormalVectorPairings.yT Y u u' t ∈ t.lam := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨h1, h2⟩ := frames_mem Y t
  exact yv_mem hrow.2.1.2.1 (Tu D u) (X.Fu u) t.frame.fl h1 h2

theorem yT'_mem (t : TauC Y u u') : NormalVectorPairings.yT' Y u u' t ∈ t.lam' := by
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨h1, h2⟩ := frames_mem Y t
  have hv : NormalVectorPairings.yv t.frame.fl (X.Fu u) ∈ t.lam := yv_mem hrow.2.1.2.1 (Tu D u') t.frame.fl (X.Fu u) h2 h1
  have hg : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  rw [← hg] at hv
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hv
  show t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)) ∈ t.lam'
  rw [← hwv]
  simpa using hw

theorem yT'_orth (t : TauC Y u u') : ∀ x ∈ (X.Fu u').X, brS (VS D) (NormalVectorPairings.yT' Y u u' t) x = 0 := by
  intro x hx
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hlx : t.lin x ∈ (t.frame.fl).X := by
    have := (CorankRelation.mem_Xsp_mapLF (γ := t.lin) hiso (lf D (X.Fu u')) (t.lin x)).2 (by simpa using hx)
    exact this
  have h := yv_orth_X t.frame.fl (X.Fu u) (t.lin x) hlx
  show (VS D).hT x (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u))) = 0
  have e := hiso x (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)))
  rw [LinearEquiv.apply_symm_apply] at e
  rw [← e]
  exact h

theorem yT'_self (t : TauC Y u u') :
    brS (VS D) (NormalVectorPairings.yT' Y u u' t) (NormalVectorPairings.yT' Y u u' t) =
      brS (VS D) (NormalVectorPairings.yv t.frame.fl (X.Fu u)) (NormalVectorPairings.yv t.frame.fl (X.Fu u)) := by
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  show (VS D).hT (t.lin.symm _) (t.lin.symm _) = _
  have e := hiso (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u))) (t.lin.symm (NormalVectorPairings.yv t.frame.fl (X.Fu u)))
  rw [LinearEquiv.apply_symm_apply] at e
  rw [← e]
  rfl

theorem lam_eq {t0 t : TauC Y u u'} (h : NormalVectorPairings.RelC Y u u' t0 t) : t.lam = t0.lam ∧ t.lam' = t0.lam' :=
  ⟨congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) h.1,
    congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) h.1⟩

end Term

theorem nmlInt_of
    (hLine : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t0 t : TauC Y u u'),
      Gt t0 ≠ 0 → Gt t ≠ 0 → NormalVectorPairings.RelC Y u u' t0 t → t.G = t0.G → 3 ≤ Tu D u → 3 ≤ Tu D u' →
        NormalVectorPairings.yT Y u u' t - NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 ∈ (X.Fu u).X ∧
        NormalVectorPairings.yT' Y u u' t - NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 ∈ (X.Fu u').X) :
    NormalVectorPairings.NmlInt := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hctx γ hNG t0 hGt0 hpt0 => ?_⟩
  have hT1 : (3 : ℕ) ≤ Tu D u := hctx.2.1.2.2.2.1
  have hT2 : (3 : ℕ) ≤ Tu D u' := hctx.2.1.2.2.2.2.1
  have hG := NormalVectorPairings.gval_occ Y t0 (by rw [hpt0]; exact hNG)
  rw [hpt0] at hG
  have hGeq : ∀ t : TauC Y u u', ptPN t = γ → t.G = t0.G := by
    intro t hpt
    have h1 := NormalVectorPairings.gval_occ Y t (by rw [hpt]; exact hNG)
    rw [hpt] at h1
    rw [Formalism.L2.SG.Pf.SatGram.gterm_G Y t, Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, h1, hG]
  have hGne := NormalVectorPairings.GPt_ne_of_NGPt _ _ hNG
  have hTne : ((Tu D u : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (show Tu D u ≠ 0 by omega)
  have hTne' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast (show Tu D u' ≠ 0 by omega)

  have hrow := (Y.rowsOK u).1 t0.lam t0.mem
  have hun := hrow.2.1.2.1
  have hy0 := yT_mem Y t0
  obtain ⟨c0, hc0⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun hy0 hy0
  have hc0' : (c0 : D.host.E) = brS (VS D) (NormalVectorPairings.yT Y u u' t0) (NormalVectorPairings.yT Y u u' t0) := hc0
  have hval : brS (VS D) (NormalVectorPairings.yT Y u u' t0) (NormalVectorPairings.yT Y u u' t0) =
      ((Tu D u : ℕ) : D.host.E) * GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    show brS (VS D) (NormalVectorPairings.yv (X.Fu u) t0.frame.fl) (NormalVectorPairings.yv (X.Fu u) t0.frame.fl) = _
    rw [NormalVectorPairings.brS_yv_yv _ _ (by simp), ← hG]
    rfl
  have hc0ne : c0 ≠ 0 := by
    intro h
    have : (c0 : D.host.E) = 0 := by rw [h]; rfl
    rw [hc0', hval] at this
    exact mul_ne_zero hTne hGne this

  have hrow' := (Y.rowsOK u').1 t0.lam' t0.mem'
  have hun' := hrow'.2.1.2.1
  have hy1 := yT'_mem Y t0
  obtain ⟨c1, hc1⟩ := Formalism.MainNotions.LatticeGluingRadicals.d_Lam_int hun' hy1 hy1
  have hc1' : (c1 : D.host.E) = brS (VS D) (NormalVectorPairings.yT' Y u u' t0) (NormalVectorPairings.yT' Y u u' t0) := hc1
  have hval' : brS (VS D) (NormalVectorPairings.yT' Y u u' t0) (NormalVectorPairings.yT' Y u u' t0) =
      ((Tu D u' : ℕ) : D.host.E) * GPt ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    rw [yT'_self, NormalVectorPairings.brS_yv_yv _ _ (by simp), NormalVectorPairings.Gflag_swap, ← hG]
  have hc1ne : c1 ≠ 0 := by
    intro h
    have : (c1 : D.host.E) = 0 := by rw [h]; rfl
    rw [hc1', hval'] at this
    exact mul_ne_zero hTne' hGne this
  refine ⟨Jfrac t0.lam (X.Fu u).X (NormalVectorPairings.yT Y u u' t0) hun (X_iso (X.Fu u)) (yv_orth_X (X.Fu u) t0.frame.fl)
      hy0 c0 hc0' hc0ne,
    Jfrac t0.lam' (X.Fu u').X (NormalVectorPairings.yT' Y u u' t0) hun' (X_iso (X.Fu u')) (yT'_orth Y t0) hy1 c1 hc1' hc1ne,
    Jfrac_ne_zero _ _ _ _ _ _ _ _ _ _, Jfrac_ne_zero _ _ _ _ _ _ _ _ _ _, fun t hGt hpt hrel => ⟨?_, ?_⟩, ?_, ?_⟩
  · obtain ⟨hl1, -⟩ := hLine D X Y u u' t0 t hGt0 hGt hrel (hGeq t hpt) hT1 hT2
    have hyt : NormalVectorPairings.yT Y u u' t ∈ t0.lam := (lam_eq Y hrel).1 ▸ yT_mem Y t
    show NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 ∈ t0.lam ⊔ (X.Fu u).X.restrictScalars (𝓞 D.host.E)
    have e : NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0 =
        NormalVectorPairings.yT Y u u' t - (NormalVectorPairings.yT Y u u' t - NormalVectorPairings.coefA Y u u' t0 t • NormalVectorPairings.yT Y u u' t0) := by
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hyt) (Submodule.mem_sup_right hl1)
  · obtain ⟨-, hl2⟩ := hLine D X Y u u' t0 t hGt0 hGt hrel (hGeq t hpt) hT1 hT2
    have hyt : NormalVectorPairings.yT' Y u u' t ∈ t0.lam' := (lam_eq Y hrel).2 ▸ yT'_mem Y t
    show NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 ∈ t0.lam' ⊔ (X.Fu u').X.restrictScalars (𝓞 D.host.E)
    have e : NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0 =
        NormalVectorPairings.yT' Y u u' t - (NormalVectorPairings.yT' Y u u' t - NormalVectorPairings.coefA' Y u u' t0 t • NormalVectorPairings.yT' Y u u' t0) := by
      abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hyt) (Submodule.mem_sup_right hl2)
  · have hb := norm_bound t0.lam (X.Fu u).X (NormalVectorPairings.yT Y u u' t0) hun (X_iso (X.Fu u))
      (yv_orth_X (X.Fu u) t0.frame.fl) hy0 c0 hc0' hc0ne
    rw [hc0', hval, abs_norm_TG] at hb
    unfold NormalInvariants.PG
    calc (1 : ℝ) ≤ _ := hb
      _ = _ := by ring
  · have hb := norm_bound t0.lam' (X.Fu u').X (NormalVectorPairings.yT' Y u u' t0) hun' (X_iso (X.Fu u'))
      (yT'_orth Y t0) hy1 c1 hc1' hc1ne
    rw [hc1', hval', abs_norm_TG] at hb
    unfold NormalInvariants.PG
    calc (1 : ℝ) ≤ _ := hb
      _ = _ := by ring

end Formalism.L2.SG.NGCut.NormalIntegrality
end
end

