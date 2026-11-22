import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelIntegralTwist
section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence
open scoped Matrix

theorem core (I : AutInst) (g : ℕ) {r : ℕ} (e0 : Fin r → VA I) (z0 : VA I) (hz0 : z0 ∈ I.Lf)
    (hzz : ZMod' I g (hA I z0 z0 + 1)) (hze : ∀ a, ZMod' I g (hA I (e0 a) z0))
    (x : I.Gf) (hxK : x ∈ I.Kset) (hxz : InMod I g (Set.range e0) ((I.fmat x - 1) *ᵥ z0))
    (v v' : VA I) (hv : InAt I g g (v - z0)) (hv' : InAt I g g (v' - z0))
    (ε c c₂ : I.E ⊗[I.F] Af I.F) (hε : ε ∈ IntAf I.F I.E) (hc : c ∈ IntAf I.F I.E) (hc₂ : c₂ ∈ IntAf I.F I.E)
    (hyp : ε • (c • (I.fmat x *ᵥ v')) = ε • (c₂ • v)) :
    ∃ N : ℕ, N.Coprime g ∧ ZMod' I g (ε * (c - c₂) * (N : I.E ⊗[I.F] Af I.F)) := by
  obtain ⟨n, hn, hnv⟩ := hv
  obtain ⟨n', hn', hnv'⟩ := hv'
  refine ⟨n * n', Nat.Coprime.mul hn hn', ?_⟩

  have hQ : Mo I g (Set.range e0) ≤ Qs I g z0 := by
    refine sup_le (Submodule.span_le.2 ?_) (mL_Qs I g hz0)
    rintro _ ⟨a, rfl⟩
    show ZMod' I g (hA I z0 (e0 a))
    rw [hA_symm]; exact Z_sig I g (hze a)
  have hmL : mL I g ≤ Qs I g z0 := mL_Qs I g hz0
  have hxmL : ∀ w ∈ mL I g, I.fmat x *ᵥ w ∈ mL I g := fun w hw =>
    pres I hxK g ∅ (mL I g) (by simp) (by simp) le_rfl w (mL_Mo I hw)
  have hNint : ∀ m : ℕ, ((m : I.E ⊗[I.F] Af I.F)) ∈ IntAf I.F I.E := fun m => natCast_mem _ m

  have hA1 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ v') + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : I.fmat x *ᵥ v' = z0 + (I.fmat x - 1) *ᵥ z0 + I.fmat x *ᵥ (v' - z0) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
      abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ (v' - z0)) =
        (n : I.E ⊗[I.F] Af I.F) * hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0))) := by
      rw [Matrix.mulVec_smul, hA_smul_right, Nat.cast_mul]; ring
    have h2 : ZMod' I g (hA I z0 ((I.fmat x - 1) *ᵥ z0)) := hQ hxz
    have h3 : ZMod' I g (hA I z0 (I.fmat x *ᵥ ((n' : I.E ⊗[I.F] Af I.F) • (v' - z0)))) := hmL (hxmL _ hnv')
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g (Z_add I g h1 (Z_smul I g (hNint (n * n')) h2)) (Z_smul I g (hNint n) h3)
    rw [e, hA_add_right, hA_add_right]
    convert this using 1
    rw [← e2]; ring
  have hA2 : ZMod' I g (((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 v + ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) := by
    have e : v = z0 + (v - z0) := by abel
    have e2 : ((n * n' : ℕ) : I.E ⊗[I.F] Af I.F) * hA I z0 (v - z0) =
        (n' : I.E ⊗[I.F] Af I.F) * hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0)) := by
      rw [hA_smul_right, Nat.cast_mul]; ring
    have h3 : ZMod' I g (hA I z0 ((n : I.E ⊗[I.F] Af I.F) • (v - z0))) := hmL hnv
    have h1 := Z_smul I g (hNint (n * n')) hzz
    have := Z_add I g h1 (Z_smul I g (hNint n') h3)
    rw [e, hA_add_right]
    convert this using 1
    rw [← e2]; ring

  have key : ε * (c * hA I z0 (I.fmat x *ᵥ v')) = ε * (c₂ * hA I z0 v) := by
    have := congrArg (fun w => hA I z0 w) hyp
    simp only [hA_smul_right] at this
    exact this
  have := Z_sub I g (Z_smul I g (mul_mem hε hc) hA1) (Z_smul I g (mul_mem hε hc₂) hA2)
  convert this using 1
  linear_combination (-((n * n' : ℕ) : I.E ⊗[I.F] Af I.F)) * key

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting

theorem res_eq {D : D7} (PP : Formalism.L2.DIV.Pl D.host.E) (g : ℕ) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (N : ℕ) (hN : N.Coprime g)
    (hZ : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (ε * (c - c₂) * (N : Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨t, ht, he⟩ := hZ
  have hs : (⟨ε, hε⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * (⟨c, hc⟩ - ⟨c₂, hc₂⟩) * (N : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (g : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨t, ht⟩ := Subtype.ext (by
    push_cast
    exact he)
  have hr := congrArg (Formalism.L2.DIV.resS D.host.F PP) hs
  simp only [map_mul, map_sub, map_natCast, hε1, one_mul] at hr
  have hg0 : ((g : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    show ((g : 𝓞 D.host.E) : 𝓞 D.host.E ⧸ PP.asIdeal) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 hg
  have hN0 : ((N : ℕ) : Formalism.L2.DIV.kP PP) ≠ 0 := by
    intro h0
    have hNm : ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h0
    have hco : IsCoprime ((N : ℤ) : 𝓞 D.host.E) ((g : ℤ) : 𝓞 D.host.E) :=
      (Nat.isCoprime_iff_coprime.2 hN).map (Int.castRingHom (𝓞 D.host.E))
    obtain ⟨a, b, hab⟩ := hco
    push_cast at hab
    apply PP.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hNm) (Ideal.mul_mem_left _ _ hg)
  rw [hg0, zero_mul] at hr
  exact sub_eq_zero.1 ((mul_eq_zero.1 hr).resolve_right hN0)

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Matrix

theorem finE_inv_val {D : D7} (y : GA D (D.sp.Y 0)) :
    ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val =
      (Formalism.L2.SG.InstExistsPf.instOf D).fmat (((Formalism.IndefR.RationalEmbedding.iota D) y).2)⁻¹ :=
  (congrArg Units.val (map_inv (Formalism.IndefR.Lev.finE (Yc D 0)) (show GA D (Yc D 0) from y)).symm).trans
    ((GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) (y⁻¹ : GA D (D.sp.Y 0))).symm.trans
      (congrArg (fun p : (Formalism.IndefR.RationalEmbedding.inst D).GA => (Formalism.L2.SG.InstExistsPf.instOf D).fmat p.2) (map_inv (Formalism.IndefR.RationalEmbedding.iota D) y)))

theorem core_res {D : D7} {r : ℕ} (e0 : Fin r → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (g : ℕ) (hz0 : z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf)
    (hzz : ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1)) (hze : ∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) g (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0))
    (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hxK : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) (hxz : InMod (Formalism.L2.SG.InstExistsPf.instOf D) g (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0))
    (v v' : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hv : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v - z0)) (hv' : InAt (Formalism.L2.SG.InstExistsPf.instOf D) g g (v' - z0))
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((g : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε c c₂ : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (w w' : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D)
    (hM : M = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x) (hw : w = v) (hw' : w' = v')
    (hyp : ε • (c • (M *ᵥ w')) = ε • (c₂ • w)) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  subst hM hw hw'
  obtain ⟨N, hN, hZ⟩ := core (Formalism.L2.SG.InstExistsPf.instOf D) g e0 z0 hz0 hzz hze x hxK hxz w w' hv hv' ε c c₂ hε hc hc₂ hyp
  exact res_eq PP g hg ε c c₂ hε hε1 hc hc₂ N hN hZ

set_option maxHeartbeats 400000 in

theorem frame_facts {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = (Formalism.L2.SG.InstExistsPf.instOf D)) (hId : IdE X) :
    ∃ (e0 : Fin D.R.rS → VA (Formalism.L2.SG.InstExistsPf.instOf D)) (z0 : VA (Formalism.L2.SG.InstExistsPf.instOf D)), z0 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ∧ ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) z0 z0 + 1) ∧
      (∀ a, ZMod' (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (hA (Formalism.L2.SG.InstExistsPf.instOf D) (e0 a) z0)) ∧
      (∀ κ ∈ rowJ X h, ∃ x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf, ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 = x ∧ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset ∧
        InMod (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (Set.range e0) (((Formalism.L2.SG.InstExistsPf.instOf D).fmat x - 1) *ᵥ z0)) ∧
      ∀ u : D.what₂.Word, ∃ (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)),
        ((Formalism.IndefR.RationalEmbedding.iota D) ((iotaX X h).symm (1, X.xu u))).2 = x ∧
        (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r)))) = z ∧
        InAt (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) (D.host.g 0 * D.host.g 1) ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z - z0) := by
  have hi : ∀ u, (iotaX X h) ((iotaX X h).symm (1, X.xu u)) = (1, X.xu u) := fun u => (iotaX X h).apply_symm_apply _
  obtain ⟨⟨I⟩, ιE, ιE_conj, ιE_F, bas, J_eq, L_eq, pl, φ_eq, n_eq, eps_eq, lam_eq, ds, low, g_eq, g0_eq, Rph,
    Rph_spec, eX, fY, ee, ff, ef, Lb, Lb_perp, Lam_split, zu, zu_norm, zu_orth, zu_Lb, Fu, Fu_e, flagZVector, Fu_fixed,
    psiEf, psiEf_add, psiEf_int, psiEf_rat, e0, f0, z0, bw, bwd, ew, vectorsInLattice, basisApprox, gramIntegral, formsAtZero, weightVectorsIntegral, ew_idem,
    ew_orth, ew_int, ew_full, bw_w, bwd_w, bw_dual, latticeSpan, e_eq, xu, xu_fix, xu_z, xu_one, xu_K⟩ := X
  dsimp only at h
  subst h
  dsimp only at g_eq
  subst g_eq
  have hs : ∀ y : D.host.E, ιE.symm y = y := fun y => by
    have := eq_of_heq (hId (ιE.symm y))
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨e0, z0, vectorsInLattice.2.1, formsAtZero.1, fun a => (formsAtZero.2 a).1, fun κ hκ => ?_, fun u => ?_⟩
  · have hk : ((Formalism.IndefR.RationalEmbedding.iota D) κ).2 ∈ K2set (Formalism.L2.SG.InstExistsPf.instOf D) (D.host.g 0 * D.host.g 1) e0 z0 bw := hκ.2
    exact ⟨_, rfl, hk.1, hk.2.2.1⟩
  · refine ⟨xu u, incl (Formalism.L2.SG.InstExistsPf.instOf D) (crdOf (Formalism.L2.SG.InstExistsPf.instOf D) ιE bas (zu u)), congrArg Prod.snd (hi u), ?_, xu_z u⟩
    funext r
    show algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE (ιE.symm (bas.repr (zu u) r))) =
      algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (ιE.symm (bas.repr (zu u) r))
    rw [RingEquiv.apply_symm_apply, hs]

theorem inv_mulVec_eq {D : D7} (y : GA D (D.sp.Y 0)) (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (hx : ((Formalism.IndefR.RationalEmbedding.iota D) y).2 = x)
    (w : Fin (Yc D 0).rank → Formalism.IndefR.Lev.EAf D) (z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) (hz : w = z) :
    Matrix.mulVec ((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from y))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val w =
      ((Formalism.L2.SG.InstExistsPf.instOf D).fmat x⁻¹ *ᵥ z : VA (Formalism.L2.SG.InstExistsPf.instOf D)) := by
  subst hx hz
  exact congrArg (fun M : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D) => Matrix.mulVec M w) (finE_inv_val y)

set_option maxHeartbeats 400000 in

theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X)
    (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ rowJ X h)
    (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (PP : Formalism.L2.DIV.Pl D.host.E) (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (ε : Formalism.IndefR.Lev.EAf D) (hε : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hε1 : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hε⟩ = 1)
    (hE : ε • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u' (Fin.cast (rank_eq X h) r)))))) = ε • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX X h).symm (1, X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (X.ιE (X.zR u (Fin.cast (rank_eq X h) r))))))) :
    Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  obtain ⟨e0, z0, hz0, hzz, hze, hK, hu⟩ := frame_facts X h hId
  obtain ⟨x, hx, hxK, hxz⟩ := hK κ hκ
  obtain ⟨y, z, hy, hz, hv⟩ := hu u
  obtain ⟨y', z', hy', hz', hv'⟩ := hu u'
  have e1 : (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val = (Formalism.L2.SG.InstExistsPf.instOf D).fmat x :=
    (GlobalTheory.SeeConjGroup.fmat_iota_eq_finE (D := D) κ).symm.trans (congrArg (Formalism.L2.SG.InstExistsPf.instOf D).fmat hx)
  have e2 := inv_mulVec_eq _ y hy _ z hz
  have e3 := inv_mulVec_eq _ y' hy' _ z' hz'
  exact core_res e0 z0 _ hz0 hzz hze x hxK hxz _ _ hv hv' PP hg ε c c₂ hε hε1 hc hc₂ _ _ _ e1 e2 e3 hE

end GlobalTheory.CongFlag

namespace GlobalTheory.CongFlag

theorem resS_eq_of_flag : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  intro D L hT Gi Gl Kc Yd cX ex W hP _ u u' κ hκ c c₂ hc hc₂ PP hPP hEq
  have lev : (pk W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev
  have hPP' : PP ∈ (pk W).Pg := hPP
  have hg := (GlobalTheory.SeeConjRead.places_over_g (pk W) lev).1 PP hPP'
  obtain ⟨ei, hei⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (GlobalTheory.TypePlaces.not_isConjPl _ _ lev.Pg PP hPP' PP hPP')
  obtain ⟨hε, hε1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D ei PP hei
  exact finiteRing_sq_sub_mul_sq_eq_of_card W.S.X W.Q.instEq hP.bot.idE u u' κ hκ c c₂ hc hc₂ PP hg (toEAf D ei) hε hε1 (hEq ei hei)

end GlobalTheory.CongFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat : ∀ D : D7, SchSchwartz D := by
  first | exact @GlobalTheory.SchSchwartzAll.schSchwartz | exact GlobalTheory.SchSchwartzAll.schSchwartz | (intros; apply GlobalTheory.SchSchwartzAll.schSchwartz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfAdelicHomPairActionLevelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatHalf_adelicHomPairAction_levels : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ (κ : A.U i α) (κ' : A.U (i + 1) γ), IsSBHalf A.e (stdHom _ _) (fun z => Φ (actO _ _ κ.1⁻¹ κ'.1⁻¹ z)) := by
  first | exact @GlobalTheory.SBMove.isSBHalf_actO_lev | exact GlobalTheory.SBMove.isSBHalf_actO_lev | (intros; apply GlobalTheory.SBMove.isSBHalf_actO_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalFactorEqIteratedChainDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MovedDat

open GlobalTheory.LocMod.StepVec

theorem rank_first_loc {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) : D.R.k + (G.s + 1) = D.R.r := by
  have := G.hs
  unfold Ranks.r
  omega

theorem rdAt_iff {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) {w : Formalism.L2.DIV.Pl D.host.E} {π' : Formalism.IndefR.Datum.EAf D →+* G.k}
    (hπ : ∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G.q.pr a)
    (hred : GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP w))
    (M : Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hM : g.val.submatrix (firstOrd (rank_first_loc G)) (firstOrd (rank_first_loc G)) = M.map (Formalism.L2.DIV.resS D.host.F w)) :
    RdAt G w x g ↔ MaxM ((x : GL _ G.k).val - M.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) := by
  have key : ∀ a b (z : 𝓞 D.host.E),
      Ideal.Quotient.mk w.asIdeal z = g.val (firstOrd (rank_first_loc G) a) (firstOrd (rank_first_loc G) b) →
      valuation G.k ((π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (M a b) - (ofSplit G.q).pr (z : D.host.E)) < 1 :=
    fun a b z hz => by
      have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
          (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
      rw [← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
      exact (hz.trans (congrFun (congrFun hM a) b)).symm
  constructor
  · intro h a b
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (firstOrd (rank_first_loc G) a) (firstOrd (rank_first_loc G) b))
    have := Valuation.map_sub_lt _ (h a b _ _ (firstOrd_val _ a) (firstOrd_val _ b) z hz) (key a b z hz)
    rwa [sub_sub_sub_cancel_right] at this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = firstOrd (rank_first_loc G) a := Fin.ext (ha.trans (firstOrd_val _ a).symm)
    obtain rfl : b' = firstOrd (rank_first_loc G) b := Fin.ext (hb.trans (firstOrd_val _ b).symm)
    have := Valuation.map_add_lt _ (h a b) (key a b z hz)
    rwa [Matrix.sub_apply, Matrix.map_apply, sub_add_sub_cancel] at this

theorem card_of_ix {κ l r t j a : ℕ} (h : κ + l = r) (e : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) : a = r + j * t := by
  have e' : (Fin κ ⊕ Fin l) ⊕ (Fin j × Fin t) ≃ Fin a := e
  have := Fintype.card_congr e'
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at this
  rw [← this, h]

theorem locF_eq_iterPhi : ∀ (D : D7) (c : Comm D) (v : VCom c) (G0 : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : Formalism.IndefR.Datum.EAf D →+* G0.k), (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (j : ℕ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (χ (c + 1) PP) (G0.S.μ (c + 1))) → ∀ (a b : ℕ) (hr : D.R.r ≤ a) (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin a) (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), GlobalTheory.LocMod.StepVec.locF D.R.t j hr (GlobalTheory.MovedDat.RdAt G0 PP) (fun x => G0.S.P.lam x) (fun c => χ c PP) (N.map (Formalism.L2.DIV.resS D.host.F PP)) = G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) := by
  intro D c v G0 PP π' hπ hred χ j hχ a b hr ea eb ha hb N
  exact locF_eq (GlobalTheory.FunObj.TieLev.iterPhi_read _ _ _ _ _ hred _ _ _ _ _ _ (firstOrd (rank_first_loc G0)) ea eb
    (isIx_of_isOrd _ (card_of_ix (rank_first_loc G0) ea) ha) (isIx_of_isOrd _ (card_of_ix (rank_first_loc G0) eb) hb) hr _ _ _
    (fun i => χ i PP) hχ _ (rdAt_iff G0 hπ hred) N)

end GlobalTheory.MovedDat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLineStableLatticeSplitsAlongWittSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.SeeSaw.SplitLat

variable {D : D7}

theorem pair_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_i₀ {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * (d.i₀ *ᵥ y) j = ∑ i, ∑ j, star ((d.q0 *ᵥ x) i) * S₀.gram i j * y j := by
  have hG : S.gram * d.i₀ = d.q0ᴴ * S₀.gram := by
    rw [gram_eq d]
    simp only [Matrix.add_mul, Matrix.mul_assoc, qX_i₀, qY_i₀, wittDecomposition_coreProj_mul_core_eq_one, Matrix.mul_zero, Matrix.mul_one, add_zero,
      zero_add]
  rw [pair_eq_dot, pair_eq_dot, Matrix.mulVec_mulVec, hG, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.star_mulVec]

theorem mulVec_eq_sum_cols {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    M *ᵥ w = ∑ i, fun r => w i * M r i := by
  funext r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem colProj_mulVec' {S : HSp D} {ρ m : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E)
    (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) (x : Fin m → D.host.E) :
    colProj q f i *ᵥ x = fun r => (q *ᵥ x) i * f r i := by
  funext k
  simp only [colProj, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem selfDual_core_monoAt (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (hL : IsSelfDualC S L)
    (hcol : ∀ y ∈ L, ∀ i, (fun r => (d.qX *ᵥ y) i * d.e r i) ∈ L ∧ (fun r => (d.qY *ᵥ y) i * d.e' r i) ∈ L) :
    IsSelfDualC S₀ (coreLat d L) ∧ ∀ v : GlobalTheory.FinPl.Pl D, MonoAt d L (coreLat d L) v := by

  have hcore : ∀ y ∈ L, d.q0 *ᵥ y ∈ coreLat d L := by
    intro y hy
    rw [mem_coreLat]
    have hdec : y = d.e *ᵥ (d.qX *ᵥ y) + d.i₀ *ᵥ (d.q0 *ᵥ y) + d.e' *ᵥ (d.qY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        d.sum_eq_one_rat, Matrix.one_mulVec]
    have hX : d.e *ᵥ (d.qX *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).1
    have hY : d.e' *ᵥ (d.qY *ᵥ y) ∈ L := by
      rw [mulVec_eq_sum_cols]; exact sum_mem fun i _ => (hcol y hy i).2
    have key : ∀ a b c z : Fin S.rank → D.host.E, z = a + b + c → b = z - a - c := by
      intro a b c z hz; rw [hz]; abel
    have h : d.i₀ *ᵥ (d.q0 *ᵥ y) = y - d.e *ᵥ (d.qX *ᵥ y) - d.e' *ᵥ (d.qY *ᵥ y) := key _ _ _ _ hdec
    rw [h]
    exact sub_mem (sub_mem hy hX) hY
  have hinj : Function.Injective ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) := by
    intro x x' hxx
    have h := congrArg (fun z => d.q0 *ᵥ z) hxx
    simpa only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one,
      Matrix.one_mulVec] using h
  refine ⟨⟨⟨?_, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩, fun v => ?_⟩
  ·
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hLfg : L.FG := hL.1.fg
    haveI : IsNoetherian (𝓞 D.host.E) L := isNoetherian_of_fg_of_noetherian L hLfg
    have hle : (coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ≤ L :=
      Submodule.map_comap_le _ _
    have h1 : (((coreLat d L).map ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))).comap L.subtype).FG :=
      IsNoetherian.noetherian _
    have h2 := h1.map L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  ·
    rw [eq_top_iff]
    intro x _
    have hx : d.i₀ *ᵥ x ∈ Submodule.span D.host.E (L : Set (Fin S.rank → D.host.E)) := by
      rw [hL.1.span_eq_top]; exact Submodule.mem_top
    have hm := Submodule.mem_map_of_mem (f := Matrix.mulVecLin d.q0) hx
    rw [Submodule.map_span, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨z, hz, rfl⟩
    exact hcore z hz
  ·
    obtain ⟨b, hb⟩ := (hL.2 (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
    refine ⟨b, ?_⟩
    rw [hb, pair_i₀, Matrix.mulVec_mulVec, wittDecomposition_coreProj_mul_core_eq_one, Matrix.one_mulVec]
  ·
    rw [mem_coreLat]
    refine (hL.2 (d.i₀ *ᵥ y)).2 fun x hx => ?_
    obtain ⟨b, hb⟩ := h (d.q0 *ᵥ x) (hcore x hx)
    exact ⟨b, hb.trans (pair_i₀ d x y).symm⟩
  ·
    have hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).1
    have hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L := fun i x hx => by
      rw [colProj_mulVec']; exact (hcol x hx i).2
    intro y
    constructor
    · intro hy
      refine ⟨fun i => ?_, fun i => ?_, ?_⟩
      · change colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hX i) _ hy
      · change colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
        rw [colMul_rat]
        exact rat_mulVec_mem_latV _ (hY i) _ hy
      · exact rat_mulVec_mem_latV d.q0 hcore _ hy
    · rintro ⟨h1, h3, h2⟩
      have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
          d.sum_eq_one, Matrix.one_mulVec]
      rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
      refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
      exact rat_mulVec_mem_latV d.i₀ (fun x hx => hx) _ h2

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceChartParahoricLevelStabiliserHeight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChartTwist

theorem chart_dict : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → v = PP.under (𝓞 D.host.F) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal ∧ (∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl) ∧ (∀ k < D.R.m, ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, ((∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chS (k + 1) x)) ∨ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chT (k + 1) x))) → LiftsChar φ PP μ (w.ξ PP)) ∧ ∀ ι, IsChart s j φ ι → (∃ e : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) ∧ (∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _) ∧ ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y)) ∧ (∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) _ _) ∧ ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  intro D c w hw j hj s hs PP hPP v φ hφ
  have hpl := GlobalTheory.T.split_projection_under_eq_residue_card_eq_absNorm D v φ PP hφ
  refine ⟨hpl.1, hpl.2, fun ξl h => GlobalTheory.T.tame_lift_residue_character_isTame_not_unramified D v φ PP (w.ξ PP) hφ (hw.ne PP hPP) ξl h, ?_, ?_⟩
  · intro k hk μ hμ
    have hres := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hw.com k hk
    have hPg : PP ∈ c.Pg := by
      classical
      rw [hw.union]; exact Finset.mem_union.2 (Or.inr hPP)
    have hq : (c.chi (k + 1) PP)⁻¹ = w.ξ PP := by rw [hw.chiQ (k + 1) PP hPP, inv_inv]
    rcases hμ with hμ | hμ
    · exact GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ (hq ▸ (hres.1 PP hPg).1) v φ hφ μ hμ
    · exact GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ (hq ▸ (hres.1 PP hPg).2) v φ hφ μ hμ
  · intro ι hι
    have hfl := hs.choose_spec.2
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_topological_iso_parahoric_chart_split_place D s j v φ ι hfl.selfDual hfl.frame hι
    refine ⟨⟨e, he, GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer D s j v φ ι hfl.selfDual hfl.frame hι e he, GlobalTheory.T.doublingHeight_splitPlaceChart_biInvariant_torus_value D s j v φ ι hfl.selfDual hfl.frame hι e he⟩,
      GlobalTheory.T.twisted_chain_chart_parahoric_eq_level D c w hw j hj s hs PP hPP v φ hφ ι hι, ?_⟩
    intro ξl hξ y hy d hd
    exact GlobalTheory.T.level_character_on_parahoric_chart_image D c w hw j hj s hs PP hPP v φ hφ ι hι ξl hξ y hy d hd

end GlobalTheory.ChartTwist
end

