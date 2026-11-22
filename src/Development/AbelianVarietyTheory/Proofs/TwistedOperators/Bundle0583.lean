import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0470
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0407
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0564
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceHermitianFormAdjoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjAdj
open GlobalTheory.SeeConjChar Matrix
variable {D : D7}

theorem hform_unitary {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) {M : GL n A} (hM : M ∈ Formalism.UG.UJ σ J) (u v : n → A) :
    Formalism.UG.hform σ J (M.val *ᵥ u) (M.val *ᵥ v) = Formalism.UG.hform σ J u v := by
  have e2 : ∀ a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
    intro a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : σ ∘ (M.val *ᵥ u) = (σ ∘ u) ᵥ* Formalism.UG.cT σ M.val := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  have hM' : Formalism.UG.cT σ M.val * J * M.val = J := hM
  rw [e2, e2, e3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM']

theorem eq_of_kill {R : Type} [CommRing R] (PP : Pl D.host.E) (f : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R)
    (hf : ∀ p ∈ PP.asIdeal, f (oToS D.host.F D.host.E p) = 0) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (b : 𝓞 D.host.E) (hb : s - oToS D.host.F D.host.E b ∈ idS D.host.F PP.asIdeal) :
    f s = f (oToS D.host.F D.host.E b) := by
  have hle : idS D.host.F PP.asIdeal ≤ RingHom.ker f := by
    unfold idS
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    exact hf p hp
  have := hle hb
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  exact this

theorem ext_oToS {R : Type} [CommRing R] (PP : Pl D.host.E) (f g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R)
    (hfg : ∀ a, f (oToS D.host.F D.host.E a) = g (oToS D.host.F D.host.E a))
    (hg : ∀ p ∈ PP.asIdeal, g (oToS D.host.F D.host.E p) = 0) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    f s = g s := by
  obtain ⟨bq, hb⟩ := cmpS_surj (F := D.host.F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ s)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
  change Ideal.Quotient.mk _ (oToS D.host.F D.host.E b) = _ at hb
  have hb' : s - oToS D.host.F D.host.E b ∈ idS D.host.F PP.asIdeal := by
    rw [← Ideal.Quotient.eq]
    exact hb.symm
  have h1 := eq_of_kill PP f (fun p hp => (hfg p).trans (hg p hp)) s b hb'
  have h2 := eq_of_kill PP g hg s b hb'
  rw [h1, h2, hfg]

noncomputable def cjS (D : D7) : Formalism.L2.Herm.intAf D.host.F D.host.E →+* Formalism.L2.Herm.intAf D.host.F D.host.E :=
  (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D).restrict (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun _ h => GlobalTheory.AdIsom.cjA_mem h)

theorem cjS_oToS (a : 𝓞 D.host.E) :
    cjS D (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (GlobalTheory.IdemSupport.cO D a) := Subtype.ext rfl

theorem resT_cjA (PP : Pl D.host.E) (z : EAf D) :
    resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z) = conjRes PP (resT PP z) := by
  by_cases hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
  · have hz' : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.AdIsom.cjA_mem hz
    rw [resT, dif_pos hz', resT, dif_pos hz]
    let f1 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
      (resS D.host.F (GlobalTheory.IdemSupport.cP PP)).comp (cjS D)
    let f2 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
      (conjRes PP).toRingHom.comp (resS D.host.F PP)
    have hO : ∀ a : 𝓞 D.host.E, f1 (oToS D.host.F D.host.E a) = f2 (oToS D.host.F D.host.E a) := by
      intro a
      show resS D.host.F (GlobalTheory.IdemSupport.cP PP) (cjS D (oToS D.host.F D.host.E a)) =
        conjRes PP (resS D.host.F PP (oToS D.host.F D.host.E a))
      rw [cjS_oToS, resS_oToS, resS_oToS]
      exact (Ideal.quotientEquiv_mk _ _ _ _ _).symm
    have hg : ∀ p ∈ PP.asIdeal, f2 (oToS D.host.F D.host.E p) = 0 := by
      intro p hp
      show conjRes PP (resS D.host.F PP (oToS D.host.F D.host.E p)) = 0
      rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    have hfin := ext_oToS PP f1 f2 hO hg ⟨z, hz⟩
    have e : (⟨GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z, hz'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = cjS D ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact hfin
  · have hz' : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z ∉ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun h => hz (GlobalTheory.AdIsom.cjA_mem_iff.1 h)
    rw [resT, dif_neg hz', resT, dif_neg hz, map_zero]

theorem resCP_adjoint : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) (κ : GA D (Yc D 0)) (x y : Fin (Yc D 0).rank → EAf D), (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y)) = GlobalTheory.SeeConjChar.conjRes PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x))) := by
  intro D X h PP κ x y
  have hH : ∀ u v, GlobalTheory.SeeConjChar.hT X h u v =
      Formalism.UG.hform (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D) ((Yc D 0).gram.map (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D)) u v := by
    intro u v
    obtain ⟨⟨I⟩⟩ := X
    dsimp only at h
    subst h
    rfl
  have hU : finE (Yc D 0) κ ∈
      Formalism.UG.UJ (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D) ((Yc D 0).gram.map (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D)) := by
    have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    rw [(Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ] at hf
    have := ((Formalism.IndefR.RationalEmbedding.iota D κ).2).2
    exact hf ▸ this
  have key : GlobalTheory.SeeConjChar.hT X h x ((finE (Yc D 0) κ).val *ᵥ y) =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D (GlobalTheory.SeeConjChar.hT X h y (((finE (Yc D 0) κ)⁻¹).val *ᵥ x)) := by
    rw [hH, hH]
    have e1 : x = (finE (Yc D 0) κ).val *ᵥ (((finE (Yc D 0) κ)⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have e2 := GlobalTheory.AdIsom.cjA_hA (Yc D 0) (((finE (Yc D 0) κ)⁻¹).val *ᵥ x) y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hA] at e2
    rw [e2]
    conv_lhs => rw [e1]
    exact hform_unitary _ _ hU _ _
  rw [key]
  exact ⟨GlobalTheory.AdIsom.cjA_mem_iff, resT_cjA PP _⟩

end GlobalTheory.SeeConjAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFlagPairingEqSignedDelta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem hT_eq_hY {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (x y : Fin (Yc D 0).rank → EAf D) : hT X h x y = hY D x y := by
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h ⊢
  subst h
  rfl

theorem hY_pair_flag_int {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (PP : Pl D.host.E) (a c : Fin (Yc D 0).rank) :
    hY D (pairAt X h PP a) (flagAt X h PP c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨β₀, h₀⟩ := GlobalTheory.StdFrames.exists_base (Yc D 0)
  have hU := GlobalTheory.StdFrames.unimod_of_isSD (GlobalTheory.StdFrames.isSD_one h₀)
  have hF := flag_pair_int X h β₀ h₀ PP
  set U := colMat (pairAt X h PP) with hUdef
  set W := colMat (flagAt X h PP) with hWdef
  set J := GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM (Yc D 0).gram with hJ
  have e1 : hY D (pairAt X h PP a) (flagAt X h PP c) = (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a c := by
    simp only [Matrix.mul_apply, Formalism.UG.hform, Formalism.UG.cT, Finset.sum_mul, Matrix.transpose_apply, Matrix.map_apply, hY]
    rw [Finset.sum_comm]
    rfl
  set A' := (β₀⁻¹).val * U with hAdef
  set B' := (β₀⁻¹).val * W with hBdef
  set G' := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef
  have hU' : U = β₀.val * A' := by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hW' : W = β₀.val * B' := by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A' * G' * B' := by
    rw [hGdef, hU', hW', GlobalTheory.StdFrames.cT_mul']
    simp only [Matrix.mul_assoc]
  rw [e1, hX']
  simp only [Matrix.mul_apply]
  refine sum_mem fun j _ => mul_mem (sum_mem fun i _ => mul_mem ?_ ?_) ?_
  · exact Formalism.UG.P.csDual_sig_mem _ (hF i a).2
  · exact hU.1 i j
  · exact (hF j c).1

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem resT_hT_pair_flag : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → ∀ PP ∈ R.Pg, ∀ a c : Fin (Yc D 0).rank, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) (flagAt X h PP c)) = if a = c then sgnD D.R.rS D.R.k a else 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R X h hL PP hPP a c
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    obtain ⟨l, hl⟩ := (hL.Pg PP).1 hPP
    have := R.C.P.overP hl
    rw [Nat.cast_mul]
    fin_cases l
    · exact PP.asIdeal.mul_mem_right _ this
    · exact PP.asIdeal.mul_mem_left _ this
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hsm : SmallAt PP (hY D (pairAt X h PP a) (flagAt X h PP c) - if a = c then sgnD D.R.rS D.R.k a else 0) := by
    by_cases he : GlobalTheory.StdFrames.cpt PP (ewT X h) = 1
    · unfold pairAt flagAt
      rw [if_pos he, if_pos he]
      exact flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_of_cpt_one X h PP hg he) a c
    · unfold pairAt flagAt
      rw [if_neg he, if_neg he]
      exact flagV_pair_table (hY D) (SmallAt PP) _ _ _ hn _ _ _ _ _ (pairTable_rev X h PP hg he) a c
  have hint := hY_pair_flag_int X h PP a c
  have hs : (if a = c then sgnD D.R.rS D.R.k a else 0 : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    unfold sgnD
    split_ifs
    exacts [neg_mem (one_mem _), one_mem _, zero_mem _]
  have key : Formalism.L2.DIV.resS D.host.F PP ⟨_, hint⟩ - Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = 0 := by
    rw [← map_sub]
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP _).2 hsm
  have hres : Formalism.L2.DIV.resS D.host.F PP ⟨_, hs⟩ = if a = c then sgnD D.R.rS D.R.k a else 0 := by
    by_cases hac : a = c
    · subst hac
      by_cases hz : a.1 = D.R.rS + D.R.k
      · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -1 := Subtype.ext (by simp [sgnD, hz])
        rw [e, map_neg, map_one]
        simp [sgnD, hz]
      · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 := Subtype.ext (by simp [sgnD, hz])
        rw [e, map_one]
        simp [sgnD, hz]
    · have e : (⟨_, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 0 := Subtype.ext (by simp [hac])
      rw [e, map_zero]
      simp [hac]
  unfold resT
  rw [hT_eq_hY, dif_pos hint, ← hres]
  exact sub_eq_zero.1 key

end GlobalTheory.SeeConjChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueOtherInstanceFormFrameStabilizerMulVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem cast_hA_add {I J : Formalism.MainNotions.S.AutInst} (e : I = J) (y z z' : Formalism.L2.SG.HidaSetting.VA J) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) (z + z'))) =
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z)) +
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z')) := by
  subst e
  simp only [cast_eq]
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cast_hA_smul {I J : Formalism.MainNotions.S.AutInst} (e : I = J) (c : TensorProduct J.F J.E (Formalism.MainNotions.S.Af J.F))
    (y z : Formalism.L2.SG.HidaSetting.VA J) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) (c • z))) =
    c * cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) e)
      (Formalism.L2.SG.HidaSetting.hA I (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) y)
        (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => Formalism.L2.SG.HidaSetting.VA I) e.symm) z)) := by
  subst e
  simp only [cast_eq]
  unfold Formalism.L2.SG.HidaSetting.hA Formalism.UG.hform
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hT_add' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (y z z' : Fin (Yc D 0).rank → EAf D) : hT X h y (z + z') = hT X h y z + hT X h y z' :=
  cast_hA_add h y z z'

theorem hT_smul' {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : EAf D) (y z : Fin (Yc D 0).rank → EAf D) : hT X h y (c • z) = c * hT X h y z :=
  cast_hA_smul h c y z

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar
open Classical
theorem resT_of_mem' {D : D7} (PP : Pl D.host.E) (x : EAf D) (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := dif_pos hx
end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar.ResStab

open Classical Matrix

theorem mem_res_eq {R k : Type} [CommRing R] [CommRing k] {S : Subring R} (ρ : S →+* k) {x : R} (s : S)
    (hx : x = s) : ∃ hm : x ∈ S, ρ ⟨x, hm⟩ = ρ s := by
  subst hx
  exact ⟨s.2, rfl⟩

theorem res_conj_mulVec {R k : Type} [CommRing R] [CommRing k] (S : Subring R) (ρ : S →+* k) (r : R → k) (hr : ∀ x (hx : x ∈ S), r x = ρ ⟨x, hx⟩) {n : ℕ}
    (f : (Fin n → R) → R) (hadd : ∀ z z', f (z + z') = f z + f z') (hsmul : ∀ (c : R) z, f (c • z) = c * f z) (β : GL (Fin n) R) (Y : Matrix (Fin n) (Fin n) S) (w : Fin n → Fin n → R)
    (N : Matrix (Fin n) (Fin n) R)
    (hNY : N = (β : Matrix (Fin n) (Fin n) R) * Y.map S.subtype * ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))
    (hw : ∀ i j, ∃ hm : (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w j) i ∈ S,
      ρ ⟨_, hm⟩ = if i = j then 1 else 0)
    (hf : ∀ z, (∀ i, (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ z) i ∈ S) → f z ∈ S) (j : Fin n) :
    ∃ hx : f (N *ᵥ w j) ∈ S,
      ρ ⟨_, hx⟩ = ∑ l, r (f (w l)) * ρ (Y l j) := by
  subst hNY
  set B : Matrix (Fin n) (Fin n) R := (β : Matrix (Fin n) (Fin n) R) with hB
  set Bi : Matrix (Fin n) (Fin n) R := ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) with hBi
  have hBiB : Bi * B = 1 := by rw [hBi, hB, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hBBi : B * Bi = 1 := by rw [hBi, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one]

  let b : Fin n → Fin n → R := fun m i => B i m
  have hb : ∀ m, Bi *ᵥ b m = Pi.single m 1 := by
    intro m
    have : b m = B *ᵥ Pi.single m 1 := by
      funext i
      simp [b, Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, hBiB, Matrix.one_mulVec]
  have ht : ∀ m, f (b m) ∈ S := by
    intro m
    refine hf _ fun i => ?_
    rw [hb m]
    by_cases hi : i = m
    · subst hi; simp only [Pi.single_eq_same]; exact S.one_mem
    · rw [Pi.single_eq_of_ne hi]; exact S.zero_mem
  let t : Fin n → S := fun m => ⟨f (b m), ht m⟩

  have hdec : ∀ z, f z = ∑ m, (Bi *ᵥ z) m * f (b m) := by
    intro z
    have hz : z = ∑ m, (Bi *ᵥ z) m • b m := by
      funext i
      have := congrFun (show B *ᵥ (Bi *ᵥ z) = z by rw [Matrix.mulVec_mulVec, hBBi, Matrix.one_mulVec]) i
      rw [← this, Finset.sum_apply]
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, b]
      exact Finset.sum_congr rfl fun m _ => mul_comm _ _
    let fl : (Fin n → R) →ₗ[R] R := ⟨⟨f, hadd⟩, hsmul⟩
    show fl z = _
    conv_lhs => rw [hz]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  have hval : ∀ z (v : Fin n → S), (∀ m, (Bi *ᵥ z) m = v m) → f z = ((∑ m, v m * t m : S) : R) := by
    intro z v hv
    rw [hdec z]
    push_cast
    exact Finset.sum_congr rfl fun m _ => by rw [hv m]

  let c : Fin n → Fin n → S := fun l i => ⟨(Bi *ᵥ w l) i, (hw i l).1⟩
  have hc : ∀ l i, ρ (c l i) = if i = l then 1 else 0 := fun l i => (hw i l).2

  have hwl : ∀ l, r (f (w l)) = ρ (t l) := by
    intro l
    obtain ⟨hm, e⟩ := mem_res_eq ρ _ (hval (w l) (c l) fun m => rfl)
    rw [hr _ hm, e, map_sum]
    simp only [map_mul, hc]
    simp

  have hN : ∀ m, (Bi *ᵥ ((B * Y.map S.subtype * Bi) *ᵥ w j)) m = ((∑ i, Y m i * c j i : S) : R) := by
    intro m
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBiB, Matrix.one_mul, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Subring.coe_subtype, c]
    push_cast
    rfl
  obtain ⟨hm, e⟩ := mem_res_eq ρ _ (hval _ (fun m => ∑ i, Y m i * c j i) hN)
  refine ⟨hm, ?_⟩
  rw [e]
  simp only [hwl, map_sum, map_mul, hc]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end GlobalTheory.SeeConjChar.ResStab

namespace GlobalTheory.SeeConjChar

open Classical GlobalTheory.SeeConjRead

theorem resT_hT_mulVec_stab : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Fin (Yc D 0).rank → Fin (Yc D 0).rank → EAf D), RedIs β PP w → ∀ N ∈ St β, ∀ y : Fin (Yc D 0).rank → EAf D, (∀ z : Fin (Yc D 0).rank → EAf D, (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h y z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ j, GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec N.val (w j))) = ∑ l, GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (w l)) * (redFn β PP N).val l j := by
  intro D X h β PP w hw N hN y hy j
  obtain ⟨Y, rfl⟩ := hN
  have hval : (Formalism.L2.DIV.frGL β Y).val =
      β.val * Y.val.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).val := by
    simp only [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul]
    rfl
  have hred : ∀ l, ((Formalism.L2.DIV.redFn β PP (Formalism.L2.DIV.frGL β Y)).val l j) =
      Formalism.L2.DIV.resS D.host.F PP (Y.val l j) := by
    intro l
    rw [Formalism.L2.DIV.redFn_frGL]
    rfl
  obtain ⟨hm, e⟩ := ResStab.res_conj_mulVec (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.DIV.resS D.host.F PP) (resT PP) (resT_of_mem' PP)
    (hT X h y) (hT_add' X h y) (fun c z => hT_smul' X h c y z) β Y.val w _ hval hw hy j
  refine ⟨hm, ?_⟩
  exact (resT_of_mem' PP _ hm).trans (e.trans (Finset.sum_congr rfl fun l _ =>
    congrArg (fun t => resT PP (hT X h y (w l)) * t) (hred l).symm))

end GlobalTheory.SeeConjChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestHypothesesAtMemberAdelicData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3

namespace GlobalTheory.PrimIn

theorem rowTest_setting_dat : Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt), K.Over B.toPre → GrpTrue Z.N f →
    z.R.toRealDat.ExAt → ∀ L : SizeData₂ (w.st Z).toD7, GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L →
    GlobalTheory.RowClaim.HidaSetting L z.R.toRealDat z.F.lv2 := by
  refine Ev.mono ?_ GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  intro K hK B f T w Z hX Wt z hOv hG hEx L hsz
  obtain ⟨hHost, hF, -, -, -, -, -, hstdX⟩ := hK (w.st Z) hOv
  have hC := z.pins.char
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak z.R z.F hC hEx).1
  have hfin : Finite (TupU w.I (usedOf w.I T Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T Wt)).finite_toSet
    exact hs.to_subtype
  exact
    { size := hsz
      eser := hG.eSerTie Z.V Z.S Z.G
      host := hHost
      hF := hF
      core := hcore
      mu_off := hC.tup.mu_off
      mu_used := hC.tup.mu_used
      mu_ne := hC.tup.mu_ne
      mu_conj := hC.tup.mu_conj
      mu_on := hC.tup.mu_on
      grp := hC.base.grp.record
      guard := z.pins.keep.guard
      fin := hfin
      fullY := hC.fullY
      fullX := hC.fullX
      std := z.pins.keep.std
      stdX := hstdX
      betaX := z.pins.keep.beta.2 }

end GlobalTheory.PrimIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallModelThetaTransformInjectiveProductsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallModel_thetaTransform_injective_products : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
    (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ (Φ + Φ') = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ + GlobalTheory.SmallDat.thetaS Γ W.ψ Φ') ∧
    (∀ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), ∀ Φ' ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.thetaS Γ W.ψ Φ' → Φ = Φ') ∧
    ∀ (f₁ : GlobalTheory.SmallDat.HomA G t i j → ℂ) (f₂ : GlobalTheory.SmallDat.HomB G i j → ℂ), IsThetaFunO W.ψ _ _ f₁ → IsThetaFunO W.ψ _ _ f₂ →
      ∃ Φ ∈ schA D.host.F (GlobalTheory.SmallDat.IxS G i j), GlobalTheory.SmallDat.thetaS Γ W.ψ Φ = GlobalTheory.SmallDat.boxS t e f₁ f₂ := by
  first | exact @GlobalTheory.SmallDat.ThBox.thetaS_box | exact GlobalTheory.SmallDat.ThBox.thetaS_box | (intros; apply GlobalTheory.SmallDat.ThBox.thetaS_box <;> assumption)
end

