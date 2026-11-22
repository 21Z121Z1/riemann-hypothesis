import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFullLevelGroupIffCongruenceLcm
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.EqCovol.FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_cc' (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

lemma herm_sub_left' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (u v y : Fin r → E) :
    herm G (u - v) y = herm G u y - herm G v y := by
  simp [herm, sub_mul, Finset.sum_sub_distrib]

lemma herm_sub_right' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x u v : Fin r → E) :
    herm G x (u - v) = herm G x u - herm G x v := by
  simp [herm, cc, mul_sub, Finset.sum_sub_distrib]

lemma herm_smul_left'' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (u y : Fin r → E) :
    herm G (c • u) y = c * herm G u y := by
  simp [herm, Finset.mul_sum, mul_assoc]

lemma herm_smul_right'' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x v : Fin r → E) :
    herm G x (c • v) = cc c * herm G x v := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma oe_smul {r : ℕ} (c : 𝓞 E) (y : Fin r → E) : c • y = (c : E) • y := by
  ext i; rfl

end GlobalTheory.EqCovol.FullLevel

open GlobalTheory.EqCovol.FullLevel in

theorem GlobalTheory.EqCovol.mem_iff_congr_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (l : Level H) (r : ℕ) (Y : Data E r), GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧ ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M' • y := by
  intro E _ _ _ H l r Y hL hS γ
  have hM0 : (l.M : E) ≠ 0 := by
    have : l.M ≠ 0 := by have := l.three_le; omega
    exact_mod_cast this
  have hA0 : (l.A : E) ≠ 0 := by exact_mod_cast l.A_pos.ne'
  constructor
  · intro hγ
    obtain ⟨hU, hM, hA⟩ := (hL γ).1 hγ
    obtain ⟨-, hMinv, -⟩ := (hL γ⁻¹).1 (Y.Γ.inv_mem hγ)
    set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
    set gi : Matrix (Fin r) (Fin r) E := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hgi
    have hggi : ∀ v, g.mulVec (gi.mulVec v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, hg, hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hunit : ∀ u v, herm Y.Gm (g.mulVec u) v = herm Y.Gm u (gi.mulVec v) := by
      intro u v
      have := hU.1 u (gi.mulVec v)
      rwa [hggi] at this
    have hcop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.coprime]; exact Submodule.mem_top
    obtain ⟨b', hb', b, hb, hsum⟩ := Submodule.mem_sup.1 hcop
    have hsumE : (b' : E) + (b : E) = 1 := by exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hsum

    have key : ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, g.mulVec x - x = l.M • y := by
      intro x hx
      obtain ⟨y1, hy1, e1⟩ := hM (b • x) (Submodule.smul_mem_smul hb hx)
      set z : Fin r → E := (l.M : E)⁻¹ • ((b' : E) • (g.mulVec x - x)) with hz
      have hzmem : z ∈ Y.Λ := by
        refine (hS z).2 fun y hy => ?_
        have hc : H.bar b' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hb'
        obtain ⟨w, hw, ew⟩ := hMinv (H.bar b' • y) (Submodule.smul_mem_smul hc hy)
        have hbarE : ((H.bar b' : 𝓞 E) : E) = cc (b' : E) := H.bar_eq b'
        rw [oe_smul, hbarE, ← Nat.cast_smul_eq_nsmul E] at ew
        have h1 : herm Y.Gm z y = herm Y.Gm x w := by
          have h2 := congrArg (herm Y.Gm x) ew
          rw [herm_sub_right', ← hunit, herm_smul_right'', herm_smul_right'', herm_smul_right'',
            cc_cc', cc, map_natCast] at h2
          rw [hz, herm_smul_left'', herm_smul_left'', herm_sub_left']
          field_simp
          linear_combination h2
        obtain ⟨n, hn⟩ := (hS x).1 hx w hw
        exact ⟨n, by rw [h1, hn]⟩
      refine ⟨z + y1, Y.Λ.add_mem hzmem hy1, ?_⟩
      rw [oe_smul, Matrix.mulVec_smul] at e1
      rw [smul_add, ← e1, ← Nat.cast_smul_eq_nsmul E, hz, smul_smul,
        mul_inv_cancel₀ hM0, one_smul, ← smul_sub, ← add_smul, hsumE, one_smul]
    refine ⟨hU, fun x hx => ?_⟩
    obtain ⟨y, hy, ey⟩ := key x hx
    obtain ⟨y', hy', ey'⟩ := hA x hx
    refine ⟨Nat.gcdA l.M l.A • y' + Nat.gcdB l.M l.A • y,
      Y.Λ.add_mem (Y.Λ.toAddSubgroup.zsmul_mem hy' _) (Y.Λ.toAddSubgroup.zsmul_mem hy _), ?_⟩
    set t := g.mulVec x - x with ht
    rw [← Nat.cast_smul_eq_nsmul E] at ey ey'
    have hy1 : y = (l.M : E)⁻¹ • t := by rw [ey, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    have hy2 : y' = (l.A : E)⁻¹ • t := by rw [ey', smul_smul, inv_mul_cancel₀ hA0, one_smul]
    have hG : ((Nat.gcd l.M l.A : ℕ) : E) = (l.M : E) * (Nat.gcdA l.M l.A : E) + (l.A : E) * (Nat.gcdB l.M l.A : E) := by
      have := congrArg (Int.cast : ℤ → E) (Nat.gcd_eq_gcd_ab l.M l.A)
      push_cast at this
      exact this
    have hGL : ((Nat.gcd l.M l.A : ℕ) : E) * (l.M' : E) = (l.M : E) * (l.A : E) := by
      unfold Level.M'
      exact_mod_cast Nat.gcd_mul_lcm l.M l.A
    rw [← Nat.cast_smul_eq_nsmul E, ← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, hy1, hy2,
      smul_smul, smul_smul, ← add_smul, smul_smul]
    conv_lhs => rw [← one_smul E t]
    congr 1
    field_simp
    linear_combination hGL.symm + (l.M' : E) * hG
  · rintro ⟨hU, h⟩
    refine (hL γ).2 ⟨hU, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := h x (Submodule.smul_le_right hx)
      obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      exact ⟨k • y, Y.Λ.toAddSubmonoid.nsmul_mem hy k, by rw [e, hk, mul_smul]⟩
    · obtain ⟨y, hy, e⟩ := h x hx
      obtain ⟨k, hk⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
      exact ⟨k • y, Y.Λ.toAddSubmonoid.nsmul_mem hy k, by rw [e, hk, mul_smul]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeIffUniformiserReductionVanishes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
namespace GlobalTheory.DilKer

open GlobalTheory.StdFrames (cpt)

theorem frMapO_dil {D : D7} (i : Fin D.R.m) (βS : GL (Fin (Vc D i).rank) (EAf D)) (βT : GL (Fin (Wc D i).rank) (EAf D))
    (a : D.host.E) (z : WO (Vc D i) (Wc D i)) :
    frMapO (Vc D i) (Wc D i) βS βT (dil i a z) = eToEAf D a • frMapO (Vc D i) (Wc D i) βS βT z := by
  have h : (dil i a z).map (toEAf D) = eToEAf D a • z.map (toEAf D) := by
    ext k l
    simp only [dil, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul, GlobalTheory.IdemIntegral.toEAf_incA]
  simp only [frMapO, h, Matrix.mul_smul, Matrix.smul_mul]

theorem isHalf_dil {D : D7} (i : Fin D.R.m) (e : AE D) (a : D.host.E) {z : WO (Vc D i) (Wc D i)} (hz : IsHalf e z) :
    IsHalf e (dil i a z) := fun k l => by
  simp only [dil, Matrix.map_apply]
  rw [mul_left_comm, hz k l]

theorem frMapO_half {D : D7} (i : Fin D.R.m) (βS : GL (Fin (Vc D i).rank) (EAf D)) (βT : GL (Fin (Wc D i).rank) (EAf D))
    {e : AE D} {z : WO (Vc D i) (Wc D i)} (hz : IsHalf e z) (k l) :
    toEAf D e * frMapO (Vc D i) (Wc D i) βS βT z k l = frMapO (Vc D i) (Wc D i) βS βT z k l := by
  have h : z.map (toEAf D) = toEAf D e • z.map (toEAf D) := by
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← RingHom.map_mul, hz a b]
  have h2 : frMapO (Vc D i) (Wc D i) βS βT z = toEAf D e • frMapO (Vc D i) (Wc D i) βS βT z := by
    conv_lhs => rw [frMapO, h]
    simp only [frMapO, Matrix.mul_smul, Matrix.smul_mul]
  conv_rhs => rw [h2]
  rfl

theorem val_cpt_eToEAf {D : D7} (PP : Pl D.host.E) (x : D.host.E) :
    Valued.v (cpt PP (eToEAf D x)) = PP.valuation D.host.E x := by
  have : eToEAf D x = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D x := rfl
  rw [this, GlobalTheory.AdIsom.cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]

theorem mem_int_of_mul {D : D7} {Q : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e Q) {ϖ : 𝓞 D.host.E}
    (hϖ : ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) {m : EAf D} (hm : toEAf D e * m = m)
    (hy : eToEAf D (ϖ : D.host.E) * m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hr : ∀ PP ∈ Q, Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * m)) < 1) :
    m ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  refine (GlobalTheory.AdIsom.mem_OA m).2 fun P => ?_
  by_cases hP : P ∈ Q
  · have h1 := hr P hP
    rw [RingHom.map_mul, Valuation.map_mul, val_cpt_eToEAf, GlobalTheory.HeckeDetChar.val_unif (hϖ P hP).1 (hϖ P hP).2] at h1
    by_cases h0 : Valued.v (cpt P m) = 0
    · rw [h0]; exact zero_le'
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (cpt P m) = WithZero.exp k := ⟨_, (WithZero.exp_log h0).symm⟩
    rw [hk] at h1 ⊢
    rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · have h0 : cpt P (toEAf D (∑ PP ∈ Q, es PP)) = 0 := by
      rw [map_sum, map_sum]
      exact Finset.sum_eq_zero fun PP hPP => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes PP hPP)).2 P fun h => hP (h ▸ hPP)
    have := congrArg (cpt P) hm
    rw [RingHom.map_mul, h0, zero_mul] at this
    rw [← this, Valuation.map_zero]
    exact zero_le'

theorem mem_localLattice_iff_redM : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (Q : Finset (Pl D.host.E)), (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : WO (Vc D i) (Wc D i), IsHalf eQ z → dil i (ϖ : D.host.E) z ∈ lattice₂ R i → (z ∈ lattice₂ R i ↔ ∀ PP ∈ Q, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) z)) = 0) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV Q hQ eQ he ϖ hϖ0 hϖ z hz hϖz
  have hI := GlobalTheory.T.mem_completedPairLattice_iff_frameMatrix_integral_on_half D G Pl0 T0 A Ks R F hC hG i hV Q hQ eQ he
  rw [frMapO_dil]
  constructor
  · intro hzL PP hPP
    have hM := (hI z hz).2 hzL
    ext k l
    have hϖi : eToEAf D (ϖ : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [← GlobalTheory.IdemIntegral.toEAf_incA]
      exact GlobalTheory.IdemIntegral.toEAf_mem_of_finPart (GlobalTheory.SplitIndex.finPart_incA_mem ϖ)
    have hint : eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := mul_mem hϖi (hM k l)
    simp only [redM, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, dif_pos hint]
    refine (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, hint⟩).2 ?_
    change Valued.v (cpt PP (eToEAf D (ϖ : D.host.E) * _)) < 1
    rw [RingHom.map_mul, Valuation.map_mul, val_cpt_eToEAf, GlobalTheory.HeckeDetChar.val_unif (hϖ PP hPP).1 (hϖ PP hPP).2]
    calc WithZero.exp (-1 : ℤ) * Valued.v (cpt PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l))
        ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr; exact (GlobalTheory.AdIsom.mem_OA _).1 (hM k l) PP
      _ < 1 := by rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  · intro hred
    have hN := (hI _ (isHalf_dil i eQ _ hz)).2 hϖz
    rw [frMapO_dil] at hN
    have hN' : ∀ k l, eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) z k l ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := fun k l => hN k l
    refine (hI z hz).1 fun k l => mem_int_of_mul he hϖ (frMapO_half i _ _ hz k l) (hN' k l) fun PP hPP => ?_
    have h1 := congrFun (congrFun (hred PP hPP) k) l
    simp only [redM, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, dif_pos (hN' k l)] at h1
    exact (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt PP ⟨_, hN' k l⟩).1 h1

end GlobalTheory.DilKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfDualWeylTensorReductionEqZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HighWtEmb

theorem exists_basis_reduction_linearIndependent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → GlobalTheory.HighWt.BaseChange →
    ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∃ (n : ℕ) (b : Module.Basis (Fin n) O (dualWeyl O N N ν)),
      LinearIndependent (O ⧸ Ideal.span {ϖ})
        (fun i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b i : MvPolynomial (Fin N × Fin N) O)) := by
  intro O _ _ _ ϖ hϖ hBC N ν hν
  haveI := GlobalTheory.NablaFin.dualWeyl_finite O N ν
  haveI : Module.Free O (dualWeyl O N N ν) := Module.free_of_finite_type_torsion_free'
  let b := (Module.Free.chooseBasis O (dualWeyl O N N ν)).reindex (Fintype.equivFin _)
  refine ⟨_, b, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  choose c hc using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}) (a j)
  let g : dualWeyl O N N ν := ∑ j, c j • b j
  have hg : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (g : MvPolynomial (Fin N × Fin N) O) = 0 := by
    rw [← ha]
    simp only [g, Submodule.coe_sum, Submodule.coe_smul, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hc]
  obtain ⟨h, hh, hgh⟩ := (hBC O ϖ hϖ N ν hν).2 g g.2 hg
  have hgh' : g = ϖ • (⟨h, hh⟩ : dualWeyl O N N ν) := Subtype.ext (by simpa using hgh)
  have hci : c i = ϖ * b.repr ⟨h, hh⟩ i := by
    have h2 := congrArg (fun x => b.repr x i) hgh'
    simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    simp [g, map_sum, Finsupp.single_apply]
  rw [← hc i, hci, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), zero_mul]

theorem exists_dual_family (k : Type) [Field k] (σ : Type) (κ : Type) [DecidableEq κ] (v : κ → MvPolynomial σ k)
    (hv : LinearIndependent k v) : ∃ ψ : κ → (MvPolynomial σ k →ₗ[k] k), ∀ i l, ψ l (v i) = if i = l then 1 else 0 := by
  let B := Module.Basis.span hv
  refine ⟨fun l => (LinearMap.exists_extend (B.coord l)).choose, fun i l => ?_⟩
  have h := (LinearMap.exists_extend (B.coord l)).choose_spec
  have hvi : v i ∈ Submodule.span k (Set.range v) := Submodule.subset_span ⟨i, rfl⟩
  have h1 := LinearMap.congr_fun h ⟨v i, hvi⟩
  have hBi : B i = ⟨v i, hvi⟩ := Module.Basis.span_apply hv i
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
  rw [h1, ← hBi, B.coord_apply, B.repr_self, Finsupp.single_apply]

theorem curry_sum_mapDomain {ι σ : Type} [Fintype ι] [DecidableEq ι] (F : ι → σ →₀ ℕ) (τ : ι) :
    (∑ ρ, Finsupp.mapDomain (fun s : σ => ((ρ, s) : ι × σ)) (F ρ)).curry τ = F τ := by
  classical
  ext s
  rw [Finsupp.curry_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (fun _ _ h => congrArg Prod.snd h) _ _
  · intro ρ _ hρ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨t, ht⟩
    exact hρ (congrArg Prod.fst ht)
  · simp

theorem exists_prod_functional : ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type)
    (φ : ι → (MvPolynomial σ k →ₗ[k] k)), ∃ Φ : MvPolynomial (ι × σ) k →ₗ[k] k,
      ∀ f : ι → MvPolynomial σ k, Φ (∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ)) = ∏ τ, φ τ (f τ) := by
  intro k _ ι _ _ σ φ
  classical
  let w : ((ι × σ) →₀ ℕ) → k := fun M => ∏ τ, φ τ (monomial (M.curry τ) 1)
  let Φ := (MvPolynomial.basisMonomials (ι × σ) k).constr k w
  have hmono : ∀ M c, Φ (monomial M c) = c * w M := by
    intro M c
    have : (monomial M c : MvPolynomial (ι × σ) k) = c • (MvPolynomial.basisMonomials (ι × σ) k M) := by
      rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hφ : ∀ τ m c, φ τ (monomial m c) = c * φ τ (monomial m 1) := by
    intro τ m c
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  refine ⟨Φ, fun f => ?_⟩
  have h1 : ∀ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ) =
      ∑ m ∈ (f τ).support, monomial (Finsupp.mapDomain (fun s : σ => ((τ, s) : ι × σ)) m) (coeff m (f τ)) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    simp only [map_sum, rename_monomial]
  have h2 : ∀ τ, φ τ (f τ) = ∑ m ∈ (f τ).support, coeff m (f τ) * φ τ (monomial m 1) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hφ τ m _
  rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_congr rfl (fun τ _ => h2 τ), Finset.prod_univ_sum,
    Finset.prod_univ_sum, map_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← monomial_sum_prod, hmono]
  simp only [w, curry_sum_mapDomain, Finset.prod_mul_distrib]

theorem linearIndependent_prod_rename : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (v : ∀ τ, κ τ → MvPolynomial σ k), (∀ τ, LinearIndependent k (v τ)) →
    LinearIndependent k (fun p : (∀ τ, κ τ) => ∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (v τ (p τ))) := by
  intro k _ ι _ _ σ κ _ v hv
  classical
  choose ψ hψ using fun τ => exists_dual_family k σ (κ τ) (v τ) (hv τ)
  rw [Fintype.linearIndependent_iff]
  intro a ha l
  obtain ⟨Φ, hΦ⟩ := exists_prod_functional k ι σ (fun τ => ψ τ (l τ))
  have h := congrArg Φ ha
  rw [map_sum, map_zero] at h
  simp only [map_smul, hΦ, hψ, smul_eq_mul] at h
  rw [Finset.sum_eq_single l] at h
  · simpa using h
  · intro p _ hp
    obtain ⟨τ, hτ⟩ : ∃ τ, p τ ≠ l τ := by
      by_contra hc
      push_neg at hc
      exact hp (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ), mul_zero]
  · simp

theorem blockRed_eq (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (g : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ g = rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι)) (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp, blockRed] at *

theorem mem_smul_top_of_redT_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange →
    ∀ y : NablaT O N mu, redT O N mu ϖ y = 0 → y ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu)) := by
  intro O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC y hy
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hb := fun τ => exists_basis_reduction_linearIndependent O ϖ hϖ hBC N (res N (mu τ)) (hanti τ)
  choose n b hli using hb
  let B := Basis.piTensorProduct b
  have hred : ∀ p, redT O N mu ϖ (B p) = ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) := by
    intro p
    simp only [B, Basis.piTensorProduct_apply, redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, AlgHom.toLinearMap_apply]
    exact Finset.prod_congr rfl fun τ _ => blockRed_eq O N ϖ τ _
  have hL := linearIndependent_prod_rename (O ⧸ Ideal.span {ϖ}) ι (Fin N × Fin N) (fun τ => Fin (n τ))
    (fun τ i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ i : MvPolynomial (Fin N × Fin N) O)) hli
  rw [Fintype.linearIndependent_iff] at hL
  have hy' : ∑ p, Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr y p) • ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) = 0 := by
    rw [← hy]
    conv_rhs => rw [← B.sum_repr y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [LinearMap.map_smul, hred]
    exact algebraMap_smul (O ⧸ Ideal.span {ϖ}) (B.repr y p) _
  have hc := hL _ hy'
  rw [← B.sum_repr y]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hp : B.repr y p ∈ Ideal.span {ϖ} := Ideal.Quotient.eq_zero_iff_mem.mp (hc p)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hp
  rw [← hd, mul_comm, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top

end GlobalTheory.HighWtEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationIntertwines
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval GlobalTheory.WeilTr

noncomputable section

namespace GlobalTheory.DblTr

theorem hasDbl_transp : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
    ∀ d' d₁' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) → (∀ x : Matrix (Fin n) (Fin d) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (incM F X.J) d' d₁' T := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e he hbij T hTe d' d₁' hd' hd₁'
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hpair.base.std
  have hL : IsLocOp e := isLocOp_of_isEv hpair.good hM₁ he
  obtain ⟨e', hL', hinv⟩ := GlobalTheory.T.local_operator_inverse_local e hL hbij
  have hTe' : ∀ Φ ∈ schA F (Fin n × Fin d), T.symm Φ = e' Φ := by
    intro Φ hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    rw [← hTe Ψ hΨ, LinearEquiv.symm_apply_apply, hTe Ψ hΨ, hinv Ψ hΨ]
  have hmem : ∀ Φ, Φ ∈ schA F (Fin n × Fin d) ↔ T Φ ∈ schA F (Fin n × Fin d) := by
    intro Φ
    constructor
    · intro h
      rw [hTe Φ h]
      exact hbij.mapsTo h
    · intro h
      obtain ⟨Ψ, hΨ, hΨe⟩ := hbij.surjOn h
      have h1 : T Ψ = T Φ := (hTe Ψ hΨ).trans hΨe
      rw [← T.injective h1]
      exact hΨ
  have hn : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hd1 : (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d), T (d'.rho B.ψ w Φ) = d₁'.rho B.ψ w (T Φ) := by
    intro w Φ hΦ
    have e1 : ∀ Ψ, d'.rho B.ψ w Ψ = M.co.rho B.ψ wᵀ Ψ := fun Ψ => by
      simp only [Darboux.rho]
      rw [← hd' wᵀ, Matrix.transpose_transpose]
    have e2 : ∀ Ψ, d₁'.rho B.ψ w Ψ = M₁.co.rho B.ψ wᵀ Ψ := fun Ψ => by
      simp only [Darboux.rho]
      rw [← hd₁' wᵀ, Matrix.transpose_transpose]
    have hρ : M.co.rho B.ψ wᵀ Φ ∈ schA F (Fin n × Fin d) :=
      GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hpair.base.std _ _ Φ hΦ
    have h := he.Heisenberg₂ wᵀ Φ hΦ
    rw [hn, hd1, Matrix.one_mul, Matrix.mul_one] at h
    rw [e1, e2, hTe _ hρ, hTe Φ hΦ, h]
  have hunit : ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨C, hC⟩ := GlobalTheory.ModelTrUnit.exists_const hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e he hbij μ hμ
    exact ⟨C, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hC Φ hΦ⟩
  exact hasDbl_of_loc (cA σ) (-1) (incM F W.J) (incM F X.J) B.ψ hψ d' d₁' T e e' hL hL' hTe hTe' hmem Heisenberg₂ hunit

end GlobalTheory.DblTr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesAdmissibleStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_evaluation_preserves_admissible : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.ModelTrUnit.exists_const | exact GlobalTheory.ModelTrUnit.exists_const | (intros; apply GlobalTheory.ModelTrUnit.exists_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDefiniteRationalPointDataComponent
section
open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

namespace GlobalTheory.DefPt.PtExist

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ Z : Comp Xo c, Nonempty (PtData Z) :=
  GlobalTheory.DefPt.Model.nonempty_ptData_all

end GlobalTheory.DefPt.PtExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemPrimeAwayFromMuStatement
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_not_mem_prime_away_from_mu : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → ∀ w : HeightOneSpectrum (𝓞 D.what₂.LL), p.R.mu w ≠ p.P.A3.A.μ0 → ((Qn d.G (p.R.mu w) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  first | exact @GlobalTheory.ThmAUpper.qn_not_mem | exact GlobalTheory.ThmAUpper.qn_not_mem | (intros; apply GlobalTheory.ThmAUpper.qn_not_mem <;> assumption)
end

