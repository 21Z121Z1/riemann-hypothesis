import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0044
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ReHermitianCombinationNonpos
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0027
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0043
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0045
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RatIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0029

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeRat
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.BridgeRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def hat (A : X.B.I.Gf) (y : (VS D).V) : VA X.B.I := X.B.I.fmat A⁻¹ *ᵥ incl X.B.I (X.crd y)

theorem hat_add (A : X.B.I.Gf) (y z : (VS D).V) : hat X A (y + z) = hat X A y + hat X A z := by
  simp only [hat]
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_add]

theorem hat_sub (A : X.B.I.Gf) (y z : (VS D).V) : hat X A (y - z) = hat X A y - hat X A z := by
  simp only [hat]
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_sub]

theorem hat_smul (A : X.B.I.Gf) (c : D.host.E) (y : (VS D).V) :
    hat X A (c • y) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm c) • hat X A y := by
  simp only [hat]
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_mul, smul_eq_mul]

theorem hat_sum (A : X.B.I.Gf) {ι : Type} (s : Finset ι) (f : ι → (VS D).V) :
    hat X A (∑ i ∈ s, f i) = ∑ i ∈ s, hat X A (f i) := by
  exact map_sum (AddMonoidHom.mk' (hat X A) (hat_add X A)) f s

theorem hat_ratLink (A : X.B.I.Gf) {b : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X b β)
    (y : (VS D).V) : hat X A (β y) = X.B.I.fmat (A⁻¹ * b.2 * A) *ᵥ hat X A y := by
  obtain ⟨M, -, -, hfm, hcrd⟩ := h
  have hone : X.B.I.fmat 1 = 1 := by simp [AutInst.fmat]
  have hincl : incl X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
        incl X.B.I (X.crd y) := by
    funext i
    simp [incl, Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [hat]
  rw [hcrd y, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X, hfm,
    Matrix.mulVec_mulVec, mul_assoc _ (X.B.I.fmat A), ← Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X,
    mul_inv_cancel, hone, mul_one, ← Matrix.mulVec_mulVec, hincl]

theorem hA_hat (A : X.B.I.Gf) (y z : (VS D).V) :
    hA X.B.I (hat X A y) (hat X A z) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((VS D).hT y z)) := by
  simp only [hat]
  rw [Formalism.L2.SG.PoincareInHH.Cut.hA_fmat X, Formalism.L2.SG.PoincareInHH.Cut.hA_crd X]

theorem mL_div {m : VA X.B.I} (hm : m ∈ mL X.B.I X.B.g) : ∃ x ∈ X.B.I.Lf, m = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
  unfold mL at hm
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨x', hx', rfl⟩ := hb
    exact ⟨x + x', add_mem hx hx', (smul_add _ _ _).symm⟩
  | smul c a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨c • x, Submodule.smul_mem _ c hx, smul_comm c _ x⟩

theorem locP_of_InAt (A : X.B.I.Gf) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf) {y : (VS D).V} (hy : InAt X.B.I X.B.g X.B.g (hat X A y))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    y ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)) := by
  obtain ⟨c, hcop, hc⟩ := hy
  obtain ⟨x, hx, hcx⟩ := mL_div X hc
  have hgB : X.B.g = gS D := X.g_eq
  have hgE : ((gS D : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  set t : D.host.E := (c : D.host.E) / ((gS D : ℕ) : D.host.E) with ht_def
  have ht : hat X A (t • y) = x := by
    rw [hat_smul]
    have hg0 : ((X.B.g : ℕ) : X.B.I.E) ≠ 0 := by
      rw [hgB]
      exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hcast : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((X.B.g : ℕ) : X.B.I.E) := (map_natCast _ _).symm
    have hunit : IsUnit ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      rw [hcast]
      exact (isUnit_iff_ne_zero.2 hg0).map _
    rw [← hunit.smul_left_cancel, ← hcx, smul_smul]
    congr 1
    rw [hcast, ← map_mul, show ((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((c : ℕ) : X.B.I.E) from (map_natCast _ _).symm]
    congr 1
    apply X.ιE.injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_natCast, map_natCast, hgB, ht_def]
    field_simp
  have hty : t • y ∈ Λ := (hlat _).2 (ht ▸ hx)
  simp only [Formalism.HermitianLatticesTheory.localization₂]
  refine ⟨((c : ℕ) : 𝓞 D.host.E), ?_, ?_⟩
  · show ((c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
    intro hcP
    have hcopZ : IsCoprime (c : ℤ) (X.B.g : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨a, b, hab⟩ := hcopZ.map (Int.castRingHom (𝓞 D.host.E))
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · simpa using hcP
    · rw [hgB]
      simpa using hP
  · have hsm : ∀ (o : 𝓞 D.host.E) (v : (VS D).V), o • v = (o : D.host.E) • v :=
      fun o v => (algebraMap_smul D.host.E o v).symm
    have hcy : ((c : ℕ) : 𝓞 D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • (t • y) := by
      rw [hsm, hsm, smul_smul]
      congr 1
      push_cast
      rw [ht_def]
      field_simp
    rw [hcy]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hty

theorem Mo_le_Lf : Mo X.B.I X.B.g (Set.range X.e0) ≤ X.B.I.Lf := by
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨a, rfl⟩
    exact (X.vectorsInLattice.1 a).1
  · rintro y ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx _

theorem ratFromAd (A : X.B.I.Gf) {u : D.what₂.Word} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf)
    (hfixE : ∀ a, hat X A (X.eX a) = incl X.B.I (X.crd (X.eX a)))
    (hFC : IsFixedConv Λ (gS D) (lf D (X.Fu u))) (hTF : ∀ a, (X.Fu u).e a = X.eX a)
    {y : (VS D).V} (hy : hat X A y ∈ Mo X.B.I X.B.g (Set.range X.e0)) :
    y ∈ NgX Λ (gS D) (lf D (X.Fu u)) (lf D (X.Fu u)) := by
  have hyΛ : y ∈ Λ := (hlat y).2 (Mo_le_Lf X hy)

  obtain ⟨s, hs, m, hm, hsm⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (IntAf X.B.I.F X.B.I.E)).1 hs
  choose t c' hc' ht using fun a => PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g
    (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X)) (c a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (c a).2
  set r : (VS D).V := ∑ a, X.ιE ((t a : 𝓞 X.B.I.E) : X.B.I.E) • X.eX a with hr

  have hdiff : InAt X.B.I X.B.g X.B.g (hat X A (y - r)) := by
    have e1 : hat X A (y - r) = (∑ a, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((t a : 𝓞 X.B.I.E) : X.B.I.E) •
        (X.e0 a - incl X.B.I (X.crd (X.eX a)))) +
        ((∑ a, ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c' a) • X.e0 a) + m) := by
      rw [hat_sub, ← hsm, ← hc, hr]
      simp only [hat_sum X A, hat_smul, RingEquiv.symm_apply_apply, hfixE]
      have e2 : ∀ a, (c a : IntAf X.B.I.F X.B.I.E) • X.e0 a =
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((t a : 𝓞 X.B.I.E) : X.B.I.E) +
            (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c' a) • X.e0 a := by
        intro a; rw [Subring.smul_def, ht a]
      simp only [e2, add_smul, Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e1]
    refine InAt_add X (InAt_sum X _ _ fun a _ => InAt_smul X (inclE_mem X.B.I ⟨t a, rfl⟩) (X.basisApprox a).1)
      (InAt_add X ⟨1, Nat.coprime_one_left _, ?_⟩ ⟨1, Nat.coprime_one_left _, by rw [Nat.cast_one, one_smul]; exact hm⟩)
    rw [Nat.cast_one, one_smul]
    refine sum_mem fun a _ => ?_
    rw [mul_smul]
    have : c' a • X.e0 a = (⟨_, hc' a⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
    rw [this]
    exact smul_mem_mL X.B.I (Submodule.smul_mem _ _ (X.vectorsInLattice.1 a).1)
  refine Formalism.L2.SG.Pf.mem_of_forall_locP fun P => ?_
  haveI := P.isPrime
  by_cases hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  ·
    have h1 := locP_of_InAt X A hlat hdiff P hP
    have h2 : r ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D (X.Fu u))) := by
      obtain ⟨cc, -, hc1, hloc⟩ := hFC.1 P
      have hc1' := hc1 hP
      rw [hloc]
      rw [hr]
      refine sum_mem fun a _ => ?_
      have hmem : X.eX a ∈ Submodule.span (𝓞 D.host.E) (Set.range fun b => cc b • (lf D (X.Fu u)).fl.e b) :=
        Submodule.subset_span ⟨a, by simp [hc1' a, hTF a, lf]⟩
      have hint : X.ιE ((t a : 𝓞 X.B.I.E) : X.B.I.E) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        have := ((t a).2 : IsIntegral ℤ ((t a : 𝓞 X.B.I.E) : X.B.I.E)).map X.ιE.toRingHom.toIntAlgHom
        exact ⟨⟨_, this⟩, rfl⟩
      obtain ⟨o, ho⟩ := hint
      rw [← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Formalism.L2.SG.Pf.mem_localization_of_mem' hmem)
    rw [show y = (y - r) + r by abel]
    exact add_mem (Formalism.L2.SG.Pf.localization_mono (le_sup_left.trans le_sup_left) h1)
      (Formalism.L2.SG.Pf.localization_mono (le_sup_right.trans le_sup_left) h2)
  ·
    refine ⟨((gS D : ℕ) : 𝓞 D.host.E), hP, ?_⟩
    exact (le_sup_left.trans le_sup_left : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ≤ _)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hyΛ)

end Formalism.L2.SG.Pf.BridgeRat
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolGcPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut
open Matrix

section Conj

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter)

theorem gam_mem_GF (γ : Gam X u) : (γ : X.B.I.GA) ∈ X.B.I.GFset := (Subgroup.mem_inf.1 γ.2).1

theorem gam_fst_mem (γ : Gam X u) : (γ : X.B.I.GA).1 ∈ Hinf X u :=
  (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).1

theorem iotaF_coe (γ : Gam X u) : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl

theorem gc_conj_sub (γ : Gam X u) (h : Hfin X u) (κ : Ku X u hK) (s : X.B.I.Ginf)
    (hs : s ∈ GcS X u hK ((h : X.B.I.Gf) * X.xu u)) :
    (γ : X.B.I.GA).1 * s * (γ : X.B.I.GA).1⁻¹ ∈
      GcS X u hK ((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) * X.xu u) := by
  rw [mem_gcS] at hs ⊢
  obtain ⟨ν, hG, rfl, hN, hF, hk⟩ := hs
  refine ⟨(γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹, ?_, rfl, ?_, ?_, ?_⟩
  · exact (Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem
      ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem (gam_mem_GF X u γ) hG)
      ((Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).inv_mem (gam_mem_GF X u γ))
  · have hH := gam_fst_mem X u γ
    have he : ∀ v a, uMat ((γ : X.B.I.GA).1 v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a) :=
      fun v a => hH v _ (Or.inl (Or.inl ⟨a, rfl⟩))
    have hz : ∀ v, uMat ((γ : X.B.I.GA).1 v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u) :=
      fun v => hH v _ (Or.inr rfl)
    refine (Formalism.L2.SG.CovariantRepresentation.ninf_conj_iff X u (γ : X.B.I.GA).1 he hz _).2 ?_
    have : (γ : X.B.I.GA).1⁻¹ * ((γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹).1 * (γ : X.B.I.GA).1 = ν.1 := by
      simp only [Prod.fst_mul, Prod.fst_inv]; group
    rw [this]; exact hN
  · have := (nfinConj_holds X u (iotaF X u γ) ν.2 hF).1
    rw [iotaF_coe] at this
    simpa only [Prod.snd_mul, Prod.snd_inv] using this
  · have hκ : (X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.K2 := κ.2
    have e : (((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ * ((γ : X.B.I.GA) * ν * (γ : X.B.I.GA)⁻¹).2 *
        (((iotaF X u γ * h * (κ : Hfin X u) : Hfin X u) : X.B.I.Gf) * X.xu u) =
        ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u)⁻¹ *
          (((h : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * ((h : X.B.I.Gf) * X.xu u)) *
          ((X.xu u)⁻¹ * ((κ : Hfin X u) : X.B.I.Gf) * X.xu u) := by
      simp only [Subgroup.coe_mul, iotaF_coe, Prod.snd_mul, Prod.snd_inv]
      group
    rw [e]
    exact hK.2.1 _ (hK.2.1 _ (hK.2.2.1 _ hκ) _ hk) _ hκ

end Conj

theorem gcConjC_holds : GcConjC := by
  intro D X u hK γ h κ
  ext s
  constructor
  · intro hs
    have e : (iotaF X u γ⁻¹ * (iotaF X u γ * h * (κ : Hfin X u)) * ((κ⁻¹ : Ku X u hK) : Hfin X u) : Hfin X u) = h := by
      rw [map_inv, InvMemClass.coe_inv]; group
    have := gc_conj_sub X u hK γ⁻¹ (iotaF X u γ * h * (κ : Hfin X u)) κ⁻¹ s hs
    rw [e] at this
    refine ⟨_, this, ?_⟩
    simp only [InvMemClass.coe_inv, Prod.fst_inv]
    group
  · rintro ⟨t, ht, rfl⟩
    exact gc_conj_sub X u hK γ h κ t ht

theorem isSFund_conj {D : D7} (X : HidaSetting D) (S : Set X.B.I.Ginf) (Ω : Set X.B.I.Ginf)
    (hΩ : IsSFund X.B.I S Ω) (a : X.B.I.Ginf) :
    IsSFund X.B.I ((fun s => a * s * a⁻¹) '' S) ((fun y => a * y) '' Ω) := by
  have hpre : (fun y => a * y) '' Ω = {x | a⁻¹ * x ∈ Ω} := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨a⁻¹ * x, hx, by group⟩
  rw [hpre]
  refine ⟨(measurable_const_mul a⁻¹) hΩ.1, fun x => ?_, fun x hx s' hs' hsx => ?_⟩
  · obtain ⟨s, hs, hsx⟩ := hΩ.2.1 (a⁻¹ * x)
    refine ⟨a * s * a⁻¹, ⟨s, hs, rfl⟩, ?_⟩
    show a⁻¹ * (a * s * a⁻¹ * x) ∈ Ω
    have : a⁻¹ * (a * s * a⁻¹ * x) = s * (a⁻¹ * x) := by group
    rwa [this]
  · obtain ⟨s, hs, rfl⟩ := hs'
    have h2 : s * (a⁻¹ * x) ∈ Ω := by
      have : a⁻¹ * (a * s * a⁻¹ * x) = s * (a⁻¹ * x) := by group
      have h := hsx; simp only [Set.mem_ofPred_eq] at h; rwa [this] at h
    have := hΩ.2.2 _ hx s hs h2
    rw [this]; group

theorem nocol_fund_exists {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (ρ : (Y.cs u).Cl) : ∃ Ω, IsSFund X.B.I (Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ) Ω := by
  have hL := ((Y.rowsOK u).1 _ ((Y.cs u).lam_mem ρ)).1.1
  have := Formalism.L2.SG.Pf.ROsub_discrete X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) hL 1
  obtain ⟨Ω, hΩ⟩ := Formalism.L2.SG.Pf.isSFund_of_discrete X.B.I
    (Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1)
  refine ⟨Ω, ?_⟩
  have e : ((Formalism.L2.SG.Pf.ROsub X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1 :
      Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) = Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ := by
    ext y
    show y ∈ ROset X (X.Fu u) (X.Fu u) ((Y.cs u).lamOf ρ) ((Y.cs u).lamOf ρ) 1 ↔ _
    constructor
    · rintro ⟨x, n, h1, h2, h3, -⟩
      exact ⟨x, n, h1, h2, h3⟩
    · rintro ⟨x, n, h1, h2, h3⟩
      exact ⟨x, n, h1, h2, h3, by simpa using h3⟩
  rwa [e] at hΩ

theorem gcFundC_holds : GcFundC := by
  intro D X Y u h
  obtain ⟨ρ, ⟨γ, κ, rfl⟩, -⟩ := Y.colReps u h
  obtain ⟨Ω, hΩ⟩ := nocol_fund_exists Y u ρ
  rw [nocolEqC_holds D X Y u ρ] at hΩ
  rw [gcConjC_holds D X u Y.hK γ ((Y.cs u).h ρ) κ]
  exact ⟨_, isSFund_conj X _ Ω hΩ _⟩

end Formalism.L2.SG.Pf.IdMeet
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfStabNFinal
section
namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.BasicNotions Formalism.L2.SG.Full

theorem stabilizer_of_neat_level
    (hN : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized →
      Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u Y.hK) : StabNC :=
  stabNC_of lattice_stabilizer_holds flag_stabilizer_holds (orthogonal_stabilizer_of_neat hN)

end Formalism.L2.SG.Pf.RegroupPf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfTermCarAll
section
namespace Formalism.L2.SG.Pf.RegroupPf

theorem term_carrier_holds : TermCarC :=
  termCarC_of rational_isomorphism_holds reduction_mod_g_holds frame_congruence_holds

end Formalism.L2.SG.Pf.RegroupPf
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameIotaA
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFrameIota

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Proj

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem hT_span_zero (e : Fin r → S.V) (v : S.V) (h : ∀ b, S.hT (e b) v = 0) :
    ∀ x ∈ Submodule.span E (Set.range e), S.hT x v = 0 := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    exact h b
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx, smul_zero]

theorem proj_exists (Λ : Submodule (𝓞 E) S.V) (hL : Submodule.IsLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {T' : E} (F' : LFlag S r T') :
    ∃ u : Fin r → S.V, ∀ l ∈ Λ, l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ Lrep Λ F' := by
  obtain ⟨ρ, hρX, hρid⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_retract Λ hL.fg (Xsp F')
  have li := F'.fl.e_indep
  have hmem : ∀ y : Λ, ((ρ y : Λ) : S.V) ∈ Submodule.span E (Set.range F'.fl.e) := fun y => hρX y

  let co : Fin r → Λ →ₗ[𝓞 E] E := fun a =>
    { toFun := fun y => li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a
      map_add' := fun y y' => by
        have e : (⟨((ρ (y + y') : Λ) : S.V), hmem (y + y')⟩ : Submodule.span E (Set.range F'.fl.e)) =
            ⟨((ρ y : Λ) : S.V), hmem y⟩ + ⟨((ρ y' : Λ) : S.V), hmem y'⟩ :=
          Subtype.ext (by simp only [map_add, Submodule.coe_add])
        rw [e, map_add, Finsupp.add_apply]
      map_smul' := fun c y => by
        have e : (⟨((ρ (c • y) : Λ) : S.V), hmem (c • y)⟩ : Submodule.span E (Set.range F'.fl.e)) =
            (algebraMap (𝓞 E) E c) • ⟨((ρ y : Λ) : S.V), hmem y⟩ :=
          Subtype.ext (by
            show ((ρ (c • y) : Λ) : S.V) = (algebraMap (𝓞 E) E c) • ((ρ y : Λ) : S.V)
            rw [LinearMap.map_smul, Submodule.coe_smul, algebraMap_smul])
        rw [e, LinearMap.map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
  have hco : ∀ a y, co a y = li.repr ⟨((ρ y : Λ) : S.V), hmem y⟩ a := fun _ _ => rfl
  have hexp : ∀ y : Λ, ((ρ y : Λ) : S.V) = ∑ a, co a y • F'.fl.e a := by
    intro y
    have h := li.linearCombination_repr ⟨((ρ y : Λ) : S.V), hmem y⟩
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ (fun i (c : E) => c • F'.fl.e i) (fun i => zero_smul E _)] at h
    rw [← h]
    rfl
  have hR := fun a => PI.UnitaryGroupMassFormula.BetaModX.Iota.riesz S.hT S.herm S.nondeg Λ hL.fg hL.span_eq_top (co a)
  choose u hu using hR

  have hdual : ∀ a b, S.hT (F'.fl.e b) (u a) = if a = b then 1 else 0 := by
    intro a b
    obtain ⟨d, hd0, hdΛ⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.exists_smul_mem Λ hL.span_eq_top (F'.fl.e b)
    have hdE : ((d : 𝓞 E) : E) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0
    have hdX : d • F'.fl.e b ∈ Xsp F' := by
      rw [← algebraMap_smul E d]
      exact (Xsp F').smul_mem _ (Submodule.subset_span ⟨b, rfl⟩)
    have hρd : ρ ⟨d • F'.fl.e b, hdΛ⟩ = ⟨d • F'.fl.e b, hdΛ⟩ := hρid _ hdX
    have hrep : co a ⟨d • F'.fl.e b, hdΛ⟩ = (d : E) * (if b = a then 1 else 0) := by
      rw [hco]
      have e : (⟨((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V), hmem _⟩ : Submodule.span E (Set.range F'.fl.e)) =
          ((d : 𝓞 E) : E) • ⟨F'.fl.e b, Submodule.subset_span ⟨b, rfl⟩⟩ :=
        Subtype.ext (by
          show ((ρ ⟨d • F'.fl.e b, hdΛ⟩ : Λ) : S.V) = ((d : 𝓞 E) : E) • F'.fl.e b
          rw [hρd]
          exact (algebraMap_smul E d _).symm)
      rw [e, LinearMap.map_smul, li.repr_eq_single b _ rfl, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
    have h1 := hu a (d • F'.fl.e b) hdΛ
    rw [hrep, ← algebraMap_smul E d, LinearMap.map_smul, smul_eq_mul] at h1
    have h2 : S.hT (u a) (F'.fl.e b) = if b = a then 1 else 0 := mul_left_cancel₀ hdE h1
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'', h2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (Ne.symm hab), if_neg hab, star_zero]
  refine ⟨u, fun l hl => ⟨?_, ?_⟩⟩
  ·
    refine Λ.sub_mem hl ?_
    have hU' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hU
    rw [← hU', Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
    intro y hy
    have hval : S.hT y (∑ a, S.hT (F'.fl.e a) l • u a) = S.hT ((ρ ⟨y, hy⟩ : Λ) : S.V) l := by
      rw [hexp, map_sum, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.map_smul, smul_eq_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        PI.UnitaryGroupMassFormula.BetaModX.Iota.herm'' (u a) y, hu a y hy, starRingEnd_apply, mul_comm]
    rw [hval]
    obtain ⟨o, ho⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.int_val hU (ρ ⟨y, hy⟩).2 hl
    rw [← ho, Submodule.mem_one]
    exact ⟨o, rfl⟩
  ·
    show l - ∑ a, S.hT (F'.fl.e a) l • u a ∈ orth S (Xsp F')
    rw [PI.UnitaryGroupMassFormula.BetaModX.Iota.mem_orth'']
    refine hT_span_zero F'.fl.e _ fun b => ?_
    rw [map_sub, map_sum]
    simp only [LinearMap.map_smul, smul_eq_mul, hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, sub_self]

end Proj

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem glob_beta {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' F'' : LFlag (VS D) D.R.rS T') (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hF : FixedHyp D Λ F) (hc' : IsFixedConv Λ (gS D) F') (hc'' : IsFixedConv Λ (gS D) F'')
    (ha' : IsAdmissible Λ (gS D) F F') (ha'' : IsAdmissible Λ (gS D) F F'')
    (hP : IsPair Λ F F' F'' β (gS D)) :
    ∀ w ∈ Lrep Λ F', β w - w ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
  intro w hw
  have hg : gS D ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨l, hl, hlw⟩ := PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_gen Λ hF.1 hF.2.1 (gS D) hg F F' hF.2.2.2 ha' w hw
  have h2 := (hP.2.2.2 w hw l hl).1 hlw
  have hle : ∀ F₁ : LFlag (VS D) D.R.rS T', IsAdmissible Λ (gS D) F F₁ → IsFixedConv Λ (gS D) F₁ →
      NgX Λ (gS D) F F₁ ≤ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ⊔ XLam Λ F := by
    intro F₁ ha hc
    unfold NgX
    exact sup_le le_rfl (Formalism.L2.SG.Pf.Act.xlam_le Λ (gS D) ha hF.2.2.2 hc)
  have e : β w - w = (l - w) - (l - β w) := by abel
  rw [e]
  exact Submodule.sub_mem _ (hle F' ha' hc' hlw) (hle F'' ha'' hc'' h2)

end D7

end Formalism.L2.SG.Pf.ScalarFrameIota
end
end

