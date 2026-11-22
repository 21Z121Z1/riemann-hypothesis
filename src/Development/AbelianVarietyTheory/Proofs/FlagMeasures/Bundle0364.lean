import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0355
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.FlagUnipotentLattices.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0344
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0358
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoprimeProjectionAdelicLatticeIntoColumns
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.Proj

section Helpers

open Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.Pf.Level Formalism.L2.SG.Pf

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

def tInv : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F :=
  Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((((D.mem u).A.T : ℕ) : X.B.I.E)⁻¹)

def pc : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I :=
  prA X + (hAlin X (incl X.B.I (X.zR u))).smulRight (tInv X u • incl X.B.I (X.zR u))

theorem pc_apply (y : VA X.B.I) : pc X u y =
    prA X y + hA X.B.I (incl X.B.I (X.zR u)) y • (tInv X u • incl X.B.I (X.zR u)) := by
  simp [pc, hAlin_apply]

theorem T_mul_tInv : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * tInv X u = 1 := by
  have h0 : (((D.mem u).A.T : ℕ) : X.B.I.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have h1 : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((D.mem u).A.T : ℕ) : X.B.I.E) := (map_natCast _ _).symm
  rw [h1, tInv, ← map_mul, mul_inv_cancel₀ h0, map_one]

theorem T_smul_pc (y : VA X.B.I) :
    (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y =
      (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • prA X y +
        hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u) := by
  rw [pc_apply, smul_add, smul_smul, smul_smul, mul_right_comm, T_mul_tInv, one_mul]

theorem adelicHermitian_anisotropic_self_eq_neg_norm : hA X.B.I (incl X.B.I (X.zR u)) (incl X.B.I (X.zR u)) =
    -(((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
  rw [HidaSetting.zR, hA_crd, X.zu_norm]
  simp

theorem hA_z_e (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.zR u)) (incl X.B.I (X.eR a)) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u)
  rw [(X.zu_orth u a).1, map_zero] at h
  rw [HidaSetting.zR, HidaSetting.eR, hA_crd, ← h]
  simp

theorem hA_z_f (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.zR u)) (incl X.B.I (X.fR a)) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u)
  rw [(X.zu_orth u a).2, map_zero] at h
  rw [HidaSetting.zR, HidaSetting.fR, hA_crd, ← h]
  simp

theorem adelicHermitian_hyperbolicE_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [HidaSetting.zR, HidaSetting.eR, hA_crd, (X.zu_orth u a).1]
  simp

theorem adelicHermitian_hyperbolicF_anisotropic_eq_zero (a : Fin D.R.rS) : hA X.B.I (incl X.B.I (X.fR a)) (incl X.B.I (X.zR u)) = 0 := by
  rw [HidaSetting.zR, HidaSetting.fR, hA_crd, (X.zu_orth u a).2]
  simp

theorem pc_e (a : Fin D.R.rS) : pc X u (incl X.B.I (X.eR a)) = 0 := by
  rw [pc_apply, prA_e, hA_z_e]; simp

theorem pc_f (a : Fin D.R.rS) : pc X u (incl X.B.I (X.fR a)) = 0 := by
  rw [pc_apply, prA_f, hA_z_f]; simp

theorem orthogonalProjection_anisotropic_eq_zero : pc X u (incl X.B.I (X.zR u)) = 0 := by
  rw [pc_apply, prA_fix X _ (adelicHermitian_hyperbolicE_anisotropic_eq_zero X u) (adelicHermitian_hyperbolicF_anisotropic_eq_zero X u), adelicHermitian_anisotropic_self_eq_neg_norm, smul_smul, neg_mul, T_mul_tInv]
  simp

theorem zR_mem : X.zR u ∈ X.B.I.L := by
  refine (X.L_eq _).2 ?_
  show toV X (X.crd (X.zu u)) ∈ (VS D).L0
  rw [toV_crd]
  exact Lb_le X (X.zu_Lb u)

theorem hE_z_int {x : Fin X.B.I.n → X.B.I.E} (hx : x ∈ X.B.I.L) :
    hE X (X.zR u) x ∈ (algebraMap (𝓞 X.B.I.E) X.B.I.E).range := by
  have hv : toV X x ∈ (VS D).L0 := (X.L_eq x).1 hx
  have hz : X.zu u ∈ (VS D).L0 := Lb_le X (X.zu_Lb u)
  have hd : toV X x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT (VS D).L0 := by
    rw [(VS D).baseLattice_isUnimodular]; exact hv
  have h2 : (VS D).hT (X.zu u) (toV X x) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) :=
    (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hd (X.zu u)) hz
  obtain ⟨b, hb⟩ := Submodule.mem_one.1 h2
  have e : hE X (X.zR u) x = X.ιE.symm ((VS D).hT (X.zu u) (toV X x)) := by
    rw [← toV_crd X (X.zu u), ← iota_hE, RingEquiv.symm_apply_apply]
    rfl
  rw [e, ← hb]
  exact ⟨⟨_, (NumberField.RingOfIntegers.isIntegral_coe b).map
      (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩, rfl⟩

theorem T_pc_Lf (y : VA X.B.I) (hy : y ∈ X.B.I.Lf) :
    (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y ∈ X.B.I.Lf := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    show (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u (incl X.B.I x) ∈ X.B.I.Lf
    rw [T_smul_pc]
    refine add_mem (natsmul_mem X _ (prA_Lf X _ (incl_mem_Lf X _ x.2))) ?_
    obtain ⟨a, ha⟩ := hE_z_int X u x.2
    rw [hA_incl, show Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.zR u) (x : Fin X.B.I.n → X.B.I.E) = hE X (X.zR u) x from rfl,
      ← ha, ← incl_smul]
    refine incl_mem_Lf X _ ?_
    have := X.B.I.L.smul_mem a (zR_mem X u)
    rwa [← IsScalarTower.algebraMap_smul X.B.I.E a] at this
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, smul_add]; exact add_mem hy hz
  | smul c y _ hy =>
    rw [Subring.smul_def, map_smul, smul_comm]
    exact X.B.I.Lf.smul_mem c hy

theorem inAt_add {x y : VA X.B.I} (hx : InAt X.B.I X.B.g X.B.g x) (hy : InAt X.B.I X.B.g X.B.g y) :
    InAt X.B.I X.B.g X.B.g (x + y) := by
  obtain ⟨c, hc, hcx⟩ := hx
  obtain ⟨d, hd, hdy⟩ := hy
  refine ⟨c * d, Nat.coprime_mul_iff_left.2 ⟨hc, hd⟩, ?_⟩
  have e : (((c * d : ℕ)) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (x + y) =
      (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) +
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y) := by
    rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)]
  rw [e]
  exact add_mem (natsmul_mem X _ hcx) (natsmul_mem X _ hdy)

theorem inAt_neg {x : VA X.B.I} (hx : InAt X.B.I X.B.g X.B.g x) : InAt X.B.I X.B.g X.B.g (-x) := by
  obtain ⟨c, hc, hcx⟩ := hx
  exact ⟨c, hc, by rw [smul_neg]; exact neg_mem hcx⟩

theorem inAt_natsmul (t : ℕ) {x : VA X.B.I} (hx : InAt X.B.I X.B.g X.B.g x) :
    InAt X.B.I X.B.g X.B.g ((t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x) := by
  obtain ⟨c, hc, hcx⟩ := hx
  exact ⟨c, hc, by rw [smul_comm]; exact natsmul_mem X _ hcx⟩

theorem inAt_of_mem {x : VA X.B.I} (hx : x ∈ mL X.B.I X.B.g) : InAt X.B.I X.B.g X.B.g x :=
  ⟨1, Nat.coprime_one_left _, by simpa using hx⟩

theorem inAt_sum {ι : Type} (s : Finset ι) (x : ι → VA X.B.I)
    (h : ∀ i ∈ s, InAt X.B.I X.B.g X.B.g (x i)) : InAt X.B.I X.B.g X.B.g (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact inAt_of_mem X (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inAt_add X (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem T_sub_mem (hT : (D.mem u).A.T ≡ 1 [MOD X.B.g]) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y - y ∈ mL X.B.I X.B.g := by
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd.1 hT.symm)
  have hg : (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y ∈ mL X.B.I X.B.g := unitaryCongruence.smul_mem_mL X.B.I hy
  have e : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y - y =
      k • ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y) := by
    rw [natsmul_eq, natsmul_eq, ← natCast_zsmul, ← natCast_zsmul y X.B.g, smul_smul, mul_comm k, ← hk, sub_smul, Nat.cast_one, one_smul]
  rw [e]
  exact zsmul_mem hg k

theorem T_pc_sub_mem (hT : (D.mem u).A.T ≡ 1 [MOD X.B.g]) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf)
    (hef : ∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧
      InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a)))
    (hz : InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u))) :
    (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y - y ∈ mL X.B.I X.B.g := by
  have hW : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y - y ∈ X.B.I.Lf :=
    sub_mem (T_pc_Lf X u y hy) hy
  have e : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y - y =
      ((((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • y - y) +
      (-((((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          ∑ a, hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a)) +
        (-((((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) •
          ∑ a, hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) +
        hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u))) := by
    rw [T_smul_pc, prA_apply, smul_sub, smul_sub]
    abel
  have hin : InAt X.B.I X.B.g X.B.g
      ((((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • pc X u y - y) := by
    rw [e]
    exact inAt_add X (inAt_of_mem X (T_sub_mem X u hT hy))
      (inAt_add X (inAt_neg X (inAt_natsmul X _ (inAt_sum X _ _ fun a _ => (hef a).2)))
        (inAt_add X (inAt_neg X (inAt_natsmul X _ (inAt_sum X _ _ fun a _ => (hef a).1))) hz))
  obtain ⟨m, hm, hmW⟩ := hin
  exact bez_vec X (mL X.B.I X.B.g) le_rfl hW hm hmW

theorem frame_expand (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (Q : Matrix (Fin X.B.I.n) (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) X.B.I.E)
    (Qi : Matrix (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) (Fin X.B.I.n) X.B.I.E)
    (hQ : Q * Qi = 1) (hq : ∀ j i, Q i (Sum.inl j) = X.crd (qFr wt j) i)
    (he : ∀ a i, Q i (Sum.inr (Sum.inl a)) = X.eR a i)
    (hf : ∀ a i, Q i (Sum.inr (Sum.inr (Sum.inl a))) = X.fR a i)
    (hz : ∀ i, Q i (Sum.inr (Sum.inr (Sum.inr ()))) = X.zR u i) (y : VA X.B.I) :
    ∃ (w : Fin (D.R.N 0) → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (s t : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
      (r : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      y = ∑ j, w j • qA X wt j + (∑ a, s a • incl X.B.I (X.eR a) + (∑ a, t a • incl X.B.I (X.fR a) +
        r • incl X.B.I (X.zR u))) := by
  let f : X.B.I.E →+* X.B.I.E ⊗[X.B.I.F] Af X.B.I.F := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
  set v := (Qi.map f) *ᵥ y with hv
  have h1 : (Q.map f) *ᵥ v = y := by
    rw [hv, mulVec_mulVec, ← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero f) (map_one f), one_mulVec]
  refine ⟨fun j => v (Sum.inl j), fun a => v (Sum.inr (Sum.inl a)), fun a => v (Sum.inr (Sum.inr (Sum.inl a))),
    v (Sum.inr (Sum.inr (Sum.inr ()))), ?_⟩
  conv_lhs => rw [← h1]
  funext i
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, Matrix.map_apply, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, hq, he, hf, hz, qA, incl, Fintype.sum_unique]
  simp only [mul_comm]
  rfl

end Helpers

end GlobalTheory.St.G.Proj

theorem GlobalTheory.St.G.g_proj : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → ∃ (c : ℕ) (p : VA X.B.I →ₗ[X.B.I.E ⊗[X.B.I.F] Af X.B.I.F] VA X.B.I), c ≡ 1 [MOD X.B.g] ∧ (∀ y, ∃ x, p y = embA X wt ιA x) ∧ (∀ x, p (embA X wt ιA x) = embA X wt ιA x) ∧ (∀ y ∈ X.B.I.Lf, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y ∈ X.B.I.Lf) ∧ (∀ a, p (incl X.B.I (X.eR a)) = 0 ∧ p (incl X.B.I (X.fR a)) = 0) ∧ p (incl X.B.I (X.zR u)) = 0 ∧ ∀ y ∈ X.B.I.Lf, (∀ a, InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.eR a)) y • incl X.B.I (X.fR a)) ∧ InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.fR a)) y • incl X.B.I (X.eR a))) → InAt X.B.I X.B.g X.B.g (hA X.B.I (incl X.B.I (X.zR u)) y • incl X.B.I (X.zR u)) → (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • p y - y ∈ mL X.B.I X.B.g := by
  intro D X u wt ιA hW hI
  obtain ⟨Q, Qi, G', hQ, -, hq, he, hf, hz, -, -⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  obtain ⟨-, -, -, hef, hzq, -⟩ := GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hI
  have hfix : ∀ x, Proj.pc X u (embA X wt ιA x) = embA X wt ιA x := fun x => by
    rw [Proj.pc_apply, Formalism.L2.SG.Pf.Level.prA_fix X _ (fun a => (hef x a).1) (fun a => (hef x a).2), hzq]
    simp
  have hT : (D.mem u).A.T ≡ 1 [MOD X.B.g] := by
    rw [X.g_eq]
    exact D.T_modEq_of_dvd u (dvd_trans (dvd_pow_self _ two_ne_zero) D.gg_dvd_modT)
  refine ⟨(D.mem u).A.T, Proj.pc X u, hT, ?_, hfix, Proj.T_pc_Lf X u,
    fun a => ⟨Proj.pc_e X u a, Proj.pc_f X u a⟩, Proj.orthogonalProjection_anisotropic_eq_zero X u, ?_⟩
  · intro y
    obtain ⟨w, s, t, r, rfl⟩ := Proj.frame_expand X u wt Q Qi hQ hq he hf hz y
    refine ⟨fun j => ιA (w j), ?_⟩
    have hqj : ∀ j, Proj.pc X u (qA X wt j) = qA X wt j := fun j => by
      have h := hfix (Pi.single j 1)
      have e : embA X wt ιA (Pi.single j 1) = qA X wt j := by
        simp [embA, Pi.single_apply]
      rwa [e] at h
    simp only [map_add, map_sum, map_smul, Proj.pc_e, Proj.pc_f, Proj.orthogonalProjection_anisotropic_eq_zero, hqj, smul_zero,
      Finset.sum_const_zero, add_zero]
    simp [embA]
  · intro y hy h1 h2
    exact Proj.T_pc_sub_mem X u hT hy h1 h2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsZEquivGramBoundedMinors
section
open NumberField Module Matrix Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Classical

namespace GlobalTheory.ReducedGram

open NumberField Module Matrix in
open scoped Classical in
private lemma upperUnitriangular_mul_apply_of_le {R : Type} [CommRing R] {N : ℕ}
    (A B : Matrix (Fin N) (Fin N) R) (hA0 : ∀ i j, j < i → A i j = 0) (hA1 : ∀ i, A i i = 1)
    (hB0 : ∀ i j, j < i → B i j = 0) (hB1 : ∀ i, B i i = 1) {i j : Fin N} (h : j ≤ i) :
    (A * B) i j = if i = j then 1 else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · split_ifs with hij
    · subst hij
      rw [hA1, hB1, one_mul]
    · rw [hA1, one_mul]
      exact hB0 i j (lt_of_le_of_ne h (fun e => hij e.symm))
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hki | hik
    · rw [hA0 i k hki, zero_mul]
    · rw [hB0 k j (lt_of_le_of_lt h hik), mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

open NumberField Module Matrix in
open scoped Classical in
private lemma exists_integral_unitriangular_reduction {K : Type} [Field K] [NumberField K]
    (hK : ∀ w : InfinitePlace K, w.IsComplex) {N : ℕ} (V : Matrix (Fin N) (Fin N) K)
    (hV0 : ∀ i j, j < i → V i j = 0) (hV1 : ∀ i, V i i = 1) :
    ∃ m : Matrix (Fin N) (Fin N) (𝓞 K), (∀ i j, j < i → m i j = 0) ∧ (∀ i, m i i = 1) ∧
      ∀ (τ : K →+* ℂ) (i j : Fin N), ‖τ ((V * m.map (fun x : 𝓞 K => (x : K))) i j)‖ ≤
        max 1 (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) := by
  set c := Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) with hc_def
  let φ : K →+* (InfinitePlace K → ℂ) := Pi.ringHom fun w => w.embedding
  let O : Subring (InfinitePlace K → ℂ) := (φ.comp (algebraMap (𝓞 K) K)).range
  let FF : Set (InfinitePlace K → ℂ) := {x | ∀ w, ‖x w‖ ≤ c}
  have hφ : ∀ (x : K) (w : InfinitePlace K), φ x w = w.embedding x := fun _ _ => rfl
  have hcov : ∀ x : InfinitePlace K → ℂ, ∃ a ∈ O, x + a ∈ FF := by
    intro x
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.coveringO_holds K hK (fun w => -x w)
    refine ⟨φ (a : K), ⟨a, rfl⟩, fun w => ?_⟩
    have e : (x + φ (a : K)) w = -(-x w - w.embedding (a : K)) := by
      rw [Pi.add_apply, hφ]
      ring
    rw [e, norm_neg]
    exact ha w
  obtain ⟨n, hn1, hn0, hnO, hnF⟩ := _root_.Formalism.HermitianLatticeCounting.P.unitriangularReduction (InfinitePlace K → ℂ) O FF N (V.map φ) hcov
    (fun i => by simp [hV1]) (fun i j h => by simp [hV0 i j h])
  have hlift : ∀ i j, ∃ a : 𝓞 K, φ (a : K) = n i j := by
    intro i j
    obtain ⟨a, ha⟩ := hnO i j
    exact ⟨a, ha⟩
  choose m₀ hm₀ using hlift
  let m : Matrix (Fin N) (Fin N) (𝓞 K) := Matrix.of m₀
  have hm : ∀ i j, φ (m i j : K) = n i j := hm₀
  have hinj : ∀ a b : 𝓞 K, φ (a : K) = φ (b : K) → a = b := fun a b h =>
    RingOfIntegers.coe_injective (φ.injective h)
  have hm0 : ∀ i j, j < i → m i j = 0 := fun i j h =>
    hinj _ _ (by rw [hm, hn0 i j h]; simp)
  have hm1 : ∀ i, m i i = 1 := fun i => hinj _ _ (by rw [hm, hn1]; simp)
  refine ⟨m, hm0, hm1, ?_⟩
  have hn : n = (m.map (fun x : 𝓞 K => (x : K))).map φ := by
    exact Matrix.ext fun i j => (hm i j).symm
  have hprod : V.map φ * n = (V * m.map (fun x : 𝓞 K => (x : K))).map φ := by
    rw [hn, Matrix.map_mul]
  have key : ∀ (i j : Fin N) (w : InfinitePlace K),
      ‖w.embedding ((V * m.map (fun x : 𝓞 K => (x : K))) i j)‖ ≤ max 1 c := by
    intro i j w
    rcases lt_or_ge i j with hij | hji
    · have h := hnF i j hij w
      rw [hprod, Matrix.map_apply, hφ] at h
      exact le_max_of_le_right h
    · rw [upperUnitriangular_mul_apply_of_le V _ hV0 hV1
        (fun a b h => by simp [hm0 a b h]) (fun a => by simp [hm1 a]) hji]
      split_ifs <;> simp
  intro τ i j
  rw [← InfinitePlace.apply, ← InfinitePlace.norm_embedding_eq]
  exact key i j _

open NumberField Module Matrix in
open scoped Classical in
private lemma det_submatrix_mul_diagonal {R : Type} [CommRing R] {N t : ℕ}
    (X : Matrix (Fin N) (Fin N) R) (s : Fin N → R) (I J : Fin t → Fin N) :
    ((X * diagonal s).submatrix I J).det = (X.submatrix I J).det * ∏ k, s (J k) := by
  have hsub : (X * diagonal s).submatrix I J = X.submatrix I J * diagonal (fun k => s (J k)) := by
    ext a b
    simp [Matrix.mul_diagonal]
  rw [hsub, det_mul, det_diagonal]

open NumberField Module Matrix in
open scoped Classical in

theorem _root_.GlobalTheory.ReducedGram.exists_reduced : ∀ (K : Type) [Field K] [NumberField K],
    (∀ w : InfinitePlace K, w.IsComplex) → ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (p : _root_.Formalism.MainNotions.S.Point K (r + 1)), _root_.Formalism.MainNotions.S.IsInCell (_root_.Formalism.MainNotions.S.ZhatOM Z) p →
    ∃ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) K, _root_.Formalism.MainNotions.S.Lat.ZEquiv Z Z₂ ∧
      ∀ (τ : K →+* ℂ) (t : ℕ) (I J : Fin t → Fin (r + 1)),
        ‖τ (Z₂.submatrix I J).det‖ ≤ 4 ^ (r + 1) * (((r + 1).factorial : ℕ) : ℝ) ^ 2 *
          (Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ))) ^ (2 * (r + 1)) *
          ∏ l ∈ Finset.Icc 1 (r + 1),
            (max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ * max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖⁻¹) := by
  intro K _ _ hK r Z p hcell
  set c := Real.sqrt (finrank ℚ K) * |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) with hc_def
  have hc : 1 ≤ c := by
    have h1 : (1 : ℝ) ≤ Real.sqrt (finrank ℚ K) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast Module.finrank_pos
    have h2 : (1 : ℝ) ≤ |(discr K : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) := by
      apply Real.one_le_rpow
      · have hd : discr K ≠ 0 := discr_ne_zero K
        have : (1 : ℤ) ≤ |discr K| := Int.one_le_abs hd
        exact_mod_cast this
      · positivity
    nlinarith
  have hmax : max 1 c = c := max_eq_right hc
  unfold _root_.Formalism.MainNotions.S.IsInCell at hcell
  obtain ⟨L, U, hL, hU, hZ⟩ := hcell
  unfold _root_.Formalism.MainNotions.S.IsLoUni at hL
  unfold _root_.Formalism.MainNotions.S.IsUpUni at hU
  set P := _root_.Formalism.MainNotions.S.ptMat p with hP
  let s : Fin (r + 1) → K := fun b => (-1) ^ (r - (b : ℕ))
  have hss : ∀ b, s b * s b = 1 := by
    intro b
    simp only [s, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hDD : diagonal s * diagonal s = 1 := by
    rw [diagonal_mul_diagonal]
    simp only [hss]
    exact diagonal_one
  have hZD : Z = _root_.Formalism.MainNotions.S.ZhatOM Z * diagonal s := by
    ext a b
    simp only [_root_.Formalism.MainNotions.S.ZhatOM, mul_diagonal, s]
    linear_combination (-Z a b) * hss b
  have hZD' : Z = L * P * U * diagonal s := by
    rw [← hZ]
    exact hZD
  let V := diagonal s * U * diagonal s
  have hVapp : ∀ i j, V i j = s i * U i j * s j := by
    intro i j
    simp [V, mul_diagonal, diagonal_mul]
  have hV0 : ∀ i j, j < i → V i j = 0 := fun i j h => by rw [hVapp, (hU i j).1 h]; ring
  have hV1 : ∀ i, V i i = 1 := fun i => by
    rw [hVapp, (hU i i).2 rfl, mul_one, hss]
  have hZeq : Z = L * (P * diagonal s) * V := by
    rw [hZD']
    calc L * P * U * diagonal s = L * P * (diagonal s * diagonal s) * U * diagonal s := by
          rw [hDD, Matrix.mul_one]
      _ = L * (P * diagonal s) * V := by simp only [V, Matrix.mul_assoc]
  obtain ⟨m, hm0, hm1, hmb⟩ := exists_integral_unitriangular_reduction hK V hV0 hV1
  obtain ⟨m', hm'0, hm'1, hm'b⟩ := exists_integral_unitriangular_reduction hK Lᵀ
    (fun i j h => by rw [transpose_apply]; exact (hL j i).1 h)
    (fun i => by rw [transpose_apply]; exact (hL i i).2 rfl)
  rw [hmax] at hmb hm'b
  let A := m'ᵀ.map (fun x : 𝓞 K => (x : K)) * L
  let B := V * m.map (fun x : 𝓞 K => (x : K))
  let W := P * diagonal s
  refine ⟨A * W * B, ⟨m'ᵀ, m, fun a b h => hm'0 b a h, fun a => hm'1 a, hm0, hm1, ?_⟩, ?_⟩
  · simp only [A, B, W]
    rw [hZeq]
    simp only [Matrix.mul_assoc, transpose_map]
  intro τ t I J
  have hmin : ∀ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : ℕ) (I J : Fin t → Fin (r + 1)),
      ((X.map τ).submatrix I J).det = τ ((X.submatrix I J).det) := by
    intro X t I J
    rw [RingHom.map_det]
    rfl
  have hsign : ∀ (t : ℕ) (J : Fin t → Fin (r + 1)), ‖τ (∏ k, s (J k))‖ = 1 := by
    intro t J
    rw [map_prod, norm_prod]
    simp [s]
  have hA : ∀ i j, ‖(A.map τ) i j‖ ≤ c := by
    intro i j
    have hAt : A = (Lᵀ * m'.map (fun x : 𝓞 K => (x : K)))ᵀ := by
      simp only [A, transpose_mul, transpose_transpose, transpose_map]
    rw [Matrix.map_apply, hAt, transpose_apply]
    exact hm'b τ j i
  have hB : ∀ i j, ‖(B.map τ) i j‖ ≤ c := fun i j => hmb τ i j
  set Pb := ∏ l ∈ Finset.range (r + 1), _root_.GlobalTheory.LoopC.CovTerm.gg2 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P (l + 1))‖ with hPb
  have hW : ∀ (t : ℕ) (I J : Fin t → Fin (r + 1)), ‖((W.map τ).submatrix I J).det‖ ≤ Pb := by
    intro t I J
    rw [hmin, det_submatrix_mul_diagonal, map_mul, norm_mul, hsign, mul_one, ← hmin]
    exact _root_.GlobalTheory.LoopC.CovTerm.minor_pt_le τ p t I J
  have hbound := _root_.Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.minorBound (r + 1) (A.map τ) (W.map τ) (B.map τ) c Pb hc hA hB hW t I J
  have hlead : ∀ l, ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ = ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P l)‖ := by
    intro l
    unfold _root_.Formalism.MainNotions.S.leadMinorE
    split_ifs with hl
    · rw [hZD', det_submatrix_mul_diagonal, map_mul, norm_mul, hsign, mul_one,
        _root_.Formalism.HermitianLatticeCounting.P.leadingMinorTriangularInvariant K (r + 1) l hl L P U (fun i => (hL i i).2 rfl) (fun i j h => (hL i j).1 h)
          (fun i => (hU i i).2 rfl) (fun i j h => (hU i j).1 h)]
    · rfl
  have hPbeq : Pb = ∏ l ∈ Finset.Icc 1 (r + 1),
      (max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖ * max 1 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE Z l)‖⁻¹) := by
    rw [hPb, Finset.range_eq_Ico,
      Finset.prod_Ico_add' (fun l => _root_.GlobalTheory.LoopC.CovTerm.gg2 ‖τ (_root_.Formalism.MainNotions.S.leadMinorE P l)‖) 0 (r + 1) 1,
      zero_add, Finset.Ico_add_one_right_eq_Icc]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [hlead]
    rfl
  rw [← hmin, Matrix.map_mul, Matrix.map_mul, ← hPbeq]
  exact hbound

end GlobalTheory.ReducedGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMatchHolds
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem genusMatch_holds : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), GenusMatch D F := by
  intro D F X u wt ιA hW hA
  obtain ⟨hT, -, -, hdeg, -, hH, hdet⟩ := record_facts D u
  have hM := (GlobalTheory.T.transported_column_lattice_has_level_and_dual_generator D X u wt hW).1
  have hL := stepLevel_tLat (S := (F u).cls0.lev)
  have hE := (GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame D X u wt ιA hW hA).1
  obtain ⟨h, hh⟩ := GlobalTheory.T.hermitianLattices_level_one_genus D.host.F D.host.E D.sp.cm (D.R.N 0) _ hH hdet (D.mem u).A.T D.R.f
    (F u).cls0.lev.Lb (Mq wt) (D.mem u).A.T_prime hT hdeg hL hM
  exact ⟨h, fun x => (hh x).trans (hE x)⟩

end GlobalTheory.St.G
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerDatumStableIffIdentificationsCompatibleStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerDatum_stable_iff_identifications_compatible : ∀ (D : D7) (T T' : D.host.E) (F0 F : LFlag (VS D) D.R.rS T) (F0' F' : LFlag (VS D) D.R.rS T') (lam lam' Λ : LV D) (γ g h b₁ b₂ : GV D), γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → Formalism.HermitianLatticesTheory.gmap γ lam' = lam → Adapt g F0 F → Adapt g (mapLF γ F0') F' → Λ = Formalism.HermitianLatticesTheory.gmap g lam → b₁ ∈ Aut0 F0 lam → b₂ ∈ Aut0 F0' lam' → h ∈ H0 F F' → (∀ x ∈ orth (VS D) (Xsp F), h x - (g * b₁ * g⁻¹) x ∈ Xsp F) → (∀ x ∈ orth (VS D) (Xsp F'), h x - (g * γ * b₂ * γ⁻¹ * g⁻¹) x ∈ Xsp F') → (gdat F F' (Formalism.HermitianLatticesTheory.gmap h Λ) = gdat F F' Λ ↔ IotaCompat lam F0 (mapLF γ F0') (mapLF (b₁ * γ * b₂⁻¹) F0') (b₁ * γ * b₂⁻¹ * γ⁻¹) (gS D)) := by
  first | exact @GlobalTheory.GdatIota.gdat_iff_iotaCompat | exact GlobalTheory.GdatIota.gdat_iff_iotaCompat | (intros; apply GlobalTheory.GdatIota.gdat_iff_iotaCompat <;> assumption)
end

