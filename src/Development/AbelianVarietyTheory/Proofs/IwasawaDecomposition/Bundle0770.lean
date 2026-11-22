import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0746
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0423
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0748
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0741
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0700
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0732
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0697
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedSubgroupColumnMatricesEntryZero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PosAgree

open Matrix

variable {k : Type} [CommRing k] {n : ℕ}

theorem vmv_mul_vmv (a α b β : Fin n → k) :
    vecMulVec a α * vecMulVec b β = (α ⬝ᵥ b) • vecMulVec a β := by
  ext i l
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem mul_vmv_mul (A B : Matrix (Fin n) (Fin n) k) (w φ : Fin n → k) :
    A * vecMulVec w φ * B = vecMulVec (A *ᵥ w) (φ ᵥ* B) := by
  ext i l
  simp only [mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m _ => by ring

theorem vecMul_vmv (φ a α : Fin n → k) : φ ᵥ* vecMulVec a α = (φ ⬝ᵥ a) • α := by
  ext i
  simp only [vecMul, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun m _ => by ring

def tU (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : GL (Fin n) k :=
  ⟨1 + vecMulVec v φ, 1 - vecMulVec v φ,
    by simp only [add_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv, h, zero_smul]; abel,
    by simp only [sub_mul, mul_add, one_mul, mul_one, vmv_mul_vmv, h, zero_smul]; abel⟩

theorem tU_val (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : (tU v φ h).val = 1 + vecMulVec v φ := rfl

theorem tU_inv_val (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) : (tU v φ h)⁻¹.val = 1 - vecMulVec v φ := rfl

theorem conj_val (g : GL (Fin n) k) (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) :
    (g * tU v φ h * g⁻¹).val = 1 + vecMulVec (g.val *ᵥ v) (φ ᵥ* (g⁻¹).val) := by
  rw [Units.val_mul, Units.val_mul, tU_val, mul_add, add_mul, mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    mul_vmv_mul]

theorem tU_mem_unip (v φ : Fin n → k) (h : φ ⬝ᵥ v = 0) (hl : ∀ i l : Fin n, l.val ≤ i.val → v i * φ l = 0) :
    tU v φ h ∈ unip k n := by
  refine ⟨fun i l (hli : l.val < i.val) => ?_, fun i => ?_⟩
  · rw [tU_val, Matrix.add_apply, vecMulVec_apply, hl i l hli.le, one_apply_ne (fun e => by rw [e] at hli; omega), add_zero]
  · rw [tU_val, Matrix.add_apply, vecMulVec_apply, hl i i le_rfl, one_apply_eq, add_zero]

theorem transvection_eq (i j : Fin n) (c : k) :
    transvection i j c = 1 + vecMulVec (Pi.single i c) (Pi.single j 1) := by
  unfold transvection
  congr 1
  ext p q
  simp only [single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

end GlobalTheory.PosAgree

namespace GlobalTheory.PosAgree

open Matrix

variable {k : Type} [CommRing k] {n : ℕ}

theorem sdot (p q : Fin n) (x : k) (h : q ≠ p) : Pi.single q 1 ⬝ᵥ Pi.single p x = 0 := by
  rw [single_dotProduct, Pi.single_apply, if_neg h, mul_zero]

theorem comm_a (p0 p1 pm : Fin n) (h01 : p0 ≠ p1) (h0m : p0 ≠ pm) (h1m : p1 ≠ pm) :
    (tU (Pi.single pm (1 : k)) (Pi.single p0 1) (sdot _ _ _ h0m))⁻¹ *
      (tU (Pi.single p0 1) (Pi.single p1 1) (sdot _ _ _ h01.symm) * tU (Pi.single pm 1) (Pi.single p0 1) (sdot _ _ _ h0m) *
        (tU (Pi.single p0 1) (Pi.single p1 1) (sdot _ _ _ h01.symm))⁻¹) =
      tU (Pi.single pm (-1)) (Pi.single p1 1) (sdot _ _ _ h1m) := by
  apply Units.ext
  simp only [Units.val_mul, tU_val, tU_inv_val, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_dotProduct, Pi.single_apply, h01, h0m, h1m, h01.symm, h0m.symm, h1m.symm,
    if_false, if_true, mul_zero, zero_smul, add_zero, sub_zero, zero_mul, mul_one]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem comm_b (p0 p1 pm : Fin n) (h01 : p0 ≠ p1) (h0m : p0 ≠ pm) (h1m : p1 ≠ pm) (a b : k) :
    tU (Pi.single p0 a) (Pi.single pm 1) (sdot _ _ _ h0m.symm) * tU (Pi.single pm b) (Pi.single p1 1) (sdot _ _ _ h1m) *
      (tU (Pi.single p0 a) (Pi.single pm 1) (sdot _ _ _ h0m.symm))⁻¹ * (tU (Pi.single pm b) (Pi.single p1 1) (sdot _ _ _ h1m))⁻¹ =
      tU (Pi.single p0 (a * b)) (Pi.single p1 1) (sdot _ _ _ h01.symm) := by
  apply Units.ext
  simp only [Units.val_mul, tU_val, tU_inv_val, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, vmv_mul_vmv,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, single_dotProduct, Pi.single_apply, h01, h0m, h1m, h01.symm, h0m.symm, h1m.symm,
    if_false, if_true, mul_zero, zero_smul, add_zero, sub_zero, zero_mul, mul_one]
  ext p q
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all [mul_comm]

end GlobalTheory.PosAgree

namespace GlobalTheory.PosAgree

open Matrix

theorem entry_zero : ∀ (k : Type) [CommRing k], IsField k → ∀ n r : ℕ, 2 ≤ r → r < n → ∀ (H : Subgroup (GL (Fin n) k)) (b : GL (Fin n) k), (∀ u ∈ unip k n, ∀ h ∈ H, u * h * u⁻¹ ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → h.val = colMat v m → h ∈ H) → (∀ (h : GL (Fin n) k) (m : Fin n) (v : Fin n → k), r ≤ (m : ℕ) → v m = 0 → (b * h * b⁻¹).val = colMat v m → h ∈ H) → (∀ i j : Fin n, (i : ℕ) + 1 = j → (j : ℕ) < r → ∃ (c : k) (h : GL (Fin n) k), h.val = Matrix.transvection i j c ∧ h ∉ H) → ∀ a c : Fin n, r ≤ (a : ℕ) → (c : ℕ) < r → b.val a c = 0 := by
  intro k _ hk n r hr hrn H b hU h2 h3 h4 a c ha hc
  classical
  by_contra hne
  have ofVal : ∀ (g h : GL (Fin n) k), g ∈ H → g.val = h.val → h ∈ H := fun g h hg e => (Units.ext e) ▸ hg
  have H4 : ∀ i j : Fin n, i.val + 1 = j.val → j.val < r →
      (∀ x : k, ∃ hx, tU (Pi.single i x) (Pi.single j 1) hx ∈ H) → False := by
    intro i j hij hj hall
    obtain ⟨x, h, hh, hn⟩ := h4 i j hij hj
    obtain ⟨hx, hm⟩ := hall x
    exact hn (ofVal _ _ hm (by rw [tU_val, hh, transvection_eq]))
  let φ : Fin n → k := fun l => b.val a l
  have hrow : φ ᵥ* (b⁻¹).val = Pi.single a 1 := by
    have e : φ = Pi.single a 1 ᵥ* b.val := by
      ext l
      simp [φ, vecMul, single_dotProduct]
    rw [e, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
  have H3 : ∀ w (hw : φ ⬝ᵥ w = 0), tU w φ hw ∈ H := fun w hw =>
    h3 _ a (b.val *ᵥ w) ha hw (by rw [conj_val, hrow]; rfl)
  let S := Finset.univ.filter (fun l : Fin n => φ l ≠ 0)
  have hcS : c ∈ S := by simp [S, φ, hne]
  set j := S.min' ⟨c, hcS⟩ with hjdef
  have hjc : j ≤ c := Finset.min'_le S c hcS
  have hφj : φ j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem S ⟨c, hcS⟩)).2
  have hlow : ∀ l, l < j → φ l = 0 := fun l hl => by
    by_contra h'
    exact absurd (Finset.min'_le S l (by simp [S, h'])) (not_le.mpr hl)
  obtain ⟨t, ht⟩ := hk.mul_inv_cancel hφj
  have hjr : j.val < r := lt_of_le_of_lt (show j.val ≤ c.val from hjc) hc
  let ψ : Fin n → k := fun l => if j < l then φ l * t else 0
  have hψ : ψ ⬝ᵥ Pi.single j 1 = 0 := by simp [ψ, dotProduct_single]
  have hu : tU (Pi.single j 1) ψ hψ ∈ unip k n := tU_mem_unip _ _ _ (fun i l hli => by
    simp only [Pi.single_apply, ψ]
    split_ifs with h1 h2 <;> first | (simp; done) | (have := Fin.lt_def.mp h2; rw [h1] at hli; omega))
  have hvec : φ ᵥ* ((tU (Pi.single j 1) ψ hψ)⁻¹).val = Pi.single j (φ j) := by
    rw [tU_inv_val, vecMul_sub, vecMul_one, vecMul_vmv, dotProduct_single, mul_one]
    ext l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ψ, Pi.single_apply]
    rcases lt_trichotomy l j with hl | hl | hl
    · rw [if_neg (not_lt.mpr hl.le), if_neg hl.ne, hlow l hl]; ring
    · rw [hl]; simp
    · rw [if_pos hl, if_neg hl.ne']; linear_combination (-(φ l)) * ht
  have KEY : ∀ (v : Fin n → k) (hv : Pi.single j 1 ⬝ᵥ v = 0), tU v (Pi.single j 1) hv ∈ H := by
    intro v hv
    have hw : φ ⬝ᵥ (t • (((tU (Pi.single j 1) ψ hψ)⁻¹).val *ᵥ v)) = 0 := by
      rw [dotProduct_smul, dotProduct_mulVec, hvec, single_dotProduct]
      rw [single_dotProduct, one_mul] at hv
      rw [hv, mul_zero, smul_zero]
    refine ofVal _ _ (hU _ hu _ (H3 _ hw)) ?_
    rw [conj_val, hvec, mulVec_smul, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec, tU_val]
    congr 1
    ext p q
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    split_ifs
    · linear_combination (v p) * ht
    · simp
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
  · have hn3 : 3 ≤ n := by omega
    let m0 : Fin n := ⟨n - 1, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    have hm0j : j ≠ m0 := fun e => by
      have := congrArg Fin.val e
      simp [m0] at this
      omega
    have hi1j : j ≠ i1 := fun e => by
      have := congrArg Fin.val e
      simp [i1] at this
      omega
    have hm0i1 : i1 ≠ m0 := fun e => by
      have := congrArg Fin.val e
      simp [m0, i1] at this
      omega
    have hX := KEY (Pi.single m0 1) (sdot _ _ _ hm0j)
    have hu1 : tU (Pi.single j 1) (Pi.single i1 1) (sdot _ _ _ hi1j.symm) ∈ unip k n :=
      tU_mem_unip _ _ _ (fun p q hpq => by
        simp only [Pi.single_apply]
        split_ifs with h1 h2 <;> first | (simp; done) | (subst h1 h2; simp [i1] at hpq; omega))
    have hQ : tU (Pi.single m0 (-1)) (Pi.single i1 1) (sdot _ _ _ hm0i1) ∈ H := by
      have := H.mul_mem (H.inv_mem hX) (hU _ hu1 _ hX)
      exact (congrArg (· ∈ H) (comm_a (k := k) j i1 m0 hi1j hm0j hm0i1)).mp this
    refine H4 j i1 (by simp [i1, hj0]) (by simp [i1]; omega) (fun x => ⟨sdot _ _ _ hi1j.symm, ?_⟩)
    have hP : tU (Pi.single j (-x)) (Pi.single m0 1) (sdot _ _ _ hm0j.symm) ∈ unip k n :=
      tU_mem_unip _ _ _ (fun p q hpq => by
        simp only [Pi.single_apply]
        split_ifs with h1 h2 <;> first | (simp; done) | (subst h1 h2; simp [m0] at hpq; omega))
    have hZ := H.mul_mem (hU _ hP _ hQ) (H.inv_mem hQ)
    exact ofVal _ _ hZ ((congrArg Units.val (comm_b j i1 m0 hi1j hm0j hm0i1 (-x) (-1))).trans
      (by rw [tU_val, tU_val, neg_mul_neg, mul_one]))
  · let i : Fin n := ⟨j.val - 1, by omega⟩
    have hij : j ≠ i := fun e => by
      have := congrArg Fin.val e
      simp [i] at this
      omega
    exact H4 i j (by simp [i]; omega) hjr (fun x => ⟨sdot _ _ _ hij, KEY _ _⟩)

end GlobalTheory.PosAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParameterOfDiscreteSeriesRay
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

set_option maxHeartbeats 4000000 in

private theorem logLam_of_part : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D →
    ∀ (X : DivX D), LamAre Z X → ∀ (i : Fin D.R.m) π (c : A3.fam3.base3.Ix) (e : D.what₂.LL →+* ℂ), e ≠ D.what₂.embLL →
    D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → D.what₂.isot ((i : ℕ) + 1) π ≤ (R.Wp3 i c).comap (Y.mj.eW i) →
    X.logLam ((i : ℕ) + 1) π e = Real.log (R.lam3 i A3.A.μ0 c (InfinitePlace.mk e)) ∧ R.EEp3 c ≠ ⊥ := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost X hX i π c e he hne hle
  have rat := GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost π
  obtain ⟨lab, hl, hv⟩ := hX
  have hov : OverIx Z π (lab π) := hl π ⟨p, fun j => by
    rw [rat j p]
    exact Submodule.map_le_iff_le_comap.1 (hp.1 j)⟩
  have hi := hov i
  rw [rat i (lab π)] at hi
  have hc : c = lab π := GlobalTheory.Mem.R3.ScalarComponentUnique.part_unique R F cG X0 Y hP hH i π c (lab π) hne hle hi
  refine ⟨?_, fun hb => ?_⟩
  · rw [(hv i π e he).1 hne, hc]
    rfl
  · have hW : R.Wp3 i c = ⊥ := by
      refine le_bot_iff.1 (iSup₂_le fun s hs => ?_)
      have hs' : R.EEc s ≤ R.EEp3 c := le_iSup₂_of_le (f := fun s (_ : R.Carries c s) => R.EEc s) s hs le_rfl
      rw [hb] at hs'
      exact absurd (le_bot_iff.1 hs') hs.1
    apply hne
    refine eq_bot_iff.2 fun x hx => ?_
    have h0 : Y.mj.eW i x ∈ R.Wp3 i c := hle hx
    rw [hW] at h0
    have hx0 : Y.mj.eW i x = 0 := (Submodule.mem_bot ℂ).1 h0
    have hn1 := Y.mj.eW_norm i x
    rw [hx0, norm_zero, zero_pow two_ne_zero] at hn1
    have hn : (0 : ℝ) < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have hn2 : ‖x‖ ^ 2 = 0 := (mul_eq_zero.1 hn1.symm).resolve_left hn.ne'
    exact (Submodule.mem_bot ℂ).2 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hn2))

set_option maxHeartbeats 4000000 in

private theorem logLam_twArgs : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0) (a : TwArgs ex t), HostHyp (w.st Z).toD7 → ∀ (X : DivX (w.st Z).toD7), LamAre t.r.Z X →
    letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (w.st Z).toD7.R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (w.st Z).toD7.what₂.LL →+* ℂ), e ≠ (w.st Z).toD7.what₂.embLL → (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro h1 h2 h3 h4 K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a hHost X hX
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  intro i π c e he hne hle
  have hW : Y.mj.eW = t.r.Y.mj.eW := by kexactB eq_of_heq heW
  have hle' : (w.st Z).toD7.what₂.isot ((i : ℕ) + 1) π ≤ (t.r.z.R.Wp3 i c).comap (t.r.Y.mj.eW i) := by
    rw [← hW]
    kexactB hle
  have h := logLam_of_part h1 h2 h3 h4 t.r.z.R t.r.z.F t.r.z.cG _ t.r.Y t.r.Z t.r.z.pins t.r.intersectionNumber_baseChange hHost X hX i π c e he hne hle'
  exact (by with_unfolding_all exact (h.1.trans (congrArg Real.log (lam_eq i _ c (InfinitePlace.mk e) h.2).symm) :))

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.parameter_of_discrete_series_ray : GlobalTheory.Published.GreenCuspidal → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (a : TwArgs q.O.ex q.x.what₂), letI := a.x.grp; letI := a.x.fin; letI := a.x.alg; ∀ (i : Fin (q.w.D q.Z).R.m) π (c : a.x.A3.fam3.base3.Ix) (e : (q.w.D q.Z).what₂.LL →+* ℂ), e ≠ (q.w.D q.Z).what₂.embLL → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≠ ⊥ → (q.w.D q.Z).what₂.isot ((i : ℕ) + 1) π ≤ (a.x.R.Wp3 i c).comap (a.x.Y.mj.eW i) → q.O.X.logLam ((i : ℕ) + 1) π e = Real.log (a.x.R.lam3 i a.x.A3.A.μ0 c (InfinitePlace.mk e)) := by
  intro hGC h1 h2 h3 h4 h5 h6 hCRD h8 h9 hL N Γ p hp hNE K q hHost hMult a
  exact logLam_twArgs h4 h5 h6 hCRD K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
    (hHost (q.w.st q.Z) q.x.isOver).1 q.O.X q.x.ox.lam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefEqConjTransposeMulSelfOfIsUnitDetStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef : ∀ {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ), P.PosDef → ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := by
  first | exact @GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | exact GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det | (intros; apply GlobalTheory.posDef_eq_conjTranspose_mul_self_of_isUnit_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefOneSubMulConjTransposeOfPosDefSwapStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_one_sub_mul_conjTranspose_of_posDef_swap : ∀ {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ), (1 - zᴴ * z).PosDef → (1 - z * zᴴ).PosDef := by
  first | exact @GlobalTheory.PosDefSwap.main | exact GlobalTheory.PosDefSwap.main | (intros; apply GlobalTheory.PosDefSwap.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveIntBilinFormEqOfPositiveRealRay
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PrimRay

theorem eq_of_toReal_eq_smul : ∀ {X : Type} [AddCommGroup X] (x y : LinearMap.BilinForm ℤ X) (d : ℝ), 0 < d →
  (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = x → k = 1) → (∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = y → k = 1) →
  toReal x = d • toReal y → x = y ∧ d = 1 := by
  intro X _ x y d hd hx hy h
  have hx0 : x ≠ 0 := fun h0 => by
    have := hx 0 0 (by simp [h0])
    simp at this
  have hy0 : y ≠ 0 := fun h0 => by
    have := hy 0 0 (by simp [h0])
    simp at this
  obtain ⟨a, b, ha, hb, hab⟩ := GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm x y d hd hy0 h
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have hcop0 := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg
  obtain ⟨a', ha'⟩ := Nat.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Nat.gcd_dvd_right a b
  generalize Nat.gcd a b = g at hg hcop0 ha' hb'
  subst ha' hb'
  have hcop : Nat.Coprime a' b' := by
    have := hcop0
    have e1 : g * a' / g = a' := Nat.mul_div_cancel_left a' hg
    have e2 : g * b' / g = b' := Nat.mul_div_cancel_left b' hg
    rwa [e1, e2] at this
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hgz : ((g : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : ∀ p q, (a' : ℤ) * x p q = (b' : ℤ) * y p q := fun p q => by
    have := LinearMap.congr_fun₂ hab p q
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    push_cast at this
    apply mul_left_cancel₀ hgz
    linear_combination this
  set z : LinearMap.BilinForm ℤ X := u • y + w • x with hz
  have hxz : ((b' : ℕ) : ℤ) • z = x := by
    ext p q
    simp only [hz, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination (-u) * h1 p q + (x p q) * huw
  have hyz : ((a' : ℕ) : ℤ) • z = y := by
    ext p q
    simp only [hz, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
    linear_combination w * h1 p q + (y p q) * huw
  have hb1 : b' = 1 := hx b' z hxz
  have ha1 : a' = 1 := hy a' z hyz
  have hxy : x = y := by
    ext p q
    simpa [ha1, hb1] using h1 p q
  refine ⟨hxy, ?_⟩
  subst hxy
  obtain ⟨p, q, hpq⟩ : ∃ p q, x p q ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx0 (LinearMap.ext₂ hc)
  have := LinearMap.congr_fun₂ h p q
  simp only [toReal_apply, LinearMap.smul_apply, smul_eq_mul] at this
  have hne : (x p q : ℝ) ≠ 0 := by exact_mod_cast hpq
  have := mul_right_cancel₀ hne (this.symm.trans (one_mul _).symm)
  exact this

end GlobalTheory.PrimRay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiSquareEvenTermsCorrespondTransport
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCorr

theorem psi_sq_terms_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)))  → ∀ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ ∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2 := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht hc σ f hE
  obtain ⟨σ', f', hE', hrel⟩ := GlobalTheory.T.exists_bundleSquare_section_transport_expansion R hR G hsa D D' A A' U U' wL hwL σ
  refine ⟨σ', f', hE', fun β Z ρ z J J' hJ hJ' => ?_⟩
  have hφ : ∀ κ, D'.toPre.famφB (2 • β) κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB (xe (2 • β)) κ :=
    PsiCompare.famφB_comp Φ.hom (hc β)
  refine GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points R hR G hsa D D' A A' U U' Φ w hw (fun e => (hlev e).1) _ _ hφ (f _) (f' _)
    (fun e Z r z J J' hJ hJ' => ?_) Z ρ z J J' hJ hJ'
  have hB := GlobalTheory.T.termExpansion_weight_correspondence_at_level R hR G hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht σ σ' f f' hE hE' hrel e Z r z J J' hJ hJ' (2 • β)
  have hC := GlobalTheory.T.torus_coord_squares_correspond' R hR G hsa D D' A A' U U' Φ w hw hΦ (fun e => (hlev e).1) xe ht β (hc β) e Z r z J J' hJ hJ'
  have hP := ExpTrans.prod_fam U'.toUnifPre e 2 (fun ψ => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ ψ)) (2 • β)

  set a := sval (f (xe (2 • β))) (r ≫ (U.gt e).pG.left) z J
  set b := sval (f' (2 • β)) (r ≫ (U'.gt e).pG.left) z J'
  set T := val ((U.gt e).t (xe (2 • β))) r z J
  set T' := val ((U'.gt e).t (2 • β)) r z J'
  set O := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)
  set P := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ
  set F := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ
  have hP' : F * P = O ^ 2 := hP
  have key : a ^ 2 * (P * T' ^ 2).val = F.val * b ^ 2 * (P * T' ^ 2).val := by
    calc a ^ 2 * (P * T' ^ 2).val = a ^ 2 * (T ^ 2).val := by rw [hC]
      _ = (a * T.val) ^ 2 := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (O.val * b * T'.val) ^ 2 := by rw [hB]
      _ = (O ^ 2).val * b ^ 2 * (T' ^ 2).val := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (F * P).val * b ^ 2 * (T' ^ 2).val := by rw [hP']
      _ = F.val * b ^ 2 * (P * T' ^ 2).val := by simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  exact (Units.mul_left_inj (P * T' ^ 2)).1 key

end GlobalTheory.SqCorr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalDatumCharactersNeOneAtFixedElementResidu
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.HeightCounting

theorem theta_xiRed_ne_one : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ), SideB D cf Rw low Pq S hL eig θ →
    2 ≤ D.R.r → D.ntw.Tw → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) ≠ 1 := by
  classical
  intro D cf Rw low Pq S hL eig θ Bs hr i kv h1
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  obtain ⟨θ', hθ', hψ⟩ := Bs.exp.psiU_gen i true
  have hu : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ D.nexp.U := by
    rw [Bs.exp.U_eq]; exact Formalism.L2.NX.tvAt_mem hr _
  have hu' : Formalism.L2.NX.tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) hr kv ∈ Formalism.IndefR.NX.U D.nd :=
    Formalism.L2.NX.tvAt_mem hr _
  have e := Bs.psiU i true _ hu hu'
  have e2 : psiUOf D.nd (NX.xiRed D) θ ⟨_, hu'⟩ = θ kv.1 (Multiplicative.ofAdd (NX.xiRed D kv)) :=
    psiXi_tvAt (p := fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.host.g kv.1) (NX.xiRed D) (fun kv => θ kv.1) hr kv
  have e3 : D.nexp.psiU i true ⟨_, hu⟩ = θ' kv (Multiplicative.ofAdd 1) :=
    (hψ ⟨_, hu⟩).trans (Formalism.L2.NX.stdVal_tvAt θ' hr kv)
  rw [e2, h1, e3] at e
  refine Formalism.L2.NX.char_one_ne (θ' kv) (hθ' hr kv) (Units.ext (e.trans ?_))
  exact map_one (readLL0 S i true)

end GlobalTheory.HeightCounting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellMemStarConeOrCentrelessStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStarOf_of_cells_starCone_or_centreless : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' := by
  first | exact @GlobalTheory.PolFan.StarCells.isStarOf_of_clauses | exact GlobalTheory.PolFan.StarCells.isStarOf_of_clauses | (intros; apply GlobalTheory.PolFan.StarCells.isStarOf_of_clauses <;> assumption)
end

