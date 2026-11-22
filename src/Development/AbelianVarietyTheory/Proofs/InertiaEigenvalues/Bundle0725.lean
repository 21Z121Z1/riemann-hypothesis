import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0714
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0717
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalTranslatesSpanPrescribedCoefficient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef.Cons

open GlobalTheory.SplitScalar

variable {D : D7}

theorem isHalf_add {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u + v) := fun i j => by
  simp only [Matrix.add_apply, mul_add, hu i j, hv i j]

theorem isHalf_neg {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := fun i j => by
  simp only [Matrix.neg_apply, mul_neg, hu i j]

theorem isHalf_sub {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) :
    IsHalf e (u - v) := by
  rw [sub_eq_add_neg]; exact GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hu (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg hv)

theorem isHalf_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) :=
  fun i j => by rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hu i j]

theorem isHalf_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := fun i j => by
  simp only [Matrix.zero_apply, mul_zero]

theorem isHalf_place_of_left {m n : ℕ} {a : AE D} (ha : a * cA D a = 0) {u : Mx D m n} (hu : IsHalf a u) :
    IsHalf (a + cA D a) u := fun i j => by
  have h : cA D a * u i j = 0 := by rw [← hu i j, ← mul_assoc, mul_comm (cA D a) a, ha, zero_mul]
  rw [add_mul, h, add_zero, hu i j]

theorem isHalf_place_of_right {m n : ℕ} {a : AE D} (ha : a * cA D a = 0) {u : Mx D m n}
    (hu : IsHalf (cA D a) u) : IsHalf (a + cA D a) u := fun i j => by
  have h : a * u i j = 0 := by rw [← hu i j, ← mul_assoc, ha, zero_mul]
  rw [add_mul, h, zero_add, hu i j]

theorem heisO_mem_locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ)
    {h : WO S T → ℂ} (hh : h ∈ locSpan ψ S T a f) {w : WO S T} (hw : IsHalf (a + cA D a) w) :
    heisO ψ S T w h ∈ locSpan ψ S T a f := by
  induction hh using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, hu, rfl⟩ := hp
    rw [heisO_heisO]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w + u, GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hw hu, rfl⟩)
  | zero =>
    rw [show heisO ψ S T w 0 = 0 from (heisL ψ S T w).map_zero]
    exact Submodule.zero_mem _
  | add p q _ _ hp hq =>
    rw [show heisO ψ S T w (p + q) = heisO ψ S T w p + heisO ψ S T w q from (heisL ψ S T w).map_add p q]
    exact Submodule.add_mem _ hp hq
  | smul c p _ hp =>
    rw [heisO_smul]
    exact Submodule.smul_mem _ _ hp

theorem self_mem_locSpan (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) :
    f ∈ locSpan ψ S T a f :=
  Submodule.subset_span ⟨0, GlobalTheory.DownLift.SplitCoef.Cons.isHalf_zero _, (heisO_zero ψ S T f).symm⟩

end GlobalTheory.DownLift.SplitCoef.Cons

open GlobalTheory.SplitScalar GlobalTheory.DownLift.SplitCoef.Cons in

theorem GlobalTheory.DownLift.SplitCoef.exists_locSpan_coef_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : WO S T → ℂ, IsSBHalf a (latH S T ΛS ΛT) Φ → ∀ x₁, IsHalf a x₁ → ∃ f' ∈ locSpan ψ S T a f, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f') = Φ x * ℓ (heisO ψ S T x₁ f) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha f hf Φ hΦ x₁ hx₁
  classical
  obtain ⟨⟨k₀, hk₀, hinv, hsupp⟩, -, -⟩ := GlobalTheory.DownLift.SplitCoef.coef_isSBHalf_uniform D ψ S T hψ ΛS ΛT hS hT a ha f hf
  obtain ⟨hΦs, kΦ, hkΦ, hΦinv, hΦsupp⟩ := hΦ
  obtain ⟨k₁, hk₁, hx₁Λ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_latO hS.1 hT.1 x₁ (half_fin ha hx₁)
  obtain ⟨k, hk, hfix, hΦk, hkx₁, hk0, hkΦ'⟩ : ∃ k : ℕ, 0 < k ∧
      (∀ u ∈ latH S T ΛS ΛT, IsHalf a u → heisO ψ S T (k • u) f = f) ∧
      (∀ u ∈ latH S T ΛS ΛT, IsHalf a u → ∀ t, Φ (t + k • u) = Φ t) ∧
      k • x₁ ∈ latH S T ΛS ΛT ∧
      (∀ y, k₀ • y ∈ latH S T ΛS ΛT → k • y ∈ latH S T ΛS ΛT) ∧
      (∀ y, kΦ • y ∈ latH S T ΛS ΛT → k • y ∈ latH S T ΛS ΛT) := by
    refine ⟨k₀ * kΦ * k₁, by positivity, fun u hu hua => ?_, fun u hu hua t => ?_, ?_, fun y hy => ?_,
      fun y hy => ?_⟩
    · rw [mul_assoc, mul_smul]
      exact hinv _ (AddSubgroup.nsmul_mem _ hu _) (Or.inl (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua _))
    · rw [show k₀ * kΦ * k₁ = kΦ * (k₀ * k₁) by ring, mul_smul]
      exact hΦinv _ (AddSubgroup.nsmul_mem _ hu _) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua _) t
    · rw [mul_smul]
      exact AddSubgroup.nsmul_mem _ hx₁Λ _
    · rw [show k₀ * kΦ * k₁ = (kΦ * k₁) * k₀ by ring, mul_smul]
      exact AddSubgroup.nsmul_mem _ hy _
    · rw [show k₀ * kΦ * k₁ = (k₀ * k₁) * kΦ by ring, mul_smul]
      exact AddSubgroup.nsmul_mem _ hy _
  have hca : IsSplitIdem D (cA D a) := isSplitIdem_conj ha
  have hcaa : cA D a * a = 0 := by rw [mul_comm]; exact ha.2.1
  obtain ⟨Y, hYne, hY, -, hYsum⟩ :=
    GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ ΛS ΛT hS hT a ha.1 (infPart_splitIdem ha) k hk
  obtain ⟨X, -, hX, hXu, -⟩ :=
    GlobalTheory.DownLift.GenQuot.reps_orth D ψ S T hψ ΛS ΛT hS hT (cA D a) hca.1 (infPart_splitIdem hca) k hk
  simp only [GlobalTheory.DualPairCheck.cA_cA] at hX hXu
  obtain ⟨n, hn⟩ : ∃ n, n = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x₁ f) := ⟨_, rfl⟩

  have hA : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x n) =
      if (∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) then (Y.card : ℂ) * ℓ (heisO ψ S T x₁ f) else 0 := by
    intro ℓ hℓ x hx
    have hg : IsThetaFunO ψ S T (heisO ψ S T x₁ f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x₁
    have hxg : IsThetaFunO ψ S T (heisO ψ S T x (heisO ψ S T x₁ f)) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg x
    have h1 : ℓ (heisO ψ S T x n) =
        (∑ y ∈ Y, ψ (symplO S T x y)) * ℓ (heisO ψ S T x (heisO ψ S T x₁ f)) := by
      rw [hn, heisO_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [heisO_comm, ℓ.map_smul, smul_eq_mul, hℓ y (hY y hy).1 _ hxg]
    have h2 : heisO ψ S T x (heisO ψ S T x₁ f) = heisO ψ S T (x + x₁) f :=
      (heisO_add_of_orth ψ S T (symplO_eq_zero S T hcaa hx hx₁) f).symm
    rw [h1, h2]
    split_ifs with hP
    · obtain ⟨u, hu, hua, rfl⟩ := hP
      have hkx : k • (k • u) ∈ latH S T ΛS ΛT := AddSubgroup.nsmul_mem _ (AddSubgroup.nsmul_mem _ hu _) _
      rw [Finset.sum_congr rfl fun y hy => (hYsum (k • u) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua k) hkx).1 ⟨u, hu, hua, rfl⟩ y hy,
        Finset.sum_const, nsmul_eq_mul, mul_one]
      have horth : symplO S T x₁ (k • u) = 0 := symplO_eq_zero S T hcaa hx₁ (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_nsmul hua k)
      rw [add_comm, heisO_add_of_orth ψ S T horth f, hfix u hu hua]
    · by_cases hkx : k • x ∈ latH S T ΛS ΛT
      · rw [(hYsum x hx hkx).2 hP, zero_mul]
      · have h3 : ℓ (heisO ψ S T (x + x₁) f) = 0 := by
          by_contra hne
          apply hkx
          have h4 := hk0 _ (hsupp ℓ hℓ (x + x₁) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_add hx hx₁) hne)
          have h5 : k • x = k • (x + x₁) - k • x₁ := by rw [nsmul_add, add_sub_cancel_right]
          rw [h5]
          exact AddSubgroup.sub_mem _ h4 hkx₁
        rw [h3, mul_zero]
  refine ⟨((Y.card : ℂ)⁻¹) • ∑ z ∈ X, Φ z • heisO ψ S T (-z) n, ?_, ?_⟩
  · have hg : heisO ψ S T x₁ f ∈ locSpan ψ S T a f :=
      heisO_mem_locSpan ψ S T a f (self_mem_locSpan ψ S T a f) (isHalf_place_of_left ha.2.1 hx₁)
    have hnm : n ∈ locSpan ψ S T a f := by
      rw [hn]
      exact Submodule.sum_mem _ fun y hy =>
        heisO_mem_locSpan ψ S T a f hg (isHalf_place_of_right ha.2.1 (hY y hy).1)
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _
      (heisO_mem_locSpan ψ S T a f hnm (isHalf_place_of_left ha.2.1 (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg (hX z hz).1))))
  · intro ℓ hℓ x hx
    have hc : (Y.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hYne.card_pos.ne'
    rw [heisO_smul, heisO_sum, ℓ.map_smul, map_sum, smul_eq_mul]
    have hterm : ∀ z ∈ X, ℓ (heisO ψ S T x (Φ z • heisO ψ S T (-z) n)) = Φ x *
        (if (∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x - z = k • u) then (Y.card : ℂ) * ℓ (heisO ψ S T x₁ f)
          else 0) := by
      intro z hz
      have hzh := (hX z hz).1
      rw [heisO_smul, ℓ.map_smul, smul_eq_mul,
        ← heisO_add_of_orth ψ S T (symplO_eq_zero S T hcaa hx (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_neg hzh)) n, ← sub_eq_add_neg,
        hA ℓ hℓ (x - z) (GlobalTheory.DownLift.SplitCoef.Cons.isHalf_sub hx hzh)]
      split_ifs with hP
      · obtain ⟨u, hu, hua, hxu⟩ := hP
        rw [(sub_eq_iff_eq_add').1 hxu, hΦk u hu hua]
      · rw [mul_zero, mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    by_cases hΦx : Φ x = 0
    · rw [hΦx, zero_mul, mul_zero, zero_mul]
    · obtain ⟨z₀, ⟨hz₀, hP₀⟩, huniq⟩ := hXu x hx (hkΦ' x (hΦsupp x hΦx))
      rw [Finset.sum_eq_single_of_mem z₀ hz₀ (fun z hz hne => if_neg fun hP => hne (huniq z ⟨hz, hP⟩)),
        if_pos hP₀]
      field_simp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ k : ℕ, 0 < k → ∃ Y : Finset (WO S T), Y.Nonempty ∧ (∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ latH S T ΛS ΛT) ∧ (∀ y', IsHalf (cA D a) y' → k • y' ∈ latH S T ΛS ΛT → ∃! y, y ∈ Y ∧ ∃ u ∈ latH S T ΛS ΛT, IsHalf (cA D a) u ∧ y' - y = k • u) ∧ ∀ x, IsHalf a x → k • x ∈ latH S T ΛS ΛT → ((∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∀ y ∈ Y, ψ (symplO S T x y) = 1) ∧ ((¬ ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∑ y ∈ Y, ψ (symplO S T x y) = 0) := by
  first | exact @GlobalTheory.DownLift.GenQuot.reps_orth | exact GlobalTheory.DownLift.GenQuot.reps_orth | (intros; apply GlobalTheory.DownLift.GenQuot.reps_orth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardAdelicAddCharStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardAdelicAddChar : ∀ (E : Type) [Field E] [NumberField E], ∃ ψ : AddChar (Ad E) ℂ, StdPsi ψ := by
  first | exact @GlobalTheory.CuspGeneric.exists_stdPsi | exact GlobalTheory.CuspGeneric.exists_stdPsi | (intros; apply GlobalTheory.CuspGeneric.exists_stdPsi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stratified_phiModule_crystalline_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : Seed bk d ρ τ), Height s → ∃ (S : Strat bk d) (T : Matrix (Fin d) (Fin d) (WCb l)), MReal S ρ T := by
  first | exact @GlobalTheory.BSP.exists_strat_mreal | exact GlobalTheory.BSP.exists_strat_mreal | (intros; apply GlobalTheory.BSP.exists_strat_mreal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedAtSplitPlace_unitary_matrix_eq : ∀ (D : D7) (V : HSp D) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (B g : GL (Fin V.rank) (Fv D.host.F v)), ∃ h : GA D V, Formalism.L2.Theta.SuppAt e V h ∧ grpCo φ V B h = g := by
  first | exact @GlobalTheory.DownLift.GenSplit.exists_suppAt_grpCo_eq | exact GlobalTheory.DownLift.GenSplit.exists_suppAt_grpCo_eq | (intros; apply GlobalTheory.DownLift.GenSplit.exists_suppAt_grpCo_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitarySupportedAtSplitPlaceLiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_supported_at_split_place_lift : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N : ℕ), IsBaseFrame S βS Λ N → ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), ∃ κ : GA D S, SuppAt e S κ ∧ κ ∈ GfC S ∧ finE S κ ∈ St βS ∧ (redFn βS PP (finE S κ)).val.map ι = h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) ∧ (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T κ 1 x) = h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * rdAdj S T βS βT φ x := by
  first | exact @GlobalTheory.DownLift.SplitCoef.exists_supp_lift_adj | exact GlobalTheory.DownLift.SplitCoef.exists_supp_lift_adj | (intros; apply GlobalTheory.DownLift.SplitCoef.exists_supp_lift_adj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinVecMemGLatOne
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LatRatStd

variable {D : D7}

theorem finVec_mem_gLat_one (T : HSp D) (v : Fin T.rank → D.host.E) :
    Formalism.L2.Pj.finVec T v ∈ Formalism.L2.Pj.gLat T 1 ↔ v ∈ L0c D T := by
  rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq, SetLike.mem_coe]
  obtain ⟨h1, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D T
  rw [← ((GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E T.rank _ hfg hsp).1 v), ← h1]
  constructor
  · rintro ⟨z, hz, e⟩
    rw [map_one, Units.val_one, Matrix.one_mulVec] at e
    subst e
    exact hz
  · intro h
    exact ⟨_, h, by rw [map_one, Units.val_one, Matrix.one_mulVec]; rfl⟩

theorem mem_latRat_iff_cols {S T : HSp D} (hG : S.gram = 1) {LS : Set (Fin S.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)}
    (hS : LS = (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E))) (hT : LT = L0c D T)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    M ∈ GlobalTheory.LatVac.latRat S T LS LT ↔ ∀ b, (fun a => M a b) ∈ Formalism.L2.Pj.latG T 1 := by
  subst hS hT
  have hg : ∀ (s : Fin S.rank → D.host.E) j, ∑ k, star (s k) * S.gram k j = star (s j) := fun s j => by
    rw [hG, Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero]) (by simp),
      Matrix.one_apply_eq, mul_one]
  constructor
  · intro hM b
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((Submodule.mem_pi.1 (SetLike.mem_coe.1 hs)) b trivial)
      obtain ⟨c', hc'⟩ := GlobalTheory.DatumFourier.star_int c
      have h1 : a • t ∈ Formalism.L2.Pj.latG T 1 :=
        Submodule.subset_span ⟨a, ha, t, (finVec_mem_gLat_one T t).2 ht, rfl⟩
      convert Submodule.smul_mem _ c' h1 using 1
      funext i
      change a * t i * _ = (c' : D.host.E) * (a * t i)
      rw [hg, hc', ← hc, mul_comm]
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
  · intro h
    have key : ∀ b, ∀ v ∈ Formalism.L2.Pj.latG T 1, (Matrix.of fun a j => v a * (Pi.single b 1 : Fin S.rank → D.host.E) j) ∈
        GlobalTheory.LatVac.latRat S T (Formalism.L2.Pj.stdLat D.host.E S.rank : Set (Fin S.rank → D.host.E)) (L0c D T) := by
      intro b v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hv
        refine AddSubgroup.subset_closure ⟨a, ha, Pi.single b 1, ?_, t, (finVec_mem_gLat_one T t).1 ht, ?_⟩
        · rw [SetLike.mem_coe, Formalism.L2.Pj.stdLat, Submodule.mem_pi]
          intro k _
          rw [Pi.single_apply]
          split_ifs
          · exact Submodule.mem_one.2 ⟨1, map_one _⟩
          · exact zero_mem _
        · ext i j
          simp only [GlobalTheory.LatVac.genMap, Matrix.of_apply, hg, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
          split_ifs <;> simp
      | zero => convert (GlobalTheory.LatVac.latRat S T _ _).zero_mem using 1; ext i j; simp
      | add x y _ _ hx hy => convert add_mem hx hy; ext i j; simp [add_mul]
      | smul c x _ hx =>
        convert GlobalTheory.LatVac.smul_mem_latRat c hx using 1
        exact Matrix.ext fun i j => mul_assoc (c : D.host.E) (x i) _
    have e : M = ∑ b, Matrix.of fun a j => M a b * (Pi.single b 1 : Fin S.rank → D.host.E) j := by
      ext i j
      simp [Matrix.sum_apply, Pi.single_apply]
    rw [e]
    exact sum_mem fun b _ => key b _ (h b)

end GlobalTheory.LatRatStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteFourierExpansionConjugateHalfSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteFourierExpansion_conjugateHalf_splitPlace : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)) (ϖ : OI v), Irreducible ϖ → ∀ (M N : ℕ), (∀ x : WO S T, IsHalf (cA D e) x → ¬ InPow ϖ M (adjCo φ S T BS BT x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T BS BT e ϖ M, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1) → ∀ (a : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) → ℂ), (∀ X Z, InPow ϖ M Z → a (X + Z) = a X) → ∃ c : WO S T →₀ ℂ, (∀ y ∈ c.support, IsHalf e y) ∧ ∀ x, IsHalf (cA D e) x → Bdd ϖ N (adjCo φ S T BS BT x) → a (adjCo φ S T BS BT x) = c.sum fun y z => z * ψ (symplO S T x y) := by
  first | exact @GlobalTheory.DownLift.GenSplit.finite_fourier_half | exact GlobalTheory.DownLift.GenSplit.finite_fourier_half | (intros; apply GlobalTheory.DownLift.GenSplit.finite_fourier_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisPhiFixedAddFinrankMonLeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_dcris_phi_fixed_add_finrank_mon_le_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) + finrank ℚ_[l] ↥((Dst P ρ).map (monV P ℚ_[l] V)) ≤ finrank ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := by
  first | exact @GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le | exact GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le | (intros; apply GlobalTheory.finrank_dcris_phi_fixed_add_finrank_mon_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockActionBasePolynomialStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_base_polynomial : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (u : GLR D n) (P : PolF D m n), ∃ (s : ℂ) (g : {τ : D.host.E →+* ℂ // InPsi H τ} → GL (Fin n) ℂ), MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (fockGL m w 1 u P) = MvPolynomial.C s * GlobalTheory.Harm.colAct ℂ _ Dw.p Dw.q (Fin n) g (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) P) := by
  first | exact @GlobalTheory.FockLetters.rename_fockGL_eq_C_mul_colAct | exact GlobalTheory.FockLetters.rename_fockGL_eq_C_mul_colAct | (intros; apply GlobalTheory.FockLetters.rename_fockGL_eq_C_mul_colAct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockDeltaBasePolynomialStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_delta_base_polynomial : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (hn : Dw.p + Dw.q ≤ n), ∃ c : ℂ, MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (w.delta m) = MvPolynomial.C c * GlobalTheory.Harm.basePoly ℂ hn (GlobalTheory.FockLetters.stepsX Dw a) (GlobalTheory.FockLetters.stepsY Dw a) := by
  first | exact @GlobalTheory.FockLetters.rename_delta_eq_smul_basePoly | exact GlobalTheory.FockLetters.rename_delta_eq_smul_basePoly | (intros; apply GlobalTheory.FockLetters.rename_delta_eq_smul_basePoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctioStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → (harm m w B).map (harmFn m w B) = Submodule.span ℂ {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} := by
  first | exact @GlobalTheory.ExportSeries.Onto.map_harm_eq | exact GlobalTheory.ExportSeries.Onto.map_harm_eq | (intros; apply GlobalTheory.ExportSeries.Onto.map_harm_eq <;> assumption)
end

