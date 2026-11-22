import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0264
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0552
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0105
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IwasawaDecompositionSmoothNearOne
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

open scoped Matrix.Norms.Operator

noncomputable section

namespace GlobalTheory.SmoothIwasawaNear

variable (E : Type) [Field E] [NumberField E] {c N : ℕ} {n : Fin c → ℕ} (e : (Σ i, Fin (n i)) ≃ Fin N)

def lowPart (X : Matrix (Fin N) (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E) :=
  Matrix.of fun p q => if blk e q < blk e p then X p q else 0

def skewLin : Matrix (Fin N) (Fin N) (Cinf E) →ₗ[ℝ] Matrix (Fin N) (Fin N) (Cinf E) where
  toFun X := lowPart E e X - (lowPart E e X).conjTranspose
  map_add' X Y := by
    refine Matrix.ext fun p q => ?_
    simp only [lowPart, Matrix.add_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    split_ifs <;> simp [star_add] <;> abel
  map_smul' r X := by
    refine Matrix.ext fun p q => ?_
    simp only [lowPart, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      RingHom.id_apply]
    split_ifs <;> simp [star_smul, smul_sub]

def skew : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Matrix (Fin N) (Fin N) (Cinf E) :=
  LinearMap.toContinuousLinearMap (skewLin E e)

theorem skew_apply (X : Matrix (Fin N) (Fin N) (Cinf E)) : skew E e X = lowPart E e X - (lowPart E e X).conjTranspose := rfl

theorem skew_conjTranspose (X : Matrix (Fin N) (Fin N) (Cinf E)) : (skew E e X).conjTranspose = -skew E e X := by
  rw [skew_apply, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, neg_sub]

theorem blockTriangular_up (X : Matrix (Fin N) (Fin N) (Cinf E)) :
    (1 + (X - skew E e X)).BlockTriangular (blk e) := by
  intro i j h
  have hij : i ≠ j := fun hh => by subst hh; exact lt_irrefl _ h
  simp [skew_apply, lowPart, Matrix.conjTranspose_apply, Matrix.one_apply_ne hij, h, not_lt_of_gt h]

def Fm (X : Matrix (Fin N) (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E) :=
  (1 + (X - skew E e X)) * NormedSpace.exp (skew E e X)

theorem contDiff_exp' {k : WithTop ℕ∞} :
    ContDiff ℝ k (NormedSpace.exp : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E)) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem contDiff_Fm {k : WithTop ℕ∞} : ContDiff ℝ k (Fm E e) :=
  (contDiff_const.add (contDiff_id.sub (skew E e).contDiff)).mul ((contDiff_exp' E).comp (skew E e).contDiff)

theorem Fm_zero : Fm E e 0 = 1 := by simp [Fm, NormedSpace.exp_zero]

theorem hasFDerivAt_Fm : HasFDerivAt (Fm E e)
    ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin N) (Fin N) (Cinf E)) : _ →L[ℝ] _)) 0 := by
  have h1 : HasFDerivAt (fun X : Matrix (Fin N) (Fin N) (Cinf E) => 1 + (X - skew E e X))
      (ContinuousLinearMap.id ℝ _ - skew E e) 0 :=
    ((hasFDerivAt_id 0).sub (skew E e).hasFDerivAt).const_add 1
  have h0 := hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin N) (Fin N) (Cinf E))
  rw [← map_zero (skew E e)] at h0
  have h2 := h0.comp (0 : Matrix (Fin N) (Fin N) (Cinf E)) (skew E e).hasFDerivAt
  have h3 := h1.mul' h2
  refine h3.congr_fderiv (ContinuousLinearMap.ext fun X => ?_)
  have hs0 : skew E e 0 = 0 := map_zero _
  show (1 + (0 - skew E e 0)) * skew E e X + (X - skew E e X) * NormedSpace.exp (skew E e 0) = X
  rw [hs0, NormedSpace.exp_zero, sub_zero, add_zero, one_mul, mul_one]
  abel

theorem exists_local_iwasawa : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (e : (Σ i, Fin (n i)) ≃ Fin N), ∃ (p : Lie E N → parab (Cinf E) e) (k : Lie E N → Kinf E N), ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (p y).1.val) (oneL E N) ∧ ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => toL (k y).1) (oneL E N) ∧ p (oneL E N) = 1 ∧ k (oneL E N) = 1 ∧ ∀ᶠ y in nhds (oneL E N), Matrix.of y = (p y).1.val * (k y).1 := by
  intro E _ _ _ c N n e
  classical
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Fm E e) 0 := (contDiff_Fm E e).contDiffAt
  have hF' := hasFDerivAt_Fm E e
  set G := hF.localInverse hF' hn with hGdef
  have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G (Fm E e 0) := hF.to_localInverse hF' hn
  have hG1 : G (Fm E e 0) = 0 := hF.localInverse_apply_image hF' hn
  have hinv : ∀ᶠ X in nhds (Fm E e 0), Fm E e (G X) = X :=
    (hF.hasStrictFDerivAt' hF' hn).eventually_right_inverse
  rw [Fm_zero] at hG hG1 hinv
  let T : Lie E N ≃L[ℝ] Matrix (Fin N) (Fin N) (Cinf E) := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  let φ : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E) := fun X => 1 + (G X - skew E e (G X))
  let ψ : Matrix (Fin N) (Fin N) (Cinf E) → Matrix (Fin N) (Fin N) (Cinf E) :=
    fun X => NormedSpace.exp (skew E e (G X))
  have hφ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ 1 :=
    contDiffAt_const.add (hG.sub ((skew E e).contDiff.contDiffAt.comp _ hG))
  have hψ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ 1 :=
    (contDiff_exp' E).contDiffAt.comp _ ((skew E e).contDiff.contDiffAt.comp _ hG)
  have hφ1 : φ 1 = 1 := by simp [φ, hG1]
  have hψ1 : ψ 1 = 1 := by simp [ψ, hG1, NormedSpace.exp_zero]
  have hunit : ∀ᶠ X in nhds (1 : Matrix (Fin N) (Fin N) (Cinf E)), IsUnit (φ X) :=
    hφ.continuousAt.eventually_mem (by rw [hφ1]; exact Units.isOpen.mem_nhds isUnit_one)
  have hTt : Filter.Tendsto (fun y : Lie E N => Matrix.of y) (nhds (oneL E N)) (nhds 1) :=
    T.continuous.tendsto (oneL E N)
  have hunitV : ∀ᶠ y in nhds (oneL E N), IsUnit (φ (Matrix.of y)) := hTt.eventually hunit
  have hinvV : ∀ᶠ y in nhds (oneL E N), Fm E e (G (Matrix.of y)) = Matrix.of y := hTt.eventually hinv
  have hU : ∀ X, ψ X ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := fun X => by
    show NormedSpace.exp (skew E e (G X)) ∈ _
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      skew_conjTranspose, ← Matrix.exp_add_of_commute _ _ (Commute.refl (skew E e (G X))).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have hφT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ (T (oneL E N)) := hφ
  have hψT : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ (T (oneL E N)) := hψ
  refine ⟨fun y => if h : IsUnit (φ (Matrix.of y)) then ⟨h.unit, blockTriangular_up E e (G (Matrix.of y))⟩ else 1,
    fun y => ⟨ψ (Matrix.of y), hU _⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have hsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => T.symm (φ (T y))) (oneL E N) :=
      T.symm.contDiff.contDiffAt.comp _ (hφT.comp (oneL E N) T.contDiff.contDiffAt)
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [hunitV] with y hy
    simp only [dif_pos hy]
    show toL (hy.unit : Matrix (Fin N) (Fin N) (Cinf E)) = _
    rw [hy.unit_spec]
    rfl
  · exact T.symm.contDiff.contDiffAt.comp _ (hψT.comp (oneL E N) T.contDiff.contDiffAt)
  · have h1 : IsUnit (φ (Matrix.of (oneL E N))) := by
      show IsUnit (φ 1)
      rw [hφ1]
      exact isUnit_one
    refine Subtype.ext (Units.ext ?_)
    simp only [dif_pos h1]
    exact (IsUnit.unit_spec _).trans hφ1
  · exact Subtype.ext hψ1
  · filter_upwards [hunitV, hinvV] with y hy hy'
    simp only [dif_pos hy]
    show Matrix.of y = (hy.unit : Matrix (Fin N) (Fin N) (Cinf E)) * ψ (Matrix.of y)
    rw [hy.unit_spec]
    exact hy'.symm

end GlobalTheory.SmoothIwasawaNear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianStabilizerNormalizesFrameUnipotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RallisCusp

open GlobalTheory.MixModel

variable {D : D7}

theorem mem_span_cols {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (v : Fin n → D.host.E) :
    v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ∃ a, I *ᵥ a = v := by
  change v ∈ Submodule.span D.host.E (Set.range I.col) ↔ _
  rw [← Matrix.range_mulVecLin]; rfl

theorem exists_mul_eq_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (M : Matrix (Fin n) (Fin n) D.host.E)
    (h : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      M *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose)) :
    ∃ A : Matrix (Fin s) (Fin s) D.host.E, M * I = I * A := by
  have h1 : ∀ j, ∃ b, I *ᵥ b = M *ᵥ I.transpose j := fun j =>
    (mem_span_cols I _).1 (h _ (Submodule.subset_span ⟨j, rfl⟩))
  choose f hf using h1
  refine ⟨Matrix.of fun i j => f j i, ?_⟩
  refine Matrix.ext fun k j => ?_
  have := congrFun (hf j) k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply] at this
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simpa using this.symm

theorem frame_gram_mul {n s : ℕ} (I : Matrix (Fin n) (Fin s) D.host.E) (J c c' : Matrix (Fin n) (Fin n) D.host.E)
    (hc : c * c' = 1) (hu : cᴴ * J * c = J) : Iᴴ * J * c = (c' * I)ᴴ * J := by
  have h1 : (c * c')ᴴ = 1 := by rw [hc, Matrix.conjTranspose_one]
  calc Iᴴ * J * c = Iᴴ * (c * c')ᴴ * J * c := by rw [h1, Matrix.mul_one]
    _ = Iᴴ * c'ᴴ * (cᴴ * J * c) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = (c' * I)ᴴ * J := by rw [hu, Matrix.conjTranspose_mul]

theorem mul_mul_mul_eq_zero {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (I : Matrix (Fin n) (Fin s) R) (A' : Matrix (Fin s) (Fin s) R) (h : C' * I = I * A') (h0 : m * I = 0) :
    C * m * C' * I = 0 := by
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Matrix.mul_assoc C, h0, Matrix.mul_zero, Matrix.zero_mul]

theorem mul_mul_mul_eq_zero' {R : Type} [CommRing R] {n s : ℕ} (C C' m : Matrix (Fin n) (Fin n) R)
    (K : Matrix (Fin s) (Fin n) R) (A' : Matrix (Fin s) (Fin s) R) (h : K * C = A' * K) (h0 : K * m = 0) :
    K * (C * m * C') = 0 := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc A', h0, Matrix.mul_zero, Matrix.zero_mul]

set_option maxHeartbeats 2000000 in

theorem conj_mem_NI : ∀ (D : D7) (W : HSp D) (Y : Lag W) (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ γ : GQ W, GlobalTheory.RallisCusp.lagAct W γ Y = Y → ∀ n ∈ NI W I, (γ : GA D W) * n * (γ : GA D W)⁻¹ ∈ NI W I := by
  intro D W Y s I _ hS γ hY n hn
  set c := gqMat W γ with hc_def
  set c' := gqMat W γ⁻¹ with hc'_def
  have hcc' : c * c' = 1 := gqMat_mul_inv W γ
  have hc'c : c' * c = 1 := gqMat_inv_mul W γ
  have memS : ∀ v, v ∈ Submodule.span D.host.E (Set.range I.transpose) ↔ ((v, 0) : _ × _) ∈ Y.1 := by
    intro v; rw [hS, Submodule.mem_comap, LinearMap.inl_apply]
  have memY : ∀ y, y ∈ Y.1 ↔ (c' *ᵥ y.1, y.2) ∈ Y.1 := by
    intro y; conv_lhs => rw [← hY]
    exact mem_lagAct W γ Y y
  have hcS : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS, memY]
    simpa [Matrix.mulVec_mulVec, hc'c] using (memS v).1 hv
  have hc'S : ∀ v ∈ Submodule.span D.host.E (Set.range I.transpose),
      c' *ᵥ v ∈ Submodule.span D.host.E (Set.range I.transpose) := by
    intro v hv
    rw [memS]
    exact (memY _).1 ((memS v).1 hv)
  obtain ⟨A, hA⟩ := exists_mul_eq_mul I c' hc'S
  obtain ⟨B, hB⟩ := exists_mul_eq_mul I c hcS
  have hIc : Iᴴ * W.gram * c = Aᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c c' hcc' (gqMat_unitary W γ), hA, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hIc' : Iᴴ * W.gram * c' = Bᴴ * (Iᴴ * W.gram) := by
    rw [frame_gram_mul I W.gram c' c hc'c (gqMat_unitary W γ⁻¹), hB, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hrat : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E), M.map (incA D) = rat M := fun _ => rfl
  have hγ : mt W (γ : GA D W) = rat c := (rat_gqMat W γ).symm
  have hγ' : mt W ((γ : GA D W)⁻¹) = rat c' := (rat_gqMat W γ⁻¹).symm
  have hle : NI W I ≤ (NI W I).comap (MulAut.conj (γ : GA D W)).toMonoidHom := by
    unfold NI
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨h1, h2, h3⟩ := hg
    apply Subgroup.subset_closure
    have hm : (matHom W ((MulAut.conj (γ : GA D W)).toMonoidHom g)).1 - 1 = rat c * ((matHom W g).1 - 1) * rat c' := by
      change mt W ((γ : GA D W) * g * (γ : GA D W)⁻¹) - 1 = rat c * (mt W g - 1) * rat c'
      rw [mt_mul, mt_mul, hγ, hγ', Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← rat_mul, hcc', rat_one]
    rw [cT_sig, hrat] at h2 h3
    rw [hrat] at h1
    have hA' : rat c' ⬝ rat I = rat I ⬝ rat A := by rw [← rat_mul, hA, rat_mul]
    have hIc2 : rat (Iᴴ * W.gram) ⬝ rat c = rat Aᴴ ⬝ rat (Iᴴ * W.gram) := by rw [← rat_mul, hIc, rat_mul]
    have hB' : rat c ⬝ rat I = rat I ⬝ rat B := by rw [← rat_mul, hB, rat_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm, hrat]
      exact mul_mul_mul_eq_zero (rat c) (rat c') _ (rat I) (rat A) hA' h1
    · rw [hm, cT_sig, hrat]
      exact mul_mul_mul_eq_zero' (rat c) (rat c') _ (rat (Iᴴ * W.gram)) (rat Aᴴ) hIc2 h2
    · intro x hx
      rw [cT_sig] at hx
      have hx' : (Iᴴ * W.gram) *ᵥ (c' *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hIc', ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      obtain ⟨a, ha⟩ := h3 (c' *ᵥ x) hx'
      refine ⟨rat B *ᵥ a, ?_⟩
      have hv : rat c' *ᵥ (fun i => incA D (x i)) = fun i => incA D ((c' *ᵥ x) i) := by
        funext i; exact (RingHom.map_mulVec (incA D) c' x i).symm
      rw [hm, hrat, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, ha, Matrix.mulVec_mulVec, hB',
        Matrix.mulVec_mulVec]
  exact hle hn

end GlobalTheory.RallisCusp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoefficientNontrivialCosetsSummableBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.Eu

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lx_eq_of_rep_rel {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x y : LX R i v}
    (h : (rep x)⁻¹ * rep y ∈ levW R i) : x = y := by
  have : (Quotient.mk _ (Quotient.out x) : LX R i v) = Quotient.mk _ (Quotient.out y) := by
    apply Quotient.sound
    change ((QuotientGroup.leftRel (levW R i)).comap (Subtype.val : locSet R i v → GA D (Wc D i))) _ _
    rw [Setoid.comap_rel, QuotientGroup.leftRel_apply]
    exact h
  exact (Quotient.out_eq x).symm.trans (this.trans (Quotient.out_eq y))

theorem rep_notMem_levW {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x : LX R i v}
    (hx : x ≠ lx0 R i v) : rep x ∉ levW R i := fun h =>
  hx (lx_eq_of_rep_rel ((levW R i).mul_mem ((levW R i).inv_mem h) (trivial_level_coset_representative_mem_level R i v)))

theorem rep_suppF {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : LX R i v) :
    SuppF (Wc D i) (fid D v) (rep x) := (Quotient.out x).2.2

theorem eq_one_of_suppF_zero {V : HSp D} {g : GA D V} (h : SuppF V 0 g) : g = 1 := by
  have e : Formalism.L2.Theta.mt V g = Formalism.L2.Theta.mt V 1 := by
    have h1 : Formalism.L2.Theta.mt V 1 = 1 := rfl
    rw [h1, ← sub_eq_zero]
    ext a b
    have := h a b
    simpa [eq_comm] using this
  exact Subtype.ext (Units.ext e)

end

theorem acoef_small : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LocSmall R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ s : HeightOneSpectrum (𝓞 D.host.F) → ℝ, Summable s ∧ (∀ v, s v < 1) ∧ ∀ v (C : Finset (Eu.LX R i v)), Eu.lx0 R i v ∉ C → ∑ x ∈ C, ‖Eu.acoef R i t μ 𝓕 v x‖ ≤ s v := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hLS μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hb⟩ := hLS μ 𝓕 hμ
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · refine Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => ?_) hs.abs
    exact max_le (le_abs_self _) (abs_nonneg _)
  · intro v C hC
    by_cases hex : ∃ f, IsFinIdem D v f
    · have hf : IsFinIdem D v (fid D v) := by
        unfold fid
        rw [dif_pos hex]
        exact hex.choose_spec
      have hinj : Function.Injective (rep : LX R i v → GA D (Wc D i)) := fun x y h =>
        lx_eq_of_rep_rel (by rw [h, inv_mul_cancel]; exact (levW R i).one_mem)
      have := hb v _ hf (C.image rep) ?_ ?_
      · rw [Finset.sum_image (fun x _ y _ h => hinj h)] at this
        exact this.trans (le_max_left _ _)
      · intro g hg
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hg
        exact ⟨rep_suppF x, rep_notMem_levW fun e => hC (e ▸ hx)⟩
      · intro g hg g' hg' h
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hg'
        rw [lx_eq_of_rep_rel h]
    · have hf : fid D v = 0 := by
        unfold fid
        rw [dif_neg hex]
      have hC0 : C = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
        have h1 : rep x = 1 := eq_one_of_suppF_zero (hf ▸ rep_suppF x)
        exact rep_notMem_levW (fun e => hC (e ▸ hx)) (h1 ▸ (levW R i).one_mem)
      rw [hC0, Finset.sum_empty]
      exact le_max_right _ _

end GlobalTheory.RawLift.Eu

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeckeSumPreservesPrincipalLevelFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hecke_sum_preserves_principal_level_forms : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ (α : GA D (Wc D i)), SuppF (Wc D i) f α → ∀ (C : Finset (GA D (Wc D i))), (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C → ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  first | exact @GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall | exact GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall | (intros; apply GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmAllRecords

theorem localLifting_admittedHypotheses_all_alt : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm2 D HW F := by
  intro hBK hTD hEC D HW F _
  exact ⟨GlobalTheory.T.restriction_corestriction_H1f D HW F, GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D,
    GlobalTheory.Per.StrictAdm.strict_adm D, GlobalTheory.T.crystalline_restrict_finite_extension_jumps D, GlobalTheory.T.frobenius_sub_one_surjective_witt_tilt⟩

end GlobalTheory.AdmAllRecords
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatAtHLat

theorem mem_latAt_iff_hat {D : D7} {S T : HSp D} (B : Base S T) (h : Bridge.Gf S) (x : Fin S.rank → D.host.E) :
    x ∈ B.latAt h ↔ (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F (B.F.ΛS : Set (Fin S.rank → D.host.E)) := by
  have e : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
      fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (((h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
    rw [← map_inv]
    funext i
    change _ = Lev.swapAE D _
    rw [RingHom.map_mulVec (Lev.swapAE D)]
    rfl
  change ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS ↔ _
  rw [e]
  constructor
  · intro hz
    have := GlobalTheory.PrincInLevel.swap_symm_mem_hat B.F.ΛS _ hz
    simpa only [AlgEquiv.symm_apply_apply] using this
  · intro hz
    exact GlobalTheory.PrincInLevel.swap_mem_hatL B.F.ΛS _ hz

theorem latAt_eq_hLat : ∀ (D : D7) (S T : HSp D) (B : Base S T), (B.F.ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → ∀ h, B.latAt h = Bridge.hLat S h := by
  intro D S T B hΛ h
  have e : Bridge.hLat S h = Submodule.span (𝓞 D.host.E) {x : Fin S.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (B.F.ΛS : Set (Fin S.rank → D.host.E))} := by
    unfold Bridge.hLat
    rw [hΛ]
    rfl
  rw [e, ← Submodule.span_eq (B.latAt h)]
  congr 1
  ext x
  exact mem_latAt_iff_hat B h x

end GlobalTheory.LatAtHLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanKilledUnionAveragesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_annihilated_union_class_averages : ∀ {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (π : G → Module.End ℂ M), (∀ g, ∀ v ∈ S, π g v ∈ S) → (∀ v ∈ S, π 1 v = v) → (∀ g h, ∀ v ∈ S, π (g * h) v = π h (π g v)) → ∀ (C : Set (G → ℂ)), (∀ c ∈ C, ∀ x : G, (fun g => c (x * g * x⁻¹)) ∈ C) → ∀ v ∈ S, v ∈ Submodule.span ℂ ({w | w ∈ S ∧ ∀ c ∈ C, ∑ g, c g • π g w = 0} ∪ {u | ∃ c ∈ C, ∃ w ∈ S, u = ∑ g, c g • π g w}) := by
  first | exact @GlobalTheory.mem_span_killed_union_averages | exact GlobalTheory.mem_span_killed_union_averages | (intros; apply GlobalTheory.mem_span_killed_union_averages <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfFixedMemSpanTranslates
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.HeckeAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}

def avg (ρ : Representation ℂ G V) (K : Subgroup G) (H : Subgroup K) (v : V) : V :=
  ∑ᶠ κ : K ⧸ H, ρ ((κ.out : K) : G) v

theorem mem_conj {g : G} {t : K} :
    t ∈ (K.map (MulAut.conj g).toMonoidHom).subgroupOf K ↔ g⁻¹ * (t : G) * g ∈ K := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, e⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    rw [← e]; simpa [mul_assoc] using hk
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem fix_eq {H : Subgroup K} {v : V} (hv : ∀ h ∈ H, ρ ((h : K) : G) v = v) {a b : K} (hab : (a : K ⧸ H) = b) :
    ρ (a : G) v = ρ (b : G) v := by
  have hm := QuotientGroup.eq.1 hab
  have : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
  rw [this, map_mul, Module.End.mul_apply, hv _ hm]

end GlobalTheory.HeckeAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicModulusSqrtCharRefinedBlocksInStagesStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicModulusSqrtChar_refinedBlocks_in_stages : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (g : ∀ a b, GL (Fin (d' a b)) k),
    deltaHalf k (fun c : Fin (∑ a, t a) => Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2))
        (flatHom (fun a b => GL (Fin (d' a b)) k) g) =
      deltaHalf k (fun a => Fin (d a)) (relEmbD k e' g) * relDeltaHalfD k (fun a b => Fin (d' a b)) g := by
  first | exact @GlobalTheory.JacStages.deltaHalf_flatHom | exact GlobalTheory.JacStages.deltaHalf_flatHom | (intros; apply GlobalTheory.JacStages.deltaHalf_flatHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SegmentLinkedShiftStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_linked_shift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (t : ℝ), (Δ.nu (t : ℂ)).Linked (Δ.nu ((t - 1 : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one | exact GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one | (intros; apply GlobalTheory.SmGL.Segment.linked_nu_nu_sub_one <;> assumption)
end

