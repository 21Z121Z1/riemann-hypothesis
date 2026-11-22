import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalClosedNonzero
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

noncomputable section

namespace GlobalTheory.UnipClosed

theorem isClosed_unip (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁) (hx : H'.x ≠ 0) :
    IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  set x : Fin d → AE F E := incV F H'.x with hxdef
  set ι : Matrix (Fin d) (Fin d₁) (AE F E) := incM F H'.ι

  set S : Set (UA σ W.J) := {u | mat u *ᵥ x = x ∧ ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} with hS
  obtain ⟨k, hk⟩ : ∃ k, H'.x k ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  have hcu : IsUnit (x k) := by
    have : x k = inclR (F := F) (AF F) (H'.x k) := rfl
    rw [this]; exact (IsUnit.mk0 _ hk).map _
  set c : (AE F E)ˣ := hcu.unit
  have hc : (c : AE F E) = x k := hcu.unit_spec
  have hline : ∀ v w : Fin d → AE F E, (∃ a : AE F E, w = v + a • x) ↔ w = v + ((w - v) k * ↑c⁻¹) • x := by
    intro v w
    constructor
    · rintro ⟨a, rfl⟩
      congr 2
      simp only [add_sub_cancel_left, Pi.smul_apply, smul_eq_mul]
      rw [← hc, mul_assoc, Units.mul_inv, mul_one]
    · intro h; exact ⟨_, h⟩
  have hm : Continuous fun g : UA σ W.J => mat g := Units.continuous_val.comp continuous_subtype_val
  have hSc : IsClosed S := by
    have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ x = x} :=
      isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
    have h2 : IsClosed {u : UA σ W.J | ∀ z, ∃ a : AE F E, mat u *ᵥ (ι *ᵥ z) = ι *ᵥ z + a • x} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun z => ?_
      simp_rw [hline]
      have hf : Continuous fun u : UA σ W.J => mat u *ᵥ (ι *ᵥ z) := hm.matrix_mulVec continuous_const
      have hg : Continuous fun u : UA σ W.J => ((mat u *ᵥ (ι *ᵥ z) - ι *ᵥ z) k * ↑c⁻¹) :=
        ((continuous_apply k).comp (hf.sub continuous_const)).mul continuous_const
      exact isClosed_eq hf (continuous_const.add (hg.smul (continuous_const : Continuous fun _ : UA σ W.J => x)))
    exact h1.inter h2
  have hsub : ∃ H : Subgroup (UA σ W.J), (H : Set (UA σ W.J)) = S := by
    refine ⟨{ carrier := S, one_mem' := ?_, mul_mem' := ?_, inv_mem' := ?_ }, rfl⟩
    · rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
      refine ⟨by rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
      obtain ⟨a, ha⟩ := hv2 z
      obtain ⟨b, hb⟩ := hu2 z
      refine ⟨b + a, ?_⟩
      rw [GlobalTheory.StabHaar.mat_mul, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu1, add_smul, add_assoc]
    · exact ⟨by simp [GlobalTheory.StabHaar.mat_one], fun z => ⟨0, by simp [GlobalTheory.StabHaar.mat_one]⟩⟩
    · rintro u ⟨hu1, hu2⟩
      have e1 : mat u⁻¹ *ᵥ x = x := by
        conv_lhs => rw [← hu1]
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      refine ⟨e1, fun z => ?_⟩
      obtain ⟨a, ha⟩ := hu2 z
      refine ⟨-a, ?_⟩
      have : mat u⁻¹ *ᵥ (mat u *ᵥ (ι *ᵥ z)) = ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
      rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, e1] at this
      rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq, this]
  obtain ⟨H, hH⟩ := hsub
  have : unip σ W H' = H := by
    apply le_antisymm
    · rw [unip, Subgroup.closure_le]; exact hH.symm ▸ subset_rfl
    · intro g hg
      have : g ∈ S := hH ▸ hg
      exact Subgroup.subset_closure this
  rw [this, hH]; exact hSc

end GlobalTheory.UnipClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentSiegelSetIff
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open Formalism.UG (cT)
open GlobalTheory.ThKLiftCusp

noncomputable section

namespace GlobalTheory.UnipMatch

open Matrix

theorem exists_genInv {K : Type} [Field K] {a b : ℕ} (M : Matrix (Fin a) (Fin b) K) :
    ∃ N : Matrix (Fin b) (Fin a) K, M * N * M = M := by
  classical
  let f := Matrix.toLin' M
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype (Submodule.ker_subtype _)
  obtain ⟨g', hg'⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict (LinearMap.range_rangeRestrict f)
  refine ⟨LinearMap.toMatrix' (g' ∘ₗ p), Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  have h1 : p (f x) = f.rangeRestrict x := by
    simpa using LinearMap.congr_fun hp (f.rangeRestrict x)
  have h2 : ∀ y, f (g' y) = y := fun y => by simpa using congrArg Subtype.val (LinearMap.congr_fun hg' y)
  show f (g' (p (f x))) = f x
  rw [h1, h2]
  rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cA_inclR (y : E) : cA σ (inclR (F := F) (AF F) y) = inclR (F := F) (AF F) (σ y) := by
  simp [cA, inclR]

theorem adMat_mulVec_eq {d j : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i l, σ (J l i) = -J i l) (c : E)
    (Y : Matrix (Fin d) (Fin j) E) (z : Fin d → AE F E) (k : Fin j) :
    (adMat F (cT (σ : E →+* E) Y * (c • J.map σ)) *ᵥ z) k =
      -(inclR (F := F) (AF F) c) * formA σ J z (incV F fun i => Y i k) := by
  simp only [mulVec, dotProduct, adMat, map_apply, mul_apply, cT, transpose_apply, Matrix.smul_apply, smul_eq_mul, formA,
    incM, incV, cA_inclR, map_sum, map_mul, map_neg, hJ, Finset.mul_sum, Finset.sum_mul, RingHom.coe_coe]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem cond_iff {d j : ℕ} (J : Matrix (Fin d) (Fin d) E) (hJ : ∀ i l, σ (J l i) = -J i l) {c : E} (hc : c ≠ 0)
    (Y : Matrix (Fin d) (Fin j) E) (U : Matrix (Fin d) (Fin d) (AE F E)) :
    (U * incM F Y = incM F Y ∧
      (∀ z, (∀ k, formA σ J z (incV F fun i => Y i k) = 0) → ∃ a, U *ᵥ z = z + incM F Y *ᵥ a) ∧
      ∀ z k, formA σ J (U *ᵥ z - z) (incV F fun i => Y i k) = 0) ↔
    ((U - 1) * adMat F Y = 0 ∧ adMat F (cT (σ : E →+* E) Y * (c • J.map σ)) * (U - 1) = 0 ∧
      ∀ x : Fin d → E, (cT (σ : E →+* E) Y * (c • J.map σ)) *ᵥ x = 0 →
        ∃ a : Fin j → AF F ⊗[F] E, (U - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F Y *ᵥ a) := by
  classical
  set M := cT (σ : E →+* E) Y * (c • J.map σ) with hM
  have hY : incM F Y = adMat F Y := rfl
  have hu : IsUnit (-(inclR (F := F) (AF F) c)) := ((IsUnit.mk0 c hc).map (inclR (F := F) (AF F))).neg
  have hb : ∀ z, (U - 1) *ᵥ z = U *ᵥ z - z := fun z => by rw [sub_mulVec, one_mulVec]
  have hker : ∀ z, (∀ k, formA σ J z (incV F fun i => Y i k) = 0) ↔ adMat F M *ᵥ z = 0 := fun z => by
    constructor
    · intro h; funext k; rw [adMat_mulVec_eq J hJ c Y z k, h k, mul_zero]; rfl
    · intro h k
      have e := adMat_mulVec_eq J hJ c Y z k
      rw [h] at e
      exact hu.mul_right_eq_zero.1 e.symm
  have h1 : U * incM F Y = incM F Y ↔ (U - 1) * adMat F Y = 0 := by
    rw [hY, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]
  have h3 : (∀ z k, formA σ J (U *ᵥ z - z) (incV F fun i => Y i k) = 0) ↔ adMat F M * (U - 1) = 0 := by
    constructor
    · intro h
      ext k l
      have e : (adMat F M *ᵥ ((U - 1) *ᵥ Pi.single l 1)) k = 0 := by
        rw [adMat_mulVec_eq J hJ c Y _ k, hb, h, mul_zero]
      rw [mulVec_mulVec, mulVec_single_one] at e
      exact e
    · intro h z k
      rw [← hb]
      refine (hker _).2 ?_ k
      rw [mulVec_mulVec, h, zero_mulVec]
  have h2 : (∀ z, (∀ k, formA σ J z (incV F fun i => Y i k) = 0) → ∃ a, U *ᵥ z = z + incM F Y *ᵥ a) ↔
      ∀ x : Fin d → E, M *ᵥ x = 0 →
        ∃ a : Fin j → AF F ⊗[F] E, (U - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = adMat F Y *ᵥ a := by
    constructor
    · intro h x hx
      have hz : adMat F M *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = 0 := funext fun k => by
        rw [show (fun i => inclR (F := F) (AF F) (x i)) = inclR (F := F) (AF F) ∘ x from rfl, adMat,
          ← RingHom.map_mulVec, hx]
        exact map_zero _
      obtain ⟨a, ha⟩ := h _ ((hker _).2 hz)
      exact ⟨a, by rw [hb, ha, hY, add_sub_cancel_left]⟩
    · intro h z hz
      have hz' := (hker z).1 hz
      obtain ⟨N, hN⟩ := exists_genInv M
      set Q : Matrix (Fin d) (Fin d) E := 1 - N * M with hQ
      have hMQ : M * Q = 0 := by rw [hQ, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hN, sub_self]
      have hcol : ∀ l, M *ᵥ (fun i => Q i l) = 0 := fun l => by
        funext k
        have := congrFun (congrFun hMQ k) l
        simpa [mulVec, dotProduct, mul_apply] using this
      choose a ha using fun l => h (fun i => Q i l) (hcol l)
      let A : Matrix (Fin j) (Fin d) (AF F ⊗[F] E) := Matrix.of fun i l => a l i
      have hQz : adMat F Q *ᵥ z = z := by
        have e : adMat F Q = 1 - adMat F N * adMat F M := by
          simp only [adMat]
          rw [hQ, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        rw [e, sub_mulVec, one_mulVec, ← mulVec_mulVec, hz', mulVec_zero, sub_zero]
      have hmQ : (U - 1) * adMat F Q = adMat F Y * A := by
        ext i l
        have := congrFun (ha l) i
        simpa [mulVec, dotProduct, mul_apply, A] using this
      refine ⟨A *ᵥ z, ?_⟩
      calc U *ᵥ z = z + (U - 1) *ᵥ z := by rw [hb]; abel
        _ = z + (U - 1) *ᵥ (adMat F Q *ᵥ z) := by rw [hQz]
        _ = z + incM F Y *ᵥ (A *ᵥ z) := by rw [mulVec_mulVec, hmQ, ← mulVec_mulVec]; rfl
  rw [h1, h2, h3]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, c, b⟩, fun ⟨a, b, c⟩ => ⟨a, c, b⟩⟩

theorem mem_unipSp_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d : ℕ) (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
    ∀ (c : E) (hc : c ≠ 0) (j : ℕ) (Y : Matrix (Fin d) (Fin j) E),
      (∀ k l, form σ W.J (fun i => Y i k) (fun i => Y i l) = 0) →
      ∀ g : UA σ W.J, g ∈ GlobalTheory.ThKLiftCusp.unipSp σ W Y ↔ toGAd hσ W.J hc g ∈ GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y := by
  intro F E _ _ _ _ _ σ hσ B d W r s hW c hc j Y _ g
  have e : (GlobalTheory.ThKLiftCusp.unipSp σ W Y).map (toGAd hσ W.J hc).toMonoidHom =
      GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y := by
    unfold GlobalTheory.ThKLiftCusp.unipSp GlobalTheory.SiegelSet.unipRad
    rw [MonoidHom.map_closure]
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (cond_iff W.J hW.skew hc Y (mat g)).1 hg
    · intro hh
      refine ⟨(toGAd hσ W.J hc).symm h, (cond_iff W.J hW.skew hc Y _).2 ?_, by simp⟩
      have : mat ((toGAd hσ W.J hc).symm h) = ((matHom _ σ (c • W.J.map σ) h) : Matrix (Fin d) (Fin d) (AE F E)) := by
        conv_rhs => rw [← (toGAd hσ W.J hc).apply_symm_apply h]
        rfl
      rw [this]
      exact hh
  rw [← e]
  exact (Subgroup.mem_map_iff_mem (toGAd hσ W.J hc).injective).symm

end GlobalTheory.UnipMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerLeviDecomposition
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PlaneProj
open Matrix
variable {A : Type} [CommRing A] {m n k : Type} [Fintype m] [Fintype n] [Fintype k]

theorem mul_vmv (M : Matrix m n A) (u : n → A) (w : k → A) : M * vecMulVec u w = vecMulVec (M *ᵥ u) w := by
  ext i j; simp [vecMulVec_apply, mul_apply, mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem vmv_transpose (u : m → A) (w : n → A) : (vecMulVec u w)ᵀ = vecMulVec w u := by
  ext i j; simp [vecMulVec_apply, mul_comm]

theorem vmv_map (c : A →+* A) (u : m → A) (w : n → A) : (vecMulVec u w).map c = vecMulVec (c ∘ u) (c ∘ w) := by
  ext i j; simp [vecMulVec_apply]

theorem vmv_mul_vmv (a : m → A) (b : n → A) (u : n → A) (w : k → A) :
    vecMulVec a b * vecMulVec u w = (b ⬝ᵥ u) • vecMulVec a w := by
  ext i j; simp [vecMulVec_apply, mul_apply, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem vmv_mulVec (u : m → A) (w : n → A) (z : n → A) : vecMulVec u w *ᵥ z = (w ⬝ᵥ z) • u := by
  ext i; simp [vecMulVec_apply, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

theorem proj_core {d d₁ : Type} [Fintype d] [Fintype d₁] [DecidableEq d] [DecidableEq d₁] (c : A →+* A)
    (P J : Matrix d d A) (J₁ : Matrix d₁ d₁ A) (ι : Matrix d d₁ A) (π : Matrix d₁ d A) (x y : d → A)
    (hP : Pᵀ * J * P.map c = J) (hPx : P *ᵥ x = x)
    (hframe : vecMulVec x (J *ᵥ (c ∘ y)) + ι * π - vecMulVec y (J *ᵥ (c ∘ x)) = 1)
    (hgram : ιᵀ * J * ι.map c = J₁) (hιx : (ιᵀ * J) *ᵥ (c ∘ x) = 0) (hxι : x ᵥ* (J * ι.map c) = 0)
    (hxx : x ⬝ᵥ (J *ᵥ (c ∘ x)) = 0) (hJ₁ : IsUnit J₁.det) :
    (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = J₁ ∧ IsUnit (π * P * ι).det ∧
      ∀ z, P *ᵥ (ι *ᵥ z) = ι *ᵥ ((π * P * ι) *ᵥ z) + ((J *ᵥ (c ∘ y)) ⬝ᵥ (P *ᵥ (ι *ᵥ z))) • x := by
  set α : d₁ → A := (J *ᵥ (c ∘ y)) ᵥ* (P * ι) with hα
  have hcx : c ∘ x = P.map c *ᵥ (c ∘ x) := by
    funext i; rw [Function.comp_apply, ← RingHom.map_mulVec, hPx]
  have hxP : x ᵥ* Pᵀ = x := by rw [vecMul_transpose, hPx]
  have hwx : (J *ᵥ (c ∘ x)) ᵥ* (P * ι) = 0 := by
    rw [← mulVec_transpose, transpose_mul, hcx, mulVec_mulVec, mulVec_mulVec,
      show ιᵀ * Pᵀ * J * P.map c = ιᵀ * (Pᵀ * J * P.map c) by simp only [Matrix.mul_assoc], hP, hιx]
  have hιπ : ι * π = 1 - vecMulVec x (J *ᵥ (c ∘ y)) + vecMulVec y (J *ᵥ (c ∘ x)) := by
    rw [← hframe]; abel
  have hιh : ι * (π * P * ι) = P * ι - vecMulVec x α := by
    rw [show ι * (π * P * ι) = (ι * π) * (P * ι) by simp only [Matrix.mul_assoc], hιπ, Matrix.add_mul, Matrix.sub_mul,
      Matrix.one_mul, vecMulVec_mul, vecMulVec_mul, hwx]
    ext i j; simp [vecMulVec_apply, α]
  have k1 : (P * ι)ᵀ * J * (P * ι).map c = J₁ := by
    calc (P * ι)ᵀ * J * (P * ι).map c = ιᵀ * (Pᵀ * J * P.map c) * ι.map c := by
          rw [Matrix.map_mul, transpose_mul]; simp only [Matrix.mul_assoc]
      _ = J₁ := by rw [hP, hgram]
  have k2 : (P * ι)ᵀ * J * (vecMulVec x α).map c = 0 := by
    have : ((P * ι)ᵀ * J) *ᵥ (c ∘ x) = 0 := by
      rw [hcx, mulVec_mulVec, transpose_mul,
        show ιᵀ * Pᵀ * J * P.map c = ιᵀ * (Pᵀ * J * P.map c) by simp only [Matrix.mul_assoc], hP, hιx]
    rw [vmv_map, mul_vmv, this]; ext i j; simp [vecMulVec_apply]
  have k3 : (vecMulVec x α)ᵀ * J * (P * ι).map c = 0 := by
    have : x ᵥ* (J * (P * ι).map c) = 0 := by
      calc x ᵥ* (J * (P * ι).map c) = (x ᵥ* Pᵀ) ᵥ* (J * (P.map c * ι.map c)) := by rw [hxP, Matrix.map_mul]
        _ = x ᵥ* (Pᵀ * J * P.map c * ι.map c) := by rw [vecMul_vecMul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hP, hxι]
    rw [vmv_transpose, Matrix.mul_assoc, vecMulVec_mul, this]; ext i j; simp [vecMulVec_apply]
  have k4 : (vecMulVec x α)ᵀ * J * (vecMulVec x α).map c = 0 := by
    rw [vmv_transpose, vmv_map, vecMulVec_mul, vmv_mul_vmv, ← dotProduct_mulVec, hxx, zero_smul]
  have hms : (P * ι - vecMulVec x α).map c = (P * ι).map c - (vecMulVec x α).map c := by
    ext i j; simp only [Matrix.map_apply, Matrix.sub_apply, map_sub]
  have hU : (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = J₁ := by
    have e0 : (π * P * ι)ᵀ * J₁ * (π * P * ι).map c = (ι * (π * P * ι))ᵀ * J * (ι * (π * P * ι)).map c := by
      simp only [← hgram, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e0, hιh, transpose_sub, hms, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, k1, k2, k3, k4]; abel
  set h := π * P * ι with hh
  refine ⟨hU, ?_, fun z => ?_⟩
  · have e := congrArg Matrix.det hU
    rw [det_mul, det_mul, det_transpose, show h.map c = c.mapMatrix h from rfl, ← RingHom.map_det] at e
    have e' : (h.det * c h.det) * J₁.det = 1 * J₁.det := by linear_combination e
    have h1 : h.det * c h.det = 1 := hJ₁.mul_right_cancel e'
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · have e3 : (ι * h) *ᵥ z = (P * ι) *ᵥ z - (α ⬝ᵥ z) • x := by rw [hιh, sub_mulVec, vmv_mulVec]
    have e4 : α ⬝ᵥ z = (J *ᵥ (c ∘ y)) ⬝ᵥ (P *ᵥ (ι *ᵥ z)) := by rw [hα, ← dotProduct_mulVec, mulVec_mulVec]
    rw [← mulVec_mulVec z ι h, ← mulVec_mulVec z P ι, e4] at e3
    rw [e3]; abel

end GlobalTheory.PlaneProj

namespace GlobalTheory.PlaneProj
open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR' (σ : E →ₐ[F] E) (a : E) : cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := by
  show Algebra.TensorProduct.map _ _ ((1 : AF F) ⊗ₜ[F] a) = (1 : AF F) ⊗ₜ[F] σ a
  simp

theorem cA_incV (σ : E →ₐ[F] E) {n : ℕ} (v : Fin n → E) :
    ⇑((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) ∘ incV F v = incV F (⇑σ ∘ v) := by
  funext i; exact cA_inclR' σ (v i)

theorem incM_map (σ : E →ₐ[F] E) {m n : Type} (M : Matrix m n E) :
    (incM F M).map ⇑((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) = incM F (M.map σ) := by
  ext i j; exact cA_inclR' σ (M i j)

theorem incM_mulVec' {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F M *ᵥ incV F v = incV F (M *ᵥ v) := by
  funext i; exact (RingHom.map_mulVec (inclR (F := F) (AF F)) M v i).symm

theorem incV_vecMul {m n : ℕ} (v : Fin m → E) (M : Matrix (Fin m) (Fin n) E) :
    incV F v ᵥ* incM F M = incV F (v ᵥ* M) := by
  funext j; exact (RingHom.map_vecMul (inclR (F := F) (AF F)) M v j).symm

theorem incV_dot {n : ℕ} (u w : Fin n → E) : incV F u ⬝ᵥ incV F w = inclR (F := F) (AF F) (u ⬝ᵥ w) := by
  simp only [incV, dotProduct, map_sum, map_mul]

theorem incM_mul {m n k : Type} [Fintype n] (M : Matrix m n E) (N : Matrix n k E) :
    incM F M * incM F N = incM F (M * N) := (Matrix.map_mul (f := inclR (F := F) (AF F))).symm

theorem incM_vmv {m n : ℕ} (u : Fin m → E) (w : Fin n → E) :
    vecMulVec (incV F u) (incV F w) = incM F (vecMulVec u w) := by
  ext i j; simp [incM, incV, vecMulVec_apply]

theorem incM_transpose {m n : Type} (M : Matrix m n E) : (incM F M)ᵀ = incM F Mᵀ := rfl

theorem incV_zero {n : ℕ} : incV F (0 : Fin n → E) = 0 := by funext i; simp [incV]

end GlobalTheory.PlaneProj

open GlobalTheory.PlaneProj Matrix in

theorem GlobalTheory.PlaneProj.exists_levi_proj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ p : UA σ W.J, mat p *ᵥ incV F H'.x = incV F H'.x → ∃ h₁ : UA σ W₁.J,
      ∀ z : Fin d₁ → AE F E, ∃ a : AE F E, mat p *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ (mat h₁ *ᵥ z) + a • incV F H'.x := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH p hp
  obtain ⟨π, -, hfr, hJ₁⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH
  have hsk := GlobalTheory.PlaneFrame.form_skew hσ hW.skew
  set c : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hc

  have eιx : (H'.ιᵀ * W.J) *ᵥ (⇑σ ∘ H'.x) = 0 := by
    funext j
    have h0 := (hH.orth (Pi.single j 1)).1
    rw [form, dotProduct_comm, dotProduct_mulVec, dotProduct_single_one] at h0
    rw [Pi.zero_apply, ← h0, ← mulVec_mulVec, mulVec_transpose]; rfl
  have exι : H'.x ᵥ* (W.J * H'.ι.map σ) = 0 := by
    funext j
    have h0 : form σ W.J H'.x (H'.ι *ᵥ Pi.single j 1) = 0 := by
      rw [hsk, (hH.orth _).1, map_zero, neg_zero]
    rw [Pi.zero_apply, ← h0, form, ← dotProduct_single_one (H'.x ᵥ* _) j, ← dotProduct_mulVec, ← mulVec_mulVec]
    congr 2
    funext i; simp [mulVec, dotProduct, Pi.single_apply]
  have hframe : vecMulVec (incV F H'.x) (incM F W.J *ᵥ (c ∘ incV F H'.y)) + incM F H'.ι * incM F π -
      vecMulVec (incV F H'.y) (incM F W.J *ᵥ (c ∘ incV F H'.x)) = 1 := by
    rw [cA_incV, cA_incV, incM_mulVec', incM_mulVec', incM_vmv, incM_vmv, incM_mul]
    have e1 : incM F (vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y))) + incM F (H'.ι * π) - incM F (vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x))) =
        incM F (vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y)) + H'.ι * π - vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x))) := by
      ext i j; simp only [incM, Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, map_add, map_sub]
    rw [e1]
    have e2 : vecMulVec H'.x (W.J *ᵥ (⇑σ ∘ H'.y)) + H'.ι * π - vecMulVec H'.y (W.J *ᵥ (⇑σ ∘ H'.x)) = 1 := hfr
    rw [e2]; ext i j; simp [incM, Matrix.one_apply]
  have hgram : (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map c = incM F W₁.J := by
    rw [incM_map, incM_transpose, incM_mul, incM_mul, hH.gram]
  have hιx : ((incM F H'.ι)ᵀ * incM F W.J) *ᵥ (c ∘ incV F H'.x) = 0 := by
    rw [cA_incV, incM_transpose, incM_mul, incM_mulVec', eιx, incV_zero]
  have hxι : incV F H'.x ᵥ* (incM F W.J * (incM F H'.ι).map c) = 0 := by
    rw [incM_map, incM_mul, incV_vecMul, exι, incV_zero]
  have hxx : incV F H'.x ⬝ᵥ (incM F W.J *ᵥ (c ∘ incV F H'.x)) = 0 := by
    rw [cA_incV, incM_mulVec', incV_dot]
    have : H'.x ⬝ᵥ (W.J *ᵥ (⇑σ ∘ H'.x)) = 0 := hH.xx
    rw [this, map_zero]
  have hJ₁' : IsUnit (incM F W₁.J).det := by
    rw [show incM F W₁.J = (inclR (F := F) (AF F)).mapMatrix W₁.J from rfl, ← RingHom.map_det]
    exact hJ₁.map _
  obtain ⟨hU, hdet, hz⟩ := proj_core c (mat p) (incM F W.J) (incM F W₁.J) (incM F H'.ι) (incM F π) (incV F H'.x) (incV F H'.y)
    p.2 hp hframe hgram hιx hxι hxx hJ₁'
  exact ⟨⟨Matrix.GeneralLinearGroup.mk'' _ hdet, hU⟩, fun z => ⟨_, hz z⟩⟩
end

