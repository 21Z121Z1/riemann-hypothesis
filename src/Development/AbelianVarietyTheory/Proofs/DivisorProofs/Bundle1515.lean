import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalRationalTranslate
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.EisCT

theorem matrix_unip_cover {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] (s : A →+* A)
    (hs : ∀ a, s (s a) = a) (hsc : Continuous s) {n r : ℕ} (J Ji : Matrix (Fin n) (Fin n) A) (hJ : cT s J = J)
    (hJi : J * Ji = 1) (C D : Matrix (Fin n) (Fin r) A) (xx : cT s C * J * C = 0) (yy : cT s D * J * D = 0)
    (xy : cT s C * J * D = 1) (h : A) (hh : h + h = 1) (S₀ : Subring (Matrix (Fin n) (Fin n) A))
    (hS : ∀ M ∈ S₀, cT s M ∈ S₀) (hJS : J ∈ S₀) (hJiS : Ji ∈ S₀) (hCD : C * cT s D ∈ S₀)
    (hhS : Matrix.scalar (Fin n) h ∈ S₀) (K : Set (Matrix (Fin n) (Fin n) A)) (hK : IsCompact K)
    (hKs : ∀ M, ∃ y ∈ S₀, M - y ∈ K) :
    ∃ K' : Set (GL (Fin n) A), IsCompact K' ∧ (∀ g ∈ K', cT s g.1 * J * g.1 = J) ∧
      ∀ g : GL (Fin n) A, cT s g.1 * J * g.1 = J → (g.1 - 1) * C = 0 →
        (∃ B : Matrix (Fin r) (Fin n) A, (g.1 - 1) * (1 - D * (cT s C * J)) = C * B) →
        ∃ γ : GL (Fin n) A, cT s γ.1 * J * γ.1 = J ∧ (γ.1 - 1) * C = 0 ∧
          (∃ B : Matrix (Fin r) (Fin n) A, (γ.1 - 1) * (1 - D * (cT s C * J)) = C * B) ∧ γ.1 ∈ S₀ ∧ (γ⁻¹).1 ∈ S₀ ∧ γ * g ∈ K' := by
  have cc : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) A), cT s (cT s Z) = Z := fun Z => Matrix.ext fun i j => hs _
  have hiJ : Ji * J = 1 := mul_eq_one_comm.1 hJi
  have yx : cT s D * J * C = 1 := by
    have := congrArg (cT s) xy
    rwa [cT_mul, cT_mul, cc, hJ, cT_one, ← Matrix.mul_assoc] at this
  have hcJi : cT s Ji = Ji := by
    have h1 := congrArg (cT s) hJi
    rw [cT_mul, hJ, cT_one] at h1
    rw [← Matrix.mul_one (cT s Ji), ← hJi, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  let st : Matrix (Fin n) (Fin n) A →+ Matrix (Fin n) (Fin n) A :=
    { toFun := fun X => Ji * cT s X * J
      map_zero' := by simp [cT]
      map_add' := fun X Y => by simp [cT, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul] }
  have st_apply : ∀ X, st X = Ji * cT s X * J := fun _ => rfl
  have hU : ∀ g : Matrix (Fin n) (Fin n) A, st g * g = 1 ↔ cT s g * J * g = J := fun g => by
    rw [st_apply, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s g)]
    constructor
    · intro h
      have := congrArg (J * ·) h
      simpa only [← Matrix.mul_assoc, hJi, Matrix.one_mul, Matrix.mul_one] using this
    · intro h
      rw [h, hiJ]
  have hst : st (C * (cT s D * J)) = D * (cT s C * J) := by
    rw [st_apply, cT_mul, cT_mul, cc, hJ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hiJ, Matrix.one_mul,
      Matrix.mul_assoc]
  obtain ⟨K', hK', h1, h2⟩ := GlobalTheory.TwoStepUnipotent.compact_mod_subring (Matrix (Fin n) (Fin n) A) st S₀
    (C * (cT s D * J)) (D * (cT s C * J)) (Matrix.scalar _ h) K
    ((continuous_const.matrix_mul (continuous_id.matrix_map hsc).matrix_transpose).matrix_mul continuous_const)
    (fun X Y => by
      simp only [st_apply, cT_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc J, hJi, Matrix.one_mul])
    (fun X => by
      simp only [st_apply, cT_mul, hJ, hcJi, cc, Matrix.mul_assoc]
      rw [hiJ, Matrix.mul_one, ← Matrix.mul_assoc, hiJ, Matrix.one_mul])
    (fun X hX => S₀.mul_mem (S₀.mul_mem hJiS (hS X hX)) hJS)
    (by rw [← Matrix.mul_assoc]; exact S₀.mul_mem hCD hJS) hhS
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (cT s D * J), yx, Matrix.one_mul]) hst
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (cT s D * J), yy]; simp)
    (by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (cT s C * J), xx]; simp)
    (by rw [← map_add, hh, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq) hK hKs
  refine ⟨K', hK', fun g hg => (hU _).1 (h1 g hg).1, fun g u1 u2 ⟨B, u3⟩ => ?_⟩
  obtain ⟨γ, ⟨p1, p2, p3⟩, p4⟩ := h2 g ⟨(hU _).2 u1, by rw [← Matrix.mul_assoc, u2, Matrix.zero_mul], by
    rw [Matrix.mul_assoc, u3, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_assoc C, yx]; simp⟩
  refine ⟨γ, (hU _).1 p1, ?_, ⟨cT s D * J * ((γ.1 - 1) * (1 - D * (cT s C * J))), ?_⟩, p4⟩
  · have := congrArg (· * C) p2
    simp only [Matrix.zero_mul] at this
    rwa [Matrix.mul_assoc, Matrix.mul_assoc C, yx, Matrix.mul_one] at this
  · rw [Matrix.mul_assoc, Matrix.sub_mul 1, Matrix.one_mul, sub_eq_zero] at p3
    rw [← Matrix.mul_assoc C, ← p3]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem mem_unipRad_iff_dual {C D : Matrix (Fin n) (Fin r) E} (xy : cT (σ : E →+* E) C * J * D = 1) (g : GAd σ J) :
    g ∈ unipRad σ J C ↔ ((matHom _ σ J g).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin r) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J g).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
  constructor
  · intro hg
    simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
      sub_eq_iff_eq_add, zero_add]
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨h1, -, h3⟩ := hg
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, xy, Matrix.mul_one, Matrix.one_mul, sub_self]
      choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
        (funext fun j => congrFun (congrFun hT j) k)
      refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
      rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
      ext i k
      exact congrFun (ha k) i
    | one => exact ⟨by simp, 0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a1, A, a2⟩ := ha
      obtain ⟨b1, B, b2⟩ := hb
      refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
      rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
        add_assoc]
    | inv a _ ha =>
      obtain ⟨a1, A, a2⟩ := ha
      have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
        conv_lhs => rw [← a1]
        rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      refine ⟨i1, -A, ?_⟩
      have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
      rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
        inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
      rw [Matrix.mul_neg]
      conv_rhs => rw [this]
      abel
  · rintro ⟨h1, B, h2⟩
    refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
    · have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
      have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
      rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
      conv_lhs => rw [← h1, cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J g).1)]
      exact congrArg _ hg
    · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
          fun i => inclR (F := F) (AF F) (x i) := by
        funext i
        have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
        rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
        exact this.symm
      rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]

theorem unipRad_cover_of_dual (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {C D : Matrix (Fin n) (Fin r) E}
    (xx : cT (σ : E →+* E) C * J * C = 0) (yy : cT (σ : E →+* E) D * J * D = 0)
    (xy : cT (σ : E →+* E) C * J * D = 1) :
    ∃ K : Set (GAd σ J), IsCompact K ∧ ∀ u ∈ unipRad σ J C, ∃ ν ∈ ratPts σ J, ν ∈ unipRad σ J C ∧ ν * u ∈ K := by
  obtain ⟨K, hK, hKs⟩ := GlobalTheory.AutFunCompare.tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  let φ := inclR (F := F) (E := E) (AF F)
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have c2 : ∀ Z Z' : Matrix (Fin n) (Fin r) E, cT (sigR (AF F) σ) (adMat F Z) * adMat F J * adMat F Z' =
      adMat F (cT (σ : E →+* E) Z * J * Z') := fun Z Z' => by
    rw [c1]; simp only [adMat, Matrix.map_mul]
  obtain ⟨K', hK', h1, h2⟩ := matrix_unip_cover (sigR (AF F) σ)
    (fun a => by
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (hσ x))
    (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ) (adMat F J) (adMat F J⁻¹)
    ((c1 J).trans (congrArg (adMat F) (Matrix.ext fun i j => hJ.1 i j)))
    (by rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hJ.2), Matrix.map_one _ (map_zero _) (map_one _)])
    (adMat F C) (adMat F D)
    (by rw [c2, xx]; exact Matrix.map_zero _ (map_zero _)) (by rw [c2, yy]; exact Matrix.map_zero _ (map_zero _))
    (by rw [c2, xy]; exact Matrix.map_one _ (map_zero _) (map_one _)) (φ (1 / 2))
    (by rw [← map_add, add_halves, map_one]) (φ.mapMatrix (m := Fin n)).range
    (by rintro _ ⟨X, rfl⟩; exact ⟨_, (c1 X).symm⟩) ⟨_, rfl⟩ ⟨_, rfl⟩
    ⟨C * cT (σ : E →+* E) D, by rw [c1]; exact Matrix.map_mul⟩
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩)
  have e : 1 - adMat F D * (cT (sigR (AF F) σ) (adMat F C) * adMat F J) =
      adMat F (1 - D * (cT (σ : E →+* E) C * J)) := by
    rw [c1]
    simp only [adMat]
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul, Matrix.map_mul]
  rw [e] at h2
  refine ⟨matHom _ σ J ⁻¹' K', (isEmbedding_matHom _ σ J).isInducing.isCompact_preimage' hK'
    fun g hg => ⟨⟨g, h1 g hg⟩, rfl⟩, fun u hu => ?_⟩
  obtain ⟨u1, u2⟩ := (mem_unipRad_iff_dual xy u).1 hu
  obtain ⟨γ, p1, p2, p3, ⟨a, ha⟩, ⟨b, hb⟩, p4⟩ := h2 (matHom _ σ J u) u.2 u1 u2
  refine ⟨⟨γ, p1⟩, ?_, (mem_unipRad_iff_dual xy _).2 ⟨p2, p3⟩, p4⟩
  have inj : Function.Injective (φ.mapMatrix (m := Fin n)) :=
    Matrix.map_injective GlobalTheory.AutFunCompare.inclA_injective
  have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, Units.mul_inv])
  refine ⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_, Units.ext ha⟩
  rw [← ha] at p1
  rw [map_mul, map_mul]
  exact p1

theorem unipotent_radical_compact_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∃ C : Set (GAd σ J), IsCompact C ∧
      ∀ u ∈ unipRad σ J (col0 X), ∃ ν ∈ ratPts σ J, ν ∈ unipRad σ J (col0 X) ∧ ν * u ∈ C := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS
  obtain ⟨hc, -, hJ, -, hW, -, -⟩ := hS
  have key : ∀ (Z Z' : Matrix (Fin n) (Fin (r + 1)) E) (i j : Fin 1),
      (cT (σ : E →+* E) (col0 Z) * J * col0 Z') i j = (cT (σ : E →+* E) Z * J * Z') 0 0 := fun _ _ _ _ => rfl
  refine unipRad_cover_of_dual (D := col0 Y) (sigma_sigma hc) hJ ?_ ?_ ?_
  · ext i j; rw [key, hW.xx]; rfl
  · ext i j; rw [key, hW.yy]; rfl
  · ext i j; rw [key, hW.xy, Subsingleton.elim i j]; simp

end GlobalTheory.EisCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelLeTensorRangeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAutForms_weight_level_le_tensor_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → forms S lam K' ≤ LinearMap.range (Phi S lam K') := by
  first | exact @GlobalTheory.BCT.TrKer.forms_le_range | exact GlobalTheory.BCT.TrKer.forms_le_range | (intros; apply GlobalTheory.BCT.TrKer.forms_le_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTorusElementExists
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.FrameTorus

open Matrix

section Gen

variable {A : Type} [CommRing A] {n q : ℕ}

theorem mul_core (X Y : Matrix (Fin n) (Fin q) A) (RX RY : Matrix (Fin q) (Fin n) A) (a b a' b' : Fin q → A)
    (h1 : RY * X = 1) (h2 : RY * Y = 0) (h3 : RX * X = 0) (h4 : RX * Y = 1)
    (ha : ∀ i, a i + a' i + a i * a' i = 0) (hb : ∀ i, b i + b' i + b i * b' i = 0) :
    (1 + X * diagonal a * RY + Y * diagonal b * RX) * (1 + X * diagonal a' * RY + Y * diagonal b' * RX) = 1 := by
  first
  | exact @_root_.GlobalTheory.AbelianSumIdentityFourth.main
  | exact _root_.GlobalTheory.AbelianSumIdentityFourth.main
  | (apply _root_.GlobalTheory.AbelianSumIdentityFourth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbelianSumIdentityFourth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbelianSumIdentityFourth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbelianSumIdentityFourth.main ..)

end Gen

section Gen2

variable {A : Type} [CommRing A] {n q : ℕ}

theorem unitary_core (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A) (a b : Fin q → A)
    (h1 : Xᵀ * J * Xc = 0) (h2 : Xᵀ * J * Yc = 1) (h3 : Yᵀ * J * Xc = 1) (h4 : Yᵀ * J * Yc = 0)
    (hab : ∀ i, a i + b i + a i * b i = 0) :
    (1 + J * Yc * diagonal a * Xᵀ + J * Xc * diagonal b * Yᵀ) * J *
      (1 + Xc * diagonal a * (Yᵀ * J) + Yc * diagonal b * (Xᵀ * J)) = J := by
  first
  | exact @_root_.GlobalTheory.DiagonalKeyIdentity.main
  | exact _root_.GlobalTheory.DiagonalKeyIdentity.main
  | (apply _root_.GlobalTheory.DiagonalKeyIdentity.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiagonalKeyIdentity.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiagonalKeyIdentity.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiagonalKeyIdentity.main ..)

theorem unitary_gen (c : A →+* A) (J : Matrix (Fin n) (Fin n) A) (X Xc Y Yc : Matrix (Fin n) (Fin q) A)
    (RX RY : Matrix (Fin q) (Fin n) A) (a b : Fin q → A)
    (hRYt : RYᵀ = J * Yc) (hRXt : RXᵀ = J * Xc) (hXc : X.map c = Xc) (hYc : Y.map c = Yc)
    (hRYc : RY.map c = Yᵀ * J) (hRXc : RX.map c = Xᵀ * J) (hac : ∀ i, c (a i) = a i) (hbc : ∀ i, c (b i) = b i)
    (h1 : Xᵀ * J * Xc = 0) (h2 : Xᵀ * J * Yc = 1) (h3 : Yᵀ * J * Xc = 1) (h4 : Yᵀ * J * Yc = 0)
    (hab : ∀ i, a i + b i + a i * b i = 0) :
    (1 + X * diagonal a * RY + Y * diagonal b * RX)ᵀ * J * (1 + X * diagonal a * RY + Y * diagonal b * RX).map c = J := by
  have hT : (1 + X * diagonal a * RY + Y * diagonal b * RX)ᵀ = 1 + J * Yc * diagonal a * Xᵀ + J * Xc * diagonal b * Yᵀ := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.diagonal_transpose, hRYt, hRXt,
      Matrix.mul_assoc]
  have hC : (1 + X * diagonal a * RY + Y * diagonal b * RX).map c =
      1 + Xc * diagonal a * (Yᵀ * J) + Yc * diagonal b * (Xᵀ * J) := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c),
      Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero c),
      Matrix.diagonal_map (map_zero c), hXc, hYc, hRYc, hRXc]
    simp only [hac, hbc]
  rw [hT, hC]
  exact unitary_core J X Xc Y Yc a b h1 h2 h3 h4 hab

end Gen2

section Conc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem realAd_mul' (a b : ℝ) : realAd F a * realAd F b = realAd F (a * b) := by
  unfold realAd
  simp only [LinearMap.inl_apply, map_mul]
  refine Prod.ext ?_ ?_
  · show _ * _ = _
    rw [← map_mul]
  · exact mul_zero _

theorem realAd_add' (s t : ℝ) : realAd F (s + t) = realAd F s + realAd F t := by
  simp only [realAd, map_add]
  rfl

theorem realAd_zero' : realAd F 0 = 0 := by
  simp only [realAd, map_zero]
  rfl

theorem realAd_key {t : ℝ} (ht : t ≠ 0) :
    realAd F (t - 1) + realAd F (t⁻¹ - 1) + realAd F (t - 1) * realAd F (t⁻¹ - 1) = 0 := by
  rw [realAd_mul', ← realAd_add', ← realAd_add']
  have : t - 1 + (t⁻¹ - 1) + (t - 1) * (t⁻¹ - 1) = 0 := by field_simp; ring
  rw [this, realAd_zero']

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

def colMat {n p : ℕ} (u : Fin p → Fin n → E) : Matrix (Fin n) (Fin p) E := Matrix.of fun k i => u i k

theorem colMat_form (σ : E →ₐ[F] E) {n p p' : ℕ} (J : Matrix (Fin n) (Fin n) E) (u : Fin p → Fin n → E)
    (v : Fin p' → Fin n → E) (i : Fin p) (j : Fin p') :
    ((colMat u)ᵀ * J * (colMat v).map (σ : E →+* E)) i j = form σ J (u i) (v j) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, form, dotProduct, Matrix.mulVec, colMat]

theorem tr_eq {n p p' : ℕ} (s : E →+* E) (J : Matrix (Fin n) (Fin n) E) (U : Matrix (Fin n) (Fin p) E)
    (V : Matrix (Fin n) (Fin p') E) : (V.map s)ᵀ * Jᵀ * U = (Uᵀ * J * V.map s)ᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Conc

theorem exists_isTorusU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → ∀ (q : ℕ) (x y : Fin q → Fin n → E),
    IsFrameU σ X.J x y → ∀ t : Fin q → ℝ, (∀ i, 0 < t i) → ∃ a : UA σ X.J, IsTorusU x y t a := by
  intro F E _ _ _ _ _ σ B n X r s hB hX q x y hF t ht
  have hσσ := sigma_sigma hB.cm
  set J := X.J with hJdef
  set sg : E →+* E := (σ : E →+* E) with hsg
  set ι : E →+* AE F E := inclR (F := F) (AF F) with hι
  set c : AE F E →+* AE F E := ((cA σ : AE F E →ₐ[AF F] AE F E) : AE F E →+* AE F E) with hc
  have hcι : ∀ e, c (ι e) = ι (sg e) := fun e => cA_inclR σ e
  have hconj : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin p') E), (M.map ι).map c = (M.map sg).map ι := by
    intro p p' M; ext i j; simp only [Matrix.map_apply]; exact hcι _
  set Xe := colMat x with hXe
  set Ye := colMat y with hYe
  have hXX : Xeᵀ * J * Xe.map sg = 0 := by ext i j; rw [colMat_form]; exact hF.1 i j
  have hYY : Yeᵀ * J * Ye.map sg = 0 := by ext i j; rw [colMat_form]; exact hF.2.1 i j
  have hXY : Xeᵀ * J * Ye.map sg = 1 := by ext i j; rw [colMat_form, hF.2.2 i j, Matrix.one_apply]
  have hJt : Jᵀ.map sg = J := by ext i j; exact hX.herm i j
  have hss : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin p') E), (M.map sg).map sg = M := by
    intro p p' M; ext i j; simp [hsg, hσσ]
  have hYX : Yeᵀ * J * Xe.map sg = 1 := by
    have e : Yeᵀ * J * Xe.map sg = ((Xeᵀ * J * Ye.map sg)ᵀ).map sg := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul, hJt,
        Matrix.transpose_map, hss, Matrix.mul_assoc]
    rw [e, hXY, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]

  set RYe : Matrix (Fin q) (Fin n) E := (Ye.map sg)ᵀ * Jᵀ with hRYe
  set RXe : Matrix (Fin q) (Fin n) E := (Xe.map sg)ᵀ * Jᵀ with hRXe
  have mapι : ∀ {p p' : ℕ} (M : Matrix (Fin p) (Fin n) E) (N : Matrix (Fin n) (Fin p') E), M.map ι * N.map ι = (M * N).map ι :=
    fun M N => (Matrix.map_mul).symm
  have z0 : ∀ {p p' : ℕ}, (0 : Matrix (Fin p) (Fin p') E).map ι = 0 := by intros; exact Matrix.map_zero _ (map_zero _)
  have o1 : ∀ {p : ℕ}, (1 : Matrix (Fin p) (Fin p) E).map ι = 1 := by intros; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : RYe.map ι * Xe.map ι = 1 := by rw [mapι, hRYe, tr_eq, hXY, Matrix.transpose_one, o1]
  have h2 : RYe.map ι * Ye.map ι = 0 := by rw [mapι, hRYe, tr_eq, hYY, Matrix.transpose_zero, z0]
  have h3 : RXe.map ι * Xe.map ι = 0 := by rw [mapι, hRXe, tr_eq, hXX, Matrix.transpose_zero, z0]
  have h4 : RXe.map ι * Ye.map ι = 1 := by rw [mapι, hRXe, tr_eq, hYX, Matrix.transpose_one, o1]
  set al : (Fin q → ℝ) → Fin q → AE F E := fun t i => algebraMap (AF F) (AE F E) (realAd F (t i - 1)) with hal
  have key : ∀ u : Fin q → ℝ, (∀ i, u i ≠ 0) → ∀ i, al u i + al (fun i => (u i)⁻¹) i + al u i * al (fun i => (u i)⁻¹) i = 0 := by
    intro u hu i
    simp only [hal, ← map_add, ← map_mul, realAd_key (hu i), map_zero]
  set M : (Fin q → ℝ) → Matrix (Fin n) (Fin n) (AE F E) := fun u =>
    1 + Xe.map ι * diagonal (al u) * RYe.map ι + Ye.map ι * diagonal (al (fun i => (u i)⁻¹)) * RXe.map ι with hM
  have ht0 : ∀ i, t i ≠ 0 := fun i => (ht i).ne'
  have ht0' : ∀ i, (fun i => (t i)⁻¹) i ≠ 0 := fun i => inv_ne_zero (ht0 i)
  have hinv : M t * M (fun i => (t i)⁻¹) = 1 :=
    mul_core _ _ _ _ _ _ _ _ h1 h2 h3 h4 (key t ht0) (key _ ht0')

  have hmem : (⟨M t, M (fun i => (t i)⁻¹), hinv, (Matrix.mul_eq_one_comm_of_card_eq (Fin n) (Fin n) (AE F E) rfl).mp hinv⟩ : GL (Fin n) (AE F E)) ∈
      UG (cA σ) (incM F X.J) := by
    show (M t)ᵀ * J.map ι * (M t).map c = J.map ι
    refine unitary_gen c (J.map ι) (Xe.map ι) ((Xe.map sg).map ι) (Ye.map ι) ((Ye.map sg).map ι) (RXe.map ι) (RYe.map ι)
      (al t) (al (fun i => (t i)⁻¹)) ?_ ?_ (hconj Xe) (hconj Ye) ?_ ?_ (fun i => (cA σ).commutes _) (fun i => (cA σ).commutes _)
      ?_ ?_ ?_ ?_ (key t ht0)
    · rw [← Matrix.transpose_map, hRYe, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
        Matrix.map_mul]
    · rw [← Matrix.transpose_map, hRXe, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
        Matrix.map_mul]
    · rw [hconj, hRYe, Matrix.map_mul, hJt, Matrix.transpose_map, hss, Matrix.map_mul, Matrix.transpose_map]
    · rw [hconj, hRXe, Matrix.map_mul, hJt, Matrix.transpose_map, hss, Matrix.map_mul, Matrix.transpose_map]
    · rw [← Matrix.transpose_map, mapι, mapι, hXX, z0]
    · rw [← Matrix.transpose_map, mapι, mapι, hXY, o1]
    · rw [← Matrix.transpose_map, mapι, mapι, hYX, o1]
    · rw [← Matrix.transpose_map, mapι, mapι, hYY, z0]

  have hM1 : M t - 1 = Xe.map ι * diagonal (al t) * RYe.map ι + Ye.map ι * diagonal (al (fun i => (t i)⁻¹)) * RXe.map ι := by
    simp only [hM]; abel
  have col : ∀ (N : Matrix (Fin n) (Fin n) (AE F E)) {p : ℕ} (Z : Matrix (Fin n) (Fin p) (AE F E)) (i : Fin p),
      N *ᵥ (fun k => Z k i) = fun k => (N * Z) k i := by
    intro N p Z i; funext k; simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  refine ⟨⟨_, hmem⟩, fun i => ?_, fun i => ?_, fun z hzx hzy => ?_⟩
  · have hx : incV F (x i) = fun k => (Xe.map ι) k i := rfl
    have e : (M t - 1) * Xe.map ι = Xe.map ι * diagonal (al t) := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3, Matrix.mul_one, Matrix.mul_zero, add_zero]
    show (M t - 1) *ᵥ incV F (x i) = _
    rw [hx, col, e]
    funext k
    simp [Matrix.mul_diagonal, Algebra.smul_def, hal, mul_comm]
  · have hy : incV F (y i) = fun k => (Ye.map ι) k i := rfl
    have e : (M t - 1) * Ye.map ι = Ye.map ι * diagonal (al (fun i => (t i)⁻¹)) := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, h2, h4, Matrix.mul_one, Matrix.mul_zero, zero_add]
    show (M t - 1) *ᵥ incV F (y i) = _
    rw [hy, col, e]
    funext k
    simp [Matrix.mul_diagonal, Algebra.smul_def, hal, mul_comm]
  · set Ze := colMat (fun _ : Fin 1 => z) with hZe
    have hz : incV F z = fun k => (Ze.map ι) k 0 := rfl
    have hYZ : RYe.map ι * Ze.map ι = 0 := by
      have e0 : Zeᵀ * J * Ye.map sg = 0 := by ext i j; rw [colMat_form]; exact hzy j
      rw [mapι, hRYe, tr_eq, e0, Matrix.transpose_zero, z0]
    have hXZ : RXe.map ι * Ze.map ι = 0 := by
      have e0 : Zeᵀ * J * Xe.map sg = 0 := by ext i j; rw [colMat_form]; exact hzx j
      rw [mapι, hRXe, tr_eq, e0, Matrix.transpose_zero, z0]
    have e : (M t - 1) * Ze.map ι = 0 := by
      rw [hM1]; simp only [Matrix.add_mul, Matrix.mul_assoc, hYZ, hXZ, Matrix.mul_zero, add_zero]
    show (M t - 1) *ᵥ incV F z = 0
    rw [hz, col, e]
    rfl

end GlobalTheory.FrameTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumProductExistsNonzero
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

namespace GlobalTheory.VacLine

theorem vacProd_ne_zero_somewhere : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in cofinite, vac v = indO v) → ∃ y : κ → Af F, vacProd vac y ≠ 0 := by
  intro F _ _ κ vac hne hcof
  classical
  have hS : {v : Pl F | ¬ vac v = indO v}.Finite := Filter.eventually_cofinite.mp hcof
  have hz : ∀ v, ∃ z : κ → Fv F v, vac v z ≠ 0 := fun v => by
    by_contra h
    push_neg at h
    exact hne v (funext h)
  choose z hz using hz
  set S := hS.toFinset with hSdef
  refine ⟨fun i => ∑ v ∈ S, singleFin v (z v i), ?_⟩
  have hev : ∀ (u : Pl F) (i : κ), evalV F u (∑ v ∈ S, singleFin v (z v i)) = if u ∈ S then z u i else 0 := by
    intro u i
    rw [map_sum]
    split_ifs with hu
    · rw [Finset.sum_eq_single u]
      · exact GlobalTheory.AdelicU.evalV_singleFin_self u (z u i)
      · intro b _ hb
        exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _
      · intro h; exact absurd hu h
    · apply Finset.sum_eq_zero
      intro b hb
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (fun h : u = b => hu (h ▸ hb)) _
  unfold vacProd
  have hsub : Function.mulSupport (fun u : Pl F => vac u fun i => evalV F u (∑ v ∈ S, singleFin v (z v i))) ⊆ (S : Set (Pl F)) := by
    intro u hu
    by_contra hnot
    apply hu
    have hmem : u ∉ S := hnot
    have hvu : vac u = indO u := by
      by_contra h
      exact hmem (by rw [hSdef, Set.Finite.mem_toFinset]; exact h)
    simp only [hev, hmem, if_false]
    rw [hvu]
    simp [indO, Set.indicator, zero_mem]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_ne_zero_iff]
  intro u hu
  have : (fun i => evalV F u (∑ v ∈ S, singleFin v (z v i))) = z u := by
    funext i; rw [hev, if_pos hu]
  rw [this]
  exact hz u

end GlobalTheory.VacLine
end

