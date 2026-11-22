import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaCharHalfDifferentiableNeZeroFamilies
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ThetaHalf

theorem exists_real_of_half {g : ℕ} {c : Fin g → ℂ} (hc : ∀ i, c i = 0 ∨ c i = 1 / 2) :
    ∃ a : Fin g → ℝ, c = fun i => (a i : ℂ) := by
  refine ⟨fun i => if c i = 0 then 0 else 1 / 2, funext fun i => ?_⟩
  rcases hc i with h | h
  · show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_pos h, h, Complex.ofReal_zero]
  · have h0 : c i ≠ 0 := by rw [h]; norm_num
    show c i = ((if c i = 0 then (0 : ℝ) else 1 / 2 : ℝ) : ℂ)
    rw [if_neg h0, h]
    norm_num

theorem thetaChar_holomorphic_ne_zero : ∀ (g : ℕ) (c₁ c₂ : Fin g → ℂ), (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → (∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → (τ.map Complex.im).PosDef → Differentiable ℂ (thetaChar τ c₁ c₂) ∧ ∃ z, thetaChar τ c₁ c₂ z ≠ 0) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B → (∀ b ∈ B, (τ b).IsSymm ∧ ((τ b).map Complex.im).PosDef) → (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B ∧ DifferentiableOn ℂ (fun b => τ b i j) B) → DifferentiableOn ℂ (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => thetaChar (τ bz.1) c₁ c₂ (h bz.1 *ᵥ bz.2)) (B ×ˢ Set.univ) := by
  intro g c₁ c₂ h₁ h₂
  obtain ⟨a, rfl⟩ := exists_real_of_half h₁
  obtain ⟨b, rfl⟩ := exists_real_of_half h₂
  refine ⟨fun τ hs hp => ⟨GlobalTheory.CanTh.differentiable_thetaChar (GlobalTheory.CanTh.mem_thetaDomain hp) a b, ?_⟩, ?_⟩
  · by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact GlobalTheory.CanTh.thetaChar_ne_zero hs hp a b (funext hcon)
  · intro m B h τ _ hτ hdiff
    have hT : ∀ i j, DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => τ w.1 i j) (B ×ˢ Set.univ) :=
      fun i j => (hdiff i j).2.comp differentiableOn_fst fun w hw => hw.1
    have hZ : DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => h w.1 *ᵥ w.2) (B ×ˢ Set.univ) := by
      rw [differentiableOn_pi]
      intro i
      simp only [Matrix.mulVec, dotProduct]
      have hj : ∀ j, DifferentiableOn ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => h w.1 i j) (B ×ˢ Set.univ) :=
        fun j => (hdiff i j).1.comp differentiableOn_fst fun w hw => hw.1
      refine DifferentiableOn.fun_sum fun j _ => (hj j).mul ?_
      have hs : Differentiable ℂ (fun w : (Fin m → ℂ) × (Fin g → ℂ) => w.2 j) := by fun_prop
      exact hs.differentiableOn
    have hdom : ∀ w ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)), τ w.1 ∈ ReciprocityTheory.PTheta.ThetaDomain (Fin g) :=
      fun w hw => GlobalTheory.CanTh.mem_thetaDomain (hτ w.1 hw.1).2
    exact GlobalTheory.CanTh.differentiableOn_thetaChar hT hZ hdom a b

end GlobalTheory.ThetaHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TrivProdOfSmallExtension
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.SmallExtLift

theorem triv_prod_of_small_extension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (ε : R), (∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) → ∀ (X Y : Over (Sp R)) (x₀ : 𝟙_ (Over (Sp R)) ⟶ X) (y₀ : 𝟙_ (Over (Sp R)) ⟶ Y), Flat X.hom → Flat Y.hom → IsProper X.hom → IsProper Y.hom → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (X).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (X).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → (∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ (Y).left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' (Y).hom (Spec.map (CommRingCat.ofHom g)) → Function.Bijective f'.appTop.hom) → ∀ M : LB (X ⊗ Y).left, M.IsLB → Triv (M.pull (lift (𝟙 X) (toUnit X ≫ y₀)).left) → Triv (M.pull (lift (toUnit Y ≫ x₀) (𝟙 Y)).left) → ∀ (X' : Scheme.{0}) (π : X' ⟶ (X ⊗ Y).left) (f' : X' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))), IsPullback π f' (X ⊗ Y).hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))) → ε ∈ IsLocalRing.maximalIdeal R → Triv (M.pull π) → Triv M := by
  intro R _ _ ε hm A B x₀ y₀ fA fB pA pB hA hB M hM ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ X' π f' P hε ⟨t, ht⟩
  have hεε : ε * ε = 0 := hm ε hε
  have sep : IsSeparated (A ⊗ B).hom := by
    change IsSeparated (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  have fl : Flat (A ⊗ B).hom := by
    change Flat (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  have : (A ⊗ B).left.IsSeparated := ⟨by
    rw [← terminal.comp_from (A ⊗ B).hom]; infer_instance⟩
  obtain ⟨I, V, j, hj, u, α, hV, haff, hu, H⟩ := exists_lift hεε P hM t ht
  by_cases h0 : ε = 0
  · exact H.gen hεε hM hV hu (fun _ => 0) fun a b x ha hb => by rw [h0, map_zero, zero_mul]
  let φ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))
  let F := Over.pullback φ
  have kA : IsProper (F.obj A).hom := by
    change IsProper (pullback.snd A.hom φ); infer_instance
  have kB : IsProper (F.obj B).hom := by
    change IsProper (pullback.snd B.hom φ); infer_instance
  let i : (F.obj A ⊗ F.obj B).left ⟶ (A ⊗ B).left :=
    (Functor.Monoidal.μIso F A B).hom.left ≫ pullback.fst (A ⊗ B).hom φ
  have Pk : IsPullback i (F.obj A ⊗ F.obj B).hom (A ⊗ B).hom φ := by
    refine IsPullback.of_iso (IsPullback.of_hasPullback (A ⊗ B).hom φ)
      ((Over.forget _).mapIso (Functor.Monoidal.μIso F A B).symm) (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · change _ ≫ 𝟙 _ = (Functor.Monoidal.μIso F A B).inv.left ≫ i
      rw [← Category.assoc, ← Over.comp_left, Iso.inv_hom_id]
      simp
    · exact (Category.comp_id _).trans (Over.w (Functor.Monoidal.μIso F A B).inv).symm
  have slice : ∀ (C : Over (Sp R)) [Flat C.hom], Function.Bijective
      (pullback.snd C.hom q).appTop.hom → ∀ (s : C ⟶ A ⊗ B) (r : A ⊗ B ⟶ C) [IsSeparated r.left],
      s ≫ r = 𝟙 C →
      ∀ (t : LB.Gen (M.pull s.left)), t.IsGen → ∀ sk : F.obj C ⟶ F.obj A ⊗ F.obj B,
      sk ≫ (Functor.Monoidal.μIso F A B).hom = F.map s → _ := fun C _ hC s r _ hs t ht sk e => by
    have h1 : s.left ≫ r.left = 𝟙 _ := congrArg (fun q => q.left) hs
    have : IsClosedImmersion (s.left ≫ r.left) := by rw [h1]; infer_instance
    have : IsClosedImmersion s.left := IsClosedImmersion.of_comp s.left r.left
    have : Flat (s.left ≫ (A ⊗ B).hom) := by rw [Over.w]; infer_instance
    exact H.slice_fibre (i := i) hεε h0 hV haff s.left (π := pullback.fst C.hom q)
      (f' := pullback.snd C.hom q) (by rw [Over.w]; exact IsPullback.of_hasPullback _ _)
      hC.2 hu t ht (iA := pullback.fst C.hom φ)
      (fk := pullback.snd C.hom φ) (by rw [Over.w]; exact pullback.condition) sk.left (by
        rw [← Category.assoc, ← Over.comp_left, e]
        exact pullback.lift_fst _ _ _)
  have one : ∀ (C D : Over (Sp R)) (z : 𝟙_ (Over (Sp R)) ⟶ D),
      toUnit (F.obj C) ≫ Functor.LaxMonoidal.ε F ≫ F.map z = F.map (toUnit C ≫ z) := fun C D z => by
    rw [F.map_comp, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Functor.OplaxMonoidal.η F)]
    exact toUnit_unique _ _
  obtain ⟨ψ, hψ⟩ := GlobalTheory.KuennethOne.kuenneth_injective (IsLocalRing.ResidueField R) (F.obj A)
    (F.obj B) (Functor.LaxMonoidal.ε F ≫ F.map x₀) (Functor.LaxMonoidal.ε F ≫ F.map y₀)
    inferInstance inferInstance inferInstance inferInstance
    (hA _ _ _ _ _ (IsPullback.of_hasPullback A.hom φ))
    (hB _ _ _ _ _ (IsPullback.of_hasPullback B.hom φ)) I
    (fun a => i ⁻¹ᵁ V a) (by rw [← Scheme.Hom.preimage_iSup, hV]; rfl)
    (fun a b => (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b))
    (fun a b d => gr_ext fun y hy => by
      rw [map_add, gr_res, gr_res, gr_res, gr_appLE, gr_appLE, gr_appLE]
      exact H.cocycle_fibre hεε h0 hM haff hu Pk.w a b d y hy.1.1 hy.1.2 hy.2)
    (@slice A _ (hA _ _ _ _ _ (IsPullback.of_hasPullback A.hom q)) _ (fst A B)
      (by change IsSeparated (pullback.fst A.hom B.hom); infer_instance)
      (by simp) t₁ ht₁ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
    (@slice B _ (hB _ _ _ _ _ (IsPullback.of_hasPullback B.hom q)) _ (snd A B)
      (by change IsSeparated (pullback.snd A.hom B.hom); infer_instance)
      (by simp) t₂ ht₂ _ (by
        rw [one, ← F.map_id]; exact Functor.Monoidal.lift_μ F _ _))
  exact H.gen_fibre hεε hm hM hV haff hu Pk ψ hψ

end GlobalTheory.SmallExtLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameEqOrthonormalMulTriangular
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.UnitFrames

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

section Mat

variable {n : ℕ}

theorem psgn_sq (p0 k : ℕ) : psgn p0 k = 1 ∨ psgn p0 k = -1 := by
  induction k with
  | zero => left; simp [psgn]
  | succ k ih =>
    rw [psgn_succ]
    rcases ih with h | h <;> rcases sgn_sq p0 k with h' | h' <;> simp [h, h']

theorem lminor_signature (p0 : ℕ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) i
      = ((psgn p0 i : ℝ) : ℂ) := by
  rw [lminor_diagonal, psgn, Complex.ofReal_prod, Finset.prod_range]
  rfl

theorem uMat_conj_eq_signature (p0 : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hs : ∀ i : Fin (n + 1), 0 < psgn p0 i * (lminor A i).re)
    (h1 : ∀ i : Fin (n + 1), ‖lminor A i‖ = 1) :
    (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ)
      = Matrix.diagonal fun a : Fin n => ((sgn p0 (a : ℕ) : ℝ) : ℂ) := by
  have hdet : ∀ c : Fin n, (blk A c).det ≠ 0 := by
    intro c h0
    have h := h1 ⟨c, Nat.lt_succ_of_lt c.isLt⟩
    have : lminor A ⟨c, Nat.lt_succ_of_lt c.isLt⟩ = 0 := h0
    rw [this] at h
    simp at h
  set B := (uMat A)ᵀ * A * (uMat A).map (starRingEnd ℂ) with hB
  have hH : B.IsHermitian := by
    have e : (uMat A).map (starRingEnd ℂ) = ((uMat A)ᵀ)ᴴ := by
      ext a c; simp [Matrix.conjTranspose_apply]
    rw [hB, e]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hA
  have hdiag : B = Matrix.diagonal fun k => B k k := by
    ext a c
    rcases lt_trichotomy a c with hac | hac | hac
    · rw [Matrix.diagonal_apply_ne _ (ne_of_lt hac), ← hH.apply a c, hB,
        uGu_lower _ hdet hac, star_zero]
    · subst hac
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ (ne_of_gt hac), hB, uGu_lower _ hdet hac]
  have hprod : ∀ i : Fin (n + 1), lminor A i
      = ∏ j : Fin i, (fun k => B k k) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
    intro i
    have e : lminor B i = lminor A i := by
      rw [hB, lminor_conj (uMat_upper _) i]
      simp only [uMat_diag, Finset.prod_const_one, one_mul, map_one, mul_one]
    rw [← e]
    exact (congrArg (fun M => lminor M i) hdiag).trans (lminor_diagonal _ i)
  have hre : ∀ k, (B k k).im = 0 := fun k => Complex.conj_eq_iff_im.1 (hH.apply k k)
  have hval : ∀ i : Fin (n + 1), lminor A i = ((psgn p0 i : ℝ) : ℂ) := by
    intro i
    have him : (lminor A i).im = 0 := by
      rw [hprod i]
      refine Complex.conj_eq_iff_im.1 ?_
      rw [map_prod]
      exact Finset.prod_congr rfl fun j _ => Complex.conj_eq_iff_im.2 (hre _)
    have hd : lminor A i = (((lminor A i).re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
    have hn := h1 i
    have hp := hs i
    rw [hd, Complex.norm_real, Real.norm_eq_abs] at hn
    rw [hd, Complex.ofReal_inj]
    rcases psgn_sq p0 i with h | h <;> rw [h] at hp ⊢
    · rw [abs_of_pos (by linarith)] at hn; exact hn
    · rw [abs_of_neg (by linarith)] at hn; linarith
  rw [hdiag]
  congr 1
  funext k
  have hsucc : lminor A k.succ = lminor A k.castSucc * B k k := by
    rw [hprod k.succ, hprod k.castSucc]
    exact prod_castLE_succ (f := fun k => B k k) k.isLt
  rw [hval, hval, Fin.val_succ, Fin.val_castSucc, psgn_succ, Complex.ofReal_mul] at hsucc
  have hne : ((psgn p0 k : ℝ) : ℂ) ≠ 0 := by
    rcases psgn_sq p0 k with h | h <;> simp [h]
  exact (mul_left_cancel₀ hne hsucc).symm

theorem det_uMat (A : Matrix (Fin n) (Fin n) ℂ) : (uMat A).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (uMat_upper _)]
  simp only [uMat_diag, Finset.prod_const_one]

theorem inv_uMat_upper (A : Matrix (Fin n) (Fin n) ℂ) : (uMat A)⁻¹.BlockTriangular id := by
  haveI := Matrix.invertibleOfIsUnitDet (uMat A) (by rw [det_uMat]; exact isUnit_one)
  exact Matrix.blockTriangular_inv_of_blockTriangular (uMat_upper A)

theorem inv_uMat_diag (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : (uMat A)⁻¹ i i = 1 := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul (uMat A)
    (by rw [det_uMat]; exact isUnit_one)) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, uMat_diag, mul_one, Matrix.one_apply_eq] at h
  · exact h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [inv_uMat_upper A h', zero_mul]
    · rw [uMat_upper A h', mul_zero]
  · simp

end Mat

theorem unit_frame_eq_orthonormal_mul_triangular :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (Gm : Matrix (Fin r) (Fin r) E), (∀ a b, cc (Gm a b) = Gm b a) → (∀ x ∈ GG Ψ Gm p0, (∀ τ i, ‖dmin Gm x τ i‖ = 1) → ∃ x₀ : Frame Ψ r, ∃ b ∈ Bor Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∀ τ i, ‖b τ i i‖ = 1) ∧ x = rmul x₀ b) ∧ (∀ x₀ : Frame Ψ r, (∀ τ : Ψ, gram τ.1 Gm (mat x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → x₀ ∈ GG Ψ Gm p0 ∧ ∀ τ i, ‖dmin Gm x₀ τ i‖ = 1) ∧ ∀ (τ : E →+* ℂ) (u x₀ : Matrix (Fin r) (Fin r) ℂ), uᵀ * Gm.map τ * u.map (starRingEnd ℂ) = Gm.map τ → gram τ Gm (u * x₀) = gram τ Gm x₀ := by
  intro E _ _ _ r p0 Ψ Gm hG
  refine ⟨fun x hx h1 => ?_, fun x₀ h => ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩,
    fun τ u x₀ hu => ?_⟩
  · refine ⟨fun τ => (mat x τ * uMat (gram τ.1 Gm (mat x τ)) : Matrix _ _ ℂ),
      fun τ => ((uMat (gram τ.1 Gm (mat x τ)))⁻¹ : Matrix _ _ ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩,
      fun τ => ?_, fun τ i => ?_, ?_⟩
    · show ((uMat (gram τ.1 Gm (mat x τ)))⁻¹).det ≠ 0
      rw [Matrix.det_nonsing_inv, det_uMat]
      simp
    · exact inv_uMat_upper _ hca
    · show gram τ.1 Gm (mat x τ * uMat (gram τ.1 Gm (mat x τ))) = _
      rw [FrameDegreeData.gram_mul]
      exact uMat_conj_eq_signature p0 _ (gram_isHermitian τ.1 hG _) (hx τ).2 (h1 τ)
    · show ‖(uMat (gram τ.1 Gm (mat x τ)))⁻¹ i i‖ = 1
      rw [inv_uMat_diag, norm_one]
    · funext τ
      show mat x τ = (mat x τ * uMat (gram τ.1 Gm (mat x τ))) * (uMat (gram τ.1 Gm (mat x τ)))⁻¹
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ (by rw [det_uMat]; exact isUnit_one)]
  · intro h0
    have h2 := congrArg Matrix.det (h τ)
    rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
      Matrix.det_diagonal] at h2
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h2.symm
    rcases sgn_sq p0 k with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature, Complex.ofReal_re]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [dmin, h τ, lminor_signature]
    rcases psgn_sq p0 i with h' | h' <;> simp [h']
  · rw [FrameDegreeData.gram_mul, FrameDegreeData.gram_eq τ Gm u, hu, FrameDegreeData.gram_eq]

end GlobalTheory.UnitFrames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UniversalFrameRingSubalgebraEqTop
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem frameRing_subalgebra_eq_top : ∀ (K : Type) [Field K] (J : Type) (m : J → ℕ) (R A : Type) [CommRing R] [Algebra K R] [CommRing A] [Algebra K A] (π : R →ₐ[K] A) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A) (s : Aˣ), FrameRing m π X s → ∀ A' : Subalgebra K A, (∀ t, π t ∈ A') → (∀ τ i j, X τ i j ∈ A') → (s : A) ∈ A' → ((s⁻¹ : Aˣ) : A) ∈ A' → (∀ τ, ∃ d ∈ A', d * (X τ).det = 1) → A' = ⊤ := by
  intro K _ J m R A _ _ _ _ π X s hF A' hπ hX hs hsi hd
  obtain ⟨hdet, huniv⟩ := hF
  let ψ : R →ₐ[K] A' := π.codRestrict A' hπ
  let g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A' := fun τ => Matrix.of fun i j => ⟨X τ i j, hX τ i j⟩
  have hg : ∀ τ, (g τ).map A'.val = X τ := fun τ => by ext i j; rfl
  let a : (A')ˣ := ⟨⟨s, hs⟩, ⟨_, hsi⟩, Subtype.ext s.mul_inv, Subtype.ext s.inv_mul⟩
  have hgu : ∀ τ, IsUnit (g τ).det := by
    intro τ
    obtain ⟨d, hdA, hd1⟩ := hd τ
    refine IsUnit.of_mul_eq_one_right (⟨d, hdA⟩ : A') ?_
    apply Subtype.ext
    have h1 : A'.val (g τ).det = (X τ).det := by
      rw [← hg τ]
      exact AlgHom.map_det A'.val (g τ)
    change d * A'.val (g τ).det = 1
    rw [h1, hd1]
  obtain ⟨k, ⟨hk1, hk2, hk3⟩, -⟩ := huniv A' ψ g a hgu
  obtain ⟨k₀, -, huq⟩ := huniv A π X s hdet
  have e1 : A'.val.comp k = k₀ := by
    apply huq
    refine ⟨?_, fun τ => ?_, ?_⟩
    · rw [AlgHom.comp_assoc, hk1]; ext t; rfl
    · rw [← hg τ, ← hk2 τ]
      conv_lhs => rw [hk2 τ, hg τ]
      ext i j; rfl
    · change A'.val (k s) = s
      rw [hk3]; rfl
  have e2 : AlgHom.id K A = k₀ := by
    apply huq
    refine ⟨by ext t; rfl, fun τ => by ext i j; rfl, rfl⟩
  rw [eq_top_iff]
  intro x _
  have : A'.val (k x) = x := by
    have := DFunLike.congr_fun (e1.trans e2.symm) x
    simpa using this
  rw [← this]
  exact (k x).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZMatEInjective
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem cc_add' (x y : E) : cc (x + y) = cc x + cc y := by simp [cc]
theorem cc_mul' (x y : E) : cc (x * y) = cc x * cc y := by simp [cc]
theorem cc_neg' (x : E) : cc (-x) = -cc x := by simp [cc]
theorem cc_zero' : cc (0 : E) = 0 := by simp [cc]
theorem cc_cc' (x : E) : cc (cc x) = x := by simp [cc]
theorem cc_sum' {ι : Type} (s : Finset ι) (f : ι → E) : cc (∑ i ∈ s, f i) = ∑ i ∈ s, cc (f i) := by
  simp [cc]

theorem herm_add_l (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

theorem herm_add_r (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by
  simp [herm, cc_add', mul_add, Finset.sum_add_distrib]

theorem herm_comb_l (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (y : Fin r → E) : herm G (∑ a, c a • e a) y = ∑ a, c a * herm G (e a) y := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem herm_comb_r (G : Matrix (Fin r) (Fin r) E) (c : Fin ρ → E) (e : Fin ρ → Fin r → E)
    (x : Fin r → E) : herm G x (∑ a, c a • e a) = ∑ a, cc (c a) * herm G x (e a) := by
  simp only [herm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cc_sum', cc_mul', Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm (γ := Fin ρ)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem herm_swap (X : Data E r) (x y : Fin r → E) : herm X.Gm x y = cc (herm X.Gm y x) := by
  simp only [herm, cc_sum', cc_mul', cc_cc', X.Gm_herm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem herm_nondeg (X : Data E r) (w : Fin r → E) (h : ∀ v, herm X.Gm v w = 0) : w = 0 := by
  have h1 : X.Gm *ᵥ (fun b => cc (w b)) = 0 := by
    funext k
    have := h (Pi.single k 1)
    simpa [herm, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have h2 := Matrix.eq_zero_of_mulVec_eq_zero X.Gm_det h1
  funext b
  have h3 : cc (w b) = 0 := congrFun h2 b
  rw [← cc_cc' (w b), h3, cc_zero']
  rfl

theorem zMatE_mulVec (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E)
    (v : Fin r → E) :
    FJ.zMatE X e β *ᵥ v = v + ∑ a, (∑ b, β a b * herm X.Gm v (e b)) • e a := by
  funext k
  simp only [FJ.zMatE, Matrix.mulVec, dotProduct, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, herm, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun l _ =>
    Finset.sum_congr rfl fun m _ => ?_
  ring

theorem zMatE_zero (X : Data E r) (e : Fin ρ → Fin r → E) : FJ.zMatE X e 0 = 1 := by
  ext k l
  simp [FJ.zMatE, Matrix.one_apply]

theorem zMatE_add (X : Data E r) (cu : FJ.CuspFD X ρ) (β β' : Matrix (Fin ρ) (Fin ρ) E) :
    FJ.zMatE X cu.e (β + β') = FJ.zMatE X cu.e β * FJ.zMatE X cu.e β' := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec]
  simp only [zMatE_mulVec, herm_add_l, herm_comb_l, cu.iso, mul_zero, Finset.sum_const_zero,
    add_zero, Matrix.add_apply, add_mul, Finset.sum_add_distrib, add_smul]
  abel

theorem zMatE_unitary (X : Data E r) (cu : FJ.CuspFD X ρ) (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : FJ.IsSkew β) (u v : Fin r → E) :
    herm X.Gm (FJ.zMatE X cu.e β *ᵥ u) (FJ.zMatE X cu.e β *ᵥ v) = herm X.Gm u v := by
  simp only [zMatE_mulVec, herm_add_l, herm_add_r, herm_comb_l, herm_comb_r, cu.iso, mul_zero,
    Finset.sum_const_zero, add_zero, cc_sum', cc_mul', hβ _ _, ← herm_swap, Finset.sum_mul]
  rw [add_assoc, add_eq_left, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  ring

theorem zMatE_injective (X : Data E r) (cu : FJ.CuspFD X ρ) :
    Function.Injective (FJ.zMatE X cu.e) := by
  intro β β' h
  have h1 : ∀ v a, ∑ b, β a b * herm X.Gm v (cu.e b) = ∑ b, β' a b * herm X.Gm v (cu.e b) := by
    intro v a
    have h2 := congrArg (· *ᵥ v) h
    simp only [zMatE_mulVec, add_right_inj] at h2
    exact Fintype.linearIndependent_iffₛ.1 cu.ind _ _ h2 a
  ext a b
  have h3 : ∑ b, cc (β a b - β' a b) • cu.e b = 0 := by
    refine herm_nondeg X _ fun v => ?_
    simp only [herm_comb_r, cc_cc', sub_mul, Finset.sum_sub_distrib, h1 v a, sub_self]
  have h4 : cc (β a b - β' a b) = 0 := Fintype.linearIndependent_iff.1 cu.ind _ h3 b
  rw [← sub_eq_zero, ← cc_cc' (β a b - β' a b), h4, cc_zero']

def zGamSub (X : Data E r) (cu : FJ.CuspFD X ρ) : AddSubgroup (Matrix (Fin ρ) (Fin ρ) E) where
  carrier := FJ.zGam X cu
  zero_mem' := ⟨fun a b => by simp [cc_zero'], 1, X.Γ.one_mem, by simp [zMatE_zero]⟩
  add_mem' := by
    rintro β β' ⟨h, γ, hγ, e⟩ ⟨h', γ', hγ', e'⟩
    refine ⟨fun a b => ?_, γ * γ', X.Γ.mul_mem hγ hγ', ?_⟩
    · rw [Matrix.add_apply, Matrix.add_apply, cc_add', h, h']; ring
    · rw [zMatE_add, ← e, ← e', Units.val_mul]
  neg_mem' := by
    rintro β ⟨h, γ, hγ, e⟩
    refine ⟨fun a b => ?_, γ⁻¹, X.Γ.inv_mem hγ, ?_⟩
    · rw [Matrix.neg_apply, Matrix.neg_apply, cc_neg', h]
    · refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [e, ← zMatE_add, add_neg_cancel, zMatE_zero]

end GlobalTheory.CuspCentre
end

