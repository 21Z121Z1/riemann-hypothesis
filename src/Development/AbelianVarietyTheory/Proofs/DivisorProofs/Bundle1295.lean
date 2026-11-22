import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalArchRestrictionSpaceOfWei
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockUpperParabolicLeviProjectionUnipotent
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.LeviHoms

variable {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)

def ix : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

theorem ix_inl_val (x : Fin a) : ((ix h (Sum.inl x) : Fin n) : ℕ) = x := by simp [ix]

theorem ix_inr_val (x : Fin b) : ((ix h (Sum.inr x) : Fin n) : ℕ) = a + x := by simp [ix]

theorem ext_ix {R : Type} {M N : Matrix (Fin n) (Fin n) R}
    (H : ∀ P Q, M (ix h P) (ix h Q) = N (ix h P) (ix h Q)) : M = N := by
  ext i j
  obtain ⟨P, rfl⟩ := (ix h).surjective i
  obtain ⟨Q, rfl⟩ := (ix h).surjective j
  exact H P Q

theorem mem_parabolic_iff (g : GLw n w) :
    g ∈ parP a n w ↔ ∀ i j, g.val (ix h (Sum.inr i)) (ix h (Sum.inl j)) = 0 := by
  constructor
  · intro hg i j
    apply hg
    have h1 : ¬ a ≤ (j : ℕ) := Nat.not_le.2 j.isLt
    simp only [ix_inl_val, ix_inr_val]
    simp [h1]
  · intro H i j hij
    obtain ⟨P, rfl⟩ := (ix h).surjective i
    obtain ⟨Q, rfl⟩ := (ix h).surjective j
    rcases P with x | x <;> rcases Q with y | y
    · have h1 : ¬ a ≤ (x : ℕ) := Nat.not_le.2 x.isLt
      simp only [ix_inl_val] at hij
      simp [h1] at hij
      exact absurd hij (by cases decide (a ≤ (y : ℕ)) <;> decide)
    · simp only [ix_inl_val, ix_inr_val] at hij
      simp at hij
      exact absurd hij (by cases decide (a ≤ (x : ℕ)) <;> decide)
    · exact H x y
    · simp only [ix_inr_val] at hij
      simp at hij

theorem blk_apply (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) (P Q : Fin a ⊕ Fin b) :
    (blk h w m X).val (ix h P) (ix h Q) = Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val P Q := by
  rw [UnipMean.blk_val]
  simp [ix]

theorem toBlocks₁₁_mul {R α β : Type} [CommRing R] [Fintype α] [Fintype β] (M N : Matrix (α ⊕ β) (α ⊕ β) R)
    (hN : N.toBlocks₂₁ = 0) : (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ := by
  ext i j
  have := fun y => congrFun (congrFun hN y) j
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, this]

theorem toBlocks₂₂_mul {R α β : Type} [CommRing R] [Fintype α] [Fintype β] (M N : Matrix (α ⊕ β) (α ⊕ β) R)
    (hM : M.toBlocks₂₁ = 0) : (M * N).toBlocks₂₂ = M.toBlocks₂₂ * N.toBlocks₂₂ := by
  ext i j
  have := fun y => congrFun (congrFun hM i) y
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type, this]

theorem toBlocks₂₁_of_mem (p : parP a n w) :
    ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₁ = 0 := by
  exact Matrix.ext fun i j => (mem_parabolic_iff h w _).1 p.2 i j

def dgH : parP a n w →* Matrix (Fin a) (Fin a) (w.adicCompletion E) × Matrix (Fin b) (Fin b) (w.adicCompletion E) where
  toFun p := (((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₁, ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₂)
  map_one' := by
    refine Prod.ext (Matrix.ext fun i j => ?_) (Matrix.ext fun i j => ?_) <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.one_apply]
  map_mul' p q := by
    have e : ((p * q : parP a n w) : GLw n w).val.submatrix (ix h) (ix h) =
        (p : GLw n w).val.submatrix (ix h) (ix h) * (q : GLw n w).val.submatrix (ix h) (ix h) := by
      rw [Matrix.submatrix_mul_equiv]; rfl
    simp only [e, Prod.mk_mul_mk]
    rw [toBlocks₁₁_mul _ _ (toBlocks₂₁_of_mem h w q), toBlocks₂₂_mul _ _ (toBlocks₂₁_of_mem h w p)]

def sH : GLw a w × GLw b w →* parP a n w where
  toFun m := ⟨blk h w m 0, (mem_parabolic_iff h w _).2 fun i j => by rw [blk_apply]; rfl⟩
  map_one' := Subtype.ext (UnipMean.blk_one_zero h w)
  map_mul' m m' := by
    apply Subtype.ext
    ext1
    simp only [Subgroup.coe_mul, Units.val_mul, UnipMean.blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add]

def piH : parP a n w →* GLw a w × GLw b w :=
  MulEquiv.prodUnits.toMonoidHom.comp ((Units.map (dgH h w)).comp (toUnits : parP a n w ≃* (parP a n w)ˣ).toMonoidHom)

theorem piH_fst_val (p : parP a n w) :
    ((piH h w p).1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) =
      ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₁ := rfl

theorem piH_snd_val (p : parP a n w) :
    ((piH h w p).2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) =
      ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₂₂ := rfl

def uH : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* parP a n w where
  toFun X := ⟨blk h w 1 (Multiplicative.toAdd X), (mem_parabolic_iff h w _).2 fun i j => by rw [blk_apply]; rfl⟩
  map_one' := Subtype.ext (UnipMean.blk_one_zero h w)
  map_mul' X Y := Subtype.ext (by simp only [toAdd_mul, Subgroup.coe_mul]; exact UnipMean.blk_add h w 1 _ _)

theorem piH_sH (m : GLw a w × GLw b w) : piH h w (sH h w m) = m := by
  refine Prod.ext (Units.ext ?_) (Units.ext ?_)
  · rw [piH_fst_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₁₁, sH, blk_apply]
  · rw [piH_snd_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₂₂, sH, blk_apply]

theorem uH_injective : Function.Injective (uH h w) := by
  intro X Y hXY
  have := congrArg (fun p : parP a n w => UnipMean.corner h w 1 (p : GLw n w)) hXY
  simpa [uH, UnipMean.corner_blk] using this

theorem piH_eq_one_iff (p : parP a n w) : piH h w p = 1 ↔ ∃ X, uH h w X = p := by
  constructor
  · intro hp
    have h1 := congrArg (fun q : GLw a w × GLw b w => (q.1 : Matrix (Fin a) (Fin a) (w.adicCompletion E))) hp
    have h2 := congrArg (fun q : GLw a w × GLw b w => (q.2 : Matrix (Fin b) (Fin b) (w.adicCompletion E))) hp
    simp only [piH_fst_val, piH_snd_val, Prod.fst_one, Prod.snd_one, Units.val_one] at h1 h2
    refine ⟨Multiplicative.ofAdd ((p : GLw n w).val.submatrix (ix h) (ix h)).toBlocks₁₂, ?_⟩
    apply Subtype.ext; ext1
    refine ext_ix h fun P Q => ?_
    simp only [uH, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [blk_apply]
    rcases P with x | x <;> rcases Q with y | y
    · have := congrFun (congrFun h1 x) y
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply] at this
      simp [this]
    · simp [Matrix.toBlocks₁₂]
    · simp [(mem_parabolic_iff h w _).1 p.2 x y]
    · have := congrFun (congrFun h2 x) y
      simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply] at this
      simp [this]
  · rintro ⟨X, rfl⟩
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · rw [piH_fst_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₁₁, uH, blk_apply]
    · rw [piH_snd_val]; exact Matrix.ext fun i j => by simp [Matrix.toBlocks₂₂, uH, blk_apply]

theorem mem_intMat_iff (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    X ∈ intMat a b w ↔ ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1 := by
  let T : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
    { carrier := {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}
      one_mem' := fun i j => by simp
      mul_mem' := fun {x y} hx hy i j => by
        simp only [Set.mem_setOf_eq, toAdd_mul, Matrix.add_apply] at *
        exact Valuation.map_add_le _ (hx i j) (hy i j)
      inv_mem' := fun {x} hx i j => by
        simp only [Set.mem_setOf_eq, toAdd_inv, Matrix.neg_apply, Valuation.map_neg] at *
        exact hx i j }
  have e : intMat a b w = T :=
    le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx) fun x hx => Subgroup.subset_closure hx
  rw [e]
  rfl

theorem ent_iff {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)} :
    (∀ i j, Valued.v (M i j) ≤ 1) ↔ ∀ P Q, Valued.v (M (ix h P) (ix h Q)) ≤ 1 := by
  constructor
  · intro H P Q; exact H _ _
  · intro H i j
    obtain ⟨P, rfl⟩ := (ix h).surjective i
    obtain ⟨Q, rfl⟩ := (ix h).surjective j
    exact H P Q

theorem one_ent {k : Type} [Fintype k] [DecidableEq k] (i j : k) :
    Valued.v ((1 : Matrix k k (w.adicCompletion E)) i j) ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem blk_ent (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (H1 : ∀ i j, Valued.v (m.1.val i j) ≤ 1) (H2 : ∀ i j, Valued.v (m.2.val i j) ≤ 1)
    (HX : ∀ i j, Valued.v ((m.1.val * X) i j) ≤ 1) : ∀ i j, Valued.v ((blk h w m X).val i j) ≤ 1 := by
  rw [ent_iff h w]
  intro P Q
  rw [blk_apply]
  rcases P with x | x <;> rcases Q with y | y
  · simpa using H1 x y
  · simpa using HX x y
  · simp
  · simpa using H2 x y

theorem sH_mem (k : GLw a w × GLw b w) (hk : k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) :
    sH h w k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (parP a n w) := by
  rw [Subgroup.mem_subgroupOf, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  rw [Subgroup.mem_prod, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val] at hk
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hk
  refine ⟨blk_ent h w k 0 a1 b1 (by simp), ?_⟩
  have e : ((sH h w k : GLw n w))⁻¹ = (sH h w k⁻¹ : GLw n w) := by rw [map_inv]; rfl
  rw [e]
  exact blk_ent h w k⁻¹ 0 a2 b2 (by simp)

theorem piH_mem (k : parP a n w) (hk : k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (parP a n w)) :
    piH h w k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
  rw [Subgroup.mem_subgroupOf, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val] at hk
  obtain ⟨k1, k2⟩ := hk
  have e : (piH h w k)⁻¹ = piH h w k⁻¹ := (map_inv _ _).symm
  rw [Subgroup.mem_prod, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_, fun i j => ?_⟩
  · rw [piH_fst_val]; exact k1 (ix h (Sum.inl i)) (ix h (Sum.inl j))
  · rw [← Prod.fst_inv, e, piH_fst_val]; exact k2 (ix h (Sum.inl i)) (ix h (Sum.inl j))
  · rw [piH_snd_val]; exact k1 (ix h (Sum.inr i)) (ix h (Sum.inr j))
  · rw [← Prod.snd_inv, e, piH_snd_val]; exact k2 (ix h (Sum.inr i)) (ix h (Sum.inr j))

theorem uH_mem_iff (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    uH h w X ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (parP a n w) ↔ X ∈ intMat a b w := by
  rw [mem_intMat_iff, Subgroup.mem_subgroupOf, GlobalTheory.BCT.GlobLev.mem_KGL_iff_val]
  constructor
  · rintro ⟨H, -⟩ i j
    have := H (ix h (Sum.inl i)) (ix h (Sum.inr j))
    simpa [uH, blk_apply] using this
  · intro H
    have e : ((uH h w X : GLw n w))⁻¹ = (uH h w X⁻¹ : GLw n w) := by rw [map_inv]; rfl
    rw [e]
    refine ⟨blk_ent h w 1 _ (fun i j => by simpa using one_ent w i j) (fun i j => by simpa using one_ent w i j)
      (by simpa using H), blk_ent h w 1 _ (fun i j => by simpa using one_ent w i j)
      (fun i j => by simpa using one_ent w i j) (by simpa using H)⟩

end GlobalTheory.LeviDesc.LeviHoms

namespace GlobalTheory.LeviDesc.LeviHoms

theorem levi_homs : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E), ∃ (s : GLw a w × GLw b w →* GlobalTheory.LeviDesc.parP a n w) (π : GlobalTheory.LeviDesc.parP a n w →* GLw a w × GLw b w) (u : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* GlobalTheory.LeviDesc.parP a n w), (∀ m, (s m : GLw n w) = blk h w m 0) ∧ (∀ X, (u X : GLw n w) = blk h w 1 (Multiplicative.toAdd X)) ∧ (∀ m, π (s m) = m) ∧ Function.Injective u ∧ (∀ p, π p = 1 ↔ ∃ X, u X = p) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b), s k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w)) ∧ (∀ k ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w), π k ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ∧ (∀ X, u X ∈ (GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w) ↔ X ∈ intMat a b w) := by
  intro E _ _ n a b h w
  exact ⟨sH h w, piH h w, uH h w, fun m => rfl, fun X => rfl, piH_sH h w, uH_injective h w, piH_eq_one_iff h w,
    fun k hk => sH_mem h w k hk, fun k hk => piH_mem h w k hk, uH_mem_iff h w⟩

end GlobalTheory.LeviDesc.LeviHoms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoeffBoundOfLinearIndependentSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem exists_coeff_le_of_linearIndependent : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ j, f j ∈ P.H a b) → LinearIndependent ℤ f → ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Fin r → ℤ) (R : ℝ), (∑ j, c j • f j) ∈ P.Bl a b R → ∀ j, |(c j : ℝ)| ≤ C * R := by
  intro k _ X _ p D hX P a b r f hf hli
  classical
  have h1 : genericPoint X ∈ ⨆ i, P.L.B.U i := by rw [P.L.isLB.cover]; trivial
  have h2 : genericPoint X ∈ ⨆ j, P.A.B.U j := by rw [P.A.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h1
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
  obtain ⟨U, hU, hgU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩
  have hl : U ≤ P.L.B.U i := fun x hx => (hle hx).1
  have hr : U ≤ P.A.B.U j := fun x hx => (hle hx).2
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have : CharZero Γ(X, U) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
  have := finiteType_int_of_isAffineOpen hX hU
  have hg : ∀ l, ∃ g, fnOf U hgU g = P.loc a b (f l) i j := fun l =>
    exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)
  choose g hg using hg
  set c0 : X.functionField := (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b with hc0def
  have hloc : ∀ h, P.loc a b h i j = h * c0 := fun h => by simp only [Pair.loc, c0, mul_assoc]
  have hc0 : c0 ≠ 0 := mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hlig : LinearIndependent ℤ g := by
    have h3 : LinearIndependent ℤ ((LinearMap.mulRight ℤ c0) ∘ f) :=
      hli.map' _ (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hc0))
    refine LinearIndependent.of_comp (fnOf U hgU).toAddMonoidHom.toIntLinearMap ?_
    have e : (⇑(fnOf U hgU).toAddMonoidHom.toIntLinearMap ∘ g) = ⇑(LinearMap.mulRight ℤ c0) ∘ f := by
      funext l
      simp [hg, hloc]
    rw [e]
    exact h3
  obtain ⟨x, hx⟩ := GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) r g hlig
  obtain ⟨-, -, -, hsurj, -⟩ := GlobalTheory.ContRead.exists_continuous_read k X p D hX U hU (fun _ _ => 0)
    fun _ => continuousOn_const
  choose σ y hy hyx using hsurj
  let M : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun s l => x s (g l)
  let w : Fin r → ℝ := fun s => Real.exp ((a * (P.L.φ (σ (x s))).φ i (y (x s)) +
    b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2)
  let E : ℝ := ∑ s, w s
  let K : ℝ := ∑ l, ∑ s, ‖M⁻¹ l s‖
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ => (Real.exp_pos _).le
  have hK : 0 ≤ K := Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun s _ => norm_nonneg _
  refine ⟨K * E, mul_nonneg hK hE, fun cc R hR l => ?_⟩
  set v : Fin r → ℂ := Matrix.mulVec M fun l => (cc l : ℂ) with hvdef
  have hsum : P.loc a b (∑ l, cc l • f l) i j = fnOf U hgU (∑ l, cc l • g l) := by
    rw [hloc, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, hg, hloc, smul_mul_assoc]
  have key : ∀ s, ‖v s‖ ≤ R * w s := by
    intro s
    have e := GlobalTheory.VolBr.nu_eq k X p P a b _ hR.1 (σ (x s)) (y (x s)) i j
      (ptsIn_mono hl (hy (x s))) (ptsIn_mono hr (hy (x s)))
    rw [hsum, ratVal_fnOf (hy (x s)), ev_eq (hy (x s)), hyx] at e
    have hv : v s = x s (∑ l, cc l • g l) := by
      simp [v, M, Matrix.mulVec, dotProduct, map_sum, map_zsmul, mul_comm]
    have hb := hR.2 (σ (x s)) (y (x s))
    rw [e] at hb
    rw [hv]
    have hw : ‖x s (∑ l, cc l • g l)‖ = ‖x s (∑ l, cc l • g l)‖ *
        Real.exp (-(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2) * w s := by
      rw [mul_assoc, ← Real.exp_add]
      have : -(a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 +
          (a * (P.L.φ (σ (x s))).φ i (y (x s)) + b * (P.A.φ (σ (x s))).φ j (y (x s))) / 2 = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    rw [hw]
    exact mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
  have hR0 : 0 ≤ R := by
    by_contra h
    push_neg at h
    have := mul_neg_of_neg_of_pos h (Real.exp_pos _ : (0 : ℝ) < w l)
    linarith [key l, norm_nonneg (v l)]
  have hinv : (fun l => (cc l : ℂ)) = Matrix.mulVec M⁻¹ v := by
    rw [hvdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hx), Matrix.one_mulVec]
  have habs : |(cc l : ℝ)| = ‖(cc l : ℂ)‖ := by simp
  rw [habs, congrFun hinv l]
  calc ‖Matrix.mulVec M⁻¹ v l‖ = ‖∑ s, M⁻¹ l s * v s‖ := rfl
    _ ≤ ∑ s, ‖M⁻¹ l s‖ * ‖v s‖ := (norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))
    _ ≤ ∑ s, ‖M⁻¹ l s‖ * (R * E) := Finset.sum_le_sum fun s _ =>
        mul_le_mul_of_nonneg_left ((key s).trans (mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := w) (fun t _ => (Real.exp_pos _).le) (Finset.mem_univ s)) hR0)) (norm_nonneg _)
    _ = (∑ s, ‖M⁻¹ l s‖) * E * R := by rw [← Finset.sum_mul]; ring
    _ ≤ K * E * R := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hE) hR0
        exact Finset.single_le_sum (f := fun l => ∑ s, ‖M⁻¹ l s‖)
          (fun t _ => Finset.sum_nonneg fun s _ => norm_nonneg _) (Finset.mem_univ l)

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorBoundMatrixMul
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem denom_bound_mul : ∀ (E κ ι : Type) [Field E] [NumberField E] [Fintype κ] [Fintype ι] (T : Matrix κ ι E), ∃ M : ℕ, 0 < M ∧ ∀ (L : ℕ) (x : ι → E), (∀ i, IsIntegral ℤ ((L : E) * x i)) → ∀ k, IsIntegral ℤ (((M * L : ℕ) : E) * ∑ i, T k i * x i) := by
  intro E κ ι _ _ _ _ T
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (Finset.univ.image (fun p : κ × ι => T p.1 p.2))
  refine ⟨y.natAbs ^ 2, by positivity, ?_⟩
  intro L x hx k
  have hT : ∀ i, IsIntegral ℤ (((y.natAbs ^ 2 : ℕ) : E) * T k i) := by
    intro i
    have h1 := hint (T k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
    have hy' : IsIntegral ℤ ((y : E)) := by
      have := (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ E y)); simpa using this
    have : ((y.natAbs ^ 2 : ℕ) : E) * T k i = (y : E) * (y • T k i) := by
      rw [zsmul_eq_mul]
      have : ((y.natAbs ^ 2 : ℕ) : E) = ((y ^ 2 : ℤ) : E) := by
        have hz : ((y.natAbs ^ 2 : ℕ) : ℤ) = y ^ 2 := by push_cast; exact sq_abs y
        rw [← hz, Int.cast_natCast]
      rw [this]; push_cast; ring
    rw [this]
    exact hy'.mul h1
  have heq : (((y.natAbs ^ 2 * L : ℕ) : E) * ∑ i, T k i * x i)
      = ∑ i, (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring
  rw [heq]
  have := Subalgebra.sum_mem (integralClosure ℤ E) (t := Finset.univ)
    (f := fun i => (((y.natAbs ^ 2 : ℕ) : E) * T k i) * ((L : E) * x i))
    (fun i _ => Subalgebra.mul_mem _ (hT i) (hx i))
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteControllingPointsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_set_controlling_regularity_of_quotient : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∃ S : Set X, S.Finite ∧ ∀ (x : X) i j, x ∈ P.L.B.U i → x ∈ P.A.B.U j → ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ S, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / P.loc 0 1 s i j) → RegAt x (g / P.loc 0 1 s i j) := by
  first | exact @GlobalTheory.VolBr.exists_finite_controlling_points | exact GlobalTheory.VolBr.exists_finite_controlling_points | (intros; apply GlobalTheory.VolBr.exists_finite_controlling_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalArchRestrictionSpaceOfWeiStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_archRestriction_space_of_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n), ∃ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C ∧ ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ v, HasWeightAt π v.embedding (lam v)) → ∀ φ ∈ π, ∀ g : UA E n, (fun x : infU E n => φ (g * (x : UA E n))) ∈ C := by
  first | exact @GlobalTheory.DefU.CoefSp.coef_space | exact GlobalTheory.DefU.CoefSp.coef_space | (intros; apply GlobalTheory.DefU.CoefSp.coef_space <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexLeviSubgroupUnipotentConjIntegr
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc.ConjStab

variable {E : Type} [Field E] [NumberField E]

def dgHom {n a b : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* GLw n w where
  toFun k := blk h w k 0
  map_one' := by
    ext : 1
    rw [LeviBlockConjugation.blk_val]
    simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.mul_zero, Matrix.fromBlocks_one, Matrix.reindex_apply]
    exact Matrix.submatrix_one_equiv _
  map_mul' k k' := by
    ext : 1
    simp only [Units.val_mul, LeviBlockConjugation.blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
      Matrix.fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp

theorem continuous_dgHom {n a b : ℕ} (h : a + b = n) (w : Pl E) : Continuous (dgHom (E := E) h w) := by
  rw [Units.continuous_iff]
  constructor
  · have e : (fun k : GLw a w × GLw b w => (dgHom h w k).val) = fun k =>
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks k.1.val (k.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 k.2.val) := by
      funext k; exact LeviBlockConjugation.blk_val h w k 0
    change Continuous fun k : GLw a w × GLw b w => (dgHom h w k).val
    rw [e]
    exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst)
      ((Units.continuous_val.comp continuous_fst).matrix_mul continuous_const) continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · have e : (fun k : GLw a w × GLw b w => ((dgHom h w k)⁻¹).val) = fun k =>
        Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
          (Matrix.fromBlocks (k.1⁻¹).val ((k.1⁻¹).val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 (k.2⁻¹).val) := by
      funext k; rw [← map_inv]; exact LeviBlockConjugation.blk_val h w k⁻¹ 0
    change Continuous fun k : GLw a w × GLw b w => ((dgHom h w k)⁻¹).val
    rw [e]
    exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst)
      ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_const) continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

def conjLevi {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw a w × GLw b w →* GLw n w :=
  (MulAut.conj (blk h w 1 X)⁻¹).toMonoidHom.comp (dgHom h w)

theorem conjLevi_apply {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (k : GLw a w × GLw b w) : conjLevi h w X k = (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X := by
  simp [conjLevi, dgHom, MulAut.conj_apply]

theorem continuous_conjLevi {n a b : ℕ} (h : a + b = n) (w : Pl E) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    Continuous (conjLevi h w X) := by
  have e : (conjLevi h w X : GLw a w × GLw b w → GLw n w) = fun k => (blk h w 1 X)⁻¹ * dgHom h w k * blk h w 1 X := by
    funext k; rw [conjLevi_apply]; rfl
  rw [e]
  exact (continuous_const.mul (continuous_dgHom h w)).mul continuous_const

end GlobalTheory.LeviDesc.ConjStab

open GlobalTheory.LeviDesc.ConjStab in

theorem GlobalTheory.LeviDesc.ConjStab.exists_stab : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), ∃ U : Subgroup (GLw a w × GLw b w),
    U ≤ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) ∧ U.relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) ≠ 0 ∧
    ∀ k ∈ U, (blk h w 1 X)⁻¹ * blk h w k 0 * blk h w 1 X ∈ GlobalTheory.LFun.KGL w n := by
  intro E _ _ n a b h w X
  set P : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)
  set C : Subgroup (GLw a w × GLw b w) := (GlobalTheory.LFun.KGL w n).comap (conjLevi h w X)
  refine ⟨P ⊓ C, inf_le_left, ?_, fun k hk => ?_⟩
  · rw [Subgroup.inf_relIndex_left]
    have hP : IsCompact (P : Set (GLw a w × GLw b w)) := by
      simp only [P, Subgroup.coe_prod]
      exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.prod (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2
    have hC : IsOpen (C : Set (GLw a w × GLw b w)) :=
      (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1.preimage (continuous_conjLevi h w X)
    haveI : CompactSpace P := isCompact_iff_compactSpace.mp hP
    haveI : Finite (P ⧸ C.subgroupOf P) :=
      Subgroup.quotient_finite_of_isOpen _ (hC.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  · have := (Subgroup.mem_inf.1 hk).2
    rw [Subgroup.mem_comap, conjLevi_apply] at this
    exact this
end
end

