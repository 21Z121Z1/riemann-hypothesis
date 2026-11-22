import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianTripleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0085
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2236
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulEqSumVecMulVecSpanningFamily
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open Matrix

noncomputable section

namespace GlobalTheory.Poinc.SumSq

theorem exists_nat_smul_sub_posDef {ι : Type*} [Fintype ι] {G B : Matrix ι ι ℝ} (hG : G.PosDef)
    (hB : B.IsHermitian) : ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • G - B).PosDef := by
  have hp : ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ G *ᵥ x := fun x hx => by
    simpa using hG.dotProduct_mulVec_pos hx
  have hne : ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  have hc : ContinuousOn (fun x : ι → ℝ => (x ⬝ᵥ B *ᵥ x) / (x ⬝ᵥ G *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div (Continuous.continuousOn ?_) (Continuous.continuousOn ?_)
      fun x hx => (hp x (hne x hx)).ne'
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    · exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_sphere (0 : ι → ℝ) 1).image_of_continuousOn hc).bddAbove
  obtain ⟨κ₀, hκ₀⟩ := exists_nat_gt C
  refine ⟨κ₀, fun κ hκ => ?_⟩
  have hκ' : C < κ := hκ₀.trans_le (by exact_mod_cast hκ)
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine IsHermitian.sub ?_ hB
    rw [IsHermitian, conjTranspose_smul, hG.isHermitian.eq, star_trivial]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
      simp [norm_smul, hn.ne']
    have h1 := hC ⟨_, hs, rfl⟩
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1
    rw [mul_div_mul_left _ _ (inv_pos.2 hn).ne', mul_div_mul_left _ _ (inv_pos.2 hn).ne',
      div_le_iff₀ (hp x hx)] at h1
    have h2 := mul_lt_mul_of_pos_right hκ' (hp x hx)
    rw [star_trivial, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    linarith

theorem posDef_symm {n : Type*} {M : Matrix n n ℝ} (hM : M.PosDef) (i j : n) : M j i = M i j := by
  have := congrFun₂ hM.isHermitian.eq i j
  simpa using this

theorem schur_posDef {n : ℕ} {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hM : M.PosDef) :
    (Matrix.of fun i j : Fin n => M 0 0 * M i.succ j.succ - M i.succ 0 * M 0 j.succ).PosDef := by
  have hs := posDef_symm hM
  have ha : 0 < M 0 0 := hM.diag_pos
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun y hy => ?_
  · ext i j
    simp [hs]
    ring
  · set B := ∑ j, M 0 j.succ * y j with hB
    set x : Fin (n + 1) → ℝ := Fin.cons (-B / M 0 0) y with hx
    have hx0 : x ≠ 0 := by
      intro h
      apply hy
      funext j
      have := congrFun h j.succ
      simpa [hx] using this
    have h1 := hM.dotProduct_mulVec_pos hx0
    rw [star_trivial] at h1 ⊢
    have e1 : x ⬝ᵥ M *ᵥ x = M 0 0 * (-B / M 0 0) ^ 2 + 2 * (-B / M 0 0) * B +
        ∑ i, y i * ∑ j, M i.succ j.succ * y j := by
      have hc : ∀ i : Fin n, M i.succ 0 = M 0 i.succ := fun i => hs 0 i.succ
      have h3 : ∑ i, y i * (M 0 i.succ * (-B / M 0 0)) = (-B / M 0 0) * B := by
        rw [hB, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [dotProduct, mulVec, Fin.sum_univ_succ, hx, Fin.cons_zero, Fin.cons_succ, hc,
        mul_add, Finset.sum_add_distrib, h3]
      rw [← hB]
      ring
    have e2 : y ⬝ᵥ (Matrix.of fun i j : Fin n => M 0 0 * M i.succ j.succ - M i.succ 0 * M 0 j.succ) *ᵥ y =
        M 0 0 * ∑ i, y i * ∑ j, M i.succ j.succ * y j - B ^ 2 := by
      have hc : ∀ i : Fin n, M i.succ 0 = M 0 i.succ := fun i => hs 0 i.succ
      simp only [dotProduct, mulVec, of_apply, hc, sub_mul, Finset.sum_sub_distrib, mul_sub]
      rw [hB, sq, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    rw [e2]
    rw [e1] at h1
    field_simp at h1
    nlinarith

theorem exists_smul_eq_sum_vecMulVec : ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ),
    (L.map (Int.cast : ℤ → ℝ)).PosDef → ∃ (ι : Type) (_ : Fintype ι) (D : ℕ) (a : ι → Fin r → ℤ),
      1 ≤ D ∧ (D : ℤ) • L = ∑ i, vecMulVec (a i) (a i) := by
  intro r
  induction r with
  | zero =>
    intro L _
    refine ⟨Empty, inferInstance, 1, Empty.elim, le_rfl, ?_⟩
    ext i
    exact i.elim0
  | succ n ih =>
    intro L hL
    have hs := posDef_symm hL
    have hsz : ∀ i j, L j i = L i j := fun i j => by
      have := hs i j
      simp only [Matrix.map_apply] at this
      exact_mod_cast this
    have ha : (0 : ℝ) < (L 0 0 : ℝ) := by simpa using (hL.diag_pos (i := 0))
    have ha' : 0 < L 0 0 := by exact_mod_cast ha
    set S : Matrix (Fin n) (Fin n) ℤ :=
      Matrix.of fun i j => L 0 0 * L i.succ j.succ - L i.succ 0 * L 0 j.succ with hS
    have hSr : (S.map (Int.cast : ℤ → ℝ)).PosDef := by
      have := schur_posDef hL
      convert this using 1
      ext i j
      simp [hS]
    obtain ⟨ι, _, D, y, hD, hy⟩ := ih S hSr
    refine ⟨Fin D ⊕ ι, inferInstance, D * (L 0 0).toNat,
      Sum.elim (fun _ => fun j => L 0 j) (fun i => Fin.cons 0 (y i)), ?_, ?_⟩
    · have : 1 ≤ (L 0 0).toNat := by omega
      nlinarith
    · have hy' : ∀ p q, (D : ℤ) * (L 0 0 * L p.succ q.succ - L p.succ 0 * L 0 q.succ) =
          ∑ i, y i p * y i q := fun p q => by
        have := congrFun₂ hy p q
        simpa [hS, Matrix.sum_apply, vecMulVec_apply] using this
      have hc : ((L 0 0).toNat : ℤ) = L 0 0 := Int.toNat_of_nonneg ha'.le
      ext p q
      simp only [Matrix.smul_apply, Matrix.sum_apply, Fintype.sum_sum_type, Sum.elim_inl,
        Sum.elim_inr, vecMulVec_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, nsmul_eq_mul]
      push_cast
      rw [hc]
      refine Fin.cases ?_ (fun p => ?_) p <;> refine Fin.cases ?_ (fun q => ?_) q
      · simp
        ring
      · simp
        ring
      · simp [hsz 0 p.succ]
        ring
      · simp only [Fin.cons_succ]
        rw [← hy' p q, hsz 0 p.succ]
        ring

theorem exists_smul_eq_sum_vecMulVec_span :
    ∀ (r : ℕ) (L : Matrix (Fin r) (Fin r) ℤ), (L.map (Int.cast : ℤ → ℝ)).PosDef →
      ∃ (D m : ℕ) (a : Fin m → Fin r → ℤ), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧
        (D : ℤ) • L = ∑ i, Matrix.vecMulVec (a i) (a i) := by
  intro r L hL
  obtain ⟨κ₀, hκ⟩ := exists_nat_smul_sub_posDef hL (isHermitian_one (α := ℝ) (n := Fin r))
  set d := max κ₀ 1 with hdd
  have hd1 : 1 ≤ d := le_max_right _ _
  have hd := hκ d (le_max_left _ _)
  set M : Matrix (Fin r) (Fin r) ℤ := (d : ℤ) • L - 1 with hMdef
  have hM : (M.map (Int.cast : ℤ → ℝ)).PosDef := by
    convert hd using 1
    ext i j
    simp only [hMdef, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  obtain ⟨ι, _, D, a, hD, ha⟩ := exists_smul_eq_sum_vecMulVec r M hM
  let b : (Fin r × Fin D) ⊕ ι → Fin r → ℤ := Sum.elim (fun p => Pi.single p.1 1) a
  have hsum : ((D * d : ℕ) : ℤ) • L = ∑ k, vecMulVec (b k) (b k) := by
    rw [Fintype.sum_sum_type]
    simp only [b, Sum.elim_inl, Sum.elim_inr]
    rw [← ha]
    ext i j
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [hMdef, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply,
      vecMulVec_apply, smul_eq_mul, Matrix.one_apply]
    simp only [nsmul_eq_mul]
    push_cast
    have hδ : ∑ c : Fin r, (Pi.single c (1 : ℤ) : Fin r → ℤ) i * (Pi.single c (1 : ℤ) : Fin r → ℤ) j =
        if i = j then 1 else 0 := by
      by_cases h : i = j
      · subst h
        simp [Pi.single_apply]
      · simp [Pi.single_apply, h]
    rw [← Finset.mul_sum, hδ]
    split_ifs <;> ring
  have hspan : Submodule.span ℤ (Set.range b) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin r)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    exact ⟨Sum.inl (j, ⟨0, hD⟩), by simp [b]⟩
  let e := Fintype.equivFin ((Fin r × Fin D) ⊕ ι)
  refine ⟨D * d, Fintype.card ((Fin r × Fin D) ⊕ ι), b ∘ e.symm, ?_, ?_, ?_⟩
  · nlinarith
  · rw [e.symm.surjective.range_comp]
    exact hspan
  · rw [hsum]
    exact (e.symm.sum_comp (fun k => vecMulVec (b k) (b k))).symm

end GlobalTheory.Poinc.SumSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfTwistedPullbacksSameBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_of_twistedPullbacks_sameBundle : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) (m : ℕ), 1 ≤ m →
    ∀ (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
      (α α' : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp K)) P.A).left, (snd (baseOver (Sp K)) P.A ^ m).left]
        ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (s₁ s₁' : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), α.IsGen → α'.IsGen →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α' th s₁' →
    ∃ c : K, (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁' : EA P (𝟙 (Sp K)) (m ^ 2)) = c • SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁ := by
  first | exact @GlobalTheory.TwistRatio.exists_smul_of_isTwistPull | exact GlobalTheory.TwistRatio.exists_smul_of_isTwistPull | (intros; apply GlobalTheory.TwistRatio.exists_smul_of_isTwistPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegular
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem exists_specializes_dominatesStalk_of_regAt (X : Scheme.{0}) [IsIntegral X]
    (V : ValuationSubring X.functionField) (y : X) (hV : ∀ g, RegAt y g → g ∈ V) :
    ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  let ψ : X.presheaf.stalk y →+* V :=
    (algebraMap (X.presheaf.stalk y) X.functionField).codRestrict V.toSubring
      fun a ↦ hV _ ⟨a, rfl⟩
  let l : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk y
  have hl : specAlgebraMap V X.functionField ≫ l = genericFieldPoint X := by
    rw [← specAlgebraMap_fromSpecStalk y, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨l (IsLocalRing.closedPoint V), ?_, dominatesStalk_iff_exists_hom.mpr ⟨l, hl, rfl⟩⟩
  have h := ((IsLocalRing.specializes_closedPoint
    ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk y).continuous)
  rw [Scheme.fromSpecStalk_closedPoint] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SquareDescent

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem square_hom_ext (A : Over S) {Z : Scheme.{0}} {f g : Z ⟶ (A ⊗ A).left}
    (h₁ : f ≫ (fst A A).left = g ≫ (fst A A).left) (h₂ : f ≫ (snd A A).left = g ≫ (snd A A).left) : f = g :=
  pullback.hom_ext h₁ h₂

theorem eSec_fst (A : Over S) [GrpObj A] : eSec (A ⊗ A) ≫ (fst A A).left = eSec A := by
  show (η[A ⊗ A] ≫ fst A A).left = η[A].left
  simp [Hom.one_def]

theorem eSec_snd (A : Over S) [GrpObj A] : eSec (A ⊗ A) ≫ (snd A A).left = eSec A := by
  show (η[A ⊗ A] ≫ snd A A).left = η[A].left
  simp [Hom.one_def]

theorem eSec_lift_one (A : Over S) [GrpObj A] : eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec (A ⊗ A) := by
  apply pullback.hom_ext
  · change eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (fst A A).left = eSec (A ⊗ A) ≫ (fst A A).left
    show (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) ≫ fst A A).left = (η[A ⊗ A] ≫ fst A A).left
    simp [Hom.one_def]
  · change eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left ≫ (snd A A).left = eSec (A ⊗ A) ≫ (snd A A).left
    show (η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) ≫ snd A A).left = (η[A ⊗ A] ≫ snd A A).left
    simp [Hom.one_def]

theorem exists_bundle_descent : ∀ (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] (A₀ : Over Y) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (ν : Ga → (A.left ⟶ A.left)) (P : LB (G2 A).left), IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsGaloisCover Ga ν φ → (∀ a, IsGrpPullback A A (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∀ a, ∃ φ₂ : (G2 A).left ⟶ (G2 A).left, IsSquare (ν a) φ₂ ∧ LBIso P (P.pull φ₂)) → ∃ (P₀ : LB (G2 A₀).left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left), P₀.IsLB ∧ IsSquare φ φ₂ ∧ LBIso P (P₀.pull φ₂) ∧ ∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen := by
  intro X Y π Ga _ ρ A _ A₀ _ φ ν P hπ hA hA₀ gp hν hνρ ν₁ νm hP ⟨t₀, ht₀⟩ hsq
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG := hL.globalFns
  have hA₂ : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  choose ν₂ hν₂ iν₂ using hsq
  have ν₂m : ∀ a c, ν₂ (a * c) = ν₂ a ≫ ν₂ c := fun a c => square_hom_ext A
    (by rw [(hν₂ _).1, Category.assoc, (hν₂ c).1, reassoc_of% (hν₂ a).1, νm])
    (by rw [(hν₂ _).2, Category.assoc, (hν₂ c).2, reassoc_of% (hν₂ a).2, νm])
  have wA : (fst A A).left ≫ A.hom = (snd A A).left ≫ A.hom := (Over.w (fst A A)).trans (Over.w (snd A A)).symm
  let φ₂ : (G2 A).left ⟶ (G2 A₀).left := pullback.lift ((fst A A).left ≫ φ) ((snd A A).left ≫ φ)
    (by rw [Category.assoc, Category.assoc, gp.1.w, reassoc_of% wA])
  have hsqφ : IsSquare φ φ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsqφ
  have hu : ∀ a, ν₂ a ≫ (G2 A).hom = (G2 A).hom ≫ ρ a := fun a => by
    rw [← Over.w (fst A A), reassoc_of% (hν₂ a).1, (hνρ a).1.w, Category.assoc]
  have hinv : ∀ a, ν₂ a ≫ φ₂ = φ₂ := fun a => square_hom_ext A₀
    (by rw [Category.assoc, hsqφ.1, reassoc_of% (hν₂ a).1, hν.inv a])
    (by rw [Category.assoc, hsqφ.2, reassoc_of% (hν₂ a).2, hν.inv a])
  have hφ₂ : IsGaloisCover Ga ν₂ φ₂ := ((galoisCover_descent X Y π Ga ρ hπ).2.2 (G2 A).left (G2 A₀).left φ₂ ν₂
    (G2 A).hom (G2 A₀).hom hu hpb.w.symm).2 hpb.flip hinv
  have he : eSec (G2 A) ≫ (G2 A).hom = 𝟙 X := Over.w η[G2 A]
  have hτ : ∀ a, eSec (G2 A) ≫ ν₂ a = ρ a ≫ eSec (G2 A) := fun a => square_hom_ext A
    (by rw [Category.assoc, (hν₂ a).1, reassoc_of% eSec_fst A, GlobalTheory.TripleDescent.one_comm (hνρ a), Category.assoc,
      eSec_fst])
    (by rw [Category.assoc, (hν₂ a).2, reassoc_of% eSec_snd A, GlobalTheory.TripleDescent.one_comm (hνρ a), Category.assoc,
      eSec_snd])
  have hc0 : cls _ (pull_isLB hP (lift (1 : A ⟶ A) (𝟙 A)).left) = 0 := (cls_eq_zero_iff _).2 ⟨t₀, ht₀⟩
  have hPe : pull (eSec (G2 A)) (cls P hP) = 0 := by
    rw [← eSec_lift_one, pull_comp, ← cls_pull hP _ (pull_isLB hP _), hc0, map_zero]
  obtain ⟨r, hr⟩ := (cls_eq_zero_iff (pull_isLB hP (eSec (G2 A)))).1 hPe
  obtain ⟨u, hu₁, hu₂⟩ := GlobalTheory.TripleDescent.exists_linearisation hP (G2 A).hom (eSec (G2 A)) he (hG _ _ hA₂).2 ρ ν₂
    hπ.mul ν₂m hτ r hr iν₂
  obtain ⟨M, hM, iM⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ φ₂ Ga ν₂ P hφ₂ hP u hu₁ hu₂
  have hMP : pull φ₂ (cls M hM) = cls P hP := ((cls_eq_iff hP (pull_isLB hM φ₂)).2 iM).symm
  have he₀ : eSec (G2 A₀) ≫ (G2 A₀).hom = 𝟙 Y := Over.w η[G2 A₀]
  have hφe : eSec (G2 A) ≫ φ₂ = π ≫ eSec (G2 A₀) := square_hom_ext A₀
    (by rw [Category.assoc, hsqφ.1, reassoc_of% eSec_fst A, GlobalTheory.TripleDescent.one_comm gp, Category.assoc, eSec_fst])
    (by rw [Category.assoc, hsqφ.2, reassoc_of% eSec_snd A, GlobalTheory.TripleDescent.one_comm gp, Category.assoc, eSec_snd])
  let P₀ : LB (G2 A₀).left := LB.LinComb M (K := Fin 2) ![𝟙 _, (G2 A₀).hom ≫ eSec (G2 A₀)] ![1, -1]
  have hP₀ : P₀.IsLB := LB.isLB_linComb hM _ _
  have hc : cls P₀ hP₀ = cls M hM - pull ((G2 A₀).hom ≫ eSec (G2 A₀)) (cls M hM) := by
    rw [cls_linComb hM, Fin.sum_univ_two]
    simp [pull_id, sub_eq_add_neg]
  refine ⟨P₀, φ₂, hP₀, hsqφ, ?_, ?_⟩
  · refine (cls_eq_iff hP (pull_isLB hP₀ φ₂)).1 ?_
    rw [cls_pull hP₀, hc, map_sub, ← pull_comp, hMP, ← Category.assoc, hpb.w, Category.assoc, ← hφe,
      ← Category.assoc, pull_comp, hMP, pull_comp, hPe, map_zero, sub_zero]
  · refine (cls_eq_zero_iff (pull_isLB hP₀ _)).1 ?_
    rw [cls_pull hP₀, hc, map_sub, ← pull_comp, ← Category.assoc, he₀]
    erw [Category.id_comp, sub_self]

end GlobalTheory.SquareDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAlgClosedCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_algClosed_charZero : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (P : PolAV (Sp C)) (k : ℕ), 1 ≤ k → ∃ ζ : Cˣ, Nonempty (Out.Level P k (unitOn ζ)) := by
  first | exact @GlobalTheory.MBLow.exists_level_algClosed_charZero | exact GlobalTheory.MBLow.exists_level_algClosed_charZero | (intros; apply GlobalTheory.MBLow.exists_level_algClosed_charZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentLiftCoefficients
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel.LiftComb

theorem lift_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (K : Type) [CommRing K] (yy : Sp K ⟶ Xo'.XF c') (g : ℕ) (e : Fin g → (Sp (DualNumber K) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (yy ≫ Y.j) (e i)) → ∀ (cf : Fin g → K), ∃ w : Sp (DualNumber K) ⟶ Y.oF.t.G.left, IsCombAtG Y.t (yy ≫ Y.j) e cf (w ≫ Y.m.φ) := by
  intro E _ _ _ H Dw l' Xo' c' W Y K _ yy g e he cf
  have hε : ∀ c : K, spMap (epsMul c) ≫ spMap (algebraMap K (DualNumber K)) = spMap (algebraMap K (DualNumber K)) := by
    intro c
    unfold spMap
    rw [← Spec.map_comp]
    congr 1
    ext a
    · simp [epsMul]
    · simp [epsMul]
  let u : Fin g → (tEpsG (yy ≫ Y.j) ⟶ Y.t.G) := fun i => Over.homMk (spMap (epsMul (cf i)) ≫ e i) (by
      simp only [tEpsG, Over.mk_hom, Category.assoc]
      rw [(he i).1]
      simp only [← Category.assoc]
      rw [hε])
  have hv : ((List.ofFn u).prod).left ≫ Y.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ yy ≫ Y.j :=
    Over.w ((List.ofFn u).prod)
  have hc := Y.m.cart.1
  refine ⟨hc.lift ((List.ofFn u).prod).left (spMap (algebraMap K (DualNumber K)) ≫ yy) (by rw [Category.assoc]; exact hv), u, fun i => rfl, ?_⟩
  rw [hc.lift_fst]

end GlobalTheory.FlatModel.LiftComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleOfEvaluationsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tate_module_of_evaluations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p)
    (ev : ℕ → Dw.La → (Over.mk (𝟙 (Sp ℂ_[p])) ⟶ P.A.A)), (∀ k a b, ev k (a + b) = ev k a * ev k b) →
    (∀ k (o : 𝓞 E) a, ev k (o • a) = ev k a ≫ P.oA.act o) →
    (∀ k m, 0 < k → 0 < m → ∀ a, ev (k * m) a ^ m = ev k a) → (∀ a, ev 1 a = 1) →
    ∃ tι : Dw.La →+ P.T, (∀ a k, (tι a).lev k = ev (p ^ k) a) ∧ ∀ (o : 𝓞 E) a, tι (o • a) = P.actT o (tι a) := by
  first | exact @GlobalTheory.FlatModel.tateLift_exists | exact GlobalTheory.FlatModel.tateLift_exists | (intros; apply GlobalTheory.FlatModel.tateLift_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusExtensionTangentOfAdditiveMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.TorVec

theorem exists_torus_tangent : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (l : D.X →+ R), ∃ gm : GtPt D (epsR R), GtTan gm ∧ gm.b = DegPre.zeroT D (epsR R) ∧ ∀ (χ : D.X) (Z : Scheme.{0}) (q : Z ⟶ (epsR R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good D.P.L z J → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (gm.s χ) q z J).val = ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv.hom (1 + TrivSqZeroExt.inr (l χ))) := by
  intro R _ _ D l
  obtain ⟨ν, hb, hv⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := epsR R)
    (fun x => GlobalTheory.TorusTangent.oneAdd (l x)) fun x y => by rw [map_add, GlobalTheory.TorusTangent.oneAdd_add]
  refine ⟨ν, ?_, hb, fun χ Z q z J hJ => ?_⟩
  · obtain ⟨g₀, h₀, v₀⟩ := GlobalTheory.TorusTangent.exists_pt (D := D) (T := baseOver (Sp R)) (fun _ => 1)
      fun _ _ => (_root_.mul_one _).symm
    refine ⟨g₀, ⟨h₀, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩, ?_, fun x => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · rw [v₀ x _ _ y J hJ, map_one, val_one]
    · rw [h₀, hb, GlobalTheory.TorusTangent.zeroT_left, GlobalTheory.TorusTangent.zeroT_left, ← Category.assoc]
      exact congrArg (· ≫ eSec D.P.A) GlobalTheory.TorusTangent.fst_inl.symm
    · refine (v₀ x _ _ y J hJ).trans (Units.ext (Eq.trans ?_
        (GlobalTheory.TorusTangent.hasVal_spMap (hv x) (TrivSqZeroExt.fstHom R R R).toRingHom hJ).symm))
      rw [GlobalTheory.TorusTangent.valR_oneAdd, map_one]
      simp
  · rw [hv χ Z q z J hJ, ← gs_unit q z ⊤ trivial]
    rfl

end GlobalTheory.MBLow.TorVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLeStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistingSection_mul_lattice_value_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (Z : Comp Xo c) (t : TwSec U x Z G₀) (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valOn Z w, ∀ f ∈ latW U G, ∃ g ∈ latW U (G + G₀), v g ≤ v f + ((t.hi w - (⌊t.lo w⌋ : ℝ) : ℝ) : EReal) := by
  first | exact @GlobalTheory.TwMulOne.exists_latW_val_le | exact GlobalTheory.TwMulOne.exists_latW_val_le | (intros; apply GlobalTheory.TwMulOne.exists_latW_val_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueGenericFibreDualNumberPointOfModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_genericFibreDualNumberPoint_of_model : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (y : epsR V ⟶ G), (∃! yA, VecAt U.toUnifPre F y yA) ∧ (∃! v : epsR (FractionRing V) ⟶ A.A, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v) ∧ ∀ (v : epsR (FractionRing V) ⟶ A.A) yA, IsVecOver (algebraMap V (FractionRing V)) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) y v → VecAt U.toUnifPre F y yA → yA ≫ (snd (TFK (R := V) F) A.A).left = spMap (dualMap (algebraMap (FractionRing V) F)) ≫ v.left := by
  first | exact @GlobalTheory.MBLow.vecAt_genFibre | exact GlobalTheory.MBLow.vecAt_genFibre | (intros; apply GlobalTheory.MBLow.vecAt_genFibre <;> assumption)
end

