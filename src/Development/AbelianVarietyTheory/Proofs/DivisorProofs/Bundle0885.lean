import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReordEqConj
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField

namespace GlobalTheory.ColumnMultSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def permUnit (κ : Type) [CommRing κ] {r : ℕ} (π : Equiv.Perm (Fin r)) : GL (Fin r) κ where
  val := π.toPEquiv.toMatrix
  inv := π.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem reord_eq_conj {D : D7} {Pg : Finset (Pl D.host.E)} {r : ℕ} (π : Equiv.Perm (Fin r)) :
    ∃ w : G0 Pg r, ∀ g : G0 Pg r, reord π g = w * g * w⁻¹ := by
  refine ⟨fun PP => permUnit (kP PP.1) π, fun g => ?_⟩
  funext PP
  apply Units.ext
  show Matrix.reindexAlgEquiv (kP PP.1) (kP PP.1) π.symm (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) =
    π.toPEquiv.toMatrix * (g PP : Matrix (Fin r) (Fin r) (kP PP.1)) * π.symm.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp

theorem columnMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.grp_levels F → R.Pg.card = 2 * D.R.f → (∀ PP ∈ R.Pg, min (D.host.g 0) (D.host.g 1) ≤ Nat.card (kP PP)) → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → (∀ χ ∈ A.X, IsAbsIrrChar χ) → (∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar D.what₂.embLL R.Pg D.R.r fun g => χ (R.eG.symm g)) → ∀ [Fintype F.P1], ∀ χ ∈ A.X, ∃ n : ℕ, (Nat.card F.P1 : D.what₂.LL)⁻¹ * ∑ h : F.P1, χ (h : G) * (((F.ψ1 h)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) = (n : D.what₂.LL) ∧ |(n : ℝ) - (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ)| ≤ 8 * (D.R.f : ℝ) * (D.R.r : ℝ) / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) * (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.nbar R.Pg D.R.k : ℝ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hlev hcard hq hadm hirr hprod _ χ hχ
  classical
  obtain ⟨ψ, hψ, -, π, -, hmem, hchi⟩ := hlev
  obtain ⟨w, hw⟩ := reord_eq_conj (D := D) (Pg := R.Pg) π
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hr : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  have hg : 0 < min (D.host.g 0) (D.host.g 1) := lt_min (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hp : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsProdCuspChar (RingHom.id ℂ) R.Pg D.R.r fun g => D.what₂.embLL (χ (R.eG.symm g)) :=
    hprod χ hχ
  obtain ⟨⟨n, hn, hb⟩, -⟩ := GlobalTheory.FinGL.MultSharpObj.multSharp D.host.E ℂ (RingHom.id ℂ) R.Pg D.R.f
    (min (D.host.g 0) (D.host.g 1)) D.R.r D.R.rS D.R.k ψ hcard hk hr hg hadm hq hψ _ hp
  refine ⟨n, ?_, hb⟩
  have hm : ∀ g : G, R.eG g ∈ (R.levR F true).H ↔ g ∈ F.P1 := fun g => by
    show R.eG.symm (R.eG g) ∈ F.P1 ↔ _
    rw [MulEquiv.symm_apply_apply]
  have hc : ∀ (g : G) (h : R.eG g ∈ (R.levR F true).H), (((R.levR F true).chi ⟨R.eG g, h⟩ : ℂˣ) : ℂ) =
      D.what₂.embLL ((F.ψ1 ⟨g, (hm g).1 h⟩ : D.what₂.LLˣ) : D.what₂.LL) := fun g h => by
    show D.what₂.embLL ((F.ψ1 ⟨R.eG.symm (R.eG g), h⟩ : D.what₂.LLˣ) : D.what₂.LL) = _
    congr 4
    exact R.eG.symm_apply_apply g
  let e : F.P1 ≃ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ).H :=
    (R.eG.trans (MulAut.conj w)).toEquiv.subtypeEquiv fun g => by
      rw [← hm, hmem, hw]; rfl
  apply D.what₂.embLL.injective
  rw [map_natCast, ← hn, map_mul, map_inv₀, map_natCast, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.levelMult
  rw [Nat.card_congr e]
  congr 1
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.finite_boundedLevelClassGroupFamily R.Pg D.R.r
  letI : Fintype (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ).H := Fintype.ofFinite _
  refine Fintype.sum_equiv e _ _ fun x => ?_
  have h1 : R.eG x ∈ (R.levR F true).H := (hm x).2 x.2
  have h2 := (hmem _).1 h1
  have he : e x = ⟨reord π (R.eG x), h2⟩ := Subtype.ext (hw _).symm
  rw [he, ← hchi _ h1 h2, map_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, hc]
  congr 2
  show χ x = χ (R.eG.symm (reord π (R.eG x)))
  rw [hw, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, (hirr χ hχ).conj]

end GlobalTheory.ColumnMultSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannRelationConverseConjAffine
section
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PeriodCoord

private theorem inv_mul_eq_mul_inv_of_intertwine {n : Type} [Fintype n] [DecidableEq n]
    (A B D : Matrix n n ℂ) (hA : A.det ≠ 0) (hD : D.det ≠ 0) (h : B * D = A * B) :
    A⁻¹ * B = B * D⁻¹ := by
  have hA' : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hD' : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  calc A⁻¹ * B = A⁻¹ * (B * D) * D⁻¹ := by
          rw [Matrix.mul_assoc A⁻¹, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hD', Matrix.mul_one]
    _ = A⁻¹ * A * B * D⁻¹ := by rw [h, Matrix.mul_assoc A⁻¹ A B]
    _ = B * D⁻¹ := by rw [Matrix.nonsing_inv_mul _ hA', Matrix.one_mul]

private theorem star_dot_mulVec {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    star (x ⬝ᵥ A *ᵥ y) = star x ⬝ᵥ A.map star *ᵥ star y := by
  simp [dotProduct, mulVec, star_sum, Finset.mul_sum]

private theorem star_mulVec' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (y : Fin g → ℂ) :
    star (A *ᵥ y) = A.map star *ᵥ star y := by
  funext i
  simp [mulVec, dotProduct, star_sum]

private theorem dot_left {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ Aᵀ *ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

private theorem map_star_mul' {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) :
    (A * B).map star = A.map star * B.map star := by
  ext i j; simp [Matrix.mul_apply, star_sum]

private theorem map_star_map_star' {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : (A.map star).map star = A := by
  ext i j; simp

private theorem conj_transpose_intertwine {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) : (C.map star)ᵀ * Cᵀ * M₀ = M₀ * C.map star * C := by
  have f0 : M₀.map star = M₀ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simpa [conjTranspose_apply] using this
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have f1' : M₀ * C.map star = (C.map star)ᵀ * M₀ᵀ := by
    have := congrArg (fun A => A.map star) f1
    simp only [map_star_mul'] at this
    have e1 : (M₀ᵀ).map star = M₀ := by rw [transpose_map, f0, transpose_transpose]
    have e2 : (Cᵀ).map star = (C.map star)ᵀ := by rw [transpose_map]
    rw [e1, e2, f0] at this
    exact this
  rw [Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, ← f1']

theorem riemann_converse {g : ℕ} (M₀ C : Matrix (Fin g) (Fin g) ℂ) (hH : M₀ᴴ = M₀) (_hdet : M₀.det ≠ 0)
    (hS : (Cᵀ * M₀)ᵀ = Cᵀ * M₀) (hY : (1 - C.map star * C).det ≠ 0) :
    (M₀ * (1 - C.map star * C)⁻¹)ᴴ = M₀ * (1 - C.map star * C)⁻¹ ∧
      ∀ z w : Fin g → ℂ, (hermForm (M₀ * (1 - C.map star * C)⁻¹) (z + C *ᵥ star z) (w + C *ᵥ star w)).im =
        (hermForm M₀ z w).im := by
  set Y := 1 - C.map star * C with hYdef
  set M := M₀ * Y⁻¹ with hMdef
  have f2 := conj_transpose_intertwine M₀ C hH hS
  have f1 : M₀ᵀ * C = Cᵀ * M₀ := by rw [transpose_mul, transpose_transpose] at hS; exact hS
  have hYh : Yᴴ = 1 - (C.map star)ᵀ * Cᵀ := by
    rw [hYdef, conjTranspose_sub, conjTranspose_one, conjTranspose_mul]
    congr 2
    · ext i j; simp
  have hYt : Yᵀ = 1 - Cᵀ * (C.map star)ᵀ := by
    rw [hYdef, transpose_sub, transpose_one, transpose_mul]

  have ha : Mᴴ = M := by
    rw [hMdef, conjTranspose_mul, conjTranspose_nonsing_inv, hH]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYh, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, f2, Matrix.mul_assoc]
    · rw [det_conjTranspose]; exact star_ne_zero.mpr hY

  have hMbar : M.map star = Mᵀ := by
    ext i j
    have := congrFun (congrFun ha j) i
    simpa [conjTranspose_apply] using this
  have hb : M.map star * C = Cᵀ * M := by
    rw [hMbar, hMdef, transpose_mul, transpose_nonsing_inv, Matrix.mul_assoc, f1, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc]
    apply inv_mul_eq_mul_inv_of_intertwine _ _ _ _ hY
    · rw [hYt, hYdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_assoc Cᵀ (C.map star)ᵀ, ← Matrix.mul_assoc (C.map star)ᵀ, f2]
      simp only [Matrix.mul_assoc]
    · rw [det_transpose]; exact hY

  have hc : M = M₀ + (C.map star)ᵀ * M.map star * C := by
    have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, hMdef, ← Matrix.mul_assoc, f2]
    have h0 : M₀ = M₀ * Y * Y⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hYu, Matrix.mul_one]
    calc M₀ * Y⁻¹ = (M₀ * Y + M₀ * C.map star * C) * Y⁻¹ := by
          rw [Matrix.mul_assoc M₀ (C.map star), ← Matrix.mul_add, hYdef, sub_add_cancel, Matrix.mul_one]
      _ = M₀ * Y * Y⁻¹ + M₀ * C.map star * C * Y⁻¹ := Matrix.add_mul _ _ _
      _ = _ := by rw [← h0]
  refine ⟨ha, fun z w => ?_⟩
  have e : hermForm M (z + C *ᵥ star z) (w + C *ᵥ star w) =
      z ⬝ᵥ M *ᵥ star w + z ⬝ᵥ (M * C.map star) *ᵥ w + star z ⬝ᵥ (Cᵀ * M) *ᵥ star w
        + star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w := by
    simp only [hermForm, star_add, star_mulVec', star_star, add_dotProduct, mulVec_add, dotProduct_add,
      dot_left, mulVec_mulVec, Matrix.mul_assoc]
    ring
  have e2 : star (z ⬝ᵥ (M * C.map star) *ᵥ w) = star z ⬝ᵥ (Cᵀ * M) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_map_star', hb]
  have e4 : star (star z ⬝ᵥ (Cᵀ * M * C.map star) *ᵥ w) = z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    rw [star_dot_mulVec, map_star_mul', map_star_mul', map_star_map_star', star_star, transpose_map]
  have e1 : z ⬝ᵥ M *ᵥ star w = hermForm M₀ z w + z ⬝ᵥ ((C.map star)ᵀ * M.map star * C) *ᵥ star w := by
    conv_lhs => rw [hc]
    rw [hermForm, add_mulVec, dotProduct_add]
  rw [e, e1, ← e2, ← e4]
  simp only [Complex.add_im, Complex.star_def, Complex.conj_im]
  ring

end GlobalTheory.PeriodCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCutUnipBMulLevSet
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

theorem truncatedRow_unipotent_mul_and_ne_zero : ∀ (n : ℕ) (ρ : Fin n), ∀ g ∈ levSet n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), rowCut ρ ((u * g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)) ∧
    ∃ j, j ≤ ρ ∧ rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 := by
  intro n ρ g hg
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB ℂ).1 hu
    funext j
    unfold rowCut
    split_ifs with hj
    · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ρ]
      · rw [hu1, one_mul]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [hu0 ρ k h, zero_mul]
        · have h' := Fin.lt_def.1 h
          rw [(hg k (by omega)).1 j (lt_of_le_of_lt hj h), mul_zero]
      · simp
    · rfl
  · by_contra hne
    push_neg at hne
    have hinv := (GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 g hg
    have h1 : ((g * g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ρ ρ = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k ≤ ρ
      · have := hne k hk
        simp only [rowCut, hk, if_true] at this
        rw [this, zero_mul]
      · push_neg at hk
        have h' := Fin.lt_def.1 hk
        rw [(hinv k (by omega)).1 ρ hk, mul_zero]

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLevelPrincipalFirstBlockIndexEqCard
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RowLevIndex

section Gen

variable {κ : Type} [CommRing κ]

theorem firstDiagonalBlock_of_diagonal_embedding {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (p : GL (Fin r) κ) (M : GL (Fin n) κ)
    (hM : M ∈ blockUT n κ r bl) (e : M = diagEmb κ h p) : blk0 n κ h bl ⟨M, hM⟩ = p := by
  subst e
  apply Units.ext
  ext i j
  rw [blockZero_val]
  show (diagEmb κ h p : Matrix (Fin n) (Fin n) κ) (Fin.castLE h i) (Fin.castLE h j) = _
  rw [diagEmb_val, diagMat_of_lt _ (show (Fin.castLE h i).val < r from i.2) (show (Fin.castLE h j).val < r from j.2)]
  rfl

theorem HK_le_HPar {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) :
    HK n κ r bl ≤ HPar n κ h bl H₀ := by
  rw [HK_eq_HPar h bl]
  intro M hM
  obtain ⟨hb, h0⟩ := mem_HPar.mp hM
  exact mem_HPar.mpr ⟨hb, by rw [Subgroup.mem_bot] at h0; rw [h0]; exact H₀.one_mem⟩

theorem mem_HK_iff {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (M : GL (Fin n) κ) (hM : M ∈ blockUT n κ r bl) :
    M ∈ HK n κ r bl ↔ blk0 n κ h bl ⟨M, hM⟩ = 1 := by
  rw [HK_eq_HPar h bl, mem_HPar]
  constructor
  · rintro ⟨_, h0⟩
    exact (Subgroup.mem_bot).mp h0
  · intro h0
    exact ⟨hM, (Subgroup.mem_bot).mpr h0⟩

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in

abbrev inL (v : Pr.vGs) : rowSG Pr sel mu := ⟨v.1, Finset.mem_union_left _ v.2⟩

theorem rowTy_inL (P : LevFam X.E X.K R.r Pr.vGs) (v : Pr.vGs) :
    rowTy Ch sel mu P (inL sel mu v) = rowTyG Ch P v := LevFam.glue_of_mem _ _ _ v.2

theorem rowTyKK_inL (v : Pr.vGs) :
    rowTyKK Ch sel mu (inL sel mu v) = rowTyK Ch v := LevFam.glue_of_mem _ _ _ v.2

theorem rowTy_H_of_not (P : LevFam X.E X.K R.r Pr.vGs) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) :
    (rowTy Ch sel mu P w).H = (rowTyKK Ch sel mu w).H := by
  unfold rowTy rowTyKK
  rw [LevFam.glue_of_not _ _ _ hw, LevFam.glue_of_not _ _ _ hw]

theorem memP (P : LevFam X.E X.K R.r Pr.vGs) (x : ↥(rowTy Ch sel mu P).inv.grp) (v : Pr.vGs) :
    x.1 (inL sel mu v) ∈ HPar (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t) (P v).H := by
  have h := x.2 (inL sel mu v) (Set.mem_univ _)
  change x.1 (inL sel mu v) ∈ (rowTy Ch sel mu P (inL sel mu v)).H at h
  rw [rowTy_inL] at h
  exact h

theorem grp_le (P : LevFam X.E X.K R.r Pr.vGs) :
    (rowTyKK Ch sel mu).inv.grp ≤ (rowTy Ch sel mu P).inv.grp := by
  intro x hx w _
  have h := hx w (Set.mem_univ _)
  change x w ∈ (rowTyKK Ch sel mu w).H at h
  change x w ∈ (rowTy Ch sel mu P w).H
  by_cases hw : w.1 ∈ Pr.vGs
  · have e1 := rowTyKK_inL Ch sel mu ⟨w.1, hw⟩
    have e2 := rowTy_inL Ch sel mu P ⟨w.1, hw⟩
    change rowTyKK Ch sel mu w = _ at e1
    change rowTy Ch sel mu P w = _ at e2
    rw [e1] at h
    rw [e2]
    exact GlobalTheory.RowLevIndex.HK_le_HPar _ _ _ h
  · rw [rowTy_H_of_not Ch sel mu P w hw]
    exact h

def blkMap (P : LevFam X.E X.K R.r Pr.vGs) : FormG (rowTy Ch sel mu P).inv →* GLG X.E R.r Pr.vGs where
  toFun x v := blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t)
    ⟨x.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P x.2 v)⟩
  map_one' := by
    funext v
    exact map_one (blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t))
  map_mul' a b := by
    funext v
    exact map_mul (blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t))
      ⟨a.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P a.2 v)⟩ ⟨b.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P b.2 v)⟩

end Rows

section Rows2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

def incl : FormG (rowTyKK Ch sel mu).inv →* FormG (rowTy Ch sel mu P).inv :=
  MonoidHom.prodMap (MonoidHom.id _) (Subgroup.inclusion (grp_le Ch sel mu P))

theorem incl_injective : Function.Injective (incl Ch sel mu P) := by
  intro a b e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg (fun x => (x.2 : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))) e
  exact Prod.ext e1 (Subtype.ext e2)

theorem range_incl : (incl Ch sel mu P).range = (blkMap Ch sel mu P).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    funext v
    have h := y.2.2 (inL sel mu v) (Set.mem_univ _)
    change y.2.1 (inL sel mu v) ∈ (rowTyKK Ch sel mu (inL sel mu v)).H at h
    rw [rowTyKK_inL] at h
    exact (GlobalTheory.RowLevIndex.mem_HK_iff (r_le_X' R) _ _ _).mp h
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have hmem : x.2.1 ∈ (rowTyKK Ch sel mu).inv.grp := by
      intro w _
      change x.2.1 w ∈ (rowTyKK Ch sel mu w).H
      by_cases hw : w.1 ∈ Pr.vGs
      · have e1 := rowTyKK_inL Ch sel mu ⟨w.1, hw⟩
        change rowTyKK Ch sel mu w = _ at e1
        rw [e1]
        exact (GlobalTheory.RowLevIndex.mem_HK_iff (r_le_X' R) _ _ (HPar_le _ _ _ (memP Ch sel mu P x.2 ⟨w.1, hw⟩))).mpr
          (congrFun hx ⟨w.1, hw⟩)
      · rw [← rowTy_H_of_not Ch sel mu P w hw]
        exact x.2.2 w (Set.mem_univ _)
    exact ⟨(x.1, ⟨x.2.1, hmem⟩), rfl⟩

open Classical in
theorem range_blkMap : (blkMap Ch sel mu P).range = P.grp := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    intro v _
    obtain ⟨_, h0⟩ := mem_HPar.mp (memP Ch sel mu P x.2 v)
    exact h0
  · intro hp
    let h : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu) := fun w =>
      if hw : w.1 ∈ Pr.vGs then diagEmb _ (r_le_X' R) (p ⟨w.1, hw⟩) else 1
    have hmem : h ∈ (rowTy Ch sel mu P).inv.grp := by
      intro w _
      change h w ∈ (rowTy Ch sel mu P w).H
      by_cases hw : w.1 ∈ Pr.vGs
      · have e2 := rowTy_inL Ch sel mu P ⟨w.1, hw⟩
        change rowTy Ch sel mu P w = _ at e2
        rw [e2]
        have hh : h w = diagEmb _ (r_le_X' R) (p ⟨w.1, hw⟩) := dif_pos hw
        rw [hh]
        exact mem_HPar.mpr ⟨diagEmb_mem_blockUT _ _ _, by
          rw [GlobalTheory.RowLevIndex.firstDiagonalBlock_of_diagonal_embedding _ _ (p ⟨w.1, hw⟩) _ _ rfl]; exact hp ⟨w.1, hw⟩ (Set.mem_univ _)⟩
      · have hh : h w = 1 := dif_neg hw
        rw [hh]
        exact Subgroup.one_mem _
    refine ⟨((1 : UF X.E (R.N R.m - 1)), ⟨h, hmem⟩), ?_⟩
    funext v
    exact GlobalTheory.RowLevIndex.firstDiagonalBlock_of_diagonal_embedding _ _ (p v) _ _ (dif_pos v.2)

end Rows2

theorem index_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs), ∃ ι : (mtildeKGSD W Ch sel mu).G →* (mtildeGSD W Ch sel mu P).G, Function.Injective ι ∧ (∀ (a : (mtildeKGSD W Ch sel mu).G) (d : (mtildeKGSD W Ch sel mu).D), ι a • d = a • d) ∧ ι.range.index = Nat.card P.grp := by
  intro X Pr R W Ch sel S mu P
  refine ⟨incl Ch sel mu P, incl_injective Ch sel mu P, fun a d => rfl, ?_⟩
  rw [range_incl, Subgroup.index_ker, range_blkMap]

end GlobalTheory.RowLevIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigOneAddMul
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs

section Additive

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {R₁ : Type} [CommRing R₁]
  [Algebra R₀ R₁]

theorem sig_mem_map (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ) (y : R₁ ⊗[R₀] B₀) :
    σ y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem x))
  | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy

theorem sig_unique (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀]
    (p : B →+* B₀) (hp : Function.Surjective p) (σ σ' : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (hσ' : α.IsSig p σ') (y : R₁ ⊗[R₀] B₀) : σ y = σ' y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x b₀ =>
    obtain ⟨b, rfl⟩ := hp b₀
    rw [hσ, hσ']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sig_one_add_mul (hI : I ^ 2 = 0) (α : Aug I π R₁) {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀]
    [Algebra R₀ B₀] (p : B →+* B₀) (hp : Function.Surjective p) (σ : R₁ ⊗[R₀] B₀ →+ B) (hσ : α.IsSig p σ)
    (z z' : R₁ ⊗[R₀] B₀) : (1 + σ z) * (1 + σ z') = 1 + σ (z + z') := by
  have h0 : σ z * σ z' = 0 := by
    have hm := Ideal.mul_mem_mul (sig_mem_map α p hp σ hσ z) (sig_mem_map α p hp σ hσ z')
    rw [← Ideal.map_mul, ← sq, hI, Ideal.zero_eq_bot, Ideal.map_bot] at hm
    exact (Submodule.mem_bot _).1 hm
  rw [map_add]
  linear_combination h0

end Additive

theorem isObU_mul : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (u u' : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (c c' : GlobalTheory.CatCoh.H2 (ext R₁ F)), IsObU L α u c → IsObU L α u' c' → IsObU L α (fun T T' a ↦ u T T' a * u' T T' a) (c + c') := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L u u' c c' h h'
  obtain ⟨v, σ, z, hv, hσ, rfl, hz⟩ := h
  obtain ⟨v', σ', z', hv', hσ', rfl, hz'⟩ := h'
  refine ⟨fun T T' a ↦ v T T' a * v' T T' a, σ, z + z', fun T T' a ↦ ?_, hσ, (map_add _ _ _).symm,
    fun T T' T'' a b ↦ ⟨?_, ?_⟩⟩
  · simp only [Units.val_mul, map_mul, hv, hv']
  · have h1 := (hz T T' T'' a b).1
    have h2 := (hz' T T' T'' a b).1
    unfold Aug.KerQ at h1 h2 ⊢
    change Algebra.TensorProduct.map α.q (AlgHom.id R₀ _) (z.1 T T' T'' a b + z'.1 T T' T'' a b) = 0
    rw [map_add, h1, h2, add_zero]
  · have e := (hz T T' T'' a b).2
    have e' := (hz' T T' T'' a b).2
    have hs : σ' T'' (z'.1 T T' T'' a b) = σ T'' (z'.1 T T' T'' a b) :=
      sig_unique α (L.p T'') (L.surj T'') _ _ (hσ' T'') (hσ T'') _
    rw [hs] at e'
    change _ = (1 + σ T'' (z.1 T T' T'' a b + z'.1 T T' T'' a b)) * _
    rw [← sig_one_add_mul hI α (L.p T'') (L.surj T'') (σ T'') (hσ T'')]
    simp only [Units.val_mul, map_mul]
    calc L.ρ b (v T T' a : L.B T') * L.ρ b (v' T T' a : L.B T') * ((v T' T'' b : L.B T'') * (v' T' T'' b : L.B T''))
        = (L.ρ b (v T T' a : L.B T') * (v T' T'' b : L.B T'')) *
            (L.ρ b (v' T T' a : L.B T') * (v' T' T'' b : L.B T'')) := by ring
      _ = _ := by rw [e, e']; ring

end GlobalTheory.LBObs
end
end

