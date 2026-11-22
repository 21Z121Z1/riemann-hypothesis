import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledIsotropicStructureGeneral
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MapConjInv

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Pull

open GlobalTheory.Dict.Extend

variable {E : Type} [Field E] {r : ℕ}

section Cast

variable {Ψ Ψ' : Finset (E →+* ℂ)}

theorem cast_symm (h : Ψ = Ψ') (x : Frame Ψ r) : castFr h.symm (castFr h x) = x := rfl

theorem cast_lact (h : Ψ = Ψ') (a : GL (Fin r) E) (x : Frame Ψ r) :
    castFr h (lact a x) = lact a (castFr h x) := rfl

theorem cast_rmul (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFr h (rmul x b) = rmul (castFr h x) (castFr h b) := rfl

theorem cast_bor (h : Ψ = Ψ') {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : castFr h b ∈ Bor Ψ' r := by
  subst h; exact hb

theorem cast_GG (h : Ψ = Ψ') {G G' : Matrix (Fin r) (Fin r) E} (hG : G = G') {p p' : ℕ} (hp : p = p')
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p) : castFr h x ∈ GG Ψ' G' p' := by
  subst h hG hp; exact hx

theorem cast_diff (h : Ψ = Ψ') : Differentiable ℂ (castFr (r := r) h) := by
  subst h; exact differentiable_id

theorem cast_bchar (h : Ψ = Ψ') {la : Wt Ψ r} {la' : Wt Ψ' r}
    (hl : ∀ (τ : Ψ') i, la' τ i = la ⟨τ.1, h ▸ τ.2⟩ i) (b : Frame Ψ r) :
    bchar la' (castFr h b) = bchar la b := by
  subst h
  obtain rfl : la' = la := funext fun τ => funext fun i => hl τ i
  rfl

theorem cast_wt (h : Ψ = Ψ') {G G' : Matrix (Fin r) (Fin r) E} (hG : G = G') {la : Wt Ψ r} {la' : Wt Ψ' r}
    (hl : ∀ (τ : Ψ') i, la' τ i = la ⟨τ.1, h ▸ τ.2⟩ i) (x : Frame Ψ' r) :
    (∏ τ, ∏ i, ‖dmin G (castFr h.symm x) τ (Fin.succ i) / dmin G (castFr h.symm x) τ i.castSucc‖ ^
        (-(la τ i : ℝ) / 2)) =
      ∏ τ, ∏ i, ‖dmin G' x τ (Fin.succ i) / dmin G' x τ i.castSucc‖ ^ (-(la' τ i : ℝ) / 2) := by
  subst h hG
  obtain rfl : la' = la := funext fun τ => funext fun i => hl τ i
  rfl

end Cast

theorem inv_mulVec (a : GL (Fin r) E) (v : Fin r → E) :
    ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_inv (a : GL (Fin r) E) (v : Fin r → E) :
    (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable [NumberField E]

theorem mem_mapL {a : GL (Fin r) E} {L : Lt E r} {v : Fin r → E} :
    (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ mapL a L ↔ v ∈ L := by
  constructor
  · rintro ⟨w, hw, e⟩
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = (a : Matrix (Fin r) (Fin r) E) *ᵥ v := e
    have : w = v := by rw [← inv_mulVec a w, e', inv_mulVec]
    exact this ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

variable [IsCMField E] {X : Data E r}

theorem isUn_inv {a : GL (Fin r) E} (ha : IsUn X a) : IsUn X a⁻¹ := fun x y => by
  rw [← ha, mulVec_inv, mulVec_inv]

theorem isUn_mul {a b : GL (Fin r) E} (ha : IsUn X a) (hb : IsUn X b) : IsUn X (a * b) := fun x y => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

theorem conj_mem {X' : Data E r} (hG : X'.Gm = X.Gm) {a g : GL (Fin r) E} {M : ℕ} (ha : IsUn X a) (hg : IsUn X g)
    (hfix : mapL g (mapL a X'.Λ) = mapL a X'.Λ)
    (hM : ∀ u ∈ mapL a X'.Λ, ∃ u' ∈ mapL a X'.Λ, (g : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')
    (hP : HasPrinc X' M) : a⁻¹ * g * a ∈ X'.Γ := by
  have hc : mapL (a⁻¹ * g * a) X'.Λ = X'.Λ := by
    rw [mapL_mul, mapL_mul, hfix, ← mapL_mul, inv_mul_cancel, mapL_one]
  refine hP _ ⟨?_, fun x => ?_⟩ fun v hv => ?_
  · rw [hG]
    exact isUn_mul (isUn_mul (isUn_inv ha) hg) ha
  · rw [← mem_mapL (a := a⁻¹ * g * a), hc]
  · obtain ⟨u', ⟨w, hw, e⟩, hu⟩ := hM _ (mem_mapL.2 hv)
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = u' := e
    refine ⟨w, hw, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, ← e',
      Matrix.mulVec_add, Matrix.mulVec_smul, inv_mulVec, inv_mulVec]

end GlobalTheory.Dict.Pull

open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull in

theorem GlobalTheory.Dict.isStabForm_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ), IsUn X ga → (∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) → (∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) → HasPrinc X' M → ChiOne X' la' → X'.IsBddSec la' P → IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → DifferentiableOn ℂ (fun x => Q (lact ga (castFr h.psi x))) X'.dom ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x ∧ ∀ b ∈ Bor X'.Ψ r, Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * Q (lact ga (castFr h.psi x)) := by
  intro E _ _ _ r X' X h ga la' la Δ M P hga hl hΔ hP hχ hb
  obtain ⟨⟨hd, hbor, hinv⟩, C, hC⟩ := hb
  have m1 : ∀ x ∈ X.dom, castFr h.psi.symm (lact ga⁻¹ x) ∈ X'.dom := fun x hx =>
    cast_GG h.psi.symm h.gm.symm h.p0.symm (lact_mem (isUn_inv hga) hx)
  have m2 : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    lact_mem hga (cast_GG h.psi h.gm h.p0 hx)
  refine ⟨⟨?_, ?_, ?_, C, ?_⟩, fun Q hQ hQb => ⟨?_, fun x hx => ⟨m2 x hx, ?_, fun b hb => ?_⟩⟩⟩
  · exact hd.comp ((cast_diff h.psi.symm).comp (differentiable_lact ga⁻¹)).differentiableOn m1
  · intro x hx b hb
    rw [lact_rmul, cast_rmul, hbor _ (m1 x hx) _ (cast_bor h.psi.symm hb), ← cast_bchar h.psi hl]
    rfl
  · intro g hg hfix x hx
    have hm := conj_mem h.gm hga (hΔ g hg).1 hfix ((hΔ g hg).2 hfix) hP
    have e : lact ga⁻¹ (lact g x) = lact (ga⁻¹ * g * ga) (lact ga⁻¹ x) := by
      rw [lact_lact, lact_lact, mul_inv_cancel_right]
    show P (castFr h.psi.symm (lact ga⁻¹ (lact g x))) = _
    rw [e, cast_lact, hinv _ hm _ (m1 x hx), hχ _ hm, _root_.one_mul]
  · intro x hx
    refine le_of_eq_of_le ?_ (hC _ (m1 x hx))
    unfold Data.pnorm
    rw [cast_wt h.psi h.gm hl]
    simp only [dmin_lact (isUn_inv hga)]
  · exact hQ.comp ((differentiable_lact ga).comp (cast_diff h.psi)).differentiableOn m2
  · rw [lact_lact, inv_mul_cancel, lact_one, cast_symm]
  · rw [cast_rmul, lact_rmul, hQb _ (m2 x hx) _ (cast_bor h.psi hb), cast_bchar h.psi hl]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MaximalIsotropicDoubledGraphOrIsotropic
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblLag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in
theorem mem_botSpan (g : M2 E r) (v : Fin r ⊕ Fin r → E) :
    v ∈ botSpan g ↔ ∃ c : Fin r → E, Sum.elim 0 c ᵥ* g = v := by
  rw [botSpan, Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => Eq.congr_left ?_
  ext j
  simp [vecMul, dotProduct, Finset.sum_apply]

theorem pair_vecMul (A B : M2 E r) (u v : Fin r ⊕ Fin r → E) :
    ((u ᵥ* A) ᵥ* B) ⬝ᵥ (fun j => cc ((v ᵥ* A) j)) = (u ᵥ* (A * B * ccT A)) ⬝ᵥ fun j => cc (v j) := by
  have e : (fun j => cc ((v ᵥ* A) j)) = ccT A *ᵥ fun j => cc (v j) := by
    ext j
    simp only [vecMul, mulVec, dotProduct, cc, ccT, map_sum, map_mul, transpose_apply, map_apply,
      mul_comm]
  rw [e, dotProduct_mulVec, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc]

theorem iso_of_mem {g : M2 E r} (hg : g ∈ UU E r) {u v : Fin r ⊕ Fin r → E}
    (hu : u ∈ botSpan g) (hv : v ∈ botSpan g) :
    (u ᵥ* Matrix.J (Fin r) E) ⬝ᵥ (fun j => cc (v j)) = 0 := by
  obtain ⟨c, rfl⟩ := (mem_botSpan _ _).1 hu
  obtain ⟨d, rfl⟩ := (mem_botSpan _ _).1 hv
  have h : ccT (ccT g) * Matrix.J (Fin r) E * ccT g = Matrix.J (Fin r) E :=
    (HAct.group_part hg).2.2.1
  rw [HAct.ccT_ccT] at h
  rw [pair_vecMul, h, Matrix.J, vecMul_fromBlocks]
  simp [dotProduct, cc]

theorem finrank_botSpan {g : M2 E r} (hg : g ∈ UU E r) : Module.finrank E (botSpan g) = r := by
  have h : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (HAct.group_part hg).1
  have hl := (Matrix.linearIndependent_rows_iff_isUnit.2 h).comp _
    (Sum.inr_injective (α := Fin r) (β := Fin r))
  have := finrank_span_eq_card hl
  rw [Fintype.card_fin] at this
  exact this

variable (X : Data E r)

theorem isUnit_dblT : IsUnit (dblT X) :=
  IsUnit.of_mul_eq_one_right _ (DblPair.dblT_left X)

theorem pair_dblT (x y x' y' : Fin r → E) :
    ((Sum.elim x y ᵥ* dblT X) ᵥ* Matrix.J (Fin r) E) ⬝ᵥ (fun j => cc ((Sum.elim x' y' ᵥ* dblT X) j)) =
      X.κ0 / 2 * (herm X.Gm x x' - herm X.Gm y y') := by
  rw [pair_vecMul, DblPair.dblT_form, vecMul_fromBlocks]
  have e : ∀ x y : Fin r → E, herm X.Gm x y = ∑ b, (x ᵥ* X.Gm) b * cc (y b) := fun x y => by
    rw [herm, Finset.sum_comm]
    simp only [vecMul, dotProduct, Finset.sum_mul]
  simp [dotProduct, e, vecMul_neg, vecMul_smul, mul_add, Finset.mul_sum, mul_assoc, sub_eq_add_neg]

theorem mem_iota (γ : GL (Fin r) E) (x y : Fin r → E) :
    Sum.elim x y ᵥ* dblT X ∈ botSpan (iota X 1 γ) ↔ y = (γ⁻¹).1 *ᵥ x := by
  have hinj : Function.Injective fun v => v ᵥ* dblT X :=
    Matrix.vecMul_injective_iff_isUnit.2 (isUnit_dblT X)
  have hk : (2 * (X.κ0 / 4)) ≠ 0 := by simp [DblPair.kappa_ne X]
  have key : ∀ c : Fin r → E, Sum.elim 0 c ᵥ* iota X 1 γ =
      Sum.elim (c ᵥ* ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹))
        ((γ⁻¹).1 *ᵥ (c ᵥ* ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹))) ᵥ* dblT X := fun c => by
    rw [iota, Matrix.inv_eq_left_inv (DblPair.dblT_left X), ← vecMul_vecMul, ← vecMul_vecMul,
      vecMul_fromBlocks, vecMul_fromBlocks]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_vecMul, vecMul_zero, zero_add, add_zero,
      inv_one, Units.val_one, transpose_one, vecMul_one, vecMul_transpose]
  rw [mem_botSpan]
  constructor
  · rintro ⟨c, hc⟩
    rw [key] at hc
    have h := hinj hc
    have h1 := congrArg (· ∘ Sum.inl) h
    have h2 := congrArg (· ∘ Sum.inr) h
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h1 h2
    rw [← h2, h1]
  · rintro rfl
    refine ⟨x ᵥ* ((2 * (X.κ0 / 4)) • X.Gm), ?_⟩
    rw [key, vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hk,
      mul_nonsing_inv _ (Ne.isUnit X.Gm_det), one_smul, vecMul_one]

noncomputable def coord : ((Fin r → E) × (Fin r → E)) ≃ₗ[E] (Fin r ⊕ Fin r → E) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r) E E).symm.trans
    (LinearEquiv.ofBijective (dblT X).vecMulLinear
      ⟨Matrix.vecMul_injective_iff_isUnit.2 (isUnit_dblT X),
        Matrix.vecMul_surjective_iff_isUnit.2 (isUnit_dblT X)⟩)

theorem coord_apply (p : (Fin r → E) × (Fin r → E)) :
    coord X p = Sum.elim p.1 p.2 ᵥ* dblT X := rfl

end GlobalTheory.SW.DblLag

open GlobalTheory.SW.DblLag in

theorem GlobalTheory.SW.lag_graph_or_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ γ' : GL (Fin r) E, IsUn X γ → IsUn X γ' → botSpan (iota X 1 γ) = botSpan (iota X 1 γ') → γ = γ') ∧ ∀ U : Lag E r, (∃ γ : GL (Fin r) E, IsUn X γ ∧ botSpan (iota X 1 γ) = U.1) ∨ ∃ ξ : Fin r → E, ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0 ∧ Sum.elim ξ 0 ᵥ* dblT X ∈ U.1 := by
  intro E _ _ _ r X
  refine ⟨fun γ γ' _ _ h => ?_, ?_⟩
  · refine inv_injective (Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_)))
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mem_iota X, ← h, mem_iota]
  rintro ⟨U, g, hg, rfl⟩
  set I := (botSpan g).comap (coord X).toLinearMap with hI
  have hm : ∀ p, p ∈ I ↔ Sum.elim p.1 p.2 ᵥ* dblT X ∈ botSpan g := fun p => Iff.rfl
  have hiso : ∀ p ∈ I, ∀ q ∈ I, herm X.Gm p.1 q.1 - herm X.Gm p.2 q.2 = 0 := fun p hp q hq => by
    have := iso_of_mem hg ((hm p).1 hp) ((hm q).1 hq)
    rw [pair_dblT] at this
    exact (mul_eq_zero.1 this).resolve_left (by simp [DblPair.kappa_ne X])
  have hd : Module.finrank E I = r := by
    rw [hI, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, finrank_botSpan hg]
  obtain ⟨a1, -, -, -, -, -, a2, -⟩ :=
    (doubled_isotropic_structure X.Gm X.Gm_herm X.Gm_det).1 I hiso hd
  by_cases h0 : DoubledSpace.left I = ⊥
  · obtain ⟨δ, ⟨d1, d2⟩, -⟩ := a2.1 h0
    refine Or.inl ⟨δ⁻¹, fun x y => ?_, ?_⟩
    · rw [← d1, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
    · ext v
      obtain ⟨⟨x, y⟩, rfl⟩ := (coord X).surjective v
      rw [coord_apply, mem_iota, inv_inv, ← d2, hm]
  · obtain ⟨ξ, hξ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact Or.inr ⟨ξ, hne, a1 ξ hξ ξ hξ, (hm (ξ, 0)).1 hξ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemImageConjugate
section
open Matrix Complex NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Classical

namespace GlobalTheory.Ker.ConjDatum

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.conjugate_twice (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.gram_conjugate (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (ComplexEmbedding.conjugate τ) G (P.map (starRingEnd ℂ)) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G P).map (starRingEnd ℂ) := by
  ext a b
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.gram, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, ComplexEmbedding.conjugate_coe_eq, map_sum]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.Ker.ConjDatum.det_map_ne {M : Matrix (Fin r) (Fin r) ℂ} (h : M.det ≠ 0) :
    (M.map (starRingEnd ℂ)).det ≠ 0 := by
  have hdet : (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det := by
    rw [RingHom.map_det]
    rfl
  rw [hdet]
  exact (map_ne_zero _).2 h

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.mem_image_conjugate (Ψ : Finset (E →+* ℂ)) (τ : E →+* ℂ) :
    τ ∈ Ψ.image ComplexEmbedding.conjugate ↔ ComplexEmbedding.conjugate τ ∈ Ψ := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rwa [_root_.GlobalTheory.Ker.ConjDatum.conjugate_twice]
  · exact fun h => ⟨_, h, _root_.GlobalTheory.Ker.ConjDatum.conjugate_twice τ⟩

def cpl (Ψ : Finset (E →+* ℂ)) (τ : Ψ) : Ψ.image ComplexEmbedding.conjugate :=
  ⟨ComplexEmbedding.conjugate τ.1, Finset.mem_image_of_mem _ τ.2⟩

def cfr (Ψ : Finset (E →+* ℂ)) (x : Frame (Ψ.image ComplexEmbedding.conjugate) r) : Frame Ψ r :=
  fun τ a b => conj (x (cpl Ψ τ) a b)

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_mem_GG (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (p : ℕ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG _ G p) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ G p := by
  intro τ
  obtain ⟨hdet, hpos⟩ := hx (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)
  have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)).map (starRingEnd ℂ) := by
    ext a b
    rfl
  have hgram : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) G (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ) =
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.gram (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ : E →+* ℂ) G
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ))).map (starRingEnd ℂ) := by
    rw [hmat]
    have h := _root_.GlobalTheory.Ker.ConjDatum.gram_conjugate (ComplexEmbedding.conjugate (τ : E →+* ℂ)) G
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ))
    rw [_root_.GlobalTheory.Ker.ConjDatum.conjugate_twice] at h
    exact h
  refine ⟨?_, fun i => ?_⟩
  · rw [hmat]
    exact _root_.GlobalTheory.Ker.ConjDatum.det_map_ne hdet
  · have h := hpos i
    have hminor : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin G (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ i =
        starRingEnd ℂ (_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin G x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ) i) := by
      simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin, _root_.ReciprocityTheory.ChartRestriction.G.FD.lminor, hgram, ← Matrix.submatrix_map]
      rw [RingHom.map_det]
      rfl
    rw [hminor, Complex.conj_re]
    exact h

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_mem_Bor (Ψ : Finset (E →+* ℂ))
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r} (hx : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor _ r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  intro τ
  obtain ⟨hdet, htri⟩ := hx (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)
  refine ⟨?_, fun a c hca => ?_⟩
  · have hmat : _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) τ =
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (_root_.GlobalTheory.Ker.ConjDatum.cpl Ψ τ)).map (starRingEnd ℂ) := by
      ext a b
      rfl
    rw [hmat]
    exact _root_.GlobalTheory.Ker.ConjDatum.det_map_ne hdet
  · simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, htri a c hca]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_rmul (Ψ : Finset (E →+* ℂ))
    (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ b) := by
  funext τ a c
  simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.mul_apply, map_sum]

open Matrix Complex NumberField in
open scoped ComplexConjugate Classical in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.Ker.ConjDatum.cfr_lact (Ψ : Finset (E →+* ℂ)) (γ : GL (Fin r) E)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame (Ψ.image ComplexEmbedding.conjugate) r) :
    _root_.GlobalTheory.Ker.ConjDatum.cfr Ψ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.GlobalTheory.Ker.ConjDatum.cfr Ψ x) := by
  funext τ a c
  simp [_root_.GlobalTheory.Ker.ConjDatum.cfr, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.mul_apply, map_sum,
    _root_.GlobalTheory.Ker.ConjDatum.cpl, ComplexEmbedding.conjugate_coe_eq]

def conjData (X : Data E r) : Data E r where
  Ψ := X.Ψ.image ComplexEmbedding.conjugate
  cmType τ := by
    rw [mem_image_conjugate, mem_image_conjugate]
    exact X.cmType _
  Gm := X.Gm
  Gm_herm := X.Gm_herm
  Gm_det := X.Gm_det
  p0 := X.p0
  p0_le := X.p0_le
  signature τ := by
    obtain ⟨P, h1, h2⟩ := X.signature ⟨_, (mem_image_conjugate _ _).1 τ.2⟩
    refine ⟨P.map (starRingEnd ℂ), det_map_ne h1, ?_⟩
    have h4 := gram_conjugate (ComplexEmbedding.conjugate τ.1) X.Gm P
    rw [conjugate_twice] at h4
    rw [h4, h2]
    ext a b
    by_cases h : a = b <;> simp [Matrix.diagonal, h]
  Λ := X.Λ
  Λ_fg := X.Λ_fg
  Λ_span := X.Λ_span
  den := X.den
  den_ne := X.den_ne
  Λ_int := X.Λ_int
  Γ := X.Γ
  Γ_stab := X.Γ_stab
  Γ_index := X.Γ_index
  Γ_free γ hγ x hx b hb h := by
    refine X.Γ_free γ hγ _ (cfr_mem_GG _ _ _ hx) _ (cfr_mem_Bor _ hb) ?_
    rw [← cfr_lact, h, cfr_rmul]
  χ _ _ := 1
  χ_mul := by simp
  χ_add := by simp
  χ_fin _ := ⟨1, one_pos, by simp⟩
  ξ0 := X.ξ0
  ξ0_im := X.ξ0_im
  ξ0_ne := X.ξ0_ne
  κ0 := -X.κ0
  κ0_xi := by
    rcases X.κ0_xi with h | h
    · right; rw [h]
    · left; rw [h, neg_neg]
  κ0_sign τ := by
    have := X.κ0_sign ⟨_, (mem_image_conjugate _ _).1 τ.2⟩
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  m := X.m
  m_pos := X.m_pos
  transv ξ hξ h0 s hs hi := by
    obtain ⟨γ, h1, h2⟩ := X.transv ξ hξ h0 (-s) (by unfold cc at hs ⊢; rw [map_neg, hs]) hi.neg
    refine ⟨γ, h1, ?_⟩
    rw [h2]
    congr 1
    ring

end

end GlobalTheory.Ker.ConjDatum
end

