import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HarmonicRowHighestEqSpanIntegralHarmonic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem natCast_mul_X_mem_symO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (Λ : Lt E n) (N : ℕ)
    (hΛ : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ) (ℓ : LtN Dw n) :
    (N : MvPolynomial (LtN Dw n) c.F) * MvPolynomial.X ℓ ∈ Formalism.L2.Pj.symO c (⟨Λ⟩ : GenLat E n) := by
  obtain ⟨τ, i, j⟩ := ℓ
  refine Subring.subset_closure (Or.inr ⟨τ, i, Pi.single j (N : E), hΛ ?_, ?_⟩)
  · have h1 : (Pi.single j (1 : E) : Fin n → E) ∈ Formalism.L2.Pj.stdLat E n := by
      intro k _
      by_cases hk : k = j
      · subst hk
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hk]
        exact Submodule.zero_mem _
    have h2 := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1
    have h3 : (N : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = Pi.single j (N : E) := by
      rw [Nat.cast_smul_eq_nsmul, ← Pi.single_nsmul]
      simp
    rwa [h3] at h2
  · unfold letB
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp

theorem exists_natCast_mul_mem_symO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (Λ : Lt E n) (N : ℕ) (hN : 0 < N)
    (hΛ : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ) (P : MvPolynomial (LtN Dw n) c.F) :
    ∃ M : ℕ, 0 < M ∧ (M : MvPolynomial (LtN Dw n) c.F) * P ∈ Formalism.L2.Pj.symO c (⟨Λ⟩ : GenLat E n) := by
  haveI := c.fin
  induction P using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := c.F) {x}
    have h1 := h x (Finset.mem_singleton_self x)
    have h2 : MvPolynomial.C (y • x) ∈ Formalism.L2.Pj.symO (Dw := Dw) c (⟨Λ⟩ : GenLat E n) :=
      Subring.subset_closure (Or.inl ⟨⟨y • x, h1⟩, rfl⟩)
    refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
    have h3 : (((y * y).natAbs : ℕ) : MvPolynomial (LtN Dw n) c.F) = ((y * y : ℤ) : MvPolynomial (LtN Dw n) c.F) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
    have h4 := Subring.mul_mem _ (intCast_mem (Formalism.L2.Pj.symO (Dw := Dw) c (⟨Λ⟩ : GenLat E n)) y) h2
    rw [h3]
    convert h4 using 1
    rw [zsmul_eq_mul, map_mul, map_intCast]
    push_cast
    ring
  | add p q hp hq =>
    obtain ⟨M, hM, h⟩ := hp
    obtain ⟨M', hM', h'⟩ := hq
    refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
    have := Subring.add_mem _ (Subring.mul_mem _ (natCast_mem _ M') h) (Subring.mul_mem _ (natCast_mem _ M) h')
    convert this using 1
    push_cast
    ring
  | mul_X p ℓ hp =>
    obtain ⟨M, hM, h⟩ := hp
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have := Subring.mul_mem _ h (natCast_mul_X_mem_symO c Λ N hΛ ℓ)
    convert this using 1
    push_cast
    ring

theorem rowHighest_eq_sum_harmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g q0 n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c σ X g q0 n a) (Λ : Lt E n) (N : ℕ), 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∀ Q ∈ Harm.rowHighest ℂ Dc.k Dc.k', ∃ (m : ℕ) (t : Fin m → ℂ) (P : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, P i ∈ harmL c (⟨Λ⟩ : GenLat E n) a) ∧ Q = ∑ i, t i • MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P i)) := by
  intro E _ _ _ H Dw l c σ r g q0 n X a Dc Λ N hN hΛ Q hQ
  obtain ⟨m, t, v, hv⟩ := Submodule.mem_span_set'.1 (Dc.span hQ)
  have hP : ∀ i, ∃ P : MvPolynomial (LtN Dw n) c.F,
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧
      MvPolynomial.rename Dc.eL (MvPolynomial.map σ P) = (v i).1 := fun i => (v i).2
  choose P hP hPv using hP
  choose M hM hMP using fun i => exists_natCast_mul_mem_symO c Λ N hN hΛ (P i)
  refine ⟨m, fun i => t i / (M i : ℂ), fun i => (M i : MvPolynomial (LtN Dw n) c.F) * P i,
    fun i => ⟨?_, hMP i⟩, ?_⟩
  · have e : (M i : MvPolynomial (LtN Dw n) c.F) * P i = (M i : c.F) • P i := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    change (M i : MvPolynomial (LtN Dw n) c.F) * P i ∈ _
    rw [e]
    exact ⟨Submodule.smul_mem _ _ (hP i).1,
      fun s k k' h u => by rw [map_smul, (hP i).2.1 s k k' h u],
      fun mm hm => (hP i).2.2 mm (MvPolynomial.support_smul hm)⟩
  · rw [← hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : (M i : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hM i).ne'
    rw [map_mul, map_mul, map_natCast, map_natCast, hPv, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      div_mul_cancel₀ _ h0]

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianFormAtFrameLaws
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem form_eq_zero_of_im {V : Type} [AddCommGroup V] [Module ℂ V] (f : V → V → ℂ)
    (h1 : ∀ w, IsLinearMap ℂ (fun z => f z w)) (h2 : ∀ z, IsLinearMap ℝ (f z)) (S : Set V)
    (hS : Submodule.span ℝ S = ⊤) (h : ∀ u ∈ S, ∀ v ∈ S, (f u v).im = 0) (z w : V) : f z w = 0 := by
  have key : ∀ z w, (f z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem u hu =>
      induction hw using Submodule.span_induction with
      | mem v hv => exact h u hu v hv
      | zero => rw [(h2 u).map_zero, zero_im]
      | add a b _ _ ha hb => rw [(h2 u).map_add, add_im, ha, hb, add_zero]
      | smul t a _ ha => rw [(h2 u).map_smul, smul_im, ha, smul_zero]
    | zero => rw [(h1 w).map_zero, zero_im]
    | add a b _ _ ha hb => rw [(h1 w).map_add, add_im, ha, hb, add_zero]
    | smul t a _ ha =>
      rw [← Complex.coe_smul, (h1 w).map_smul, smul_eq_mul, im_ofReal_mul, ha, mul_zero]
  have h3 := key (I • z) w
  rw [(h1 w).map_smul, smul_eq_mul, I_mul_im] at h3
  exact Complex.ext h3 (key z w)

theorem hermForm_eq_of_im {g : ℕ} (M M' : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ u ∈ S, ∀ v ∈ S, (hermForm M (a * u) v).im = (hermForm M' u (b * v)).im) (z w : Fin g → ℂ) :
    hermForm M (a * z) w = hermForm M' z (b * w) := by
  refine sub_eq_zero.1 (form_eq_zero_of_im (fun z w => hermForm M (a * z) w - hermForm M' z (b * w))
    (fun w => ⟨fun u v => ?_, fun c u => ?_⟩) (fun z => ⟨fun u v => ?_, fun c u => ?_⟩) S hS
    (fun u hu v hv => by rw [sub_im, h u hu v hv, sub_self]) z w)
  · simp only [hermForm, mul_add, add_dotProduct]; ring
  · simp only [hermForm, mul_smul_comm, smul_dotProduct, smul_eq_mul]; ring
  · simp only [hermForm, mul_add, star_add, mulVec_add, dotProduct_add]; ring
  · simp only [hermForm, mul_smul_comm, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_sub]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

theorem hx_eq_hermForm (x : Frame X.Ψ r) (z w : Fin g → ℂ) :
    hx X bas idx x z w = hermForm (ThFr.Hm X bas idx x) z w := (hermForm_Hm bas idx x z w).symm

theorem span_range_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Submodule.span ℝ (Set.range (pv X idx x)) = ⊤ := by
  have col (s : Fin g → Fin g ⊕ Fin g) (t : Fin g → ℝ) :
      perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) ∈ Submodule.span ℝ (Set.range (pv X idx x)) := by
    have : perMat X bas idx s x *ᵥ (fun k => (t k : ℂ)) =
        ∑ k, t k • pv X idx x (bas (Pi.single (s k) 1)) := by
      funext i
      simp [mulVec, dotProduct, pv, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  refine eq_top_iff.2 fun z _ => ?_
  have hu := isUnit_det_perMat idx hs hx
  have hY := (tauMat_im_posDef idx hs hx).det_pos.ne'.isUnit
  set τ := tauMat X bas idx x with hτ
  set y := hMat X bas idx x *ᵥ z with hy
  obtain ⟨t, ht⟩ : ∃ t : Fin g → ℝ, τ.map Complex.im *ᵥ t = fun k => (y k).im :=
    ⟨(τ.map Complex.im)⁻¹ *ᵥ _, by rw [mulVec_mulVec, mul_nonsing_inv _ hY, one_mulVec]⟩
  have h1 : y = (fun k => (((y - τ *ᵥ fun k => (t k : ℂ)) k).re : ℂ)) + τ *ᵥ fun k => (t k : ℂ) := by
    funext k
    apply Complex.ext
    · simp
    · have := congrFun ht k
      simp only [mulVec, dotProduct, map_apply] at this
      simp [mulVec, dotProduct, this]
  have hAB : perMat X bas idx Sum.inl x * τ = perMat X bas idx Sum.inr x :=
    mul_nonsing_inv_cancel_left _ _ hu
  have h2 : z = perMat X bas idx Sum.inl x *ᵥ y := by
    rw [hy, mulVec_mulVec, hMat, mul_nonsing_inv _ hu, one_mulVec]
  rw [h2, h1, mulVec_add, mulVec_mulVec, hAB]
  exact add_mem (col _ _) (col _ _)

theorem span_image_pv (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (L : Lt E r)
    (hL : Submodule.span E (L : Set (Fin r → E)) = ⊤) :
    Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ := by
  rw [eq_top_iff, ← span_range_pv idx hs hx, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  obtain ⟨k, hk, hv⟩ := GlobalTheory.LatFin.exists_int_smul_mem L hL v
  have : pv X idx x v = (k : ℝ)⁻¹ • pv X idx x (k • v) := by
    funext i
    have hk' : (k : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
    rw [pv, pv, per_zsmul]
    simp only [Function.comp_apply, Pi.smul_apply, zsmul_eq_mul, real_smul, ofReal_inv, Pi.mul_apply, Pi.intCast_apply,
      ofReal_intCast]
    rw [inv_mul_cancel_left₀ hk']
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hv, rfl⟩)

theorem pv_smul (x : Frame X.Ψ r) (a : E) (v : Fin r → E) :
    pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j :=
  funext fun _ => per_smul X x a v _

theorem EF_smul_left (a : E) (u v : Fin r → E) : EF X (a • u) v = EF X u (cc a • v) := by
  have h (b : E) : IsCMField.complexConj E (IsCMField.complexConj E a * b) = a * IsCMField.complexConj E b := by
    rw [map_mul, IsCMField.complexConj_apply_apply]
  simp only [EF_def, herm, cc, Pi.smul_apply, smul_eq_mul, h]
  congr 2
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hx_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x ∈ X.dom, (∀ z w, hx X bas idx x w z = conj (hx X bas idx x z w)) ∧ (∀ z, z ≠ 0 → 0 < (hx X bas idx x z z).re) ∧ (∀ u v, (hx X bas idx x (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) ∧ (∀ (a : E) z w, hx X bas idx x (fun j => rowType X (idx j) a * z j) w = hx X bas idx x z (fun j => rowType X (idx j) (cc a) * w j)) ∧ (∀ (a : E) v, pv X idx x (a • v) = fun j => rowType X (idx j) a * pv X idx x v j) ∧ Function.Injective (pv X idx x) ∧ (∀ L : Lt E r, Submodule.span E (L : Set (Fin r → E)) = ⊤ → Submodule.span ℝ (pv X idx x '' (L : Set (Fin r → E))) = ⊤ ∧ ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ u ∈ L, ∀ v ∈ L, (hermForm Hm (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ)) → ∀ z w, hermForm Hm z w = hx X bas idx x z w) ∧ ∀ ga : GL (Fin r) E, IsUn X ga → lact ga x ∈ X.dom ∧ (∀ v, pv X idx (lact ga x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v) = pv X idx x v) ∧ (IsUnitFr X x → IsUnitFr X (lact ga x)) ∧ ∀ z w, hx X bas idx (lact ga x) z w = hx X bas idx x z w := by
  intro E _ _ _ r X g bas idx n hs _ x hx
  have him {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v) :
      (hermForm (ThFr.Hm X bas idx x) (pv X idx x u) (pv X idx x v)).im = (EF X u v : ℝ) :=
    im_hermForm_Hm idx hs hx u v
  simp only [hx_eq_hermForm]
  refine ⟨fun z w => ?_, fun z hz => hermForm_Hm_pos idx hs hx hz, him hx, fun a z w => ?_,
    pv_smul idx x, fun u v h => ?_, fun L hL => ⟨span_image_pv idx hs hx L hL, fun M _ h z w => ?_⟩,
    fun ga hga => ⟨hga.lact_mem hx, fun v => ?_, fun h τ i => ?_, fun z w => ?_⟩⟩
  · have hH := Hm_isHermitian idx hs hx
    rw [hermForm, hermForm, ← RCLike.star_def, ← star_dotProduct_star, star_mulVec, star_star, hH.eq,
      dotProduct_mulVec]
  · refine hermForm_eq_of_im _ _ (fun j => rowType X (idx j) a) (fun j => rowType X (idx j) (cc a)) _
      (span_range_pv idx hs hx) ?_ z w
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have h1 := him hx (a • u) v
    have h2 := him hx u (cc a • v)
    rw [pv_smul] at h1 h2
    rw [EF_smul_left] at h1
    exact h1.trans h2.symm
  · obtain ⟨m, rfl⟩ := vecQ_surjective X bas u
    obtain ⟨m', rfl⟩ := vecQ_surjective X bas v
    have h' (t) : EF X (vecQ X bas m) (vecQ X bas t) = EF X (vecQ X bas m') (vecQ X bas t) := by
      have := (him hx (vecQ X bas m) (vecQ X bas t)).symm.trans (h ▸ him hx (vecQ X bas m') (vecQ X bas t))
      exact_mod_cast this
    simp only [EF_vecQ hs] at h'
    congr 1
    funext j
    rcases j with j | j
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
    · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)
  · have := hermForm_eq_of_im M (ThFr.Hm X bas idx x) 1 1 _ (span_image_pv idx hs hx L hL) (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [_root_.one_mul, _root_.one_mul, h u hu v hv, him hx]) z w
    rwa [_root_.one_mul, _root_.one_mul] at this
  · rw [pv, per_lact x hga, pv]
  · have e1 : mat (lact ga x) τ = (ga : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have e2 : FD.gram τ.1 X.Gm (mat (lact ga x) τ) = FD.gram τ.1 X.Gm (mat x τ) := by
      ext a b
      simp only [FD.gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hga]
    have h' := h τ i
    unfold dmin at h' ⊢
    rwa [e2]
  · have := hermForm_eq_of_im (ThFr.Hm X bas idx (lact ga x)) (ThFr.Hm X bas idx x) 1 1 _
      (span_range_pv idx hs hx) (by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      have h1 := him (hga.lact_mem hx) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ u) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ v)
      rw [pv, pv, per_lact x hga, per_lact x hga, EF_def, hga, ← EF_def] at h1
      rw [_root_.one_mul, _root_.one_mul, him hx]
      exact h1) z w
    rwa [_root_.one_mul, _root_.one_mul] at this

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

section DoubleCoset
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in

theorem _root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen (Γ K : Subgroup G) (hK : IsOpen (K : Set G)) (a : G) :
    IsOpen {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} := by
  have hunion : {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} =
      ⋃ γ ∈ Γ, (fun k => γ * a * k) '' (K : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
  rw [hunion]
  exact isOpen_biUnion fun γ _ => isOpenMap_mul_left (γ * a) _ hK

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem _root_.GlobalTheory.Ker.tsum_indicator_coset (Γ K : Subgroup G) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (x : G) :
    ∑' γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x)
      = ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) *
        {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}.indicator 1 x := by
  by_cases hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨γ₀, hγ₀, k₀, hk₀, rfl⟩ := hx
    set T : Set Γ := {γ | a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K} with hT
    have hterm : ∀ γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)
        (γ • (γ₀ * a * k₀)) = T.indicator (1 : Γ → ENNReal) γ := by
      intro γ
      by_cases hγ : γ ∈ T
      · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem]
        · rfl
        · exact hγ
      · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem]
        exact hγ
    simp_rw [hterm]
    rw [← tsum_subtype T (1 : Γ → ENNReal)]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hinj : Function.Injective (fun γ : Γ => (γ : G) * γ₀) :=
      fun γ δ hγδ => Subtype.ext (mul_right_cancel hγδ)
    have himg : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K} = (fun γ : Γ => (γ : G) * γ₀) '' T := by
      ext δ
      constructor
      · rintro ⟨hδ, hδK⟩
        refine ⟨⟨δ * γ₀⁻¹, Γ.mul_mem hδ (Γ.inv_mem hγ₀)⟩, ?_, by simp⟩
        show a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) ∈ K
        have heq : a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) = a⁻¹ * δ * a * k₀ := by group
        rw [heq]
        exact K.mul_mem hδK hk₀
      · rintro ⟨γ, hγ, rfl⟩
        refine ⟨Γ.mul_mem γ.2 hγ₀, ?_⟩
        have hγ' : a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K := hγ
        have heq : a⁻¹ * ((γ : G) * γ₀) * a = a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) * k₀⁻¹ := by group
        rw [heq]
        exact K.mul_mem hγ' (K.inv_mem hk₀)
    rw [← hinj.encard_image, ← himg, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    refine ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem ?_ _
    intro hmem
    have hk : a⁻¹ * ((γ : G) * x) ∈ K := hmem
    exact hx ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hk, by group⟩

variable [MeasurableSpace G] [BorelSpace G]

end DoubleCoset

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem measure_fd_inter_doubleCoset_mul_ncard_eq {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (D : Set G)
    (hD : IsFundamentalDomain Γ D ν) (hK : IsOpen (K : Set G)) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) :
    ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} ∩ D) *
      ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) = ν K := by
  have hC : MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} :=
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet
  have hmeasK : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)) :=
    hK.measurableSet.preimage (measurable_const_mul _)
  have hwhole : ∫⁻ x, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator 1 x ∂ν = ν K := by
    rw [lintegral_indicator_one hmeasK, measure_preimage_mul]
  have hinv := (Equiv.inv Γ).tsum_eq (fun γ : Γ =>
    ∫⁻ x in D, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ⁻¹ • x) ∂ν)
  simp only [Equiv.inv_apply, inv_inv] at hinv
  rw [← hwhole, hD.lintegral_eq_tsum', ← hinv, ← lintegral_tsum]
  · simp_rw [_root_.GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin]
    rw [lintegral_const_mul _ (measurable_one.indicator hC), lintegral_indicator_one hC,
      Measure.restrict_apply hC, mul_comm]
  · intro γ
    exact ((measurable_one.indicator hmeasK).comp (measurable_const_smul γ)).aemeasurable

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in

theorem _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (K : Set G) → ν K ≠ ⊤ → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) → ∀ F : G → ℂ, (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) → ν 𝓖 ≠ ⊤ ∧ IntegrableOn F 𝓖 ν ∧ ∫ x in 𝓖, F x ∂ν = ((ν K).toReal : ℂ) * ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * F (h i) := by
  intro G _ _ _ _ _ ν _ Γ K _ 𝓖 h𝓖 hK hKtop ι _ h huniq hfin F hFΓ hFK
  have hCmeas : ∀ i, MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} := fun i =>
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK (h i)).measurableSet
  have hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard ≠ 0 := fun i =>
    ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simpa using K.one_mem⟩).ne'
  have hCG : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) =
      ν K / ({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ENNReal) := by
    intro i
    rw [ENNReal.eq_div_iff (by exact_mod_cast hpos i) (ENNReal.natCast_ne_top _), mul_comm]
    exact measure_fd_inter_doubleCoset_mul_ncard_eq ν Γ K 𝓖 h𝓖 hK (h i) (hfin i)
  have hCGtop : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) ≠ ⊤ := by
    intro i
    rw [hCG i]
    exact (ENNReal.div_lt_top hKtop (by exact_mod_cast hpos i)).ne
  have h𝓖top : ν 𝓖 ≠ ⊤ := by
    have hsub : 𝓖 ⊆ ⋃ i, ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) := fun x hx =>
      Set.mem_iUnion.2 ⟨(huniq x).exists.choose, (huniq x).exists.choose_spec, hx⟩
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (measure_iUnion_fintype_le _ _))
    exact ENNReal.sum_ne_top.2 fun i _ => hCGtop i
  have hdecomp : ∀ x, F x =
      ∑ i, {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i)) x := by
    intro x
    obtain ⟨i, hi, hiuniq⟩ := huniq x
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} from hi)]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hi
      rw [hFK k hk, hFΓ γ hγ]
    · intro j _ hj
      exact Set.indicator_of_notMem
        (show x ∉ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h j * k} from fun hx => hj (hiuniq j hx)) _
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  have hint : ∀ i, IntegrableOn
      ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i))) 𝓖 ν := by
    intro i
    refine (integrable_indicator_iff (hCmeas i)).2 ?_
    refine integrableOn_const ?_
    rw [Measure.restrict_apply (hCmeas i)]
    exact hCGtop i
  refine ⟨h𝓖top, ?_, ?_⟩
  · exact (integrable_finset_sum _ fun i _ => hint i).congr
      (ae_of_all _ fun x => (hdecomp x).symm)
  · refine (congrArg (fun f : G → ℂ => ∫ x in 𝓖, f x ∂ν) (funext hdecomp)).trans ?_
    rw [integral_finset_sum _ fun i _ => hint i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (hCmeas i), measureReal_def, Measure.restrict_apply (hCmeas i),
      hCG i, ENNReal.toReal_div, ENNReal.toReal_natCast, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivLetterPushforwardEqColumnAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

open GlobalTheory.Dict.ColPoly in

theorem GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  intro E _ _ _ H Dw l c s r g X idx e q0 n hr eL hdir htype h P F hF
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := hF.contDiff
  let a : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ := fun v k =>
    s (Formalism.L2.Pj.embF c (eL.symm v).1 (h k (eL.symm v).2.2))
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) := fun v k =>
    eL ⟨(eL.symm v).1, (eL.symm v).2.1, k⟩
  let Φ : MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ :=
    MvPolynomial.aeval fun v => ∑ k, MvPolynomial.C (a v k) * MvPolynomial.X (j v k)
  have ha : ∀ v k, a (eL v) k = s (Formalism.L2.Pj.embF c v.1 (h k v.2.2)) := fun v k => by
    simp only [a]; rw [Equiv.symm_apply_apply]
  have hj : ∀ v k, j (eL v) k = eL ⟨v.1, v.2.1, k⟩ := fun v k => by
    simp only [j]; rw [Equiv.symm_apply_apply]
  have hΦ : ∀ Q : MvPolynomial (LtN Dw n) c.F,
      MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h Q)) =
        Φ (MvPolynomial.rename eL (MvPolynomial.map s Q)) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P v hP =>
      simp only [map_mul, hP]
      congr 1
      simp [pushLet, letB, Φ, ha, hj]
  rw [hΦ, ColPoly.polyDeriv_subst hF' a j Φ (fun v => by simp [Φ])]
  refine Eq.symm ((polyDeriv_comp_linear hF' (hActL X idx h) _ _ 0).trans ?_)
  rw [map_zero]
  congr 1
  funext v k i
  obtain ⟨⟨τ, ρ, b⟩, rfl⟩ := eL.surjective v
  change Dict.hAct X idx h _ k i = _
  simp only [Dict.hAct, ha, hj, hdir, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b (fun l _ hl => by simp [hl]) (by simp),
    Finset.sum_eq_single k (fun l _ hl => by simp [hl.symm]) (by simp)]
  by_cases hi : i = e.symm ⟨τ, ρ⟩
  · subst hi
    simp only [htype, Equiv.apply_symm_apply, Pi.single_eq_same]
    rfl
  · simp [hi]
end

