import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0045
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HmEqDiagonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HermDiag

private theorem hermForm_eq_star_swap {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsHermitian)
    (z w : Fin g → ℂ) : hermForm A z w = star (hermForm A w z) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hA.apply j i]
  ring

private theorem eq_of_im_hermForm_eq_of_real_span_eq_univ {g : ℕ} {La : Type} [AddCommGroup La] (A B : Matrix (Fin g) (Fin g) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (P : La →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (h : ∀ a b, (hermForm A (P a) (P b)).im = (hermForm B (P a) (P b)).im) : A = B := by
  let L : (Fin g → ℂ) → (Fin g → ℂ) →ₗ[ℝ] ℝ := fun w =>
    { toFun := fun z => (hermForm A z w).im - (hermForm B z w).im
      map_add' := fun z z' => by
        simp only [hermForm, add_dotProduct, Complex.add_im]; ring
      map_smul' := fun t z => by
        simp only [hermForm, smul_dotProduct, Complex.smul_im, RingHom.id_apply, smul_eq_mul]; ring }
  have hL : ∀ w z, L w z = (hermForm A z w).im - (hermForm B z w).im := fun _ _ => rfl
  have zero_of : ∀ w, (∀ a, L w (P a) = 0) → ∀ z, L w z = 0 := by
    intro w hw z
    have h0 : L w = 0 := LinearMap.ext_on hP (fun y hy => by
      obtain ⟨a, rfl⟩ := hy
      simpa using hw a)
    rw [h0]; rfl
  have key1 : ∀ a z, L (P a) z = 0 := fun a => zero_of _ (fun b => by rw [hL, h b a, sub_self])
  have key2 : ∀ z w, L w z = 0 := by
    intro z w
    refine zero_of w (fun a => ?_) z
    have h1 := key1 a w
    rw [hL] at h1 ⊢
    rw [hermForm_eq_star_swap A hA (P a) w, hermForm_eq_star_swap B hB (P a) w]
    simp only [Complex.star_def, Complex.conj_im]
    linarith
  ext i j
  apply Complex.ext
  · have h1 := key2 (Pi.single i Complex.I) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith
  · have h1 := key2 (Pi.single i 1) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith

theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), GoodEmb c σ → IsUnf U → (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu hg hU ho
  obtain ⟨hr, htype, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := htype k
  have hbij : Function.Bijective (relab c σ) := by
    rw [← Finite.injective_iff_bijective]
    intro τ₁ τ₂ h12
    ext y
    have h1 : σ (Formalism.L2.Pj.embF c τ₁ y) = σ (Formalism.L2.Pj.embF c τ₂ y) :=
      congrArg (fun f : E →+* ℂ => f y) h12
    exact congrArg Subtype.val (σ.injective h1)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq
      simpa using this
    have h2 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, h1, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  have hkey : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
    intro τ
    have hg' : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hg
    have hρ : ((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
    rcases hsq τ with h | h
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (h.trans hρ.symm)
      have h3 : relab c σ τ (H.rt : E) = H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = H.rt0
        rw [e, hg']
      rw [h3, h]
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = -IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (by
          show τ (H.rt : E) = -((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ)
          rw [h, hρ])
      have h3 : relab c σ τ (H.rt : E) = -H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = -H.rt0
        rw [e, map_neg, hg']
      rw [h3, h]
  have hpm : ∀ τ, relab c σ τ ∈ (U.X k).Ψ → Dw.mult τ = Dw.p := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_pos hτ]
  have hqm : ∀ τ, relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = Dw.q := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_neg hτ]
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hr
    (relab c σ) hbij Dw.mult hpm hqm
  set idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans f with hidx
  have hz : ∀ a j, W.Pm a j = if ((idx j).2 : ℕ) < Dw.q then
      FD.hermC (idx j).1.1 (U.X k).Gm (FD.col (FD.mat x.1 (idx j).1) (idx j).2)
        (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))
      else ((FD.mat x.1 (idx j).1)⁻¹.mulVec (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))) (idx j).2 := by
    intro a j
    rw [W.pm_eq a j]
    unfold Formalism.L2.Pj.perFr
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨hin, h1, h2⟩ | ⟨hout, h1, h2, h3⟩
    · have hi : (U.X k).p0 + ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dif_pos hin, dif_pos hi, if_neg (by omega)]
      have e1 : (f (W.e j)).1 = ⟨relab c σ (W.e j).1, hin⟩ := Subtype.ext h1
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 + ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 + ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
    · have hcj : conjEmb (relab c σ (W.e j).1) = (f (W.e j)).1.1 := by
        rw [h1]
        exact RingHom.ext fun y => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      have hin' : conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ := by
        rw [hcj]
        exact (f (W.e j)).1.2
      have hi : (U.X k).p0 - 1 - ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dif_neg hout, dif_pos hin', dif_pos hi, if_pos (by omega)]
      have e1 : (f (W.e j)).1 = ⟨conjEmb (relab c σ (W.e j).1), hin'⟩ := Subtype.ext hcj.symm
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 - 1 - ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 - 1 - ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have hx : ∀ τ : (U.X k).Ψ, FD.gram τ.1 (U.X k).Gm (FD.mat x.1 τ) =
      Matrix.diagonal fun a : Fin r => ((FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ) := by
    intro τ
    rw [← hp0]
    exact ho τ
  set D0 : Matrix (Fin W.g) (Fin W.g) ℂ :=
    Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) with hD0
  have hD : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im = (hermForm D0 (W.Pm a) (W.Pm b)).im := by
    intro a b
    rw [Wu.c1 a b, hD0, GlobalTheory.OrthoHerm.im_diag_eq_trace Dw.q (-(U.X k).ξ0) (U.X k).Gm (U.X k).Ψ
      (U.X k).cmType idx hcc x.1 hx (W.φ k a : Fin r → E) (W.φ k b : Fin r → E) (W.Pm a) (W.Pm b)
      (hz a) (hz b), ← W.isom k a b]
    push_cast
    rfl
  have hD0h : D0.IsHermitian := by
    rw [hD0]
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext j
    simp
  obtain ⟨-, -, -, hspan, -⟩ := W.per
  have hHm : Wu.Hm = D0 := eq_of_im_hermForm_eq_of_real_span_eq_univ Wu.Hm D0 Wu.herm hD0h W.Pm hspan hD
  rw [hHm, hD0]
  congr 1
  funext j
  have hpos := Wu.pos (Pi.single j 1) (by simp)
  rw [hHm, hD0] at hpos
  have hdiag : (hermForm (Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ))
      (Pi.single j 1) (Pi.single j 1)).re = 2 * ((idx j).1.1 (-(U.X k).ξ0)).im := by
    simp [hermForm]
  rw [hdiag, map_neg, Complex.neg_im] at hpos
  have hre : ((idx j).1.1 (U.X k).ξ0).re = 0 := by
    have h1 : starRingEnd ℂ ((idx j).1.1 (U.X k).ξ0) = -((idx j).1.1 (U.X k).ξ0) := by
      rw [← NumberField.IsCMField.complexEmbedding_complexConj (φ := (idx j).1.1) (x := (U.X k).ξ0),
        ← map_neg]
      congr 1
      exact (U.X k).ξ0_im
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hnorm : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖(idx j).1.1 (U.X k).ξ0‖ := by
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨-, h1, -⟩ | ⟨-, h1, -, -⟩
    · rw [h1]
    · rw [h1, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  have hfin : ((idx j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    rw [hnorm, ← (Complex.abs_im_eq_norm).mpr hre, map_neg, Complex.neg_im,
      abs_of_neg (by linarith)]
  rw [hfin]

end GlobalTheory.HermDiag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRepsLevelTranslates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ}

theorem levReps_act_mul (a b : 𝓞 E) (v : I2.Vsp dim) : I2.act a (I2.act b v) = I2.act (a * b) v := by
  ext i
  simp only [I2.act, RingOfIntegers.coe_eq_algebraMap, map_mul]
  exact (mul_assoc _ _ _).symm

theorem levReps_act_nat (m : ℕ) (v : I2.Vsp dim) : I2.act (m : 𝓞 E) v = (m : ℂ) • v := by
  ext i
  simp [I2.act]

theorem levReps_act_smul (a : 𝓞 E) (c : ℂ) (v : I2.Vsp dim) : I2.act a (c • v) = c • I2.act a v := by
  ext i
  simp [I2.act]
  ring

theorem levReps_act_add (a : 𝓞 E) (v w : I2.Vsp dim) : I2.act a (v + w) = I2.act a v + I2.act a w := by
  ext i
  simp [I2.act, mul_add]

theorem levReps_act_neg (a : 𝓞 E) (v : I2.Vsp dim) : I2.act a (-v) = -I2.act a v := by
  ext i
  simp [I2.act]

end

theorem isReps_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (T : I2.PT E) (mk : Dw.La →+ I2.Vsp T.dim) (α : 𝓞 E), α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → (∀ a, mk a ∈ T.L) → (∀ (β : 𝓞 E) a, mk (β • a) = I2.act β (mk a)) → (∀ a, (∃ v ∈ T.L, mk a = (l.M : ℂ) • v) → ∃ b, a = l.M • b) → (∀ v ∈ T.L, ∃ a, ∃ v' ∈ T.L, v = mk a + (l.M : ℂ) • v') → ∀ x2 : LevQ Dw l → Dw.La, (∀ q, x2 q ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ q, x2 q - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ n : ℕ, ∃ K : Finset (Fin n → I2.Vsp T.dim), I2.IsReps T l.M n (vspActL α) K ∧ ∀ b ∈ K, ∃ q : Fin n → LevQ Dw l, b = fun i => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 (q i)))) := by
  intro E _ _ _ H Dw l T mk α hα hMb hL hlin hinj hsurj x2 hx2 hrep n
  classical
  haveI : Finite (LevQ Dw l) := (card_levQ E H Dw l).1
  haveI : Fintype (LevQ Dw l) := Fintype.ofFinite _
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hbb : H.bar (H.bar α) = α := by
    apply Subtype.ext
    change ((H.bar (H.bar α) : 𝓞 E) : E) = (α : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have hmap : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {α} := by
    rw [hMb, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) hbb
  have hsm : ∀ (c : 𝓞 E) (y : Dw.La), y ∈ Ideal.span {c} • (⊤ : Submodule (𝓞 E) Dw.La) ↔ ∃ z, y = c • z := by
    intro c y
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨z, _, h⟩ => ⟨z, h.symm⟩, fun ⟨z, h⟩ => ⟨z, trivial, h.symm⟩⟩
  have hu : ∀ q, ∃ u : Dw.La, x2 q = α • α • u := by
    intro q
    have h := hx2 q
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, hsm] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨(2 : 𝓞 E) • z, ?_⟩
    rw [hz, smul_smul, smul_smul]
    congr 1
    ring
  have hcls : ∀ q, (Submodule.Quotient.mk (x2 q) : LevQ Dw l) = q := by
    intro q
    rw [(Submodule.Quotient.eq _).2 (hrep q)]
    exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  obtain ⟨r, s, hrs⟩ : ∃ r s : 𝓞 E, r * H.bar α + s * α = 1 := by
    have h := l.coprime
    rw [hmap, hMb, Ideal.eq_top_iff_one, ← Ideal.span_insert, Ideal.mem_span_pair] at h
    exact h
  set t : LevQ Dw l → I2.Vsp T.dim := fun q => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 q))) with ht
  have hαt : ∀ q, I2.act α (t q) = -((l.M : ℂ)⁻¹ • mk (x2 q)) := by
    intro q
    simp only [ht]
    rw [levReps_act_mul, hα, levReps_act_nat, smul_neg, smul_smul]
    congr 2
    field_simp
  have hMt : ∀ q, (l.M : ℂ) • t q ∈ T.L := by
    intro q
    obtain ⟨u, hq⟩ := hu q
    have : (l.M : ℂ) • t q = -mk (α • u) := by
      simp only [ht]
      rw [hq, hlin α (α • u), levReps_act_neg, levReps_act_smul, levReps_act_mul, mul_comm (H.bar α), hα,
        levReps_act_nat, smul_neg, smul_smul, smul_smul]
      have : (l.M : ℂ) * ((l.M : ℂ) ^ 2)⁻¹ * l.M = 1 := by field_simp
      rw [this, one_smul]
    rw [this]
    exact T.L.neg_mem (hL _)
  have hsub : ∀ (b : I2.Vsp T.dim) q, vspActL α (b - t q) = I2.act α b + (l.M : ℂ)⁻¹ • mk (x2 q) := by
    intro b q
    rw [map_sub]
    change I2.act α b - I2.act α (t q) = _
    rw [hαt, sub_neg_eq_add]
  have hex : ∀ b : I2.Vsp T.dim, (l.M : ℂ) • b ∈ T.L → ∃ q, vspActL α (b - t q) ∈ T.L := by
    intro b hb
    obtain ⟨a, v', hv', hab⟩ := hsurj _ hb
    refine ⟨Submodule.Quotient.mk (-(α • a)), ?_⟩
    set q : LevQ Dw l := Submodule.Quotient.mk (-(α • a)) with hq
    have h1 : x2 q - -(α • a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 ((hcls q).trans hq)
    rw [hMb, hsm] at h1
    obtain ⟨d, hd⟩ := h1
    obtain ⟨u, hqu⟩ := hu q
    have h2 : x2 q + α • a = (l.M : 𝓞 E) • (r • (α • u + a) + s • d) := by
      have e1 : x2 q + α • a = α • (α • u + a) := by rw [hqu, smul_add]
      have e2 : x2 q + α • a = H.bar α • d := by rw [← hd, sub_neg_eq_add]
      calc x2 q + α • a = (r * H.bar α + s * α) • (x2 q + α • a) := by rw [hrs, one_smul]
        _ = (r * H.bar α) • α • (α • u + a) + (s * α) • H.bar α • d := by rw [add_smul, ← e1, ← e2]
        _ = _ := by
          rw [← hα, smul_add (α * H.bar α)]
          simp only [smul_smul (r * H.bar α), smul_smul (s * α), smul_smul (α * H.bar α)]
          congr 2 <;> ring
    have hb' : b = (l.M : ℂ)⁻¹ • mk a + v' := by
      calc b = (l.M : ℂ)⁻¹ • (l.M : ℂ) • b := by rw [smul_smul, inv_mul_cancel₀ hM, one_smul]
        _ = _ := by rw [hab, smul_add, smul_smul, inv_mul_cancel₀ hM, one_smul]
    have h3 : vspActL α (b - t q) = mk (r • (α • u + a) + s • d) + I2.act α v' := by
      rw [hsub, hb', levReps_act_add, levReps_act_smul, ← hlin, add_right_comm, ← smul_add, ← map_add,
        add_comm (α • a), h2, hlin, levReps_act_nat, smul_smul, inv_mul_cancel₀ hM, one_smul]
    rw [h3]
    exact T.L.add_mem (hL _) (T.stable _ _ hv')
  have huniq : ∀ (b : I2.Vsp T.dim) q q', vspActL α (b - t q) ∈ T.L → vspActL α (b - t q') ∈ T.L → q = q' := by
    intro b q q' h h'
    have h1 := T.L.sub_mem h h'
    rw [hsub, hsub, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub] at h1
    obtain ⟨z, hz⟩ := hinj (x2 q - x2 q') ⟨_, h1, by rw [smul_smul, mul_inv_cancel₀ hM, one_smul]⟩
    rw [← hcls q, ← hcls q']
    refine (Submodule.Quotient.eq _).2 ?_
    rw [hMb, hsm]
    exact ⟨α • z, by rw [hz, smul_smul, mul_comm, hα, Nat.cast_smul_eq_nsmul]⟩
  refine ⟨Finset.univ.image (fun q : Fin n → LevQ Dw l => fun i => t (q i)), ⟨?_, ?_⟩, ?_⟩
  · intro b hb k
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact hMt _
  · intro b hb
    choose q hq using fun k => hex (b k) (hb k)
    refine ⟨fun i => t (q i), ⟨Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, hq⟩, ?_⟩
    rintro b' ⟨hb', h'⟩
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb'
    funext k
    rw [huniq (b k) _ _ (h' k) (hq k)]
  · intro b hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨q, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeviLogSumSqFibreZeroAndNonposAtMax
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviFibre

theorem contDiffAt_two_of_eventually {n : ℕ} {f : V n → ℂ} {z0 : V n}
    (h : ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ f z) : ContDiffAt ℂ 2 f z0 := by
  obtain ⟨U, hU, hUo, hz⟩ := eventually_nhds_iff.1 h
  exact ReciprocityTheory.L2DbarEstimates.C.holo_contDiffAt_complex hUo
    (fun z hz => (hU z hz).differentiableWithinAt) hz 2

theorem sum_wd_mul {n : ℕ} {f : V n → ℂ} {z0 : V n} (h : DifferentiableAt ℂ f z0)
    (ξ : Fin n → ℂ) : ∑ j, wd n j f z0 * ξ j = fderiv ℂ f z0 (WithLp.toLp 2 ξ) := by
  have hξ : (WithLp.toLp 2 ξ : V n) = ∑ j, ξ j • bas n j := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (WithLp.toLp 2 ξ)]
    simp [bas]
  rw [hξ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wd_of_differentiableAt h, map_smul, smul_eq_mul, mul_comm]

theorem fderiv_eq_of_quot {n : ℕ} {f g : V n → ℂ} {z0 v : V n} (hf : DifferentiableAt ℂ f z0)
    (hg : DifferentiableAt ℂ g z0) (h0 : g z0 ≠ 0)
    (h : fderiv ℂ (fun z => f z / g z) z0 v = 0) :
    fderiv ℂ f z0 v = (fderiv ℂ g z0 v / g z0) * f z0 := by
  have hq : DifferentiableAt ℂ (fun z => f z / g z) z0 := by
    simp only [div_eq_mul_inv]
    exact hf.mul (hg.inv h0)
  have hev : f =ᶠ[𝓝 z0] fun z => (f z / g z) * g z := by
    filter_upwards [hg.continuousAt.eventually_ne h0] with z hz
    field_simp
  rw [hev.fderiv_eq, fderiv_fun_mul hq hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, h]
  field_simp
  ring

theorem levi_log_sum_eq_zero {n m : ℕ} (z0 : V n) (ξ : Fin n → ℂ) (s : Fin m → V n → ℂ)
    (k0 : Fin m) (hs : ∀ k, ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ (s k) z) (h0 : s k0 z0 ≠ 0)
    (hq : ∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0) :
    leviV n (fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ)) z0 ξ = 0 := by
  have hne : (fun i => s i z0) ≠ 0 := fun h => h0 (congrFun h k0)
  have key := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n m s z0 ξ
    (fun k => contDiffAt_two_of_eventually (hs k)) hne
  have hJ : ReciprocityTheory.L2DbarEstimates.H.wJac n m s z0 *ᵥ ξ =
      (fderiv ℂ (s k0) z0 (WithLp.toLp 2 ξ) / s k0 z0) • (fun i => s i z0) := by
    funext i
    have := sum_wd_mul (hs i).self_of_nhds ξ
    rw [fderiv_eq_of_quot (hs i).self_of_nhds (hs k0).self_of_nhds h0 (hq i)] at this
    simpa [ReciprocityTheory.L2DbarEstimates.H.wJac, Matrix.mulVec, dotProduct] using this
  have hP : ReciprocityTheory.L2DbarEstimates.projPerp (fun i => s i z0) *ᵥ (fun i => s i z0) = 0 :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.BigA.projPerp_self _ hne
  rw [hJ, Matrix.mulVec_smul, hP, smul_zero] at key
  simp only [ReciprocityTheory.L2DbarEstimates.sqNorm, Complex.normSq_eq_norm_sq] at key
  rw [key]
  simp

theorem main : ∀ (n : ℕ) (z0 : V n) (ξ : Fin n → ℂ), (∀ (m : ℕ) (s : Fin m → V n → ℂ) (k0 : Fin m), (∀ k, ∀ᶠ z in 𝓝 z0, DifferentiableAt ℂ (s k) z) → s k0 z0 ≠ 0 → (∀ k, fderiv ℂ (fun z => s k z / s k0 z) z0 (WithLp.toLp 2 ξ) = 0) → (leviV n (fun z => ((Real.log (∑ k, ‖s k z‖ ^ 2) : ℝ) : ℂ)) z0 ξ).re = 0) ∧ ∀ g : V n → ℝ, ContDiffAt ℝ 2 g z0 → IsLocalMax g z0 → (leviV n (fun z => ((g z : ℝ) : ℂ)) z0 ξ).re ≤ 0 := by
  intro n z0 ξ
  refine ⟨fun m s k0 hs h0 hq => ?_, fun g hg hmax => ?_⟩
  · rw [levi_log_sum_eq_zero z0 ξ s k0 hs h0 hq, Complex.zero_re]
  · exact ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hg hmax ξ

end GlobalTheory.LeviFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PolyDerivProdFockEqTranslate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem polyDeriv_comp_linear_equiv {σ V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (e : V ≃L[ℂ] W) (P : MvPolynomial σ ℂ) (u : σ → V)
    (G : W → ℂ) (x : V) :
    I2.polyDeriv P u (fun z => G (e z)) x = I2.polyDeriv P (fun ℓ => e (u ℓ)) G (e x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := e.iteratedFDerivWithin_comp_right G (s := Set.univ) uniqueDiffOn_univ (x := x)
    (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have h' : (fun z => G (e z)) = G ∘ e := rfl
  rw [h', h]
  rfl

theorem lintor_hf_neg_right {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf v (-w) = -I2.Hf v w := by
  simp [I2.Hf]

theorem lintor_hf_neg_left {J : Type} [Fintype J] (v w : EuclideanSpace ℂ J) :
    I2.Hf (-v) w = -I2.Hf v w := by
  simp [I2.Hf]

theorem polyDeriv_prod_fock_eq_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : I2.PT E) (g : ℕ) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] I2.Vsp X.dim) (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ), (∀ z w, I2.Hf (ψ z) (ψ w) = hermForm Hm z w) → Differentiable ℂ θ → ∀ (n N : ℕ) (a : Fin n → Fin g → ℂ) (Io : Type) (P : MvPolynomial Io ℂ) (u : Io → Fin n → Fin g → ℂ), I2.polyDeriv P u (fun z => ∏ b, fock Hm ((N : ℤ) ^ 2) (a b) (fun w => θ ((N : ℂ) • w)) (z b)) 0 = I2.polyDeriv P (fun ℓ b => ψ (u ℓ b)) (X.U (N ^ 2) (fun b => -ψ (a b)) (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0 := by
  intro E _ _ _ X g ψ Hm θ hH _ n N a Io P u
  let e : (Fin n → Fin g → ℂ) ≃L[ℂ] (Fin n → I2.Vsp X.dim) :=
    ContinuousLinearEquiv.piCongrRight fun _ => ψ.toContinuousLinearEquiv
  have he : ∀ z, e z = fun b => ψ (z b) := fun _ => rfl
  have key := polyDeriv_comp_linear_equiv e P u (X.U (N ^ 2) (fun b => -ψ (a b))
    (I2.s0 X ((N : ℂ) • LinearMap.id) fun v => θ (ψ.symm (v 0)))) 0
  rw [map_zero] at key
  refine Eq.trans ?_ key
  congr 1
  funext z
  rw [he]
  simp only [fock, I2.PT.U, I2.s0, I2.HC, lintor_hf_neg_right, lintor_hf_neg_left, hH, neg_neg,
    Finset.prod_mul_distrib, ← Complex.exp_sum, Pi.sub_apply, sub_neg_eq_add,
    LinearMap.smul_apply, LinearMap.id_apply, ← map_add, ← map_smul, LinearEquiv.symm_apply_apply]
  congr 2
  simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div, mul_neg]
  push_cast
  rfl

end GlobalTheory.AnVal
end

