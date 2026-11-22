import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HuaIntegralPositiveDefiniteQuadric
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.HuaQuadric

variable {p q : ℕ}

theorem exists_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, IsUnit R.det ∧ A = Rᴴ * R := by
  open scoped MatrixOrder in
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
  refine ⟨R, ?_, hR⟩
  have h := hA.det_pos.ne'
  rw [hR, det_mul] at h
  exact (right_ne_zero_of_mul h).isUnit

theorem shear_fromBlocks (a : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin p) (Fin q) ℂ) (c : Matrix (Fin q) (Fin p) ℂ)
    (d : Matrix (Fin q) (Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    shear (fromBlocks a b c d) Z = fromBlocks a (a * Z + b) (Zᴴ * a + c) ((Zᴴ * a + c) * Z + (Zᴴ * b + d)) := by
  simp [shear, fromBlocks_conjTranspose, fromBlocks_multiply]

theorem exists_square {A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hA : A.PosDef) :
    ∃ (R : Matrix (Fin p) (Fin p) ℂ) (T : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin p) (Fin q) ℂ),
      IsUnit R.det ∧ IsUnit T.det ∧ A.det = (Complex.normSq R.det * Complex.normSq T.det : ℝ) ∧
      ∀ Z, (shear A Z).toBlocks₂₂ = Tᴴ * (1 + (R * Z * T⁻¹ + C)ᴴ * (R * Z * T⁻¹ + C)) * T := by
  obtain ⟨R, hR, ha⟩ := exists_factor (posDef_blocks hA).1
  have e : A.toBlocks₂₁ = A.toBlocks₁₂ᴴ := by
    ext a b
    exact (hA.1.apply _ _).symm
  have hRh : IsUnit Rᴴ.det := by rw [det_conjTranspose]; exact hR.star
  obtain ⟨c, hc⟩ : ∃ c, A.toBlocks₁₂ = Rᴴ * R * c :=
    ⟨R⁻¹ * (Rᴴ⁻¹ * A.toBlocks₁₂), by
      rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hR, mul_nonsing_inv_cancel_left _ _ hRh]⟩
  have hA' : A = fromBlocks (Rᴴ * R) (Rᴴ * R * c) (cᴴ * (Rᴴ * R)) A.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks A, e, ha, hc]
    simp [conjTranspose_mul, Matrix.mul_assoc]
  generalize A.toBlocks₂₂ = d at hA'
  have hs : shear A (-c) = fromBlocks (Rᴴ * R) 0 0 (d - cᴴ * (Rᴴ * R * c)) := by
    rw [hA', shear_fromBlocks]
    simp [sub_eq_neg_add]
  have hS := (posDef_blocks (posDef_shear hA (-c))).2.1
  rw [hs, toBlocks_fromBlocks₂₂] at hS
  obtain ⟨T, hT, ht⟩ := exists_factor hS
  have hTh : IsUnit Tᴴ.det := by rw [det_conjTranspose]; exact hT.star
  refine ⟨R, T, R * c * T⁻¹, hR, hT, ?_, fun Z => ?_⟩
  · rw [← det_shear A (-c), hs, ht, det_fromBlocks_zero₂₁, det_mul, det_mul, det_conjTranspose, det_conjTranspose]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    rfl
  · rw [hA', shear_fromBlocks, toBlocks_fromBlocks₂₂, eq_add_of_sub_eq ht]
    simp only [conjTranspose_mul, conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      conjTranspose_nonsing_inv, mul_nonsing_inv_cancel_left _ _ hTh,
      nonsing_inv_mul _ hT, Matrix.mul_one, Matrix.one_mul]
    abel

theorem quadric : ∀ (p q : ℕ) (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (A.det.re ^ (-(q : ℤ)) / grassConst p q) := by
  intro p q A hA
  obtain ⟨R, T, C, hR, hT, hd, hZ⟩ := exists_square hA
  have hr : 0 < Complex.normSq R.det := Complex.normSq_pos.2 hR.ne_zero
  have ht : 0 < Complex.normSq T.det := Complex.normSq_pos.2 hT.ne_zero
  let f : (Fin p × Fin q → ℂ) → ℝ≥0∞ := fun v =>
    ENNReal.ofReal ((1 + (toMat v)ᴴ * toMat v).det.re ^ (-((p + q : ℕ) : ℤ)))
  have hf : Measurable f :=
    ((Complex.continuous_re.comp (continuous_const.add
      (continuous_toMat.matrix_conjTranspose.matrix_mul continuous_toMat)).matrix_det).measurable.pow_const
        _).ennreal_ofReal
  have h1 : ∀ v : Fin p × Fin q → ℂ,
      ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) =
        ENNReal.ofReal (Complex.normSq T.det ^ (-((p + q : ℕ) : ℤ))) * f (vecOf (R * toMat v * T⁻¹ + C)) := by
    intro v
    simp only [f, toMat_vecOf]
    rw [← ENNReal.ofReal_mul (zpow_pos ht _).le, ← mul_zpow, hZ, det_mul, det_mul, det_conjTranspose, mul_right_comm,
      ← Complex.re_ofReal_mul, Complex.normSq_eq_conj_mul_self]
    rfl
  simp_rw [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    GlobalTheory.FlagFibre.lintegral_affine p q R T⁻¹ C hR (isUnit_nonsing_inv_det _ hT) f hf]
  have h2 : ∫⁻ v, f v = ENNReal.ofReal (grassConst p q)⁻¹ := GlobalTheory.HuaIntegral.dual_mass p q
  have h3 : Complex.normSq T⁻¹.det = (Complex.normSq T.det)⁻¹ := by
    rw [det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀]
  rw [h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul (zpow_pos ht _).le, ← ENNReal.ofReal_mul (by positivity), hd,
    Complex.ofReal_re, div_eq_mul_inv]
  congr 2
  simp only [_root_.zpow_neg, _root_.zpow_natCast, pow_add, mul_pow, inv_pow]
  field_simp

end GlobalTheory.HuaQuadric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo

namespace GlobalTheory.ShFam.Pad

variable {F : Type} [Field F] [NumberField F]

theorem residueCharacteristic_prime (v : HeightOneSpectrum (𝓞 F)) : (resP v).Prime := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  exact CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) _

theorem residueCharacteristic_mem (v : HeightOneSpectrum (𝓞 F)) : ((resP v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar

theorem ioOf_le_one_iff (p : ℕ) [Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (hv : (p : 𝓞 F) ∈ v.asIdeal) (ε : Ext v) :
    ∀ a, ‖ioOf p ε a‖ ≤ 1 ↔ a ∈ ε.O := by
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding (l := p) F (AlgebraicClosure F) v ε.O hv
    (GlobalTheory.TrueGeo.ExtConj.lies_over ε)
  have h : ∃ io : AlgebraicClosure F →+* ℂ_[p], ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O :=
    ⟨(algebraMap (PadicAlgCl p) ℂ_[p]).comp j, fun a => by
      rw [hj, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends]⟩
  exact Classical.epsilon_spec h

theorem log_w_eq (p : ℕ) [hp : Fact p.Prime] {v : HeightOneSpectrum (𝓞 F)} (ε : Ext v)
    (io : AlgebraicClosure F →+* ℂ_[p]) (h : ∀ a, ‖io a‖ ≤ 1 ↔ a ∈ ε.O) (a : AlgebraicClosure F) :
    Real.log (ε.w a) = (-Real.log (ε.w p) / Real.log p) * Real.log ‖io a‖ := by
  let u : AbsoluteValue (AlgebraicClosure F) ℝ := (NormedField.toAbsoluteValue ℂ_[p]).comp io.injective
  have hu (x) : u x = ‖io x‖ := rfl
  have he : u.IsEquiv ε.w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have h1 : u x⁻¹ ≤ 1 ↔ ε.w x⁻¹ ≤ 1 := by rw [hu, h, ε.mem_O]
      rw [map_inv₀, map_inv₀, inv_le_one₀ (u.pos hx), inv_le_one₀ (ε.w.pos hx)] at h1
      rw [← not_le, ← not_le, h1]
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hw (x) : Real.log (ε.w x) = c * Real.log ‖io x‖ := by
    rw [← congrFun hce x, hu]
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Real.zero_rpow hc.ne']
    · exact Real.log_rpow (norm_pos_iff.2 ((map_ne_zero io).2 hx)) c
  have hn : ‖io p‖ = (p : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have hl : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  rw [hw, hw, hn, Real.log_inv]
  field_simp

theorem ioOf_spec : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v), ∃ hp : (resP v).Prime, haveI := Fact.mk hp; (∀ a, ‖ioOf (resP v) ε a‖ ≤ 1 ↔ a ∈ ε.O) ∧ ∀ a, Real.log (ε.w a) = (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log ‖ioOf (resP v) ε a‖ := fun _ _ _ v ε =>
  ⟨residueCharacteristic_prime v, by
    haveI := Fact.mk (residueCharacteristic_prime v)
    exact ⟨ioOf_le_one_iff _ (residueCharacteristic_mem v) ε, log_w_eq _ ε _ (ioOf_le_one_iff _ (residueCharacteristic_mem v) ε)⟩⟩

end GlobalTheory.ShFam.Pad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsEigBasisPull
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.OpenReg

namespace GlobalTheory.CuspFrom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def IsEigBasis {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ)
    {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (v i)) ∧ (∀ i (a : 𝓞 E), v i ≫ (t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ v i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x v a w

variable {O : Type} [CommRing O] {β : O →+* c.F}

theorem EigFrame.isEigBasis {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (g : EigFrame Z φ x) (τ : E →+* ℂ) : IsEigBasis Z.t φ x τ (g.v τ) :=
  ⟨g.tan τ, g.eig τ, g.basis τ⟩

def eigFrameOf {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)) (h : ∀ τ, IsEigBasis Z.t φ x τ (v τ)) :
    EigFrame Z φ x :=
  ⟨v, fun τ => (h τ).1, fun τ => (h τ).2.1, fun τ => (h τ).2.2⟩

section Transport

variable {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ S'} {τ : E →+* ℂ} {n : ℕ}

theorem isEigBasis_push {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} (h : IsEigBasis t' φ x τ v) :
    IsEigBasis t φ (x ≫ f) τ (fun i => v i ≫ m.φ) := by
  have hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := fun i => (h.1 i).1
  refine ⟨fun i => (tan_iff m rfl (hv i)).2 (h.1 i), fun i a => (eig_iff m (hv i) a _).2 (h.2.1 i a),
    fun w hw he => ?_⟩
  obtain ⟨w', hw1, rfl⟩ := exists_lift m (spMap (algebraMap R (DualNumber R)) ≫ x) w (by rw [hw.1, Category.assoc])
  have hb := h.2.2 w' ((tan_iff m rfl hw1).1 hw) fun a => (eig_iff m hw1 a _).1 (he a)
  exact (existsUnique_congr fun cf => comb_iff m rfl hv cf hw1).2 hb

theorem isEigBasis_pull {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsEigBasis t φ (x ≫ f) τ v) :
    ∃ v' : Fin n → (Sp (DualNumber R) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = v i) ∧ IsEigBasis t' φ x τ v' := by
  choose v' hv1 hv2 using fun i =>
    exists_lift m (spMap (algebraMap R (DualNumber R)) ≫ x) (v i) (by rw [(h.1 i).1, Category.assoc])
  have e : v = fun i => v' i ≫ m.φ := funext fun i => (hv2 i).symm
  subst e
  refine ⟨v', fun i => rfl, fun i => (tan_iff m rfl (hv1 i)).1 (h.1 i), fun i a => (eig_iff m (hv1 i) a _).1 (h.2.1 i a),
    fun w hw he => ?_⟩
  have hb := h.2.2 (w ≫ m.φ) ((tan_iff m rfl hw.1).2 hw) fun a => (eig_iff m hw.1 a _).2 (he a)
  exact (existsUnique_congr fun cf => comb_iff m rfl hv1 cf hw.1).1 hb

end Transport

end GlobalTheory.CuspFrom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomainStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1) → (∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 → muF X (x0F X) (proj X hj κ ⁻¹' N) = 0) → ∀ F, IsFD (gammaU X hj κ) F → ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧ IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  first | exact @GlobalTheory.FlagFibre.FundPre.isFundSet_preimage | exact GlobalTheory.FlagFibre.FundPre.isFundSet_preimage | (intros; apply GlobalTheory.FlagFibre.FundPre.isFundSet_preimage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.TrueGeo GlobalTheory.Cartier

namespace GlobalTheory.ShFam.CoordUniq

section Lin

variable {K : Type} [Field K] {m n : ℕ}

theorem tri_of_mul {T₁ T₂ M : Fin m → Fin m → K} (h₁ : ∀ i k, i < k → T₁ i k = 0) (h₂ : ∀ i k, i < k → T₂ i k = 0)
    (hd : ∀ i, T₂ i i ≠ 0) (h : ∀ i k, T₁ i k = ∑ j, T₂ i j * M j k) (i : Fin m) : ∀ k, i < k → M i k = 0 := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro k hk
    have e := h i k
    rw [h₁ i k hk, Finset.sum_eq_single i (fun j _ hj => by
      rcases lt_or_gt_of_ne hj with hj | hj
      · rw [ih j hj k (hj.trans hk), mul_zero]
      · rw [h₂ i j hj, zero_mul]) (by simp)] at e
    exact (mul_eq_zero.1 e.symm).resolve_left (hd i)

theorem diag_of_mul {T₂ M : Fin m → Fin m → K} (h₂ : ∀ i k, i < k → T₂ i k = 0) (hM : ∀ i k, i < k → M i k = 0)
    (i : Fin m) : ∑ j, T₂ i j * M j i = T₂ i i * M i i :=
  Finset.sum_eq_single i (fun j _ hj => by
    rcases lt_or_gt_of_ne hj with hj | hj
    · rw [hM j i hj, mul_zero]
    · rw [h₂ i j hj, zero_mul]) (by simp)

theorem indep_of_tri {T : Fin m → Fin m → K} (h : ∀ i k, i < k → T i k = 0) (hd : ∀ i, T i i ≠ 0)
    {e : Fin m → Fin n → K} (hg : ∀ a : Fin m → K, ∑ i, a i • ∑ j, T i j • e j = 0 → a = 0)
    {b : Fin m → K} (hb : ∑ j, b j • e j = 0) : b = 0 := by
  have hdet : IsUnit (Matrix.of T).det := by
    rw [Matrix.det_of_isLowerTriangular (Matrix.of T) (fun i k hk => h i k hk)]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have e1 : Matrix.vecMul (Matrix.vecMul b (Matrix.of T)⁻¹) (Matrix.of T) = b := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  have e2 := hg (Matrix.vecMul b (Matrix.of T)⁻¹) (by
    rw [← hb]
    conv_rhs => rw [← e1]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    rfl)
  rw [← e1, e2, Matrix.zero_vecMul]

end Lin

section Frames

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem exists_matrix {R : Type} [CommRing R] [IsLocalRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ f₂ : EigFrame Z φ x) (τ : E →+* ℂ) :
    ∃ M : Fin (Dw.mult τ) → Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∃ T₁ T₂ : Fin (Dw.mult τ) → Fin (Dw.mult τ) → k,
        (∀ i, T₁ i i = t₁ τ i) ∧ (∀ i, T₂ i i = t₂ τ i) ∧ (∀ i k, i < k → T₁ i k = 0) ∧ (∀ i k, i < k → T₂ i k = 0) ∧
          ∀ i k, T₁ i k = ∑ j, T₂ i j * ψ (M j k) := by
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan τ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan τ i)
  choose M hM using fun i => (f₁.basis τ _ (f₂.tan τ i) (f₂.eig τ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v τ = fun j => vec Z.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  refine ⟨M, fun {k} _ ψ φ' x' g t₁ t₂ h₁ h₂ => ?_⟩
  obtain ⟨rfl, rfl, h₁⟩ := h₁
  obtain ⟨-, -, h₂⟩ := h₂
  choose T₁ a₁ b₁ c₁ using h₁ τ
  choose T₂ a₂ b₂ c₂ using h₂ τ
  letI : Algebra R k := ψ.toAlgebra
  obtain ⟨xc', hx', hv⟩ := vec_bc (S' := k) hx
  change ∀ cc, vec Z.t (spMap ψ ≫ x) xc' (ψ ∘ cc) = spMap (dualMap ψ) ≫ vec Z.t x xc cc at hv
  choose G hG using fun i => vec_exists hx' _ (g.tan τ i)
  have d₁ : ∀ i, G i = ∑ j, T₁ i j • (ψ ∘ e₁ j) := fun i => by
    have := c₁ i
    simp only [he₁, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have d₂ : ∀ i, G i = ∑ j, T₂ i j • (ψ ∘ e₂ j) := fun i => by
    have := c₂ i
    simp only [he₂, ← hv] at this
    rw [hG i] at this
    exact (comb_iff hx' _ _ _).1 this
  have hind : ∀ a : Fin (Dw.mult τ) → k, ∑ i, a i • G i = 0 → a = 0 := fun a ha => by
    have hb := g.basis τ _ (vec_tan hx' 0) ((vec_eig_iff hx' _ _).2 (Submodule.zero_mem _))
    rw [show g.v τ = fun j => vec Z.t _ xc' (G j) from funext hG] at hb
    exact hb.unique ((comb_iff hx' _ _ _).2 ha.symm) ((comb_iff hx' _ _ _).2 (by simp))
  refine ⟨T₁, T₂, a₁, a₂, b₁, b₂, fun i k' => ?_⟩
  have := indep_of_tri b₁ (fun i => a₁ i ▸ (t₁ τ i).ne_zero) (e := fun j => ψ ∘ e₁ j)
    (fun a ha => hind a (by simpa only [d₁] using ha))
    (b := fun k' => T₁ i k' - ∑ j, T₂ i j * ψ (M j k')) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← d₁, d₂, sub_eq_zero]
      funext q
      simp only [hM', Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_sum, map_mul,
        Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm)
  exact sub_eq_zero.1 (congrFun this k')

theorem exists_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → R, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, (t₁ τ i : k) = t₂ τ i * ψ (u τ i) := by
  obtain rfl : φ₁ = φ₂ := RingHom.ext fun a => hι ((RingHom.congr_fun h₁.2.1 a).symm.trans (RingHom.congr_fun h₂.2.1 a))
  choose M hM using exists_matrix f₁ f₂
  have hT : ∀ τ i k, i < k → M τ i k = 0 := fun τ i k hk => by
    obtain ⟨T₁, T₂, -, a₂, b₁, b₂, h⟩ := hM τ ι f₀ t₁ t₂ h₁ h₂
    exact hι ((tri_of_mul (M := fun i k => ι (M τ i k)) b₁ b₂ (fun i => a₂ i ▸ (t₂ τ i).ne_zero) h i k hk).trans
      (map_zero ι).symm)
  refine ⟨fun τ i => M τ i i, fun {k} _ ψ φ' x' g s₁ s₂ g₁ g₂ τ i => ?_⟩
  obtain ⟨T₁, T₂, a₁, a₂, -, b₂, h⟩ := hM τ ψ g s₁ s₂ g₁ g₂
  rw [← a₁, ← a₂, h]
  exact diag_of_mul (M := fun i k => ψ (M τ i k)) b₂ (fun i k hk => by simp only [hT τ i k hk, map_zero]) i

theorem exists_unit_ratio {R : Type} [CommRing R] [IsLocalRing R] {φ₁ φ₂ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (f₁ : EigFrame Z φ₁ x) (f₂ : EigFrame Z φ₂ x) {K : Type} [Field K] {ι : R →+* K} (hι : Function.Injective ι)
    {φ₀ : c.F →+* K} {x₀ : Sp K ⟶ Z.X} {f₀ : EigFrame Z φ₀ x₀} {t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ}
    (h₁ : f₁.Tri ι f₀ t₁) (h₂ : f₂.Tri ι f₀ t₂) :
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Rˣ, ∀ {k : Type} [Field k] (ψ : R →+* k) {φ' : c.F →+* k}
      {x' : Sp k ⟶ Z.X} (g : EigFrame Z φ' x') (t₁ t₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ),
      f₁.Tri ψ g t₁ → f₂.Tri ψ g t₂ → ∀ τ i, t₁ τ i = t₂ τ i * Units.map (ψ : R →* k) (u τ i) := by
  obtain ⟨u, hu⟩ := exists_ratio f₁ f₂ hι h₁ h₂
  obtain ⟨v, hv⟩ := exists_ratio f₂ f₁ hι h₂ h₁
  have huv : ∀ τ i, u τ i * v τ i = 1 := fun τ i => hι (by
    have a := hu ι f₀ _ _ h₁ h₂ τ i
    have b := hv ι f₀ _ _ h₂ h₁ τ i
    rw [a, mul_assoc] at b
    rw [map_mul, map_one]
    exact (mul_left_cancel₀ (t₂ τ i).ne_zero ((mul_one _).trans b)).symm)
  exact ⟨fun τ i => Units.mkOfMulEqOne _ _ (huv τ i), fun ψ _ _ g s₁ s₂ g₁ g₂ τ i =>
    Units.ext (hu ψ g s₁ s₂ g₁ g₂ τ i)⟩

end Frames

theorem isLocalHom_of_algebraic {R F k : Type} [CommRing R] [IsLocalRing R] [Field F] [CharZero F] (φ : F →+* R)
    [Field k] [CharZero k] [Algebra.IsAlgebraic ℚ k] (ψ : R →+* k) : IsLocalHom ψ := by
  letI : Algebra ℚ R := (φ.comp (algebraMap ℚ F)).toAlgebra
  let ψ' : R →ₐ[ℚ] k := { ψ with commutes' := fun q => by simp }
  refine ⟨fun a ha => ?_⟩
  have h0 : ψ a ≠ 0 := ha.ne_zero
  have hi : IsIntegral ℚ (ψ a) := (Algebra.IsAlgebraic.isAlgebraic _).isIntegral
  have hc := minpoly.coeff_zero_ne_zero hi h0
  have h1 : ψ (Polynomial.aeval a (minpoly ℚ (ψ a))) = 0 :=
    (Polynomial.aeval_algHom_apply ψ' a _).symm.trans (minpoly.aeval ℚ (ψ a))
  have h2 : ¬ IsUnit (Polynomial.aeval a (minpoly ℚ (ψ a))) := fun h => (h.map ψ).ne_zero h1
  by_contra hna
  rw [← Polynomial.X_mul_divX_add (minpoly ℚ (ψ a)), map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  have h3 : algebraMap ℚ R ((minpoly ℚ (ψ a)).coeff 0) ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem (IsLocalRing.maximalIdeal R) h2
      (Ideal.mul_mem_right (Polynomial.aeval a (minpoly ℚ (ψ a)).divX) _ hna)
    rwa [add_sub_cancel_left] at this
  exact h3 (hc.isUnit.map _)

theorem stalk_ext {X : Scheme.{0}} {k : Type} [Field k] {y y' : X} {ψ : X.presheaf.stalk y →+* k}
    {ψ' : X.presheaf.stalk y' →+* k} (h : IsLocalHom ψ) (h' : IsLocalHom ψ')
    (e : spMap ψ ≫ X.fromSpecStalk y = spMap ψ' ≫ X.fromSpecStalk y') : y = y' ∧ HEq ψ ψ' := by
  have := (SpecToEquivOfLocalRing X (.of k)).symm.injective (a₁ := ⟨y, CommRingCat.ofHom ψ, h⟩)
    (a₂ := ⟨y', CommRingCat.ofHom ψ', h'⟩) e
  obtain ⟨rfl, e'⟩ := Sigma.mk.inj_iff.1 this
  exact ⟨rfl, heq_of_eq (congrArg (fun f => f.1.hom) (eq_of_heq e'))⟩

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {σ : Y.Y.Fn}

theorem exists_isCoord (hσ : ∀ y, (divOf Y n).RegularAt y σ) (h : Y.Carries p g) : ∃ a, IsCoord Y p g n σ a := by
  obtain ⟨y, ψ, φ₁, f, t, t', h₁, h₂, h₃⟩ := h
  obtain ⟨φ₂, f₂, t₂, hT, ht⟩ := Y.gr_spec y
  obtain ⟨u, hu⟩ := exists_unit_ratio f f₂ (IsFractionRing.injective (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) h₂ hT
  have ht' : ∀ τ i, (Y.gr τ i).IsEqn y (t τ i) := fun τ i => (ht τ i).iff_unitAt.2
    ⟨u τ i, (u τ i).isUnit, by
      rw [hu _ _ _ _ h₂ hT τ i, Units.val_mul, mul_div_cancel_left₀ _ (Units.ne_zero _)]; rfl⟩
  have hE : ∀ s : Finset (Letter Dw), (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn y (∏ z ∈ s, t z.1 z.2 ^ n z) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht' _ _).zsmul _).add ih
  obtain ⟨r, hr⟩ := (hE Finset.univ).regularAt_iff.1 (hσ y)
  exact ⟨_, y, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, hr, rfl⟩

end Coord

end GlobalTheory.ShFam.CoordUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPerHolOne
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.PeriodSpan

variable {X : Scheme.{0}} (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X)

def torusPts (E : TorusExtension ((Over.pullback y).obj G)) : Set (Over.mk y ⟶ G) :=
  letI := E.addCommGroup
  {x | ∃ t : Over.mk (𝟙 (Sp ℂ)) ⟶ splitTorus (Spec (.of ℂ)) E.X, (t ≫ E.i).left ≫ pullback.fst G.hom y = x.left}

def IsPerHol (ψ : ℂ → (Over.mk y ⟶ G)) : Prop :=
  (∀ s t, ψ (s + t) = ψ s * ψ t) ∧ IsHolTo Set.univ (fun s => (ψ s).left) ∧
    ψ (2 * Real.pi * Complex.I) = 1

def perHolSub : Subgroup (Over.mk y ⟶ G) :=
  Subgroup.closure (⋃ (ψ : ℂ → (Over.mk y ⟶ G)) (_ : IsPerHol G y ψ), Set.range ψ)

end GlobalTheory.PeriodSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecompositionStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMinor_blockDecomposition : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ H : Matrix (Fin r) (Fin r) ℂ, IsUnit (reindex e e H).toBlocks₂₂.det → (∀ (i : Fin (r + 1)) (k : Fin (q + 1)), (i : ℕ) = k → lminor H i = lminor (reindex e e H).toBlocks₂₂ k) ∧ ∀ (i : Fin (r + 1)) (k : Fin (p + 1)), (i : ℕ) = q + k → lminor H i = (reindex e e H).toBlocks₂₂.det * lminor (schur (reindex e e H)) k := by
  first | exact @GlobalTheory.FlagFibre.lminor_block | exact GlobalTheory.FlagFibre.lminor_block | (intros; apply GlobalTheory.FlagFibre.lminor_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreservingStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_pi_fibre_measurePreserving : ∀ (T A B C : Type) [Fintype T] [MeasureSpace A] [MeasureSpace B] [MeasureSpace C] [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)] [SigmaFinite (volume : Measure C)] (g : A × B → C) (π : C → A) (D : C → ℝ≥0∞) (φ : (T → A) → ℝ≥0∞), MeasurePreserving g volume volume → Measurable π → (∀ w, π (g w) = w.1) → Measurable D → Measurable φ → ∫⁻ c : T → C, φ (fun t => π (c t)) * ∏ t, D (c t) = ∫⁻ a : T → A, φ a * ∏ t, ∫⁻ b, D (g (a t, b)) := by
  first | exact @GlobalTheory.ProdFibre.lintegral_pi_fibre | exact GlobalTheory.ProdFibre.lintegral_pi_fibre | (intros; apply GlobalTheory.ProdFibre.lintegral_pi_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinatesStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_flagFibreChartCoordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), MeasurePreserving (coords X κ) volume volume := by
  first | exact @GlobalTheory.FlagFibre.measurePreserving_coords_sorted | exact GlobalTheory.FlagFibre.measurePreserving_coords_sorted | (intros; apply GlobalTheory.FlagFibre.measurePreserving_coords_sorted <;> assumption)
end

