import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

-- bundled from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfEqMulInvPow
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.JointModelGuards

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_of_eq_mul_inv_pow (W : ValuationSubring ℂ) {x a : ℂ} (ha : a ∈ W) (n : ℕ) (h : x = a * x⁻¹ ^ n) :
    x ∈ W := by
  rcases W.mem_or_inv_mem x with hx | hx
  · exact hx
  · rw [h]; exact mul_mem ha (pow_mem hx n)

theorem exists_root_and_zeta (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have hr : H.rt0 ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hz : zeta l.A ∈ c.F := c.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hd : (H.d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr H.d_prime.ne_zero
  have hr0 : H.rt0 ≠ 0 := fun h => by
    have := H.sqrt_neg_disc_sq
    rw [h] at this
    exact hd (by simpa using this)
  have hrW : H.rt0 ∈ W := mem_of_eq_mul_inv_pow W (a := -(H.d : ℂ)) (neg_mem (natCast_mem W _)) 1 (by
    rw [← H.sqrt_neg_disc_sq]; field_simp)
  have hp : IsPrimitiveRoot (zeta l.A) l.A := Complex.isPrimitiveRoot_exp l.A l.A_pos.ne'
  have hz0 : zeta l.A ≠ 0 := hp.ne_zero l.A_pos.ne'
  have hzW : zeta l.A ∈ W := mem_of_eq_mul_inv_pow W (a := 1) (one_mem W) (l.A - 1) (by
    have h1 : zeta l.A * zeta l.A ^ (l.A - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel l.A_pos]; exact hp.pow_eq_one
    rw [one_mul, inv_pow]
    exact eq_inv_of_mul_eq_one_left h1)
  exact ⟨⟨⟨_, hr⟩, hrW⟩, ⟨⟨_, hz⟩, hzW⟩, rfl, rfl⟩

theorem localRing_ne_top (l : Level H) (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p.Prime)
    (hW : (p : ℂ) ∈ W.nonunits) : c.V W ≠ ⊤ := by
  intro h
  have h1 : ((p : c.F))⁻¹ ∈ c.V W := by rw [h]; trivial
  have h2 : ((p : ℂ))⁻¹ ∈ W := by simpa [ValuationSubring.mem_comap] using h1
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [ValuationSubring.mem_nonunits_iff] at hW
  have h3 := (W.valuation_le_one_iff _).mpr h2
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hp0))] at h3
  exact absurd hW (not_lt.mpr h3)

end GlobalTheory.JointModelGuards
end

-- bundled from Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.PsiUnitOnIffInterior
section
noncomputable section
namespace GlobalTheory.DegActCheck
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {R : Type} [CommRing R] [IsDomain R]

theorem psiUnitOn_iff_interior (D : Out.DegPre R) (χ : D.X) (U : Set (Sp R)) :
    PsiUnitOn D χ U ↔ PsiUnitOn D χ (interior U) :=
  ⟨fun h j V hV hU => h j V hV (hU.trans interior_subset),
   fun h j V hV hU => h j V hV (interior_maximal hU V.isOpen)⟩

theorem qkExt_compat {D : Out.DegPre R} {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F') {k : ℕ} (p : Out.QkPt D F k)
    (p' : Out.QkPt D F' k) (h : QkExt f p p') :
    f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' := by
  have h1 := Over.w p.g.b
  have h2 := Over.w p'.g.b
  rw [h.2.1] at h2
  have h3 : spMap f ≫ (Out.jFK (R := R) F ≫ Out.jK R) = Out.jFK (R := R) F' ≫ Out.jK R := by
    refine Eq.trans ?_ h2
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (spMap f ≫ ·) h1.symm
  have h4 : CommRingCat.ofHom ((f.comp (algebraMap (FractionRing R) F)).comp (algebraMap R (FractionRing R))) =
      CommRingCat.ofHom ((algebraMap (FractionRing R) F').comp (algebraMap R (FractionRing R))) := by
    apply Spec.map_injective
    simp only [CommRingCat.ofHom_comp, Spec.map_comp]
    exact (Category.assoc _ _ _).trans h3
  exact IsLocalization.ringHom_ext (nonZeroDivisors R) (congrArg CommRingCat.Hom.hom h4)

theorem halfUnit_add_star {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.bar H.rt) ^ 2 = H.rt ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hne : H.bar H.rt ≠ H.rt := by
    intro h
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have h1 : IsCMField.complexConj E (H.rt : E) = (H.rt : E) := by rw [← H.bar_eq, h]
    have h2 := IsCMField.complexEmbedding_complexConj E τ (H.rt : E)
    rw [h1] at h2
    have h3 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => τ (x : E)) H.rt_sq
      simpa using this
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2.symm
    rw [hr] at h3
    have : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h3
    nlinarith [sq_nonneg r]
  have hb : H.bar H.rt = -H.rt := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left hne
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar H.two_weight_eq_one_add_root
    rw [map_mul, map_add, map_one, hb, map_ofNat] at this
    rw [this]; ring
  have : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by rw [mul_add, H.two_weight_eq_one_add_root, h2]; ring
  exact mul_left_cancel₀ two_ne_zero this

section Sums
variable {O : Type} [CommRing O] [StarRing O] (D : Out.DegPre R) [Module O D.X] (oa : D.OAct O) (w : O) (y : D.X)

theorem pt_act : D.xK y ≫ (oa.onB.act w).left = D.xK (w • y) := by
  show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R) ≫ D.c (w • y)).left
  rw [oa.c_lin, ← Over.comp_left, Category.assoc]

theorem pt_sum : D.xK y ≫ (padd D.P.A (𝟙 _) (oa.onB.act w)).left = D.xK (y + w • y) := by
  show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R) ≫ D.c (y + w • y)).left
  rw [D.c_add, oa.c_lin, ← Over.comp_left]
  congr 1
  simp only [padd, Category.assoc, comp_lift_assoc, Category.comp_id]

theorem pt_zero : D.xK y ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit (Out.TK R)).left ≫ eSec D.P.A := by
  show (toUnit (Out.TK R) ≫ D.c y).left ≫ _ = (toUnit (Out.TK R)).left ≫ (η[D.P.A]).left
  rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, comp_toUnit]

end Sums

end GlobalTheory.DegActCheck
end
end

