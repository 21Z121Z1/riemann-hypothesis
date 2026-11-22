import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmCurveHomExistsPureTypeVectorAnyLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmCurveHom_exists_pureTypeVector_anyLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (φ : C.P.A.left ⟶ Xo.univ.t.G.left) (x : ℂ → (Over.mk (F.u i P) ⟶ Xo.univ.t.G)) (ε : ℤˣ), (∀ z, (x z).left = C.pt z ≫ φ) → (∀ z w, x (z + w) = x z * x w) → (∀ z, x ((1 + ((ε : ℤ) : ℂ) * H.rt0) / 2 * z) = x z ≫ Xo.univ.t.act.act H.w0) → ∃ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∀ z : ℂ, x z = F.ex i P (z • P a) := by
  first | exact @GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector | exact GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector | (intros; apply GlobalTheory.CurveHomLiftAnyLevel.exists_pure_vector <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointEigenbasisBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedPoint_eigenbasis_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S) (τ : E →+* ℂ) (w : (Sp (DualNumber T) ⟶ Xo.univ.t.G.left)), IsTanAt (spMap ψ.toRingHom ≫ y.x) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt (spMap ψ.toRingHom ≫ y.x) (fun i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i) a w := by
  first | exact @GlobalTheory.Frames.eigenbasis_baseChange | exact GlobalTheory.Frames.eigenbasis_baseChange | (intros; apply GlobalTheory.Frames.eigenbasis_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NonemptyThetaDataFlagDomainModelsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaData_flagDomainModels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, Nonempty (ThetaData e F M k) := by
  first | exact @GlobalTheory.FrameUnif.nonempty_thetaData | exact GlobalTheory.FrameUnif.nonempty_thetaData | (intros; apply GlobalTheory.FrameUnif.nonempty_thetaData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PrincipalGroupActsFreelyOnFlags
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PrincFree

theorem cmType_of_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ↔ ¬ (ComplexEmbedding.conjugate τ) (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hsq : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hE]; simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hconj : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero] at h1 h2
    have h3 : z.re = 0 := by
      by_contra h
      have h4 : z.im = 0 := by
        have : z.re * z.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h
      rw [h4] at h1
      nlinarith [mul_self_nonneg z.re]
    apply Complex.ext <;> simp [h3]
  have hne : H.rt0 ≠ 0 := by
    intro h
    have h1 := H.sqrt_neg_disc_sq
    rw [h] at h1
    have h2 : (H.d : ℂ) = 0 := by simpa using h1
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  rw [ComplexEmbedding.conjugate_coe_eq, hconj _ hsq]
  constructor
  · intro h h'
    rw [h] at h'
    exact hne (by linear_combination (-1 / 2 : ℂ) * h')
  · intro h
    have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [hsq, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
    · exact h2
    · exact absurd (by rw [h2, neg_neg]) h

theorem exists_equiv_of_stab {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L]
    {r : ℕ} (φ : L →ₗ[𝓞 E] (Fin r → E)) (hφ : Function.Injective φ) (γ : GL (Fin r) E)
    (hγ : ∀ v, v ∈ LinearMap.range φ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ LinearMap.range φ) :
    ∃ g : L ≃ₗ[𝓞 E] L, ∀ a, φ (g a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  choose f hf using fun a : L => (hγ (φ a)).1 (LinearMap.mem_range_self φ a)
  let g : L →ₗ[𝓞 E] L :=
    { toFun := f
      map_add' := fun a b => hφ (by rw [map_add, hf, hf, hf, map_add, Matrix.mulVec_add])
      map_smul' := fun c a => hφ (by
        rw [RingHom.id_apply, map_smul, hf, hf, map_smul, Matrix.mulVec_smul]) }
  have hri : ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  refine ⟨LinearEquiv.ofBijective g ⟨fun a b hab => hφ ?_, fun b => ?_⟩, hf⟩
  · have h : f a = f b := hab
    rw [← hli (φ a), ← hli (φ b), ← hf, ← hf, h]
  · obtain ⟨a, ha⟩ := (hγ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ φ b)).2
      (by rw [hri]; exact LinearMap.mem_range_self φ b)
    exact ⟨a, hφ (by rw [← hri (φ b), ← ha]; exact hf a)⟩

theorem princ_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Di : Datum H) (r : ℕ) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ0 : Di.La →ₗ[𝓞 E] (Fin r → E)), cc ξ₀ = -ξ₀ → (Function.Injective φ0 ∧ Submodule.span E (Set.range φ0) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Di.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ0 x) (φ0 y))) → ∀ (Ψ : Finset (E →+* ℂ)) (q : ℕ), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → ∀ γ ∈ princ l Gm Di φ0, ∀ x ∈ GG Ψ Gm q, ∀ b ∈ Bor Ψ r, lact γ x = rmul x b → γ = 1 := by
  intro E _ _ _ H l Di r ξ₀ Gm φ0 _ ⟨hinj, hsp, hG, _, hEF⟩ Ψ q hΨ γ hγ x hx b hb hxb
  obtain ⟨hU, hhalf, -⟩ := hγ
  obtain ⟨g, hg⟩ := exists_equiv_of_stab φ0 hinj γ hU.2
  have hiso : ∀ a a', Di.EF (g a) (g a') = Di.EF a a' := by
    intro a a'
    have : ((Di.EF (g a) (g a') : ℤ) : ℚ) = ((Di.EF a a' : ℤ) : ℚ) := by
      rw [hEF, hEF, hg, hg, hU.1]
    exact_mod_cast this
  have hfull := GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H Di l g hiso (fun a ha => by
    obtain ⟨e, he⟩ := hhalf a ha
    exact ⟨e, hinj (by rw [hg, he, map_add, map_nsmul])⟩)
  have hfin := Di.fin
  refine GlobalTheory.GamFree.gam_free GlobalTheory.latMinkowski E r q l.M Ψ Gm (LinearMap.range φ0) γ
    (fun τ => ?_) hG ?_ ?_ l.three_le hU ?_ x hx b hb hxb
  · rw [hΨ, hΨ]; exact cmType_of_rt H τ
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map φ0
  · rw [LinearMap.coe_range]; exact hsp
  · rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := hfull a
    exact ⟨φ0 e, LinearMap.mem_range_self φ0 e, by rw [← hg, he, map_add, map_nsmul]⟩

end GlobalTheory.PrincFree
end

