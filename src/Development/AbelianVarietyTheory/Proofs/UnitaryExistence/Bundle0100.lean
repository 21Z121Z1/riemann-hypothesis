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
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SelfDualLatticeOccurs
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem GlobalTheory.selfDual_lattice_occurs : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)) (f : ℕ → Dw.La →ₗ[𝓞 E] Λ'), l.A = 1 → σ' (baseKA l).ρ = H.rt0 → IsTypeFn H Dw.p Dw.q ty → ModelBase M → (∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm v y) = n) ↔ v ∈ Λ') → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ v, f (n * m) a = f n a + n • v) → (∀ n : ℕ, 0 < n → (∀ a, (∃ v, f n a = n • v) ↔ ∃ v, a = n • v) ∧ ∀ a', ∃ a v, a' = f n a + n • v) → (∀ n : ℕ, 0 < n → ∀ a a', ∃ z : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm (f n a) (f n a')) - (Dw.EF a a' : ℤ) = n * z) → ∃ (k : Fin F.n) (γ : GL (Fin r) E), (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ (∀ v, v ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ (M.X k).Λ) ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ (M.X k).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f l.M a : Fin r → E) = (M.φ k (F.t k a) : Fin r → E) + l.M • w := by
  intro hH E _ _ _ H Dw l Xo σ' g ty F r M ξ₀ Gm φ Λ' f hA hσ hty hM hk hφ hfg hsp hsd hc hb hi
  have hξ : cc (-ξ₀) = -(-ξ₀) := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg, h]
  obtain ⟨D', φ', hp, hq, hr, hφ'⟩ := GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice E H Dw r (-ξ₀) Gm φ Λ' hξ hφ hfg hsp hsd
  let e : D'.La ≃ₗ[𝓞 E] Λ' := (LinearEquiv.ofInjective φ' hφ'.1).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ x, φ' (e.symm x) = (x : Fin r → E) := fun x => by
    have : ∀ y, ((e y : Λ') : Fin r → E) = φ' y := fun y => rfl
    rw [← this, e.apply_symm_apply]
  obtain ⟨k, gam, hg1, hg2⟩ := GlobalTheory.allClassesSt_of_hasseNorm hH E H Dw l Xo σ' g ty F hA hσ hty D'
    (fun n => e.symm.toLinearMap ∘ₗ f n) hp hq
    ⟨fun n m hn hm a => by
      obtain ⟨v, hv⟩ := hc n m hn hm a
      exact ⟨e.symm v, by simp [hv]⟩,
     fun n hn => ⟨fun a => by
      rw [← (hb n hn).1 a]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨e v, ?_⟩
        rw [← map_nsmul, ← hv]
        simp
      · rintro ⟨v, hv⟩
        exact ⟨e.symm v, by simp [hv]⟩,
      fun a' => by
        obtain ⟨a, v, hv⟩ := (hb n hn).2 (e a')
        refine ⟨a, e.symm v, ?_⟩
        apply e.injective
        simp [hv]⟩⟩
    (fun n hn a a' => by
      obtain ⟨z, hz⟩ := hi n hn a a'
      refine ⟨z, ?_⟩
      have h := hφ'.2.2.2.2 (e.symm (f n a)) (e.symm (f n a'))
      rw [he, he] at h
      rw [← h] at hz
      exact_mod_cast hz)
  let ψ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hψ : ∀ a, ψ a = (M.φ k a : Fin r → E) := fun a => rfl
  have hrange : Set.range ψ = ((M.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (M.φ k a).2
    · intro hv
      exact ⟨(M.φ k).symm ⟨v, hv⟩, by rw [hψ, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨γ, hγ1, hγ2⟩ := GlobalTheory.T.exists_unitary_matrix_of_lattice_isometry E H D' (F.Di k) r (-ξ₀) Gm φ' ψ gam hξ hφ'
    ⟨Subtype.val_injective.comp (M.φ k).injective, by rw [hrange]; exact (M.X k).Λ_span, hφ.2.2.1, hφ.2.2.2.1,
      fun x y => by
        have h := hM.ef k x y
        rw [(hk k).1, (hk k).2] at h
        exact h⟩ hg1
  refine ⟨k, γ, hγ1, fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun a ha => ?_⟩
  · have h := hγ2 (e.symm ⟨v, hv⟩)
    rw [he] at h
    rw [← h]
    exact (M.φ k _).2
  · have h := hγ2 (gam.symm ((M.φ k).symm ⟨_, hv⟩))
    rw [LinearEquiv.apply_symm_apply, hψ, LinearEquiv.apply_symm_apply] at h
    have h2 := congrArg (fun w => ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    rw [h2, ← hr]
    exact LinearMap.mem_range_self _ _
  · obtain ⟨w, hw⟩ := hg2 a ha
    refine ⟨M.φ k w, (M.φ k w).2, ?_⟩
    have h := hγ2 (e.symm (f l.M a))
    rw [he] at h
    rw [← h]
    change ψ (gam ((e.symm.toLinearMap ∘ₗ f l.M) a)) = ψ (F.t k a) + l.M • ψ w
    rw [hw, map_add, map_nsmul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.ThetaPtChg

theorem exists_chart_point {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  let q : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hq : p q ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
  refine ⟨j, fun q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [this]
  exact hj

theorem val_of_secBC (hS : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    (x x' : Sp ℂ ⟶ Xo.X) (hx : x' = x) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ)
    (h : SecBC (RingHom.id ℂ) a x x' s s') (p : Over.mk x ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι) (v v' : ℂ)
    (hv : ∀ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = p.left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = v)
    (hv' : ∀ pt : Sp ℂ ⟶ Gx x', pt ≫ gxFst x' = p.left → pt ≫ gxSnd x' = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) = v') : v' = a * v := by
  subst hx
  have hid : x' = spMap (RingHom.id ℂ) ≫ x' := by
    simp [spMap]
  have h2 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) x' x' x' hid hid).2.1
    a s s').1 h
  let pt : Sp ℂ ⟶ Gx x' := (CartesianMonoidalCategory.lift (𝟙 (Over.mk x')) p).left
  have e1 : pt ≫ gxFst x' = p.left := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk x')) p)
    exact this
  have e2 : pt ≫ gxSnd x' = 𝟙 (Sp ℂ) := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk x')) p)
    exact this
  rw [← hv pt e1 e2, ← hv' pt e1 e2]
  exact (congrArg (valAt' pt ((PPx x').U (fun _ => j))) (h2 (fun _ => j))).trans
    ((GlobalTheory.sec_values_complex_fibre hS E H Dw l Xo x' s).1 a _ pt e2)

theorem thetaPt_change : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsThetaPt T b κ y → IsThetaPt T b' κ' y' → ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) → (∀ a, T.Pf (T.co b') (gam a) = h₀ *ᵥ T.Pf (T.co b) a) → y'.x = y.x ∧ (∀ τ i, IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (h₀⁻¹ *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) ∧ ∃ t₀ : (CAt σ)ˣ, SecBC (RingHom.id (CAt σ)) (t₀ : CAt σ) y.x y'.x y.s y'.s ∧ toC (t₀ : CAt σ) ^ 2 * (κ ^ 2 * (T.h b').det * h₀.det) = κ' ^ 2 * (T.h b).det := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y y' gam h₀ hy hy' hgam hP
  obtain ⟨hg1, hg2, hg3⟩ := hgam
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k
    (T.Pf (T.co b)) (T.Pf (T.co b')) gam h₀ hp hp' hg1 hg2 hg3 hP
  have hx : y'.x = y.x := hy'.1.trans (hu.symm.trans hy.1.symm)
  refine ⟨hx, fun τ i => ?_, ?_⟩
  · refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k (T.Pf (T.co b)) hp k (T.Pf (T.co b')) (Matrix.mulVecLin h₀) hp'
      hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy'.2.1 τ i
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y y').1 hx
  refine ⟨a, hbc, ?_⟩
  obtain ⟨hhd, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨z, hz⟩ : ∃ z, T.h b *ᵥ z = w :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hhd, Matrix.one_mulVec]⟩
  obtain ⟨j, hj⟩ := exists_chart_point Xo.univ.t.PP.isLB (F.ex k (T.Pf (T.co b)) z).left
  have hmult := GlobalTheory.thetaFrame_det_mul_sq_invariant_uncond E H Dw l Xo _ g _ F k T.m (T.co ⁻¹' (M.X k).dom)
    (fun b => T.Pf (T.co b)) T.bas T.h T.ta T.c₁ T.c₂ T.fr (fun b hb => T.isPer _ hb) T.sympl T.adapt
    (fun b hb => (T.norm b hb).2.2.2) T.half₁ T.half₂ T.fr_hol T.fr_ne T.fr_coc T.fr_rig T.fr_sec
    b hb b' hb' gam h₀ hg1 hg2 hg3 hP j z hj
  have hne : thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) ≠ 0 :=
    mul_ne_zero (by rw [hz]; exact hw) (T.fr_ne j b z hb hj)
  have hw0 : (F.ex k (T.Pf (T.co b)) z).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) :=
    (Over.w (F.ex k (T.Pf (T.co b)) z)).trans hy.1.symm
  have hval := val_of_secBC hS (Xo := Xo) y.x y'.x hx y.s y'.s (toC (a : CAt σ)) hbc
    (Over.homMk (F.ex k (T.Pf (T.co b)) z).left hw0) j _ _
    (fun pt h1 h2 => hy.2.2 j z pt h1 h2 hj)
    (fun pt h1 h2 => hy'.2.2 j (h₀ *ᵥ z) pt (h1.trans (hex z).symm) h2 (by rw [hex z]; exact hj))
  apply mul_right_cancel₀ (pow_ne_zero 2 hne)
  rw [mul_assoc κ', mul_assoc κ] at hval
  generalize thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) = S at *
  generalize thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ (h₀ *ᵥ z)) * T.fr j (b', h₀ *ᵥ z) = S' at *
  linear_combination (-κ' ^ 2) * hmult - (T.h b').det * h₀.det * (κ' * S' + toC (a : CAt σ) * (κ * S)) * hval

end GlobalTheory.ThetaPtChg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.WeightZeroValue

open GlobalTheory.Frames GlobalTheory.NonDominant Polynomial

theorem poly_const (P Q : ℂ[X]) (h : ∀ c : ℂ, c ≠ 0 → P.eval c = Q.eval c⁻¹) (s : ℂ) : P.eval s = P.eval 0 := by
  have h0 : P - C (Q.coeff 0) = 0 := by
    refine poly_eq_zero _ Q.divX 1 one_pos 1 fun c hc => ?_
    have e := congrArg (eval c⁻¹) (Polynomial.X_mul_divX_add Q)
    rw [eval_add, eval_mul, eval_X, eval_C] at e
    rw [eval_sub, eval_C, h c hc, ← e]
    field_simp
    ring
  rw [sub_eq_zero.1 h0, eval_C, eval_C]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def Keeps (σ : c.F →+* ℂ) (f : Rul Xo c) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) : Prop :=
  ∀ y y' : FrPt Xo c (CAt σ), FrChg (S := CAt σ) g 1 y y' → evR Xo c f y' = evR Xo c f y

theorem Keeps.mul {f : Rul Xo c} {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ}
    (hg : Keeps σ f g) (hg' : Keeps σ f g') (hu : ∀ τ, IsUnit (g τ).det) (hu' : ∀ τ, IsUnit (g' τ).det) :
    Keeps σ f fun τ => g τ * g' τ := fun y y' h => by
  obtain ⟨y₁, h₁, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y g' 1 hu'
  obtain ⟨y₂, h₂, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y₁ g 1 hu
  have h₃ := (frChg_refl_and_comp E H Dw l Xo c _ y y₁ y₂).2 _ _ _ _ h₁ h₂
  rw [Units.val_one, _root_.mul_one] at h₃
  have e : y₂ = y' := (existsUnique_frChg E H Dw l Xo c (CAt σ) y (fun τ => (g τ * g' τ : Matrix _ _ ℂ)) 1
    (fun τ => show IsUnit (g τ * g' τ).det by rw [Matrix.det_mul]; exact (hu τ).mul (hu' τ))).unique h₃ h
  rw [← e, hg _ _ h₂, hg' _ _ h₁]

theorem evR_bor {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {t : Ix Dw → (CAt σ)ˣ} {y y' : FrPt Xo c (CAt σ)}
    (h : FrBor t y y') : evR Xo c f y' = evR Xo c f y := by
  have e : ex Dw 0 0 = 0 := funext fun i => by cases i <;> rfl
  rw [evR_weight hf h, e]
  simp [wchar]

theorem keeps_lower {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ} (h0 : ∀ τ i j, i < j → g τ i j = 0)
    (hd : ∀ τ i, g τ i i ≠ 0) : Keeps σ f g := fun y y' h => by
  let t : Ix Dw → ℂˣ := fun i => match i with
    | none => 1
    | some p => Units.mk0 _ (hd p.1 p.2)
  exact evR_bor (t := t) hf (((frBor_calculus E H Dw l Xo c _ y y' y').1 t).2 ⟨g, h0, fun _ _ => rfl, h⟩)

open Classical in

def only {R : Type} [CommRing R] (τ : E →+* ℂ) (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) :
    ∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) R := Function.update (fun _ => 1) τ M

section Only

variable {R : Type} [CommRing R] {τ : E →+* ℂ}

theorem only_self (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) : only τ M τ = M := by simp [only]

theorem only_of_ne (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) {ρ : E →+* ℂ} (h : ρ ≠ τ) :
    only τ M ρ = 1 := by
  unfold only
  exact @Function.update_of_ne _ _ (fun a b => Classical.propDecidable (a = b)) _ _ h _ _

theorem only_det {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R} (hM : IsUnit M.det) (ρ : E →+* ℂ) :
    IsUnit (only τ M ρ).det := by
  by_cases h : ρ = τ
  · subst h; rwa [only_self]
  · simp [only_of_ne _ h]

theorem only_mul (M N : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) :
    (fun ρ => only τ M ρ * only τ N ρ) = only τ (M * N) := funext fun ρ => by
  by_cases h : ρ = τ
  · subst h; simp [only_self]
  · simp [only_of_ne _ h]

theorem only_map (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R[X]) (s : R) :
    (fun ρ => (only τ M ρ).map (eval s)) = only τ (M.map (eval s)) := funext fun ρ => by
  by_cases h : ρ = τ
  · subst h; simp [only_self]
  · simp [only_of_ne _ h]

end Only

theorem keeps_only_lower {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ}
    {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ} (h0 : ∀ i j, i < j → M i j = 0) (hd : ∀ i, M i i ≠ 0) :
    Keeps σ f (only τ M) := by
  refine keeps_lower hf (fun ρ i j hij => ?_) fun ρ i => ?_
  · by_cases h : ρ = τ
    · subst h; rw [only_self]; exact h0 i j hij
    · rw [only_of_ne _ h, Matrix.one_apply_ne hij.ne]
  · by_cases h : ρ = τ
    · subst h; rw [only_self]; exact hd i
    · simp [only_of_ne _ h]

theorem keeps_upper {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ} {i j : Fin (Dw.mult τ)} (hij : i < j)
    (r : ℂ) : Keeps σ f (only τ (Matrix.transvection i j r)) := fun y y' hy' => by
  have hT : ∀ s : CAt σ, (Matrix.transvection i j (X : (CAt σ)[X])).map (eval s) = Matrix.transvection i j s :=
    fun s => by
      ext k m
      simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        eval_add]
      split_ifs <;> simp
  have hsw : ∀ {R : Type} [CommRing R], IsUnit (Matrix.swap R i j).det := fun {R} _ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (Matrix.swap_mul_self i j))
  have hTd : ∀ {R : Type} [CommRing R] (s : R), IsUnit (Matrix.transvection i j s).det := fun s => by
    rw [Matrix.det_transvection_of_ne _ _ hij.ne]; exact isUnit_one
  obtain ⟨P, hP⟩ := exists_poly hf y (only τ (Matrix.transvection i j X)) (only_det (hTd _))
  obtain ⟨w, hw, -⟩ := existsUnique_frChg E H Dw l Xo c _ y (only τ (Matrix.swap _ i j)) 1 (only_det hsw)
  obtain ⟨Q, hQ⟩ := exists_poly hf w (only τ (Matrix.transvection i j X)) (only_det (hTd _))
  simp only [only_map, hT] at hP hQ
  have hc := poly_const P Q (fun s hs => by
    obtain ⟨B, hB, hBd, hBe⟩ := transvection_eq hij s hs
    obtain ⟨y₁, hy₁, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) w
      (only τ (Matrix.transvection i j (s⁻¹ : ℂ))) 1 (only_det (hTd _))
    have hBu : IsUnit B.det := by
      have := hTd s
      rw [← hBe, Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_left this
    obtain ⟨y₂, hy₂, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y₁ (only (R := CAt σ) τ B) 1 (only_det hBu)
    have e3 := keeps_only_lower (σ := σ) hf hB (fun k => by
      rw [hBd k]; split_ifs <;> simp [hs]) y₁ y₂ hy₂
    have h1 := (frChg_refl_and_comp E H Dw l Xo c _ y w y₁).2 _ _ _ _ hw hy₁
    rw [only_mul (R := CAt σ) (Matrix.transvection i j (s⁻¹ : ℂ))] at h1
    have h2 := (frChg_refl_and_comp E H Dw l Xo c _ y y₁ y₂).2 _ _ _ _ h1 hy₂
    rw [only_mul (R := CAt σ) B, Units.val_one, _root_.mul_one, _root_.mul_one] at h2
    have e1 : evR Xo c f y₂ = P.eval s :=
      hP s y₂ ((congrArg (fun M => FrChg (only (R := CAt σ) τ M) 1 y y₂) hBe).mp h2)
    have e2 : evR Xo c f y₁ = Q.eval (s⁻¹ : ℂ) := hQ _ y₁ hy₁
    exact e1.symm.trans (e3.trans e2)) r
  have h0 := hP 0 y (by
    have : only τ (Matrix.transvection i j (0 : CAt σ)) = fun _ => 1 := by simp [only]
    rw [this]
    exact (frChg_refl_and_comp E H Dw l Xo c _ y y y).1)
  exact (hP r y' hy').trans (hc.trans h0.symm)

theorem keeps_only {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ}
    (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hM : M.det ≠ 0) : Keeps σ f (only τ M) := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => Keeps σ f (only τ M)) M hM
    (fun d hd => ?_) (fun t => ?_) fun A B hA hB kA kB => ?_
  · rw [Matrix.det_diagonal] at hd
    exact keeps_only_lower hf (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne) fun i => by
      rw [Matrix.diagonal_apply_eq]; exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ i)
  · rcases lt_or_gt_of_ne t.hij with h | h
    · exact keeps_upper hf h t.c
    · refine keeps_only_lower hf (fun k m hkm => ?_) fun k => ?_
      · rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hkm.ne,
          Matrix.single_apply_of_ne, add_zero]
        rintro ⟨rfl, rfl⟩
        exact absurd h (not_lt.2 hkm.le)
      · rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq,
          Matrix.single_apply_of_ne, add_zero]
        · exact one_ne_zero
        · rintro ⟨h1, h2⟩
          exact t.hij (h1.trans h2.symm)
  · rw [← only_mul]
    exact kA.mul kB (only_det hA.isUnit) (only_det hB.isUnit)

theorem keeps_all {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hg : ∀ τ, IsUnit (g τ).det) :
    Keeps σ f g := by
  classical
  have key : ∀ s : Finset (E →+* ℂ), Keeps σ f fun ρ => if ρ ∈ s then g ρ else 1 := fun s => by
    induction s using Finset.induction_on with
    | empty => exact keeps_lower hf (fun τ i j hij => by simp [Matrix.one_apply_ne hij.ne]) fun τ i => by simp
    | insert τ s hτ ih =>
      have := (keeps_only (σ := σ) hf (g τ) (hg τ).ne_zero).mul ih (only_det (hg τ)) fun ρ => by
        split_ifs
        · exact hg ρ
        · simp
      convert this using 2 with ρ
      by_cases h : ρ = τ
      · subst h; simp [only_self, hτ]
      · simp [only_of_ne _ h, h]
  simpa using key Finset.univ

theorem evR_eq_of_same_point {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {y y' : FrPt Xo c (CAt σ)} (h : y'.x = y.x) :
    evR Xo c f y' = evR Xo c f y := by
  obtain ⟨g, s, hg, hzw⟩ := (frChg_exists_unique E H Dw l Xo c _ y y').1 h
  obtain ⟨z1, h1, -⟩ := existsUnique_frChg E H Dw l Xo c _ y g 1 hg
  obtain ⟨z2, h2, -⟩ := existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
  have h3 := (frChg_refl_and_comp E H Dw l Xo c _ y z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
  have e : z2 = y' := (existsUnique_frChg E H Dw l Xo c _ y g s hg).unique h3 hzw
  let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
    | none => s
    | some _ => 1
  rw [← e, evR_bor (t := t) hf (((frBor_calculus E H Dw l Xo c _ z1 z2 z2).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩)]
  exact keeps_all hf g hg y z1 h1

theorem evR_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ), ∀ f ∈ sec Xo c 0 0, ∀ (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((τ : ℂ →+* ℂ).comp σ))), y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x → Formalism.L2.PjFree.toC (evR Xo c f y') = τ (Formalism.L2.PjFree.toC (evR Xo c f y)) := by
  intro E _ _ _ H D l Xo c σ τ f hf y y' h
  let φ : CAt σ →ₐ[c.F] CAt ((τ : ℂ →+* ℂ).comp σ) := { (τ : ℂ →+* ℂ) with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c _ _ φ y
  rw [evR_eq_of_same_point hf (h.trans hz.1.symm), evR_map hf φ hz]
  rfl

end GlobalTheory.WeightZeroValue
end
end

