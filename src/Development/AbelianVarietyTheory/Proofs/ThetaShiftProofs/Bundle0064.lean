import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0105
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0069

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataDescentNumberFieldStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmArcData_descent_numberField : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (σ₁ : K →+* ℂ) (σ : c.F →+* ℂ) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left) (n : ℕ), letI := H.starRing; σ₁.comp (algebraMap c.F K) = σ → 0 < n → IsPolFibre (σ₁.comp (algebraMap (𝓞 K) K)) B.pol aC.D₀.P φ → (∀ x, (aC.oa.onB.act x).left ≫ φ = φ ≫ (B.t.act.act x).left) → TauCan aC.D₀ n → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (_ : Algebra c.F K₂) (i : K →ₐ[c.F] K₂) (σ₂ : K₂ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₂ (algebraMap c.F K₂)) (p : Out.IsPullDeg σ₂ a.D₀ aC.D₀) (ψ : a.D₀.P.A.left ⟶ B.pol.A.left), σ₂.comp (i : K →+* K₂) = σ₁ ∧ InBC σ₂ a aC p ∧ TauCan a.D₀ n ∧ IsPolFibre ((i : K →+* K₂).comp (algebraMap (𝓞 K) K)) B.pol a.D₀.P ψ ∧ ∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left := by
  first | exact @GlobalTheory.ArcCM.exists_arcIn_numberField | exact GlobalTheory.ArcCM.exists_arcIn_numberField | (intros; apply GlobalTheory.ArcCM.exists_arcIn_numberField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFrBor
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries Matrix

namespace GlobalTheory.ValNorm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_idx (hσ : GoodEmb c σ) (X : Data E r) (hr : r = Dw.p + Dw.q) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j,
      (X.p0 ≤ ((idx j).2 : ℕ) ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = X.p0 + (e j).2) ∨
      (((idx j).2 : ℕ) < X.p0 ∧ conjEmb (idx j).1.1 = relab c σ (e j).1 ∧
        ((idx j).2 : ℕ) = X.p0 - 1 - (e j).2 ∧ ((e j).2 : ℕ) < X.p0)) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < X.p0 then
          hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
        else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2 := by
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv X.Ψ X.cmType Dw.p Dw.q r hr (relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ X.Ψ × Fin r, ∀ j,
      (relab c σ (e j).1 ∈ X.Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
      (relab c σ (e j).1 ∉ X.Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
        ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
  rw [← hp0] at hi
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · exact Or.inl ⟨by omega, b, c'⟩
    · exact Or.inr ⟨by omega, by rw [b]; exact hcc _, c', d⟩
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl

theorem exists_move (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (x b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) :
    ∃ h₀ : Matrix (Fin g) (Fin g) ℂ,
      (∀ v : Fin r → E, (fun j => perFr (U.X k) (rmul x b) v (relab c σ (e j).1) (e j).2) =
        h₀ *ᵥ fun j => perFr (U.X k) x v (relab c σ (e j).1) (e j).2) ∧
      (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧
      ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
        ∏ j, h₀⁻¹ j j ^ (a ((e j).1, (e j).2) + n / 2) = bchar (laU U a n k) b := by
  obtain ⟨idx, hi, hper⟩ := exists_idx hσ (U.X k) hr hp0 hty e
  obtain ⟨hbij, -, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (U.X k).p0 idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega)] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
      · omega
    · rw [if_pos a1] at h2
      rcases hi j' with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
      · omega
      · exact ⟨hbij.1 (by rw [← b1, ← b2, h1]), by omega⟩
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (U.X k).p0 idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (U.X k).p0 idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (U.X k).p0 idx b, fun v => ?_, PerBor.inv_support _ _ _ hu hs, fun a n => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (U.X k).Gm x v _ _ (fun j => hper _ _ j) (fun j => hper _ _ j)
  · unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (U.X k).Ψ) (i : Fin r) => b τ i i ^ laU U a n k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, hdiag]
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rcases hi j with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩
    · rw [if_neg (by omega), if_pos a1, b1, hinv,
        show ((idx j).2 : ℕ) - (U.X k).p0 = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
    · rw [if_pos a1, if_neg (by omega), b1, hinv,
        show (U.X k).p0 - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring

theorem exists_frBor (hσ : GoodEmb c σ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k : U.Comp) (hr : r = Dw.p + Dw.q)
    (hp0 : (U.X k).p0 = Dw.q) (hty : ∀ τ : E →+* ℂ, τ ∈ (U.X k).Ψ ↔ τ (H.rt : E) = H.rt0)
    (x : (U.X k).dom) (b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) (h : rmul x.1 b ∈ (U.X k).dom) :
    ∃ (t : Ix Dw → (CAt σ)ˣ) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)),
      FrBor t (U.un k x) (U.un k ⟨_, h⟩) ∧ FrChg G (t none : CAt σ) (U.un k x) (U.un k ⟨_, h⟩) ∧
      ∀ a n, toC (wchar (ex Dw a n) t) * bchar (laU U 0 n k) b =
        toC (t none : CAt σ) ^ n * bchar (laU U a n k) b := by
  obtain ⟨h₀, hP, htri, hw⟩ := exists_move hσ U k hr hp0 hty Uw.e x.1 b hb
  have hp := Uw.period k x
  have hp' := Uw.period k ⟨_, h⟩
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ _ _ Uw.F (Uw.ik k)
    (Uw.Pm k x) (Uw.Pm k ⟨_, h⟩) (LinearEquiv.refl _ _) h₀ hp hp' (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
    (fun a => ⟨0, by simp⟩) (fun a => by
      have e1 : Uw.Pm k x a = _ := funext (Uw.Pm_eq k x a)
      have e2 : Uw.Pm k ⟨_, h⟩ a = _ := funext (Uw.Pm_eq k ⟨_, h⟩ a)
      rw [LinearEquiv.refl_apply, e1, e2]
      exact hP _)
  obtain ⟨hy1, hy2⟩ := Uw.lie k x
  obtain ⟨hy1', hy2'⟩ := Uw.lie k ⟨_, h⟩
  have hxx : (U.un k ⟨_, h⟩).x = (U.un k x).x := hy1'.trans (hu.symm.trans hy1.symm)
  have hder : ∀ τ i, IsDerivAt0 (fun z => (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left)
      (h₀⁻¹ *ᵥ Pi.single (Uw.e.symm ⟨τ, i⟩) 1) ((U.un k ⟨_, h⟩).u τ i) := by
    intro τ i
    refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F (Uw.ik k) (Uw.Pm k x) hp (Uw.ik k)
      (Uw.Pm k ⟨_, h⟩) (Matrix.mulVecLin h₀) hp' hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy2' τ i
  obtain ⟨G, t₀, -, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) _ _).1 hxx
  have hinv : (h₀⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det h₀ hdet).ne_zero
  have hdiag := GlobalTheory.NormUnBor.diag_ne_zero Uw.e h₀⁻¹ hinv htri
  let d : Fin Uw.g → (CAt σ)ˣ := fun j => (Units.mk0 (h₀⁻¹ j j) (hdiag j) : ℂˣ)
  let t : Ix Dw → (CAt σ)ˣ := fun o => Option.elim o t₀ (fun p => d (Uw.e.symm p))
  refine ⟨t, G, ⟨hxx, fun τ i => ⟨fun i' => (h₀⁻¹ (Uw.e.symm ⟨τ, i'⟩) (Uw.e.symm ⟨τ, i⟩) : ℂ), rfl, ?_, ?_⟩, ?_⟩,
    hG, ?_⟩
  · intro j hj
    by_contra hne
    have := (htri _ _ hne).2
    rw [Uw.e.apply_symm_apply, Uw.e.apply_symm_apply] at this
    exact absurd hj (not_lt.2 this)
  · rw [hy1]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ Uw.F _ _ hp _ _ _ (hy2 τ) _ _).2 ?_
    rw [GlobalTheory.NormUnBor.col_eq_sum Uw.e h₀⁻¹ htri]
    exact hder τ i
  · obtain ⟨pm, h1, h2, h3⟩ := hG.2.2
    refine ⟨pm, h1, ?_, h3⟩
    rw [h2]
    simp [spMap]
  · intro a n
    rw [← hw a n, ← hw 0 n]
    show (∏ o : Ix Dw, toC ((t o : (CAt σ)ˣ) : CAt σ) ^ ex Dw a n o) * _ = _
    rw [Fintype.prod_option, mul_assoc]
    congr 1
    rw [← Equiv.prod_comp Uw.e, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    show h₀⁻¹ (Uw.e.symm (Uw.e j)) (Uw.e.symm (Uw.e j)) ^ a ((Uw.e j).1, (Uw.e j).2) * _ = _
    rw [Uw.e.symm_apply_apply, ← pow_add, Pi.zero_apply, zero_add]

theorem exists_unit (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ ∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1 := by
  obtain ⟨_, b, hb, hg, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun τ i => ?_⟩
  unfold dmin lminor
  rw [hg, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

end GlobalTheory.ValNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSubspaceIsometric
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

namespace GlobalTheory.AbelianLetters

open AppellHumbertTrivial

theorem mulVec_period {g : ℕ} (h τ : Matrix (Fin g) (Fin g) ℂ) (p : (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ))
    (hp : ∀ k, h.mulVec (p (Pi.single (.inl k) 1)) = Pi.single k 1 ∧
      h.mulVec (p (Pi.single (.inr k) 1)) = τ.mulVec (Pi.single k 1)) (u : Fin g ⊕ Fin g → ℤ) :
    h.mulVec (p u) = (fun i => (u (.inl i) : ℂ)) + τ.mulVec (fun i => (u (.inr i) : ℂ)) := by
  have e : ∀ (x : Fin g → ℤ), (fun i => (x i : ℂ)) = ∑ k, x k • (Pi.single k 1 : Fin g → ℂ) := fun x => by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hu : u = ∑ k, u k • (Pi.single k 1 : Fin g ⊕ Fin g → ℤ) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hu]
  rw [map_sum, Matrix.mulVec_sum, Fintype.sum_sum_type, e fun i => u (.inl i), e fun i => u (.inr i), Matrix.mulVec_sum]
  simp only [map_zsmul, Matrix.mulVec_smul, (hp _).1, (hp _).2]

theorem surjective_mulVec {g : ℕ} (h : Matrix (Fin g) (Fin g) ℂ) (e : Fin g → Fin g → ℂ)
    (he : ∀ k, h.mulVec (e k) = Pi.single k 1) : Function.Surjective h.mulVec := fun x =>
  ⟨∑ k, x k • e k, by
    rw [Matrix.mulVec_sum]
    funext i
    simp [Matrix.mulVec_smul, he, Finset.sum_apply, Pi.single_apply]⟩

theorem re_hermForm_eq {g g' : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (Hm' : Matrix (Fin g') (Fin g') ℂ)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (s : Set (Fin g → ℂ))
    (hs : ∀ p ∈ s, ∀ q ∈ s, (hermForm Hm' (F p) (F q)).im = (hermForm Hm p q).im) (z : Fin g → ℂ)
    (hz : z ∈ Submodule.span ℝ s) (hi : Complex.I • z ∈ Submodule.span ℝ s) :
    (hermForm Hm' (F z) (F z)).re = (hermForm Hm z z).re := by
  have key : ∀ p ∈ Submodule.span ℝ s, ∀ q ∈ Submodule.span ℝ s,
      (hermForm Hm' (F p) (F q)).im = (hermForm Hm p q).im := by
    intro p hp q hq
    induction hp, hq using Submodule.span_induction₂ with
    | mem_mem p q hp hq => exact hs p hp q hq
    | zero_left y _ => simp [hermForm]
    | zero_right y _ => simp [hermForm]
    | add_left x y z _ _ _ h₁ h₂ => simp only [map_add, hermForm_add_left, Complex.add_im, h₁, h₂]
    | add_right x y z _ _ _ h₁ h₂ => simp only [map_add, hermForm_add_right, Complex.add_im, h₁, h₂]
    | smul_left r x y _ _ h =>
      rw [← Complex.coe_smul, map_smul, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul,
        Complex.im_ofReal_mul, h]
    | smul_right r x y _ _ h =>
      rw [← Complex.coe_smul, map_smul, hermForm_smul_right, hermForm_smul_right, Complex.star_def, Complex.conj_ofReal,
        Complex.im_ofReal_mul, Complex.im_ofReal_mul, h]
  have := key _ hi _ hz
  rw [map_smul, hermForm_smul_left, hermForm_smul_left] at this
  simpa using this

noncomputable def piHerm {g g' : ℕ} (Hm : Matrix (Fin g') (Fin g') ℂ) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (l : Fin g' → ℂ) :
    (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun z := Real.pi * hermForm Hm (F z) l
  map_add' x y := by rw [map_add, hermForm_add_left, mul_add]
  map_smul' t x := by rw [map_smul, hermForm_smul_left, RingHom.id_apply, smul_eq_mul]; ring

noncomputable def dotForm {g : ℕ} (h : Matrix (Fin g) (Fin g) ℂ) (n : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun z := -(2 * Real.pi * Complex.I) * (n ⬝ᵥ h.mulVec z)
  map_add' x y := by rw [Matrix.mulVec_add, dotProduct_add, mul_add]
  map_smul' t x := by rw [Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul, smul_eq_mul]; ring

theorem im_eq_neg_omega {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hτ : τ.IsSymm) (u v : Fin g ⊕ Fin g → ℤ) (x : ℂ)
    (h : Real.pi * star x - -(2 * Real.pi * Complex.I) * ((fun i => (u (.inr i) : ℂ)) ⬝ᵥ
        ((fun i => (v (.inl i) : ℂ)) + τ.mulVec (fun i => (v (.inr i) : ℂ)))) =
      Real.pi * x - -(2 * Real.pi * Complex.I) * ((fun i => (v (.inr i) : ℂ)) ⬝ᵥ
        ((fun i => (u (.inl i) : ℂ)) + τ.mulVec (fun i => (u (.inr i) : ℂ))))) :
    x.im = ((-omegaStd u v : ℤ) : ℝ) := by
  have hs : (fun i => (u (.inr i) : ℂ)) ⬝ᵥ τ.mulVec (fun i => (v (.inr i) : ℂ)) =
      (fun i => (v (.inr i) : ℂ)) ⬝ᵥ τ.mulVec (fun i => (u (.inr i) : ℂ)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hτ.eq, dotProduct_comm]
  have ho : ((omegaStd u v : ℤ) : ℂ) = (fun i => (v (.inr i) : ℂ)) ⬝ᵥ (fun i => (u (.inl i) : ℂ)) -
      (fun i => (u (.inr i) : ℂ)) ⬝ᵥ (fun i => (v (.inl i) : ℂ)) := by
    simp [omegaStd, dotProduct, mul_comm]
  rw [dotProduct_add, dotProduct_add, hs] at h
  have hx : x - star x = (2 * x.im : ℝ) * Complex.I := Complex.sub_conj x
  have h2 : (2 * Real.pi * Complex.I) * (x.im : ℂ) = (2 * Real.pi * Complex.I) * ((-omegaStd u v : ℤ) : ℂ) := by
    push_cast at hx ⊢
    rw [ho]
    linear_combination -h - (Real.pi : ℂ) * hx
  exact_mod_cast mul_left_cancel₀ Complex.two_pi_I_ne_zero h2

theorem exists_subspace_isometric : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (n' : ℕ) (sB : ∀ Tt : Over (Sp ℂ), (Tt ⟶ a.D₀.P.A) → Out.GtPt a.D₀ Tt), 0 < n' → (∀ Tt b, (sB Tt b).b = b ^ n') → (∀ Tt b b', Out.GtPt.IsAdd (sB Tt b) (sB Tt b') (sB Tt (b * b'))) → (∀ (Tt Tt' : Over (Sp ℂ)) (h : Tt' ⟶ Tt) b, Out.GtPt.IsPull h.left (sB Tt b) (sB Tt' (h ≫ b))) → ∃ V : Submodule ℂ (Fin g → ℂ), (∀ z ∈ V, z ∈ Submodule.span ℝ {p | ∃ v, Ha.y v = 0 ∧ p = Ha.P₀ v}) ∧ ∀ (v : epsR ℂ ⟶ a.D₀.P.A) (ν : Out.GtPt a.D₀ (epsR ℂ)) (z : Fin g → ℂ), IsTangent v → Out.GtPt.IsPull (spMap (epsScaleR ((n' : ℂ)⁻¹))) (sB (epsR ℂ) v) ν → AnVec Ha ν z → z ∈ V ∧ ∀ (w : ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ) (x : ℝ), Ha.T < w.im → IsRiem Fu Ha.i (Ha.Pw w) Hm → Arch.IsLieNormAt a.D₀.P v (RingHom.id ℂ) x → x = Real.log (Real.pi * (hermForm Hm z z).re) / 2 := by
  intro hL hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha n sB hn hb hadd hpull
  have hT : Ha.T < ((Ha.T + 1 : ℝ) * Complex.I).im := by simp
  have hty : IsTypeFn H Dw.p Dw.q ty := by
    rw [← (Fu.sig Ha.i).1, ← (Fu.sig Ha.i).2]
    exact PeriodCompare.isTypeFn_of_isPeriod (Ha.period _ hT)
  obtain ⟨th, hth⟩ := (ThetaOverField.nonzero_generates hL hL2 ℂ a.D₀ ⟨fun _ => 0, fun _ _ => by simp⟩).2.2
  obtain ⟨Θ⟩ := T.arc_model_witness_extension hL hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha hty th hth
  obtain ⟨nn, hN, -, -, hnn, -, -⟩ := holArc_nilpotent E H Dw l Xo c σ O β Y a χ W g ty Fu Ha
  have hP : ∀ w v, Ha.y v = 0 → Ha.Pw w v = Ha.P₀ v := fun w v hv => by
    rw [Ha.Pw_eq, hN, hnn v hv, map_zero, smul_zero, add_zero]
  obtain ⟨u, hu, hu0, hum⟩ := T.exists_nonvanishing_multiplicative_ratio a.D₀ g n Ha.ex₀ sB hb hadd hpull Ha.add
  have hud := T.torusCoordinateRatio_differentiableAt_origin a.D₀ g n Ha.ex₀ _ (hb _ _) Ha.add Ha.hol_b Ha.hol_chi u hu
  have hu1 : ∀ x, u x 0 = 1 := fun x => mul_left_cancel₀ (hu0 x 0) (by simpa using (hum x 0 0).symm)
  have hue : ∀ x z, u x z = Complex.exp (fderiv ℂ (u x) 0 z) := fun x =>
    Doubling.eq_cexp_fderiv_of_map_add (hud x) (hu0 x 0) (hum x)
  obtain ⟨hz1, htor⟩ := T.torusCoordinateRatio_eq_torusCoord_over_origin a.D₀ g n Ha.ex₀ sB hb hadd hpull Ha.add
  let p : ℂ → (Fin g ⊕ Fin g → ℤ) →+ (Fin g → ℂ) := fun w => (Ha.Pw w).comp Θ.bas.toAddMonoidHom
  have hp : ∀ w v, p w v = Ha.Pw w (Θ.bas v) := fun _ _ => rfl
  let V : Submodule ℂ (Fin g → ℂ) := ⨅ x, LinearMap.ker (fderiv ℂ (u x) 0).toLinearMap
  have hV : ∀ z ∈ V, z ∈ Submodule.span ℝ {p | ∃ v, Ha.y v = 0 ∧ p = Ha.P₀ v} := by
    intro z hz
    refine Submodule.span_mono ?_ (T.mem_realSpan_periods_of_character_kernel g n Θ.S Θ.h (Θ.τ _) (p _)
      (fun k => (fderiv ℂ (u (Ha.y (Θ.bas (Pi.single (.inr k) 1)))) 0).toLinearMap) hn (Θ.pos _ hT).2 (Θ.per _)
      (fun k hk k' hk' s => ?_) (fun v hv k hk => ?_) z fun k _ => (Submodule.mem_iInf _).1 hz _)
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨_, (Θ.ker v).2 hv, hP _ _ ((Θ.ker v).2 hv)⟩
    · obtain ⟨hy, hs⟩ := (Ha.riemann (Θ.bas (Pi.single (.inl k') 1))).1 ((Θ.orth _).2 ⟨fun k => by simp, fun k hk => by
        rw [Pi.single_eq_of_ne]
        rintro ⟨rfl⟩
        exact hk hk'⟩)
      obtain ⟨x₁, h₁, -⟩ := hs s
      obtain ⟨x₂, h₂, h₃⟩ := hs (n * s)
      rw [mul_smul] at h₂
      rw [hp, hP _ _ hy]
      refine (hue _ _).symm.trans ((htor u hu _ _ h₁.1 h₂ _).trans ((h₃ _).trans ?_))
      rw [Θ.sympl]
      congr 1
      by_cases e : k' = k
      · subst e
        simp [omegaStd, Pi.single_apply]
      · simp [omegaStd, Pi.single_apply, e, Ne.symm e]
    · have hy := (Θ.ker v).2 hv
      rw [hp, hP _ _ hy]
      refine (hue _ _).symm.trans (htor u hu _ _ ((Ha.ker _).2 ⟨_, hy, rfl⟩).1 (hz1 _ ((Ha.ker _).2 ⟨n • Θ.bas v, ?_, ?_⟩)) _)
      · rw [map_nsmul, hy, smul_zero]
      · rw [map_nsmul, Nat.cast_smul_eq_nsmul]
  refine ⟨V, hV, fun v ν z hv hν hz => ?_⟩
  have hνb : ν.b.left = v.left := by rw [hν.1, hb, T.tangentVector_pow_scale_inv_eq _ v n hn hv]
  have hd : IsDerivAt0 (fun z => (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left)) z v.left := hνb ▸ hz.1
  have hzV : z ∈ V := (Submodule.mem_iInf _).2 fun x =>
    T.fderiv_torusCoordinateRatio_eq_zero_of_tangent a.D₀ g n Ha.ex₀ sB hb hadd hpull Ha.add Ha.hol_b Ha.hol_chi hn u hu hud hu1 v ν z hν hd hz.2 x
  refine ⟨hzV, ?_⟩
  rintro w Hm x hw hR ⟨P', φ, wL, η', hφ, hwL, hη, uu, Hm', χ', z', hAH, hD, rfl⟩
  have hη' : η'.left ≫ φ = v.left := by
    have e : dualMap (RingHom.id ℂ) = RingHom.id _ := RingHom.ext fun z => TrivSqZeroExt.inl_fst_add_inr_snd_eq z
    rw [hη, e]
    exact (congrArg (· ≫ v.left) (Spec.map_id _)).trans (Category.id_comp _)
  have hid : (fun z => 𝟙 (Sp ℂ) ≫ (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left)) = fun z => (show Sp ℂ ⟶ _ from (Ha.ex₀ z).b.left) :=
    funext fun z => Category.id_comp _
  obtain ⟨F, hF, hFΛ, hFd⟩ := T.exists_linearLift_additiveHolomorphic_abelian a.D₀.P P' φ hφ uu g (Out.TF (R := ℂ) ℂ) (𝟙 (Sp ℂ))
    ((Category.id_comp _).trans tf_hom) (fun z => (Ha.ex₀ z).b) (b_add Ha.add) (hid ▸ Ha.hol_b)
  obtain rfl : z' = F z := hFd z z' η' (by rw [hη']; exact hid ▸ hd) hD
  obtain ⟨fr, f₁, f₂, f₃, -, f₅⟩ := Θ.onB w hw
  obtain ⟨ρ, r₁, r₂, r₃⟩ := T.exists_entire_unit_appellHumbert_frame_ratio P'.A _ a.D₀.P.L P'.L a.D₀.P.isLB P'.isLB φ wL hwL g _ uu Hm' χ' hAH _ F
    (fun z => (hF z).trans (Category.id_comp _)) fr th _ f₁ f₂ f₃ f₅
  obtain ⟨t₁, t₂, t₃⟩ := T.thetaCharOff_ne_zero_differentiable_quasiPeriodic' g Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.pos w hw).1 (Θ.pos w hw).2 Θ.half₁ Θ.half₂ Θ.c₁_S
  have hfac : ∀ v, Ha.y (Θ.bas v) = 0 → ∃ a₁ b₁ : ℂ, a₁ ≠ 0 ∧
      (∀ z, Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec (z + p w v)) =
        a₁ * Complex.exp (dotForm Θ.h (fun i => (v (.inr i) : ℂ)) z) *
          (Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z))) ∧
      ∀ z, Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec (z + p w v)) * ρ (z + p w v) =
        b₁ * Complex.exp (piHerm Hm' F (F (p w v)) z) *
          (Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z) * ρ z) := by
    intro v hy
    obtain ⟨a₁, ha₁, ha⟩ := t₃ (fun i => v (.inl i)) (fun i => v (.inr i)) ((Θ.ker v).1 hy)
    have hl : F (p w v) ∈ uu.Λ := hFΛ _ ((Ha.ker _).2 ⟨_, hy, hP _ _ hy⟩).1
    refine ⟨a₁, χ' ⟨_, hl⟩ * Complex.exp (Real.pi / 2 * hermForm Hm' (F (p w v)) (F (p w v))), ha₁, fun z => ?_,
      fun z => ?_⟩
    · rw [Matrix.mulVec_add, mulVec_period Θ.h (Θ.τ w) (p w) (Θ.per w), ha]
      simp only [dotForm, LinearMap.coe_mk, AddHom.coe_mk]
      ring
    · rw [r₃ _ ⟨_, hl⟩ rfl, Complex.exp_add]
      simp only [piHerm, LinearMap.coe_mk, AddHom.coe_mk]
      ring
  have hθ : (fun z => Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) ≠ 0 := fun h0 => t₁ (funext fun y => by
    obtain ⟨z, rfl⟩ := surjective_mulVec Θ.h _ (fun k => (Θ.per w k).1) y
    exact (mul_eq_zero.1 (congrFun h0 z)).resolve_left Θ.κ_ne)
  have hθd : Differentiable ℂ (fun z => Θ.κ * thetaCharOff Θ.S (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) :=
    (t₂.comp (LinearMap.toContinuousLinearMap Θ.h.mulVecLin).differentiable).const_mul _
  have := re_hermForm_eq Hm Hm' F _ ?_ z (hV z hzV) (hV _ (V.smul_mem Complex.I hzV))
  · rw [← this]; rfl
  rintro _ ⟨v₁, h₁, rfl⟩ _ ⟨v₂, h₂, rfl⟩
  obtain ⟨v₁, rfl⟩ := Θ.bas.surjective v₁
  obtain ⟨v₂, rfl⟩ := Θ.bas.surjective v₂
  obtain ⟨a₁, b₁, ha₁, e₁, e₁'⟩ := hfac v₁ h₁
  obtain ⟨a₂, b₂, ha₂, e₂, e₂'⟩ := hfac v₂ h₂
  have hc := T.factor_exponent_commutator_eq_of_quasiPeriodic g _ ρ _ _ _ _ _ _ a₁ a₂ b₁ b₂ hθd hθ r₁ r₂ ha₁ ha₂ e₁ e₂ e₁' e₂'
  simp only [piHerm, dotForm, LinearMap.coe_mk, AddHom.coe_mk, mulVec_period Θ.h (Θ.τ w) (p w) (Θ.per w)] at hc
  rw [hermForm_swap hAH.1] at hc
  rw [← hP w _ h₁, ← hP w _ h₂, hR.2.2, Θ.sympl]
  exact im_eq_neg_omega _ (Θ.pos w hw).1 v₁ v₂ _ hc

end GlobalTheory.AbelianLetters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LamDegreeParameters
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

theorem GlobalTheory.ArcCM.lamDegSt_logOm₂ : Known → ∀ (D : D7) (T : Core D) (large₂ : SizeData₂ D), T.Q.Pins → GlobalTheory.LamF.LamDegSt T.Q.H large₂.logOm :=
  fun _ D T large₂ h => (GlobalTheory.LamF.lambdaBundle_conditions_iff.1 _ _ _).2 (GlobalTheory.LamF.lam_ind_len_deg.2.2 D T.Q h.1 large₂)
end

