import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameAdjointnessSeriesTrivial
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFrameOfIsPeriod
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBFr
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0037
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameAdjointnessSeriesTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFrame_adjointness_series_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → (∀ a : 𝓞 E, star a = H.bar a) → ∀ e : ∀ m, FrTy y g Φ.jx m, Φ.IsAnE e → ∀ a : 𝓞 E, ∃ wL : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)]) (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet ℂ (Fin 2 × Fin g) m)ˣ, (u : Jet ℂ (Fin 2 × Fin g) m) = psJet m ((anFB ty).ad a) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wL (lift (jpt y g Φ.jx m (0 : Fin 2)) (jpt y g Φ.jx m (1 : Fin 2))).left) (pe y g Φ.jx e m ![fun j => psIn g m ![0] ((anFB ty).A.act a j), fun j => MvPolynomial.X ((1 : Fin 2), j)])) (scaleGen _ _ (unitΓ u) (pe y g Φ.jx e m ![fun j => MvPolynomial.X ((0 : Fin 2), j), fun j => psIn g m ![1] ((anFB ty).A.act (H.bar a) j)])) := by
  first | exact @GlobalTheory.AnValAd.adjoint_series_trivial | exact GlobalTheory.AnValAd.adjoint_series_trivial | (intros; apply GlobalTheory.AnValAd.adjoint_series_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompInj

open ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.Frames
open scoped Matrix ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem dom_nonempty {r : ℕ} (X : Data E r) : ∃ x, x ∈ X.dom := by
  choose P hP0 hP using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP0 τ, fun i => ?_⟩⟩
  apply GlobalTheory.PeriodOnto.lminor_sign
  have h1 : GlobalTheory.PeriodOnto.sgnMat r X.p0 * gram τ.1 X.Gm (mat (fun τ => P τ) τ) = 1 := by
    change GlobalTheory.PeriodOnto.sgnMat r X.p0 * gram τ.1 X.Gm (P τ) = 1
    rw [hP, GlobalTheory.PeriodOnto.sgnMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    unfold sgn
    split_ifs <;> simp
  rw [h1]
  exact Matrix.PosDef.one

theorem im_eq_of_span {g : ℕ} {Λ : Type} (P : Λ → Fin g → ℂ) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (A B : Matrix (Fin g) (Fin g) ℂ) (h : ∀ x y, (hermForm A (P x) (P y)).im = (hermForm B (P x) (P y)).im)
    (z z' : Fin g → ℂ) : (hermForm A z z').im = (hermForm B z z').im := by
  have hz : z ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  have hz' : z' ∈ Submodule.span ℝ (Set.range P) := by rw [hspan]; trivial
  unfold hermForm at *
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, rfl⟩ := hz
    induction hz' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact h x y
    | zero => simp
    | add _ _ _ _ h1 h2 =>
      simp only [star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im, h1, h2]
    | smul c _ _ h1 =>
      simp only [star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im, h1]
  | zero => simp
  | add _ _ _ _ h1 h2 => simp only [add_dotProduct, Complex.add_im, h1, h2]
  | smul c _ _ h1 => simp only [smul_dotProduct, Complex.smul_im, h1]

theorem not_im_neg (H : Host E) (D : Datum H) {r : ℕ} (hr : 1 ≤ r) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La → (Fin r → E)) (Ψ : Finset (E →+* ℂ))
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) {g : ℕ} (idx : Fin g ≃ Ψ × Fin r)
    (ty : Fin g → (E →+* ℂ)) (q : ℕ) (hξ : cc ξ = -ξ) (hG : ∀ a b, cc (Gm a b) = Gm b a)
    (hEF : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y)))
    (x : Frame Ψ r) (hx : x ∈ GG Ψ Gm q) (P : D.La →+ (Fin g → ℂ))
    (hP : ∀ v k, P v k = GlobalTheory.FramePeriod.locPer (idx k).1.1 Gm q (mat x (idx k).1) (Data.emb (idx k).1.1 (φ v))
      (idx k).2) (hper : IsPeriod D ty P) (hneg : ∀ τ ∈ Ψ, (τ ξ).im < 0) : False := by
  classical
  obtain ⟨-, -, -, hspan, Hm, -, hpos, hIm⟩ := hper
  choose Hl hH hp hI using fun τ : Ψ =>
    (GlobalTheory.FramePeriod.exists_loc τ.1 Gm hG q (mat x τ) (hx τ).1 (hx τ).2).2
  have hblk : ∀ v (τ : Ψ), (fun a => P v (idx.symm (τ, a))) =
      GlobalTheory.FramePeriod.locPer τ.1 Gm q (mat x τ) (Data.emb τ.1 (φ v)) := by
    intro v τ
    funext a
    rw [hP, idx.apply_symm_apply]
  have key := im_eq_of_span P hspan Hm (Matrix.of fun k l => if (idx k).1 = (idx l).1 then
      ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ) * Hl (idx k).1 (idx k).2 (idx l).2 else 0) (by
    intro v w
    rw [GlobalTheory.FramePeriod.hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.im_sum, hIm]
    have h1 : ((D.EF v w : ℤ) : ℝ) = ((Algebra.trace ℚ E (ξ * herm Gm (φ v) (φ w)) : ℚ) : ℝ) := by
      rw [← hEF]; simp
    rw [h1, GlobalTheory.FramePeriod.trace_re Ψ hcm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hblk, hblk, Complex.im_ofReal_mul, hI, map_mul, ← hermC_emb]
    have h2 : (τ.1 ξ).re = 0 := by
      have h3 := congrArg Complex.re (emb_cc τ.1 ξ)
      rw [hξ, map_neg, Complex.neg_re, Complex.conj_re] at h3
      linarith
    rw [Complex.mul_re, h2]
    ring)
  have hI' : ∀ (A : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ),
      (hermForm A (Complex.I • z) z).im = (hermForm A z z).re := by
    intro A z
    simp [hermForm]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
    by_cases h : ComplexEmbedding.conjugate σ ∈ Ψ
    · exact ⟨_, h⟩
    · exact ⟨σ, (hcm σ).2 h⟩
  have hz : (fun _ => 1 : Fin g → ℂ) ≠ 0 := fun h => by
    simpa using congrFun h (idx.symm (⟨τ, hτ⟩, ⟨0, hr⟩))
  have h1 := key (Complex.I • fun _ => 1) (fun _ => 1)
  rw [hI', hI', GlobalTheory.FramePeriod.hermForm_block idx (fun τ : Ψ => 2 * (τ.1 ξ).im) Hl, Complex.re_sum] at h1
  have h2 := hpos _ hz
  rw [h1] at h2
  refine absurd h2 (not_lt.2 (Finset.sum_nonpos fun t _ => ?_))
  rw [Complex.re_ofReal_mul]
  have h3 := hp t (fun _ => 1) (fun h => by simpa using congrFun h ⟨0, hr⟩)
  have h4 := hneg t.1 t.2
  nlinarith

variable {H : Host E} {Dw : Datum H} {l : Level H}

theorem exists_idx {c : Coeff l} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {r g : ℕ} (hr : r = Dw.p + Dw.q)
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (X : Data E r) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) :
    ∃ idx : Fin g ≃ X.Ψ × Fin r, (∀ j, relab c σ (e j).1 =
      if ((idx j).2 : ℕ) < Dw.q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧
      ∀ (x : Frame X.Ψ r) (v : Fin r → E) j, perFr X x v (relab c σ (e j).1) (e j).2 =
        if ((idx j).2 : ℕ) < Dw.q then hermC (idx j).1.1 X.Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v)
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
  refine ⟨idx, fun j => ?_, fun x v j => ?_⟩
  · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
    · rw [if_neg (by omega), b]
    · rw [if_pos (by omega), b, hcc]
  · have h := hi j
    generalize idx j = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rw [← hp0] at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dif_pos a, dif_pos hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dif_neg a, dif_pos (show conjEmb (relab c σ (e j).1) ∈ X.Ψ from hτ), dif_pos hn]
      rfl

theorem exists_frame {c : Coeff l} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {r g : ℕ} (h1 : 1 ≤ r)
    (hr : r = Dw.p + Dw.q) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (X : Data E r) (hp0 : X.p0 = Dw.q)
    (hty : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) (D : Datum H) (hp : D.p = Dw.p) (hq : D.q = Dw.q)
    (φ : D.La ≃ₗ[𝓞 E] X.Λ)
    (hEF : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ a : Fin r → E) (φ b)))
    (x₀ : Frame X.Ψ r) (hx₀ : x₀ ∈ X.dom) (P₀ : D.La →+ (Fin g → ℂ))
    (hP₀ : ∀ a j, P₀ a j = perFr X x₀ (φ a : Fin r → E) (relab c σ (e j).1) (e j).2)
    (hper₀ : IsPeriod D (fun j => relab c σ (e j).1) P₀) (P : D.La →+ (Fin g → ℂ))
    (hper : IsPeriod D (fun j => relab c σ (e j).1) P) :
    ∃ x ∈ X.dom, ∀ a j, P a j = perFr X x (φ a : Fin r → E) (relab c σ (e j).1) (e j).2 := by
  obtain ⟨idx, hi, hper'⟩ := exists_idx hσ hr e X hp0 hty
  have hξ : cc (-X.ξ0) = -(-X.ξ0) := by
    have h := X.ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  have hpos : ∀ τ ∈ X.Ψ, 0 < (τ (-X.ξ0)).im := by
    rcases X.κ0_xi with h | h
    · intro τ hτ
      have := X.κ0_sign ⟨τ, hτ⟩
      rw [h, map_mul, map_ofNat] at this
      rw [map_neg, Complex.neg_im]
      simp at this
      linarith
    · exfalso
      refine not_im_neg H D h1 (-X.ξ0) X.Gm (fun a => (φ a : Fin r → E)) X.Ψ X.cmType idx _ Dw.q hξ X.Gm_herm hEF
        x₀ (hp0 ▸ hx₀) P₀ (fun v k => by rw [hP₀, hper']; rfl) hper₀ fun τ hτ => ?_
      have := X.κ0_sign ⟨τ, hτ⟩
      rw [h, map_neg, map_mul, map_ofNat] at this
      rw [map_neg, Complex.neg_im]
      simp at this
      linarith
  let ψ : D.La →ₗ[𝓞 E] (Fin r → E) := X.Λ.subtype ∘ₗ φ.toLinearMap
  have hψ : Set.range ψ = (X.Λ : Set (Fin r → E)) := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact (φ a).2
    · intro hy
      exact ⟨φ.symm ⟨y, hy⟩, by simp [ψ]⟩
  obtain ⟨x, hx, hPx⟩ := GlobalTheory.exists_frame_of_isPeriod E H D r (-X.ξ0) X.Gm ψ X.Ψ hty g idx _
    (by rw [hq]; exact hi) hξ hpos
    ⟨fun a b hab => φ.injective (Subtype.ext hab), by rw [hψ]; exact X.Λ_span, X.Gm_herm, X.Gm_det, hEF⟩
    (by rw [hp, hq]; exact hr) P hper
  refine ⟨x, by rw [hq, ← hp0] at hx; exact hx, fun a j => ?_⟩
  rw [hper', hPx, hq]
  rfl

theorem frBor_of_eq {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (y y' : FrPt Xo c S) (hx : y'.x = y.x) (hu : ∀ τ i, y'.u τ i = y.u τ i) :
    ∃ t : Ix Dw → Sˣ, FrBor t y y' := by
  obtain ⟨g, a, h⟩ := Model.exists_frChg y y' hx
  have ha := Model.FrChg.isUnit h
  refine ⟨fun k => Option.elim k ha.unit (fun _ => 1), (Model.frBor_iff _ _ _).2 ⟨fun _ => 1, fun τ i => ?_,
    fun τ i j hij => Matrix.one_apply_ne hij.ne, hx, fun τ i => ?_, h.2.2⟩⟩
  · exact Matrix.one_apply_eq i
  · rw [hu]
    exact (GlobalTheory.Reg.BorelGroupoid.chg_refl y).2.1 τ i

end GlobalTheory.CompInj

namespace GlobalTheory

open CompInj

theorem card_comp_le_periodSpaces : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty), IsTypeFn H D.p D.q ty ∧ Fintype.card U.Comp ≤ F.n := by
  intro _ E _ _ _ H D l Xo c σ r U h1 hσ hU
  obtain ⟨hr, hX, -, hfib, -, g, e, F, ik, φ, hEF, hP⟩ := hU
  refine ⟨g, _, F, (GlobalTheory.Relab.relab_good E H l c σ hσ).2.2.2 D g e, ?_⟩
  suffices hinj : Function.Injective ik by simpa using Fintype.card_le_of_injective ik hinj
  intro k k' hk
  obtain ⟨x, hx⟩ := dom_nonempty (U.X k)
  obtain ⟨x₀, hx₀⟩ := dom_nonempty (U.X k')
  obtain ⟨P, -, hper, hpt, hder, -⟩ := hP k ⟨x, hx⟩
  obtain ⟨P₀, hP₀, hper₀, -⟩ := hP k' ⟨x₀, hx₀⟩
  have hP' := fun y => (hP k' y).imp fun _ h => (⟨h.1, h.2.2.1, h.2.2.2.1⟩ : _ ∧ _ ∧ _)
  have hEF' := hEF k'
  generalize φ k' = ψ at hP₀ hP' hEF'
  clear hP hEF φ
  generalize ik k' = n at *
  subst hk
  obtain ⟨x', hx', hPx⟩ := exists_frame hσ h1 hr e (U.X k') (hX k').1 (hX k').2 _ (F.sig _).1 (F.sig _).2 ψ hEF'
    x₀ hx₀ P₀ hP₀ hper₀ P hper
  obtain ⟨P', hP', hpt', hder'⟩ := hP' ⟨x', hx'⟩
  obtain rfl : P = P' := by
    ext a j
    rw [hPx, hP']
  have hbor := frBor_of_eq (U.un k ⟨x, hx⟩) (U.un k' ⟨x', hx'⟩) (hpt'.trans hpt.symm) fun τ i =>
    ((GlobalTheory.isDerivAt0_ex_isTanAt E H D l Xo _ g _ F _ P hper).2.1 _).unique (hder' τ i) (hder τ i)
  obtain ⟨γ, -, b, -, h⟩ := (hfib k k' _ _).1 hbor
  exact (congrArg Sigma.fst h).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesCubeDefectAlongChartOverRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

noncomputable section

namespace GlobalTheory.ChartFrames

section Alg

variable {S Ix : Type} [CommRing S]

theorem nilpotent_of_le (m : ℕ) (I : Ideal (Jet S Ix m))
    (h : ∀ p : MvPolynomial Ix S, Ideal.Quotient.mk _ p ∈ I → p ∈ orig S Ix) : IsNilpotent I := by
  refine ⟨m + 1, le_bot_iff.1 ?_⟩
  have h1 : I ≤ Ideal.map (Ideal.Quotient.mk (orig S Ix ^ (m + 1))) (orig S Ix) := by
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.mem_map_of_mem _ (h p ha)
  refine (Ideal.pow_right_mono h1 _).trans ?_
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem trunc_surj (m : ℕ) :
    Function.Surjective ((jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) : Jet S Ix (m + 1) →+* Jet S Ix m) := by
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

theorem trunc_nil (m : ℕ) : IsNilpotent
    (RingHom.ker ((jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) : Jet S Ix (m + 1) →+* Jet S Ix m)) :=
  nilpotent_of_le _ _ fun p hp => by
    have : Ideal.Quotient.mk (orig S Ix ^ (m + 1)) p = 0 := hp
    exact Ideal.pow_le_self (Nat.succ_ne_zero m) (Ideal.Quotient.eq_zero_iff_mem.1 this)

theorem aug_surj (m : ℕ) : Function.Surjective ((jetAug : Jet S Ix m →ₐ[S] S) : Jet S Ix m →+* S) :=
  fun a => ⟨algebraMap S _ a, (jetAug : Jet S Ix m →ₐ[S] S).commutes a⟩

theorem aug_nil (m : ℕ) : IsNilpotent (RingHom.ker ((jetAug : Jet S Ix m →ₐ[S] S) : Jet S Ix m →+* S)) :=
  nilpotent_of_le _ _ fun p hp => by
    have h1 : MvPolynomial.aeval (fun _ => (0 : S)) p = 0 := hp
    have h2 : MvPolynomial.constantCoeff p = 0 := by simpa using h1
    simpa [h2] using sub_const_mem_orig p

variable (d : ℕ)

theorem aug_axis0 (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (axis0 d m) = jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  fin_cases i <;> simp [jetSubstP, jetMap_mk, jetAug_X]

theorem aug_axis1 (m : ℕ) : (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S).comp (axis1 d m) = jetAug := by
  apply jet_hom_ext
  rintro ⟨i, j⟩
  fin_cases i <;> simp [jetSubstP, jetMap_mk, jetAug_X]

theorem trunc_axis0 (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (axis0 d (m + 1)) =
    (axis0 d m).comp (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _) := by
  apply jet_hom_ext
  intro p
  rfl

theorem trunc_axis1 (m : ℕ) : (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] _).comp (axis1 d (m + 1)) =
    (axis1 d m).comp (jetTrunc : Jet S (Fin 2 × Fin d) (m + 1) →ₐ[S] _) := by
  apply jet_hom_ext
  intro p
  rfl

theorem aug_trunc (m : ℕ) : (jetAug : Jet S Ix m →ₐ[S] S).comp (jetTrunc : Jet S Ix (m + 1) →ₐ[S] _) = jetAug := by
  apply jet_hom_ext
  intro p
  rfl

theorem cancel₀ {U : Type} [CommGroup U] (a b : U) : a * b⁻¹ * a⁻¹ * b = 1 := by
  rw [mul_right_comm a, mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

theorem cancel₁ {U : Type} [CommGroup U] (a b : U) : a * a⁻¹ * b⁻¹ * b = 1 := by
  rw [mul_inv_cancel, _root_.one_mul, inv_mul_cancel]

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem exists_norm {T : Over X0} (p q : T ⟶ t.G) (s₁ s₂ s₀ : T ⟶ T)
    (h₁ : s₁ ≫ (p * q) = p) (h₂ : s₂ ≫ (p * q) = q) (h₀ : s₀ ≫ (p * q) = 1)
    (g₁ : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (p * q).left) (fun _ => 1))) (hg₁ : g₁.IsGen) :
    ∃ e : LB.Gen (LB.LinComb t.PP.L (cφG t ![p, q]) (cε 2)), e.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good t.PP.L z J →
        val e r z J = val g₁ r z J * (val g₁ (r ≫ s₁.left) z J)⁻¹ * (val g₁ (r ≫ s₂.left) z J)⁻¹ *
          val g₁ (r ≫ s₀.left) z J := by
  obtain ⟨e, he, hv⟩ := exists_gen t.PP.isLB (φ' := cφG t ![p, q]) (ε' := cε 2) (fun U _ h => by
      have hc := prod_cube2 t.G (fun w : T ⟶ t.G => h w.left) ![p, q]
      refine Eq.trans ?_ hc.symm
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, ← Over.comp_left, h₁, h₂, h₀,
        Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one, zpow_neg, zpow_one]
      ac_rfl)
    (LB.mulGen t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ g₁
      (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ g₁ s₁.left))) (LB.invGen t.PP.L _ _ (LB.pullGen t.PP.L _ _ g₁ s₂.left)))
      (LB.pullGen t.PP.L _ _ g₁ s₀.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hg₁
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg₁ _)))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg₁ _))) (DVR.pullGen_isGen _ _ _ _ hg₁ _))
  refine ⟨e, he, fun Z r z J hJ => (hv Z r z J hJ).trans ?_⟩
  rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_pull hJ, val_pull hJ]

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

theorem exists_tower {Ix : Type} (P : ∀ m, overAt x0 (Jet S Ix m) ⟶ t.G)
    (h0 : Formalism.L2.Pj.homAt x0 (jetAug : Jet S Ix 0 →ₐ[S] S) ≫ P 0 = 1)
    (htr : ∀ m, Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m) ≫ P (m + 1) = P m) :
    ∃ g₁ : ∀ m, LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1)), (∀ m, (g₁ m).IsGen) ∧
      ∀ m (Z : Scheme.{0}) (r : Z ⟶ (overAt x0 (Jet S Ix m)).left) (z : Z) (J), Good t.PP.L z J →
        val (g₁ (m + 1)) (r ≫ (Formalism.L2.Pj.homAt x0 (jetTrunc : Jet S Ix (m + 1) →ₐ[S] Jet S Ix m)).left) z J =
          val (g₁ m) r z J := by
  obtain ⟨g0, hg0, -⟩ := GlobalTheory.NilGen.exists_gen_lift_of_isNilpotent t.G.left t.PP.L t.PP.isLB (Jet S Ix 0) S _ (aug_surj 0) (aug_nil 0)
    PUnit.{1} (fun _ => (P 0).left) (fun _ => 1) PUnit.{1} (fun _ => (overAt x0 S).hom ≫ eSec t.G) (fun _ => 1)
    (LB.pullGen t.PP.L (fun _ : PUnit.{1} => eSec t.G) (fun _ => 1) t.PP.rig (overAt x0 S).hom)
    (DVR.pullGen_isGen _ _ _ _ t.PP.rigGen _) (fun U _ h => by
      have := congrArg Over.Hom.left h0
      exact Finset.prod_congr rfl fun k _ => congrArg (fun w => h w ^ (1 : ℤ)) this)
  have step := fun m (g : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1))) (hg : g.IsGen) =>
    GlobalTheory.NilGen.exists_gen_lift_of_isNilpotent t.G.left t.PP.L t.PP.isLB (Jet S Ix (m + 1)) (Jet S Ix m) _ (trunc_surj m) (trunc_nil m)
      PUnit.{1} (fun _ => (P (m + 1)).left) (fun _ => 1) PUnit.{1} (fun _ => (P m).left) (fun _ => 1) g hg
      (fun U _ h => by
        have := congrArg Over.Hom.left (htr m)
        exact Finset.prod_congr rfl fun k _ => congrArg (fun w => h w ^ (1 : ℤ)) this)
  choose f hf hc using step
  let g₁ : ∀ m, {g : LB.Gen (LB.LinComb t.PP.L (fun _ : PUnit.{1} => (P m).left) (fun _ => 1)) // g.IsGen} :=
    fun m => Nat.rec ⟨g0, hg0⟩ (fun m g => ⟨f m g.1 g.2, hf m g.1 g.2⟩) m
  refine ⟨fun m => (g₁ m).1, fun m => (g₁ m).2, fun m Z r z J hJ => ?_⟩
  exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (hc m (g₁ m).1 (g₁ m).2) r)

end Geo

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber S) ⟶ t.G.left)) (uvec : κ → Fin d → S) (x : ∀ m, jOG x0 d m 1 ⟶ t.G), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ a j, MvPowerSeries.constantCoeff (act a j) = 0) → IsChartG t x0 d F act tg uvec x → ∃ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) ∧ FrTrunc t x0 d x e ∧ FrAxes t x0 d x e := by
  intro E _ _ _ H X0 t S _ x0 d F act κ _ tg uvec x _ _ hch

  let c : ∀ m, Fin 2 → (jOG x0 d m 2 ⟶ jOG x0 d m 1) := fun m i => Formalism.L2.Pj.homAt x0 (jetCopy d m i)
  let a0 : ∀ m, jOG x0 d m 1 ⟶ jOG x0 d m 2 := fun m => Formalism.L2.Pj.homAt x0 (axis0 d m)
  let a1 : ∀ m, jOG x0 d m 1 ⟶ jOG x0 d m 2 := fun m => Formalism.L2.Pj.homAt x0 (axis1 d m)
  let o : ∀ m n, overAt x0 S ⟶ jOG x0 d m n := fun m n => Formalism.L2.Pj.homAt x0 jetAug
  let u : ∀ m n, jOG x0 d m n ⟶ overAt x0 S := fun m n => Formalism.L2.Pj.homAt x0 (Algebra.ofId S _)
  let tr : ∀ m n, jOG x0 d m n ⟶ jOG x0 d (m + 1) n := fun m n => Formalism.L2.Pj.homAt x0 jetTrunc
  have a0c0 : ∀ m, a0 m ≫ c m 0 = u m 1 ≫ o m 1 := fun m => by
    simp only [a0, c, u, o, homAt_comp, first_axis_at_first_copy]
  have a0c1 : ∀ m, a0 m ≫ c m 1 = 𝟙 _ := fun m => by
    simp only [a0, c, homAt_comp, first_axis_at_second_copy, homAt_id]
  have a1c0 : ∀ m, a1 m ≫ c m 0 = 𝟙 _ := fun m => by
    simp only [a1, c, homAt_comp, second_axis_at_first_copy, homAt_id]
  have a1c1 : ∀ m, a1 m ≫ c m 1 = u m 1 ≫ o m 1 := fun m => by
    simp only [a1, c, u, o, homAt_comp, second_axis_at_second_copy]
  have oa0 : ∀ m, o m 1 ≫ a0 m = o m 2 := fun m => by
    simp only [a0, o, homAt_comp, aug_axis0]
  have oa1 : ∀ m, o m 1 ≫ a1 m = o m 2 := fun m => by
    simp only [a1, o, homAt_comp, aug_axis1]
  have oc : ∀ m i, o m 2 ≫ c m i = o m 1 := fun m i => by
    simp only [c, o, homAt_comp, aug_copy]
  have a0u : ∀ m, a0 m ≫ u m 2 = u m 1 := fun m => by
    simp only [a0, u, homAt_comp, Algebra.comp_ofId]
  have a1u : ∀ m, a1 m ≫ u m 2 = u m 1 := fun m => by
    simp only [a1, u, homAt_comp, Algebra.comp_ofId]
  have tru : ∀ m, tr m 2 ≫ u (m + 1) 2 = u m 2 := fun m => by
    simp only [tr, u, homAt_comp, Algebra.comp_ofId]
  have otr : ∀ m, o m 2 ≫ tr m 2 = o (m + 1) 2 := fun m => by
    simp only [tr, o, homAt_comp, aug_trunc]
  have trc : ∀ m i, tr m 2 ≫ c (m + 1) i = c m i ≫ tr m 1 := fun m i => by
    simp only [tr, c, homAt_comp, copy_trunc]
  have tra0 : ∀ m, tr m 1 ≫ a0 (m + 1) = a0 m ≫ tr m 2 := fun m => by
    simp only [tr, a0, homAt_comp, trunc_axis0]
  have tra1 : ∀ m, tr m 1 ≫ a1 (m + 1) = a1 m ≫ tr m 2 := fun m => by
    simp only [tr, a1, homAt_comp, trunc_axis1]
  have ox : ∀ m, o m 1 ≫ x m = 1 := hch.zero
  have trx : ∀ m, tr m 1 ≫ x (m + 1) = x m := hch.trunc
  have hj : ∀ m i, jptG t x0 d x m i = c m i ≫ x m := fun _ _ => rfl
  obtain ⟨g₁, hg₁, hg₁t⟩ := exists_tower t x0
    (fun m => jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2))
    (by
      change o 0 2 ≫ _ = _
      simp only [hj, MonObj.comp_mul, reassoc_of% (oc 0), ox, _root_.mul_one])
    (fun m => by
      change tr m 2 ≫ _ = _
      simp only [hj, MonObj.comp_mul, reassoc_of% (trc m), trx])
  have key := fun m => exists_norm t (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))
    (c m 0 ≫ a1 m) (c m 1 ≫ a0 m) (u m 2 ≫ o m 2)
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (a1c0 m), reassoc_of% (a1c1 m), ox,
      MonObj.comp_one, _root_.mul_one])
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (a0c0 m), reassoc_of% (a0c1 m), ox,
      MonObj.comp_one, _root_.one_mul])
    (by simp only [hj, MonObj.comp_mul, Category.assoc, reassoc_of% (oc m), ox, MonObj.comp_one, _root_.mul_one])
    (g₁ m) (hg₁ m)
  choose e he hv using key
  refine ⟨e, he, fun m => corr_of_val t.PP.isLB fun y J hJ => ?_, fun m => ⟨corr_of_val t.PP.isLB fun y J hJ => ?_,
    corr_of_val t.PP.isLB fun y J hJ => ?_⟩⟩
  · refine (val_pull hJ _ _ _).trans ((hv (m + 1) _ _ y J hJ).trans (Eq.trans ?_ (hv m _ _ y J hJ).symm))
    have e1 : ∀ (s : jOG x0 d m 2 ⟶ jOG x0 d m 2) (s' : jOG x0 d (m + 1) 2 ⟶ jOG x0 d (m + 1) 2),
        tr m 2 ≫ s' = s ≫ tr m 2 →
        val (g₁ (m + 1)) ((𝟙 _ ≫ (tr m 2).left) ≫ s'.left) y J = val (g₁ m) (𝟙 _ ≫ s.left) y J := by
      intro s s' hs
      rw [Category.assoc, ← Over.comp_left, hs, Over.comp_left, ← Category.assoc]
      exact hg₁t m _ _ y J hJ
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (hg₁t m _ _ y J hJ)
      (congrArg _ (e1 _ _ ?_))) (congrArg _ (e1 _ _ ?_))) (e1 _ _ ?_)
    · simp only [Category.assoc, reassoc_of% (trc m), tra1]
    · simp only [Category.assoc, reassoc_of% (trc m), tra0]
    · simp only [Category.assoc, reassoc_of% (tru m), otr]
  · refine (val_pull hJ _ _ _).trans ((hv m _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    change val (g₁ m) (𝟙 _ ≫ (a0 m).left) y J * (val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J)⁻¹ *
      (val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J)⁻¹ * val (g₁ m) ((𝟙 _ ≫ (a0 m).left) ≫ _) y J = 1
    simp only [Category.id_comp, ← Over.comp_left, reassoc_of% (a0c0 m), reassoc_of% (a0c1 m), reassoc_of% (a0u m), oa1]
    exact cancel₀ _ _
  · refine (val_pull hJ _ _ _).trans ((hv m _ _ y J hJ).trans (Eq.trans ?_ (val_one _).symm))
    change val (g₁ m) (𝟙 _ ≫ (a1 m).left) y J * (val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J)⁻¹ *
      (val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J)⁻¹ * val (g₁ m) ((𝟙 _ ≫ (a1 m).left) ≫ _) y J = 1
    simp only [Category.id_comp, ← Over.comp_left, reassoc_of% (a1c0 m), reassoc_of% (a1c1 m), reassoc_of% (a1u m), oa0]
    exact cancel₁ _ _

end GlobalTheory.ChartFrames
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentativesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_group_lattice_class_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → Dw.La, (∀ i₀, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • zz i₀ j))) ∧ (∀ i i', (∀ b, Dw.ModN (N ^ 2) (zz i b - zz i' b)) → i = i') ∧ ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → ∃ i, ∀ b, Dw.ModN (N ^ 2) (a b - zz i b) := by
  first | exact @GlobalTheory.ZCount.exists_class_representatives | exact GlobalTheory.ZCount.exists_class_representatives | (intros; apply GlobalTheory.ZCount.exists_class_representatives <;> assumption)
end

