import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0267
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeMetricGramMatrixLocalHolomorphicImPart
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeGramLocal

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem del_im_of_differentiableAt {F : E → ℂ} {z : E} (hF : DifferentiableAt ℂ F z) (ξ : E) :
    del (fun x => ((F x).im : ℂ)) z ξ = (1 / (2 * I)) * fderiv ℂ F z ξ := by
  have hR : DifferentiableAt ℝ F z := hF.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun x => conj (F x)) z :=
    (conjCLE : ℂ →L[ℝ] ℂ).differentiableAt.comp z hR
  have e : (fun x => ((F x).im : ℂ)) = fun x => (1 / (2 * I)) • (F x - conj (F x)) := by
    funext x; rw [im_eq_sub_conj, smul_eq_mul]; ring
  rw [e, del_const_smul _ (hR.fun_sub hc), ContinuousLinearMap.smul_apply, del_sub hR hc,
    ContinuousLinearMap.sub_apply, del_conj, dbar_eq_zero hF, del_eq_fderiv hF]
  simp

theorem ddbar_im_of_contDiffAt {F : E → ℂ} {z : E} (hF : ContDiffAt ℂ 2 F z) :
    ddbar (fun x => ((F x).im : ℂ)) z = 0 := by
  have h := leviForm_re_eq_zero (f := fun x => -I * F x) (contDiffAt_const.mul hF)
  have e : (fun x => ((F x).im : ℂ)) = fun x => (((-I * F x).re : ℝ) : ℂ) := by
    funext x; simp
  rw [e]; exact h

theorem contDiffAt_im_of_analyticAt {F : E → ℂ} {z : E} (hF : AnalyticAt ℂ F z)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (fun x => ((F x).im : ℂ)) z :=
  (ofRealCLM.comp imCLM).contDiff.contDiffAt.comp z (hF.contDiffAt.restrict_scalars ℝ)

end General

def locLog (w₀ w : ℂ) : ℂ := Complex.log (w / w₀) + Complex.log w₀

theorem exp_locLog {w₀ w : ℂ} (h0 : w₀ ≠ 0) (h : w / w₀ ∈ slitPlane) :
    exp (locLog w₀ w) = w := by
  rw [locLog, exp_add, exp_log (slitPlane_ne_zero h), exp_log h0, div_mul_cancel₀ _ h0]

theorem hasDerivAt_locLog {w₀ w : ℂ} (h : w / w₀ ∈ slitPlane) :
    HasDerivAt (locLog w₀) (1 / w₀ / (w / w₀)) w :=
  (((hasDerivAt_id w).div_const w₀).clog h).add_const _

end GlobalTheory.HodgeGramLocal

namespace GlobalTheory.HodgeGramLocal

variable {n a g : ℕ}

def locEntry (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (j k : Fin g) (x : Fin n → ℂ) : ℂ :=
  τ₀ x j k + ∑ i, locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i)) / (2 * Real.pi * I) *
    ((B i j k : ℤ) : ℂ)

theorem isOpen_polydisc (n : ℕ) : IsOpen (polydisc n 1) := by
  rw [show polydisc n 1 = ⋂ k, {z : Fin n → ℂ | ‖z k‖ < 1} by ext; simp [polydisc]]
  exact isOpen_iInter_of_finite fun k =>
    isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const

theorem hodgeGram_local (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (hP : IsPeriodChart rk τ₀ B) :
    ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧
      (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) •
        ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) +
          ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) •
            ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧
      ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by
  intro z hz
  let V : Set (Fin n → ℂ) := {x | x ∈ polydisc n 1 ∧
    ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane}
  have hVo : IsOpen V := by
    have h2 : IsOpen {x : Fin n → ℂ |
        ∀ i : Fin a, x (Fin.castLE ha i) / z (Fin.castLE ha i) ∈ slitPlane} := by
      simp only [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_slitPlane.preimage (by fun_prop)
    exact (isOpen_polydisc n).inter h2
  have hzV : z ∈ V := ⟨hz.1, fun i => by rw [div_self (hz.2 i)]; exact one_mem_slitPlane⟩
  have hV : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]

  have hterm : ∀ (j k : Fin g) (i : Fin a) (x : Fin n → ℂ), x ∈ V →
      HasFDerivAt (fun y : Fin n → ℂ => locLog (z (Fin.castLE ha i)) (y (Fin.castLE ha i)) /
        (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ))
        ((1 / z (Fin.castLE ha i) / (x (Fin.castLE ha i) / z (Fin.castLE ha i)) /
          (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k i x hx => by
      have h1 := ((hasDerivAt_locLog (hx.2 i)).div_const (2 * (Real.pi : ℂ) * I)).mul_const
        ((B i j k : ℤ) : ℂ)
      have h2 : HasFDerivAt (fun y : Fin n → ℂ => y (Fin.castLE ha i))
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
        hasFDerivAt_apply _ _
      exact h1.comp_hasFDerivAt x h2
  have hτ : ∀ j k, ∀ x ∈ V, HasFDerivAt (fun y => τ₀ y j k) (fderiv ℂ (fun y => τ₀ y j k) x) x :=
    fun j k x hx => ((hP.holo j k).differentiableAt ((isOpen_polydisc n).mem_nhds hx.1)).hasFDerivAt
  have hloc : ∀ j k, ∀ x ∈ V, HasFDerivAt (locEntry ha τ₀ B z j k)
      (fderiv ℂ (fun y => τ₀ y j k) x + ∑ i, (1 / z (Fin.castLE ha i) /
        (x (Fin.castLE ha i) / z (Fin.castLE ha i)) / (2 * Real.pi * I) * ((B i j k : ℤ) : ℂ)) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (Fin.castLE ha i)) x :=
    fun j k x hx => (hτ j k x hx).add (HasFDerivAt.fun_sum fun i _ => hterm j k i x hx)
  have hdiff : ∀ j k, DifferentiableOn ℂ (locEntry ha τ₀ B z j k) V := fun j k x hx =>
    (hloc j k x hx).differentiableAt.differentiableWithinAt
  have hF : ∀ j k, AnalyticAt ℂ (locEntry ha τ₀ B z j k) z := fun j k =>
    ReciprocityTheory.AnForm.Osgood.osgood n V _ hVo (hdiff j k) z hzV
  have heq : ∀ x ∈ V, hodgeGram ha τ₀ B x = of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) := by
    intro x hx
    have hL : ∀ i, exp ((fun i => locLog (z (Fin.castLE ha i)) (x (Fin.castLE ha i))) i) =
        x (Fin.castLE ha i) := fun i => exp_locLog (hz.2 i) (hx.2 i)
    rw [hodgeGram, ← im_period ha τ₀ B x _ hL]
    ext j k
    simp [period, locEntry, Matrix.sum_apply]
  have hev : hodgeGram ha τ₀ B =ᶠ[𝓝 z] fun x => of fun j k => ((locEntry ha τ₀ B z j k x).im : ℂ) :=
    Filter.eventually_of_mem hV heq
  have hev' : ∀ j k, (fun x => hodgeGram ha τ₀ B x j k) =ᶠ[𝓝 z]
      fun x => ((locEntry ha τ₀ B z j k x).im : ℂ) := fun j k =>
    Filter.eventually_of_mem hV fun x hx => by
      show hodgeGram ha τ₀ B x j k = _
      rw [heq x hx]; rfl
  refine ⟨fun j k => (contDiffAt_im_of_analyticAt (hF j k)).congr_of_eventuallyEq (hev' j k),
    fun ξ => ?_, fun ξ η => ?_⟩
  · rw [mdel_congr hev]
    ext j k
    simp only [mdel_apply, of_apply]
    rw [del_im_of_differentiableAt (hF j k).differentiableAt, (hloc j k z hzV).fderiv]
    simp [Matrix.sum_apply, div_self (hz.2 _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  · ext j k
    rw [mddbar_apply, ddbar_congr (hev' j k),
      ddbar_im_of_contDiffAt ((hF j k).contDiffAt)]
    rfl

end GlobalTheory.HodgeGramLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvr
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem ideal_map_eq_span_pow_uniformizer
    : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  intro V W _ _ _ _ _ _ f _ ϖ w e a I hϖ hw hfe hI
  by_cases h0 : I = ⊥
  · exfalso
    subst h0
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at hI
    exact hw.ne_zero (pow_eq_zero_iff'.mp hI).1
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hϖ
  refine ⟨b, ?_, hb⟩
  rw [hb, Ideal.map_span, Set.image_singleton, map_pow,
    Ideal.span_singleton_eq_span_singleton] at hI
  have h1 : Associated (w ^ (e * b)) (w ^ a) := by
    rw [pow_mul]
    exact (hfe.pow_pow (n := b)).symm.trans hI
  have hw0 : w ≠ 0 := hw.ne_zero
  have hwu : ¬ IsUnit w := hw.not_isUnit
  apply le_antisymm
  · exact (pow_dvd_pow_iff hw0 hwu).mp h1.dvd
  · exact (pow_dvd_pow_iff hw0 hwu).mp h1.symm.dvd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) : Frame Ψ r :=
  fun τ k a => τ.1 (u a k)

theorem col_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) (τ : Ψ) (a : Fin r) :
    col (mat (frm Ψ u) τ) a = Data.emb τ.1 (u a) := rfl

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem hermC_emb {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]

theorem im_emb_herm_self {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (x : Fin r → E) : (τ (herm G x x)).im = 0 := by
  have h2 : conj (τ (herm G x x)) = τ (herm G x x) := by
    rw [← emb_cc, HermitianTraceFormVanishing.herm_conj G hG x x]
  exact Complex.conj_eq_iff_im.1 h2

theorem dmin_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem psgn_mul_dmin {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (p0 : ℕ)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    psgn p0 i * (dmin G (frm Ψ u) τ i).re = ∏ k : Fin i, (sgn p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) k : Fin r) *
      (τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))).re) := by
  have hr : ∀ w : Fin r → E, τ.1 (herm G w w) = ((τ.1 (herm G w w)).re : ℂ) := fun w =>
    Complex.ext (by simp) (by simp [im_emb_herm_self τ.1 G hG w])
  rw [dmin_frm Ψ G u ho τ i, Finset.prod_mul_distrib, psgn, ← Fin.prod_univ_eq_prod_range]
  congr 1
  rw [Finset.prod_congr rfl (fun k _ => hr _), ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_succ {r : ℕ} (f : Fin r → ℝ) (j : Fin r) :
    ∏ k : Fin (j.succ : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) k) =
      (∏ k : Fin (j.castSucc : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) k)) * f j := by
  change ∏ k : Fin ((j : ℕ) + 1), f (Fin.castLE _ k) = (∏ k : Fin (j : ℕ), f (Fin.castLE _ k)) * f j
  rw [Fin.prod_univ_castSucc]
  rfl

theorem sign_of_mem {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hu : frm X.Ψ u ∈ X.dom) (τ : X.Ψ) (j : Fin r) :
    0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re := by
  have h1 := (hu τ).2 j.succ
  have h0 := (hu τ).2 j.castSucc
  rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ] at h1 h0
  rw [prod_succ (fun k => sgn X.p0 k * (τ.1 (herm X.Gm (u k) (u k))).re)] at h1
  exact (pos_iff_pos_of_mul_pos h1).1 h0

theorem mem_of_sign {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hd : (Matrix.of u).det ≠ 0)
    (hs : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re) : frm X.Ψ u ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have : mat (frm X.Ψ u) τ = τ.1.mapMatrix (Matrix.of u).transpose := by
      ext k a; rfl
    rw [this, ← RingHom.map_det, Matrix.det_transpose]
    exact (map_ne_zero τ.1).2 hd
  · rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ]
    exact Finset.prod_pos fun k _ => hs τ _

end

end GlobalTheory.OrthoFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBot
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory.QSA

theorem infinitePlace_completion_nhdsNE_neBot : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), (𝓝[≠] (0 : w.Completion)).NeBot := by
  intro F _ _ w
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  have h2 : ‖(2 : w.Completion)‖ = 2 := by
    have := (AddMonoidHomClass.isometry_iff_norm _).1 hiso (2 : w.Completion)
    rw [← this, map_ofNat]; simp
  letI : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by rw [h2]; norm_num⟩ }
  exact NormedField.nhdsNE_neBot (0 : w.Completion)
end GlobalTheory.QSA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveTraceGaloisData
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.TorsorTrace

theorem injective_trace_galoisData : ∀ (F D : Type) [CommRing F] [CommRing D] [Algebra F D] (q : ℕ) [NeZero q]
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[F] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor F D q act →
    Function.Injective (algebraMap F D) ∧
    (∃ τ : D →ₗ[F] F, ∀ d : D, algebraMap F D (τ d) = ∑ g, act g d) ∧
    ∃ (n : ℕ) (x y : Fin n → D), ∀ g, ∑ i, x i * act g (y i) = if g = 1 then 1 else 0 := by
  intro F D _ _ _ q _ act h
  obtain ⟨_, _, hff, hbij⟩ := h
  have hinj : Function.Injective (algebraMap F D) := FaithfulSMul.algebraMap_injective F D
  refine ⟨hinj, ?_, ?_⟩
  · have hex : ∀ d : D, ∃ c : F, algebraMap F D c = ∑ g, act g d := by
      intro d
      have hfix : ∀ k, act k (∑ g, act g d) = ∑ g, act g d := by
        intro k
        rw [map_sum]
        refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ ?_
        intro g
        simp [map_mul]
      have h1 : (∑ g, act g d) ⊗ₜ[F] (1 : D) = (1 : D) ⊗ₜ[F] (∑ g, act g d) := by
        apply hbij.1
        rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
          map_one, map_one, mul_one, one_mul]
        funext k
        exact (hfix k).symm
      have := (Algebra.IsEffective.of_faithfullyFlat F D (∑ g, act g d)).1 (by
        rw [Algebra.TensorProduct.includeLeftSubRight_apply, h1, sub_self])
      obtain ⟨c, hc⟩ := this
      exact ⟨c, hc⟩
    choose t ht using hex
    refine ⟨{ toFun := t, map_add' := ?_, map_smul' := ?_ }, ht⟩
    · intro a b
      apply hinj
      simp [ht, Finset.sum_add_distrib]
    · intro a b
      apply hinj
      rw [RingHom.id_apply, smul_eq_mul, map_mul, ht, ht, ← Algebra.smul_def, Finset.smul_sum]
      simp
  · obtain ⟨z, hz⟩ := hbij.2 (fun g => if g = 1 then 1 else 0)
    obtain ⟨n, x, y, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    refine ⟨n, x, y, fun g => ?_⟩
    have := congrFun hz g
    rw [map_sum, Finset.sum_apply] at this
    exact this

end GlobalTheory.TorsorTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB
section
open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def intInd (n d : ℕ) : Matrix (Fin n) (Fin d) k → ℂ := Set.indicator {Y | ∀ i j, Y i j ∈ 𝒪[k]} 1

def diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : GL (Fin n) k := SplitFlip.diagGL fun i => if i = i0 then x else 1

def cosetRep {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T : Fin d → SplitFlip.Res k 1) : Matrix (Fin n) (Fin d) k :=
  Matrix.of fun i j => if i = i0 then -((ϖ : k)⁻¹ * ((Quotient.out (T j) : 𝒪[k]) : k)) else 0

theorem intInd_mem_SB (n d : ℕ) : intInd k n d ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k) := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isCompact_intMatrix
  have ho : IsOpen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := SplitFlip.isOpen_intMatrix
  have hW : IsClopen {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} := ⟨hc.isClosed, ho⟩
  refine ⟨?_, HasCompactSupport.intro' hc hW.isClosed fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]}
  · filter_upwards [hW.isOpen.mem_nhds hx] with y hy
    simp only [Set.mem_setOf_eq] at hx
    simp [intInd, Set.indicator_apply, hy, hx]
  · filter_upwards [hW.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx hy
    simp [intInd, Set.indicator_apply, hy, hx]

theorem intInd_zero (n d : ℕ) : intInd k n d 0 = 1 :=
  Set.indicator_of_mem (show (0 : Matrix (Fin n) (Fin d) k) ∈ {Y | ∀ i j, Y i j ∈ 𝒪[k]} from
    fun _ _ => zero_mem _) _

theorem det_diagAt {n : ℕ} (x : kˣ) (i0 : Fin n) : Matrix.GeneralLinearGroup.det (diagAt x i0) = x := by
  rw [diagAt, SplitFlip.det_diagGL, Fintype.prod_eq_single i0 (fun i hi => if_neg hi), if_pos rfl]

theorem diagAt_val {n : ℕ} (x : kˣ) (i0 : Fin n) :
    (diagAt x i0).val = Matrix.diagonal fun i => if i = i0 then (x : k) else 1 := by
  rw [diagAt, SplitFlip.diagGL_val]
  congr 1; funext i; split_ifs <;> simp

end GlobalTheory.HeisUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableHeckeTermDecayIntegrand
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermDecay

noncomputable section
namespace GlobalTheory.HeckeTwo.TermDecay

theorem continuous_qZ (σ : ℂ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) : Continuous (qZ σ a b m y) := by
  unfold qZ
  have h1 : Continuous fun t : ℝ => ((t : ℂ) + (y : ℂ) * I) ^ (-a) :=
    (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).zpow₀ (-a)
      fun t => Or.inl (GlobalTheory.HeckeTwo.TermSmooth.u_ne hy t)
  have h2 : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ)) ^ (-σ - (b : ℂ)) :=
    (by fun_prop : Continuous fun t : ℝ => (((t ^ 2 + y ^ 2 : ℝ) : ℂ))).cpow continuous_const
      fun t => Complex.ofReal_mem_slitPlane.2 (by positivity)
  exact (h1.mul h2).mul continuous_const

theorem norm_qZ (σ : ℂ) (a : ℤ) (b m : ℕ) {y : ℝ} (hy : y ≠ 0) (t : ℝ) :
    ‖qZ σ a b m y t‖ = (t ^ 2 + y ^ 2) ^ (-((a : ℝ) / 2 + b + σ.re)) * |y| ^ m := by
  have hQ : 0 < t ^ 2 + y ^ 2 := by positivity
  have hnu : ‖(t : ℂ) + (y : ℂ) * I‖ = Real.sqrt (t ^ 2 + y ^ 2) := by
    rw [← Complex.normSq_add_mul_I, Complex.norm_def]
  unfold qZ
  rw [norm_mul, norm_mul, norm_zpow, hnu, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_eq_rpow, ← Real.rpow_intCast,
    ← Real.rpow_mul hQ.le, ← Real.rpow_add hQ]
  congr 2
  simp
  ring

theorem integrable_qZ : ∀ σ ∈ halfPlane, ∀ (a : ℤ) (b m : ℕ), 2 ≤ a + 2 * b → ∀ y : ℝ, y ≠ 0 →
    MeasureTheory.Integrable (qZ σ a b m y) := by
  intro σ hσ a b m hab y hy
  have hσ' : -1 / 2 < σ.re := hσ
  set e : ℝ := (a : ℝ) / 2 + b + σ.re with he
  have hab' : (2 : ℝ) ≤ a + 2 * b := by exact_mod_cast hab
  have he1 : 1 / 2 < e := by rw [he]; linarith
  set κ := min 1 (y ^ 2) with hκ
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  refine (((integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := 2 * e) (by simp; linarith)).const_mul
    (κ ^ (-e) * |y| ^ m))).mono' (continuous_qZ σ a b m hy).aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun t => ?_)
  rw [norm_qZ σ a b m hy t]
  have hQk : κ * (1 + ‖t‖ ^ 2) ≤ t ^ 2 + y ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    have h1 : κ ≤ 1 := min_le_left _ _
    have h2 : κ ≤ y ^ 2 := min_le_right _ _
    nlinarith [sq_nonneg t]
  have hA : (t ^ 2 + y ^ 2) ^ (-e) ≤ κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2) := by
    rw [show -(2 * e) / 2 = -e by ring, ← Real.mul_rpow hκ0.le (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hQk (by linarith)
  calc (t ^ 2 + y ^ 2) ^ (-e) * |y| ^ m ≤ (κ ^ (-e) * (1 + ‖t‖ ^ 2) ^ (-(2 * e) / 2)) * |y| ^ m :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = _ := by ring

end GlobalTheory.HeckeTwo.TermDecay
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFormsEqSpanIntegralRationalFormsStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralForms_eq_span_integralRationalForms : ∀ (LL Ks WL G0 : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G0) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ), A.IsKsForm → (∀ u : J0, ∀ f ∈ A.WK, A.ρ u f ∈ A.WK) → (∀ u : J0, ((A.chi u * lam0 u : LLˣ) : LL) ∈ Set.range (algebraMap Ks LL)) → A.Mall J0 lam0 = Submodule.span (𝓞 LL) {y | y ∈ A.MK ∧ y ∈ A.typeP J0 lam0} := by
  first | exact @GlobalTheory.mall_eq_span_rat | exact GlobalTheory.mall_eq_span_rat | (intros; apply GlobalTheory.mall_eq_span_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspacesStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_maps_eigenspaces : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ ρ' : Λ → Matrix (Fin h) (Fin h) O) (X : Matrix (Fin h) (Fin h) O), (∀ l, X * ρ l = ρ' l * X) → (∀ σ : Λ →+* O, (eig C ρ σ).map (Matrix.toLin' (X.map (algebraMap O C))) ≤ eig C ρ' σ) ∧ ((⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) → ∀ σ : Λ →+* O, LinearMap.range (Matrix.toLin' (X.map (algebraMap O C))) ⊓ eig C ρ' σ = (eig C ρ σ).map (Matrix.toLin' (X.map (algebraMap O C)))) := by
  first | exact @GlobalTheory.DetInv.eig_map_equivariant | exact GlobalTheory.DetInv.eig_map_equivariant | (intros; apply GlobalTheory.DetInv.eig_map_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartSpecMapCompStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineCombinationInChart_specMap_comp : ∀ (Y : Scheme.{0}) (V : Y.Opens) (S S' : Type) [CommRing S] [CommRing S'] (g : S →+* S') (ι : Type) [Fintype ι]
    (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), GlobalTheory.SecGlue.IsCombIn V u c w a →
    GlobalTheory.SecGlue.IsCombIn V (spMap g ≫ u) (spMap g ≫ c) (fun i => spMap g ≫ w i) (fun i => g (a i)) := by
  first | exact @GlobalTheory.SecGlue.isCombIn_spMap_comp | exact GlobalTheory.SecGlue.isCombIn_spMap_comp | (intros; apply GlobalTheory.SecGlue.isCombIn_spMap_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineCombinationInChartUniqueStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineCombinationInChart_unique : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V → ∀ (S : Type) [CommRing S] (ι : Type) [Fintype ι]
    (u c c' : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    GlobalTheory.SecGlue.IsCombIn V u c w a → GlobalTheory.SecGlue.IsCombIn V u c' w a → c = c' := by
  first | exact @GlobalTheory.SecGlue.combIn_unique | exact GlobalTheory.SecGlue.combIn_unique | (intros; apply GlobalTheory.SecGlue.combIn_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassTorsionQCoefficientsStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients : ∀ (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N) (k : ℕ), 0 < M → M • x = 0 → IsIntegral ℤ ((M : ℂ) ^ 2 * cB N x k) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * cD N x k) ∧ IsIntegral ℤ (12 * (M : ℂ) ^ 2 * cP N x k) ∧ IsIntegral ℤ (12 * cG N k) := by
  first | exact @GlobalTheory.WpFam.isIntegral_coefficients | exact GlobalTheory.WpFam.isIntegral_coefficients | (intros; apply GlobalTheory.WpFam.isIntegral_coefficients <;> assumption)
end

