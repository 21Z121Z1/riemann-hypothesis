import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0173
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.JPMemAwayP
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFundamentalDomainOfExtensionStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  first | exact @GlobalTheory.prod_fundamentalDomain_of_extension | exact GlobalTheory.prod_fundamentalDomain_of_extension | (intros; apply GlobalTheory.prod_fundamentalDomain_of_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureEqNormalFormRootMeasure
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RootNormal

variable {k r : ℕ}

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem det_Hpk : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem unit_det {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ _ det_Hpk).2.2 g hg).1

theorem mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ det_Hpk).1, fun a => by simp, by simp⟩, n, hn, by simp⟩

theorem twoFl_of {z z' : Fin (2 * r + k + 1) → ℂ} {n n' g : Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (h : TwoFl k r z z' (n * g * n')) : TwoFl k r z z' g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · have G := uHGroup _ _ (det_Hpk (k := k) (r := r))
    have e : g = n⁻¹ * (n * g * n') * n'⁻¹ := by
      rw [Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn.1),
        Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hn'.1)]
    rw [e]
    exact G.2.1 _ (G.2.1 _ (G.2.2 _ hn.1).2 _ h5) _ (G.2.2 _ hn'.1).2
  · rwa [gInv k r z z' h1 h2 _ (mem_S z hn) _ (mem_S z' hn')] at h6
  · unfold Dr at h7 ⊢
    rwa [dInv k r z z' h1 h2 _ (mem_S z hn) _ (mem_S z' hn')] at h7

def patEquiv (p : Point ℂ (r + 1)) (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) :
    UTin (fun a : Fin r => blockIdx p.1 a.val) ≃ rootPat p :=
  Equiv.ofBijective
    (fun q => ⟨(q.1.1.1.castSucc, q.1.1.2.castSucc), by
      simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Fin.castSucc_lt_castSucc_iff.2 q.1.2, q.2⟩⟩)
    (by
      constructor
      · rintro ⟨⟨⟨a, b⟩, h1⟩, h2⟩ ⟨⟨⟨c, d⟩, h3⟩, h4⟩ e
        simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.castSucc_inj] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · rintro ⟨⟨a, b⟩, hq⟩
        simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        obtain ⟨h1, h2⟩ := hq
        have h1' : a.val < b.val := h1
        have ha : a.val < r := by omega
        have hb : b.val < r := by
          by_contra hb
          have : b.val = r := by omega
          exact h ⟨a.val, ha⟩ (h2.trans (congrArg (blockIdx p.1) this))
        exact ⟨⟨⟨(⟨a.val, ha⟩, ⟨b.val, hb⟩), h1'⟩, h2⟩, rfl⟩)

theorem card_le (p : Point ℂ (r + 1)) (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) :
    (rootPat p).card ≤ r ^ 2 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (patEquiv p h)]
  refine (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans ?_)
  simp [sq]

theorem measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Measurable (rootCoords k r z p) := by
  refine Continuous.measurable (continuous_pi fun q => ?_)
  unfold rootCoords flagMat
  split_ifs
  · unfold Matrix.mulVec dotProduct
    simp only [Matrix.of_apply]
    fun_prop
  all_goals exact continuous_const

theorem measurable_in (β : Fin r → ℕ) :
    Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
  have : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
    refine (NCoord.cont_uEmb k r).comp (continuous_pi fun q => ?_)
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact (show Continuous (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) from this).measurable

theorem pOf_mem (q : PPar k r) : pOf k r q ∈ Nset k r :=
  (((Rad.radical k r).1 _ _).2.2.2 ((Rad.radical k r).2.1 _ _)).1

theorem pOf_e (q : PPar k r) (a : Fin r) : pOf k r q *ᵥ bvec (eI k r a) = bvec (eI k r a) :=
  ((Rad.radical k r).1 _ _).1 a

theorem pOf_inv_e (q : PPar k r) (a : Fin r) : (pOf k r q)⁻¹ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  conv_lhs => rw [← pOf_e q a]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (unit_det (pOf_mem q).1), Matrix.one_mulVec]

theorem conj_entry (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (((pOf k r q)⁻¹ * uEmb k r u * pOf k r q) *ᵥ bvec (eI k r b)) (eI k r a) = u a b := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pOf_e, UEmb.uEmb_eI, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, pOf_inv_e]
  simp [bvec, Pi.single_apply, UEmb.eI_inj, Finset.sum_apply]

theorem conj_mem {P Q g x : Mat k r} (hP : P ∈ Nset k r) (hQ : Q ∈ Nset k r) (hg : g ∈ GG k r) (hx : x ∈ Rset k r g) :
    P * x * P⁻¹ ∈ Rset k r (Q * g * P⁻¹) := by
  have N := nSubgroup k r
  refine ⟨N.2.1 _ (N.2.1 _ hP _ hx.1) _ (N.2.2 _ hP), ?_⟩
  have e : Q * g * P⁻¹ * (P * x * P⁻¹) * (Q * g * P⁻¹)⁻¹ = Q * (g * x * g⁻¹) * Q⁻¹ := by
    have hu := unit_det hP.1
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  rw [e]
  exact N.2.1 _ (N.2.1 _ hQ _ hx.2) _ (N.2.2 _ hQ)

theorem eq_map (z' : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1))
    (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) {g : Mat k r} (hg : g ∈ GG k r) (p₁ p₀ : PPar k r)
    (hN : IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g * (pOf k r p₀)⁻¹))
    (μ : Measure (Mt k r)) (c : ℝ≥0∞) (h0 : μ {x | Matrix.of x ∉ Rset k r g} = 0)
    (h1 : μ.map (rootCoords k r z' p) = c • volume) :
    μ = (c • lebR k r (fun a => blockIdx p.1 a.val)).map (conjM (pOf k r p₀)⁻¹) := by
  set β : Fin r → ℕ := fun a => blockIdx p.1 a.val with hβ
  have hu := unit_det (pOf_mem p₀).1
  let E : (rootPat p → ℂ) → (UTin β → ℂ) := fun y q => y (patEquiv p h q)
  have hE : MeasurePreserving E volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : rootPat p => ℂ) (patEquiv p h)).symm _
  have hF := measurable_in (k := k) β
  have hC := (continuous_conj (pOf k r p₀)⁻¹).measurable
  have hR := measurable_rootCoords z' p
  have key : ∀ x : Mt k r, Matrix.of x ∈ Rset k r g →
      conjM (pOf k r p₀)⁻¹ (Matrix.of.symm (uEmb k r (upperIn β (E (rootCoords k r z' p x))))) = x := by
    intro x hx
    have h2 := conj_mem (pOf_mem p₀) (pOf_mem p₁) hg hx
    rw [(GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular k r _ _ hN).1] at h2
    obtain ⟨y, hy⟩ := h2
    have hx' : Matrix.of x = (pOf k r p₀)⁻¹ * uEmb k r (upperIn β y) * pOf k r p₀ := by
      simp only at hy
      rw [hy]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    have hy' : E (rootCoords k r z' p x) = y := by
      funext q
      change flagMat k r z' (Matrix.of x) q.1.1.1.castSucc q.1.1.2.castSucc = _
      unfold flagMat fvec
      rw [dif_pos (show q.1.1.1.castSucc.val < r from q.1.1.1.2), dif_pos (show q.1.1.2.castSucc.val < r from q.1.1.2.2), hx']
      refine (conj_entry p₀ _ q.1.1.1 q.1.1.2).trans ?_
      unfold upperIn upper
      rw [dif_pos q.1.2]
      exact dif_pos q.2
    rw [hy']
    unfold conjM
    rw [Matrix.nonsing_inv_nonsing_inv _ hu]
    exact hx'.symm
  have hae : (conjM (pOf k r p₀)⁻¹ ∘ (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) ∘ E ∘
      rootCoords k r z' p) =ᵐ[μ] id := by
    refine measure_mono_null (fun x hx hx' => hx (key x hx')) h0
  have := Measure.map_congr (mβ := inferInstance) hae
  rw [Measure.map_id, ← Measure.map_map hC (hF.comp (hE.measurable.comp hR)), ← Measure.map_map hF (hE.measurable.comp hR),
    ← Measure.map_map hE.measurable hR, h1] at this
  refine this.symm.trans ?_
  congr 1
  unfold lebR
  rw [Measure.map_smul, hE.map_eq, Measure.map_smul]

theorem rootMeas_normR : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (p : Point ℂ (D.R.rS + 1)) (γ : MatKR D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS)) (θ' : ℝ), TwoFl D.R.k D.R.rS z z' γ → IsRootMeasR D z z' p γ μR → 0 ≤ θ' → 0 ≤ D.host.ka / gg D → (rootPat p).card ≤ D.R.rS ^ 2 ∧ NormR D.R.k D.R.rS γ (θ' * (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) (ENNReal.ofReal θ' • μR) := by
  intro D z z' p γ μR θ' hT hR hθ _
  obtain ⟨n, hn, n', hn', g, rfl, hZ, μ, h0, h1, rfl⟩ := hR
  have hg := twoFl_of hn hn' hT
  obtain ⟨p₁, p₀, -, hN, -, h⟩ := GlobalTheory.T.exists_radical_normalForm_pair_of_flags _ _ z z' g p hg hZ
  have N := nSubgroup D.R.k D.R.rS
  have hu₀ := unit_det (pOf_mem p₀).1
  have hu₁ := unit_det (pOf_mem p₁).1
  refine ⟨card_le p h, n * (pOf _ _ p₁)⁻¹, N.2.1 _ hn _ (N.2.2 _ (pOf_mem p₁)), pOf _ _ p₀ * n',
    N.2.1 _ (pOf_mem p₀) _ hn', _, _, hN, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu₀, Matrix.nonsing_inv_mul_cancel_left _ _ hu₁]
  · have e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)]
    have e2 : (conjM (pOf _ _ p₀ * n')⁻¹ : Mt D.R.k D.R.rS → _) = conjM n'⁻¹ ∘ conjM (pOf _ _ p₀)⁻¹ := by
      funext x
      change (pOf _ _ p₀ * n')⁻¹ * Matrix.of x * (pOf _ _ p₀ * n')⁻¹⁻¹ =
        n'⁻¹ * ((pOf _ _ p₀)⁻¹ * Matrix.of x * (pOf _ _ p₀)⁻¹⁻¹) * n'⁻¹⁻¹
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [e1, e2, eq_map z' p h hg.2.2.2.2.1 p₁ p₀ hN μ _ h0 h1,
      Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable,
      ENNReal.ofReal_mul hθ, mul_smul, Measure.map_smul (ENNReal.ofReal θ')]

end GlobalTheory.Amp.RootNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RotationInvariantMeasureUnitCircleArcStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Tube
open scoped InnerProductSpace ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rotationInvariant_measure_unitCircle_arc : ∀ (τ : Measure ℂ) (ρ : ℝ), τ Set.univ < ⊤ → τ {z | ‖z‖ ≠ 1} = 0 → (∀ u : ℂ, ‖u‖ = 1 → τ.map (fun z => u * z) = τ) → 0 < ρ → ρ ≤ Real.pi → τ ((fun θ : ℝ => Complex.exp (θ * Complex.I)) '' Metric.ball 0 ρ) = τ Set.univ * ENNReal.ofReal (ρ / Real.pi) := by
  first | exact @GlobalTheory.CircleArc.measure_arc | exact GlobalTheory.CircleArc.measure_arc | (intros; apply GlobalTheory.CircleArc.measure_arc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledSkewLatticeFundamentalDomainOfImaginaryParStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledSkewLattice_fundamentalDomain_of_imaginaryParts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  first | exact @GlobalTheory.SnMass.SkewDom.skewDom | exact GlobalTheory.SnMass.SkewDom.skewDom | (intros; apply GlobalTheory.SnMass.SkewDom.skewDom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
section
open MeasureTheory FourierTransform Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SelfDualDiagReal

theorem selfDual_of_transport {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : V → V → ℝ) (hs : ∀ x y, B x y = B y x) (T R : V ≃L[ℝ] E)
    (hR : ∀ x y, B x y = inner ℝ (T x) (R y)) (μ : Measure V) [hμ : μ.IsAddHaarMeasure]
    (a b : ℂ) (hab : a * b = 1) (haI : ∀ g : E → ℂ, ∫ x, g (T x) ∂μ = a * ∫ w, g w)
    (hbI : ∀ g : E → ℂ, ∫ x, g (R x) ∂μ = b * ∫ w, g w) :
    SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ))) := by
  refine ⟨hμ, ?_⟩
  intro Φ hΦc hΦs hint z
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab

  set ψ : E → ℂ := fun w => Φ (T.symm w) with hψdef
  set φ : E → ℂ := fun w => ψ (-w) with hφdef
  have hφc : Continuous φ := hΦc.comp (T.symm.continuous.comp continuous_neg)
  have hφs : HasCompactSupport φ :=
    (hΦs.comp_homeomorph T.symm.toHomeomorph).comp_homeomorph (Homeomorph.neg E)
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  have hψφ : 𝓕⁻ ψ = 𝓕 φ := Real.fourierInv_eq_fourier_comp_neg ψ

  have hhat : ∀ y, ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ
      = a * 𝓕⁻ ψ (R y) := by
    intro y
    have h := haI (fun w => ψ w * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ w (R y) : ℝ) : ℂ)))
    simp only [hψdef, ContinuousLinearEquiv.symm_apply_apply] at h
    simp_rw [hR]
    rw [h, Real.fourierInv_eq']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hint' : Integrable (fun y => 𝓕⁻ ψ (R y)) μ := by
    have h2 : (fun y => 𝓕⁻ ψ (R y)) = fun y => a⁻¹ *
        ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ := by
      funext y
      rw [hhat y, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    rw [h2]
    exact hint.const_mul _
  obtain ⟨c, -, -, hiff⟩ := GlobalTheory.exists_pos_integral_comp_equiv_haar R μ
  have hFi : Integrable (𝓕 φ) := by
    rw [← hψφ]
    exact (hiff _).1 hint'
  have hinv : 𝓕⁻ (𝓕⁻ ψ) = φ := by
    rw [hψφ]
    exact hφc.fourierInv_fourier_eq hφi hFi
  have hsym : ∀ y, B y z = inner ℝ (R y) (T z) := fun y => by
    rw [hs, hR, real_inner_comm]
  have hlast : ∫ u, 𝓕⁻ ψ u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))
      = 𝓕⁻ (𝓕⁻ ψ) (T z) := by
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  calc _ = ∫ y, (fun u => a * (𝓕⁻ ψ u *
          Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ)))) (R y) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [hhat y, hsym y, mul_assoc]
    _ = b * ∫ u, a * (𝓕⁻ ψ u *
          Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))) :=
          hbI (fun u => a * (𝓕⁻ ψ u *
            Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))))
    _ = (a * b) * φ (T z) := by
        rw [integral_const_mul, hlast, hinv]
        ring
    _ = Φ (-z) := by
        rw [hab, one_mul, hφdef, hψdef]
        simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply]

theorem exists_diag_equiv (κ : Type) [Fintype κ] (d : κ → ℝ) (hd : ∀ k, d k ≠ 0) :
    ∃ D : (κ → ℝ) ≃L[ℝ] (κ → ℝ), (∀ y k, D y k = d k * y k) ∧
      ∀ g : (κ → ℝ) → ℂ, ∫ x, g (D x) = ((|∏ k, d k|⁻¹ : ℝ) : ℂ) * ∫ w, g w := by
  classical
  set f : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) := Matrix.toLin' (Matrix.diagonal d) with hf
  have hdet : LinearMap.det f = ∏ k, d k := by
    rw [hf, LinearMap.det_toLin', Matrix.det_diagonal]
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hd k
  set D : (κ → ℝ) ≃L[ℝ] (κ → ℝ) := (LinearMap.equivOfDetNeZero f hne).toContinuousLinearEquiv
    with hDdef
  have hDf : ∀ x, D x = f x := fun x => rfl
  refine ⟨D, ?_, ?_⟩
  · intro y k
    rw [hDf, hf, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  · intro g
    have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (κ → ℝ)) hne
    have hcoe : (⇑D.toHomeomorph : (κ → ℝ) → (κ → ℝ)) = ⇑f := rfl
    have h := D.toHomeomorph.measurableEmbedding.integral_map (μ := (volume : Measure (κ → ℝ))) g
    rw [hcoe, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), hdet,
      abs_inv] at h
    calc ∫ x, g (D x) = ∫ x, g (f x) := rfl
      _ = _ := by rw [← h, Complex.real_smul]

theorem exists_euclid_equiv (κ : Type) [Fintype κ] :
    ∃ T : (κ → ℝ) ≃L[ℝ] EuclideanSpace ℝ κ, (∀ x y, inner ℝ (T x) (T y) = ∑ k, x k * y k) ∧
      ∀ g : EuclideanSpace ℝ κ → ℂ, ∫ x, g (T x) = ∫ w, g w := by
  refine ⟨(EuclideanSpace.equiv κ ℝ).symm, ?_, ?_⟩
  · intro x y
    simp [PiLp.inner_apply, mul_comm]
  · intro g
    exact (PiLp.volume_preserving_toLp κ).integral_comp
      (MeasurableEquiv.toLp 2 (κ → ℝ)).measurableEmbedding g

theorem selfDual_diag (κ : Type) [Fintype κ] (d : κ → ℝ) (hd : ∀ k, d k ≠ 0) :
    SelfDual (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)))
      (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) := by
  obtain ⟨D, hD, hDI⟩ := exists_diag_equiv κ d hd
  obtain ⟨T, hT, hTI⟩ := exists_euclid_equiv κ
  set s : ℝ := ∏ k, √|d k| with hsdef
  have hs0 : 0 < s := Finset.prod_pos fun k _ => Real.sqrt_pos.2 (abs_pos.2 (hd k))
  have hsq : s * s = |∏ k, d k| := by
    rw [Finset.abs_prod, hsdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (abs_nonneg _)
  have hr : |∏ k, d k| ≠ 0 := abs_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => hd k)
  have : (ENNReal.ofReal s • (volume : Measure (κ → ℝ))).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (by simpa using hs0) ENNReal.ofReal_ne_top
  have hint : ∀ g : (κ → ℝ) → ℂ,
      ∫ x, g x ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = (s : ℂ) * ∫ x, g x := by
    intro g
    rw [integral_smul_measure, ENNReal.toReal_ofReal hs0.le, Complex.real_smul]
  have hsym : ∀ x y : κ → ℝ, ∑ k, d k * (x k * y k) = ∑ k, d k * (y k * x k) := by
    intro x y
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR : ∀ x y : κ → ℝ, ∑ k, d k * (x k * y k) = inner ℝ (T x) ((D.trans T) y) := by
    intro x y
    rw [ContinuousLinearEquiv.trans_apply, hT]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD]
    ring
  have hab : (s : ℂ) * ((s : ℂ) * ((|∏ k, d k|⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hsq, ← Complex.ofReal_mul, mul_inv_cancel₀ hr,
      Complex.ofReal_one]
  have haI : ∀ g : EuclideanSpace ℝ κ → ℂ,
      ∫ x, g (T x) ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = (s : ℂ) * ∫ w, g w := by
    intro g
    rw [hint, hTI]
  have hbI : ∀ g : EuclideanSpace ℝ κ → ℂ,
      ∫ x, g ((D.trans T) x) ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) =
        ((s : ℂ) * ((|∏ k, d k|⁻¹ : ℝ) : ℂ)) * ∫ w, g w := by
    intro g
    rw [hint]
    simp only [ContinuousLinearEquiv.trans_apply]
    rw [hDI (fun x => g (T x)), hTI]
    ring
  exact selfDual_of_transport (V := κ → ℝ) (E := EuclideanSpace ℝ κ)
    (fun x y => ∑ k, d k * (x k * y k)) hsym T (D.trans T) hR _ _ _ hab haI hbI

theorem eq_of_selfDual_diag : ∀ (κ : Type) [Fintype κ] (d : κ → ℝ), (∀ k, d k ≠ 0) →
    ∀ μ : Measure (κ → ℝ), SelfDual μ (fun x y => Complex.exp
      (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) →
      μ = ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)) := by
  intro κ _ d hd μ hμ
  classical
  have hν := selfDual_diag κ d hd
  have : (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ))).IsAddHaarMeasure := hν.1
  let Bl : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => ∑ k, d k * (x k * y k))
    (fun x x' y => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun x y y' => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
  have hBl : ∀ x y, Bl x y = ∑ k, d k * (x k * y k) := fun x y => rfl
  have hsymm : ∀ x y, Bl x y = Bl y x := fun x y => by
    rw [hBl, hBl]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hnd : ∀ x, (∀ y, Bl x y = 0) → x = 0 := by
    intro x hx
    funext k
    have h := hx (Pi.single k 1)
    rw [hBl] at h
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    exact (mul_eq_zero.1 h).resolve_left (hd k)
  obtain ⟨-, hsch⟩ := GlobalTheory.fourier_inversion_haar_symm_form Bl hsymm hnd
    (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ))) inferInstance
  obtain ⟨u, -, hu_cs, hu_sm, -, hu0⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (x := (0 : κ → ℝ)) (s := Set.univ) Filter.univ_mem
  have hΦcs : HasCompactSupport (⇑Complex.ofRealCLM ∘ u) := hu_cs.comp_left (map_zero _)
  have hΦsm := Complex.ofRealCLM.contDiff.comp hu_sm
  have hI := (hsch (hΦcs.toSchwartzMap hΦsm)).2
  exact SelfDual.eq_of_test hν hμ (⇑Complex.ofRealCLM ∘ u) hΦsm.continuous hΦcs hI 0
    (by simp [hu0])

end GlobalTheory.SelfDualDiagReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothFunctionalOrbitSmoothVectorStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_functional_orbit_smoothVector : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (σ : Mat k r → (H →L[ℂ] H)) (Λ : H →L[ℂ] B), IsURepOn (GG k r) σ → ∀ v : H, IsSmoothVec (k := k) (r := r) σ v → SmoothOnH (Hpk k r) (fun g : Mat k r => Λ (σ g v)) ∧ ∀ ws : List (Mat k r), (∀ X ∈ ws, InLieHpk k r X) → ∀ x ∈ GG k r, rdWord ws (fun g : Mat k r => Λ (σ g v)) x = Λ (σ x (dsigW σ ws v)) := by
  first | exact @GlobalTheory.SgInfOrb.smooth_rdWord_functional | exact GlobalTheory.SgInfOrb.smooth_rdWord_functional | (intros; apply GlobalTheory.SgInfOrb.smooth_rdWord_functional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponents
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem split_components :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ (L : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E ⊗[F] v.adicCompletion F), y ∈ loc v L ↔ (∃ y₁ ∈ loc v L, ∀ b, (sp (y₁ b)).1 = (sp (y b)).1) ∧ ∃ y₂ ∈ loc v L, ∀ b, (sp (y₂ b)).2 = (sp (y b)).2) ∧ (∀ g : GL (Fin n) (v.adicCompletion F), ∃! h : UPts cm.sig J (v.adicCompletion F), bc ((RingHom.fst _ _).comp sp.toRingHom) h.1 = g) ∧ ∀ x y : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x y)).1 = ∑ i, ∑ j, (sp (x i)).2 * (sp (inclE (F := F) (v.adicCompletion F) (J i j))).1 * (sp (y j)).1 := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet v sp hsig hdiag
  refine ⟨?_, ?_, ?_⟩
  · intro L y
    refine ⟨fun hy => ⟨⟨y, hy, fun _ => rfl⟩, y, hy, fun _ => rfl⟩, ?_⟩
    rintro ⟨⟨y₁, h₁, e₁⟩, y₂, h₂, e₂⟩
    have hint : ∀ x, x ∈ intV E v ↔
        (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
      split_integral_local F E v sp hdiag
    have ha : sp.symm (1, 0) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
    have hb : sp.symm (0, 1) ∈ intV E v := by
      rw [hint, sp.apply_symm_apply]; exact ⟨zero_mem _, one_mem _⟩
    have hm := (loc v L).add_mem ((loc v L).smul_mem ⟨_, ha⟩ h₁) ((loc v L).smul_mem ⟨_, hb⟩ h₂)
    have hy : y = (⟨_, ha⟩ : intV E v) • y₁ + (⟨_, hb⟩ : intV E v) • y₂ := by
      funext b
      apply sp.injective
      change sp (y b) = sp (sp.symm (1, 0) * y₁ b + sp.symm (0, 1) * y₂ b)
      rw [map_add, map_mul, map_mul, sp.apply_symm_apply, sp.apply_symm_apply]
      ext
      · simp [e₁ b]
      · simp [e₂ b]
    rw [hy]; exact hm
  · intro g
    obtain ⟨e, he⟩ := Formalism.L2.G.exists_locGL cm.sig J hJ (isUnit_iff_ne_zero.2 hdet) _ sp hsig
    refine ⟨e.symm g, ?_, fun h hh => ?_⟩
    · exact (he _).symm.trans (e.apply_symm_apply g)
    · rw [MulEquiv.eq_symm_apply]
      exact (he _).trans hh
  · intro x y
    unfold hR hform
    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Prod.fst_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, hsig]
    rfl

end GlobalTheory.St.G
end

