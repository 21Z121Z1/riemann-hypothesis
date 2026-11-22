import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.StTopClass
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0306
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0304
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0310
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitude
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SimTheta

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mem_UJ_smul_iff (s : A →+* A) (J : Matrix n n A) (c d : A) (hdc : d * c = 1) (u : GL n A) :
    u ∈ UJ s (c • J) ↔ u ∈ UJ s J := by
  have hscale : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) =
      c • (cT s (u : Matrix n n A) * J * (u : Matrix n n A)) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  constructor
  · intro h
    have h' : cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J := h
    rw [hscale] at h'
    change cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J
    have h2 := congrArg (fun B : Matrix n n A => d • B) h'
    simpa only [smul_smul, hdc, one_smul] using h2
  · intro h
    have h' : cT s (u : Matrix n n A) * J * (u : Matrix n n A) = J := h
    change cT s (u : Matrix n n A) * (c • J) * (u : Matrix n n A) = c • J
    rw [hscale, h']

theorem conj_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G * u * G⁻¹ ∈ UJ s J := by
  refine GlobalTheory.CompanionTheory.SW.HIsom.conj_mem_UJ s J G u ?_
  rw [hG]
  exact (mem_UJ_smul_iff s J c d hdc u).2 hu

theorem conj_inv_mem (s : A →+* A) (J : Matrix n n A) (G : GL n A) (c d : A) (hdc : d * c = 1)
    (hG : cT s (G : Matrix n n A) * J * (G : Matrix n n A) = c • J) (u : GL n A) (hu : u ∈ UJ s J) :
    G⁻¹ * u * G ∈ UJ s J := by
  have h := GlobalTheory.CompanionTheory.SW.HIsom.conj_inv_mem_UJ s J G u hu
  rw [hG] at h
  exact (mem_UJ_smul_iff s J c d hdc _).1 h

end Generic

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem JR_smul (R : Type) [CommRing R] [Algebra F R] {M : ℕ} (c : E)
    (J : Matrix (Fin M) (Fin M) E) :
    JR (F := F) R (c • J) = inclR (F := F) R c • JR (F := F) R J := by
  ext i j
  simp [JR, Matrix.map_apply]

theorem gramE_smul (σ : E →ₐ[F] E) {M n : ℕ} (c : E) (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) : gramE σ (c • J) X = c • gramE σ J X := by
  ext a b
  simp only [gramE, hE, hform, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

def gramEquiv (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E) (c : E)
    (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    (T : Matrix (Fin n) (Fin n) E) :
    {X : Fin n → Fin M → E | gramE σ J X = T} ≃ {X : Fin n → Fin M → E | gramE σ J X = c • T} where
  toFun X := ⟨SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E) X.1, by
    have := X.2
    simp only [Set.mem_setOf_eq] at this ⊢
    rw [SWIsom.gramE_ratAct, hg, gramE_smul, this]⟩
  invFun Y := ⟨SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1, by
    have hY := Y.2
    simp only [Set.mem_setOf_eq] at hY ⊢
    have h1 : gramE σ J (SWIsom.ratAct (g : Matrix (Fin M) (Fin M) E)
        (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1)) =
        c • gramE σ J (SWIsom.ratAct ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) Y.1) := by
      rw [SWIsom.gramE_ratAct, hg, gramE_smul]
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one, hY] at h1
    exact (smul_right_injective _ hc h1).symm⟩
  left_inv X := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ X.1) = X.1
    rw [SWIsom.ratAct_mul, Units.inv_mul, SWIsom.ratAct_one]
  right_inv Y := by
    apply Subtype.ext
    change SWIsom.ratAct _ (SWIsom.ratAct _ Y.1) = Y.1
    rw [SWIsom.ratAct_mul, Units.mul_inv, SWIsom.ratAct_one]

end Alg

theorem unitaryConj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (g : GL (Fin M) E)
    (l : F) (hl : l ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) =
      (algebraMap F E l) • J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    ∃ e : HA R σ J ≃ₜ* HA R σ J,
      (∀ u, HA.mat R σ J (e u) = bc (inclR R) g * HA.mat R σ J u * (bc (inclR R) g)⁻¹) ∧
      ∀ u, HA.mat R σ J (e u) ∈ HFin R σ J ↔ HA.mat R σ J u ∈ HFin R σ J := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  haveI : IsTopologicalRing (R ⊗[F] E) := GlobalTheory.CompanionTheory.SW.HIsom.isTopologicalRing_tens F E R
  set G : GL (Fin M) (R ⊗[F] E) := bc (inclR R) g with hG
  have hdcE : algebraMap F E l⁻¹ * algebraMap F E l = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hl, map_one]
  have hdcR : inclR (F := F) R (algebraMap F E l⁻¹) * inclR (F := F) R (algebraMap F E l) = 1 := by
    rw [← map_mul, hdcE, map_one]
  have hGR : cT (sigR R σ) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (G : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = inclR (F := F) R (algebraMap F E l) • JR R J := by
    rw [← GlobalTheory.CompanionTheory.SW.HIsom.JR_conj R σ J g, hg, JR_smul]
  have h₁ : ∀ u ∈ HR R σ J, G * u * G⁻¹ ∈ HR R σ J := fun u hu =>
    conj_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  have h₂ : ∀ u ∈ HR R σ J, G⁻¹ * u * G ∈ HR R σ J := fun u hu =>
    conj_inv_mem (sigR R σ) (JR R J) G _ _ hdcR hGR u hu
  refine ⟨GlobalTheory.CompanionTheory.SW.HIsom.conjHomeo _ _ G h₁ h₂, fun u => rfl, fun u => ?_⟩
  change G * HA.mat R σ J u * G⁻¹ ∈ HFin R σ J ↔ _
  constructor
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g⁻¹ * w * g, conj_inv_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = G * HA.mat R σ J u * G⁻¹ := hwu
    simp only [map_mul, map_inv, this, ← hG]
    group
  · rintro ⟨w, hw, hwu⟩
    refine ⟨g * w * g⁻¹, conj_mem (σ : E →+* E) J g _ _ hdcE hg w hw, ?_⟩
    have : bc (inclR R) w = HA.mat R σ J u := hwu
    simp only [map_mul, map_inv, this, ← hG]

section Theta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem theta_map (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (g : GL (Fin M) E) (c : E) (hc : c ≠ 0)
    (hg : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = c • J)
    [LocallyCompactSpace (AF F)] [SecondCountableTopology (AF F)] [T2Space (AF F)]
    (He : HA (AF F) σ J ≃ᵐ HA (AF F) σ J)
    (hmat : ∀ u, HA.mat (AF F) σ J (He u) =
      bc (inclR (AF F)) g * HA.mat (AF F) σ J u * (bc (inclR (AF F)) g)⁻¹)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (T : Matrix (Fin n) (Fin n) E) :
    (thetaMeas σ J (μ.map He.symm) (He ⁻¹' 𝓕) {X | gramE σ J X = T}).map
        (actTup (AF F) (bc (inclR (AF F)) g)) =
      thetaMeas σ J μ 𝓕 {X | gramE σ J X = c • T} := by
  obtain ⟨tg, -, -, -, bs, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : BorelSpace (Fin n → Fin M → AF F ⊗[F] E) :=
    (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)).2.2.2.2.2.2.2.1 n M
  set G : GL (Fin M) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
  have hmG := SWIsom.measurable_actTup (n := n) σ hCM (AF F) G
  have hmf : ∀ Y : Fin n → Fin M → AF F ⊗[F] E,
      Measurable fun h : HA (AF F) σ J => actW (AF F) σ J h⁻¹ Y := fun Y =>
    ((hact n).1.comp (continuous_inv.prodMk continuous_const)).measurable
  have hmass : (μ.map He.symm) (He ⁻¹' 𝓕) = μ 𝓕 := by
    rw [He.symm.map_apply]
    congr 1
    ext x
    simp
  have hrest : ((μ.map He.symm).restrict (He ⁻¹' 𝓕)).map He = μ.restrict 𝓕 := by
    rw [← He.restrict_map, Measure.map_map He.measurable He.symm.measurable]
    simp
  unfold thetaMeas
  rw [Measure.map_smul, hmass]
  congr 1
  rw [Measure.map_sum hmG.aemeasurable, ← SWIsom.sum_reindex (gramEquiv σ J g c hc hg T)]
  congr 1
  funext X
  rw [Measure.map_map hmG (hmf _)]
  have hcomp : (actTup (AF F) G ∘ fun h => actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) =
      (fun h => actW (AF F) σ J h⁻¹
        (ratTup (AF F) ((gramEquiv σ J g c hc hg T X : _) : Fin n → Fin M → E))) ∘ He := by
    funext h
    have := SWIsom.act_conj (AF F) σ G He hmat h (ratTup (AF F) (X : Fin n → Fin M → E))
    simp only [Function.comp]
    rw [this, ← SWIsom.ratTup_ratAct]
    rfl
  rw [hcomp, ← Measure.map_map (hmf _) He.measurable, hrest]

end Theta

theorem theta_simil : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  intro F E _ _ _ _ _ σ hCM M J hJ μ 𝓕 hμ h𝓕 γ l hl hγ
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := unitaryConj F E σ hCM M J γ l hl hγ (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  haveI := tg
  haveI := bs
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M J (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M J (μ.map He.symm) (He ⁻¹' 𝓕) :=
    SWIsom.isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hc : algebraMap F E l ≠ 0 := by
    simpa using hl
  refine ⟨_, _, hμ', h𝓕', ?_⟩
  intro n T T' hT'
  subst hT'
  exact theta_map σ hCM J hJ γ _ hc hγ He hmat μ 𝓕 T

end GlobalTheory.CompanionTheory.SW.SimTheta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceSingleMulSingle
section
open Matrix MvPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.TopClass

open PositivityTheory.RgTw

variable {n : ℕ}

def secExpr {R : Type*} [Ring R] (A B C E Z : R) : R :=
  -((Z * A + A * Z) * B + A * (Z * B + B * Z)) - ((Z * E + E * Z) * C + E * (Z * C + C * Z))

def secDer (d : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun Z := secExpr d dᴴ d⁻¹ dᴴ⁻¹ Z
  map_add' X Y := by simp only [secExpr, add_mul, mul_add]; abel
  map_smul' c X := by
    simp only [secExpr, RingHom.id_apply, smul_sub, smul_neg, smul_add, Matrix.smul_mul, Matrix.mul_smul, add_mul,
      mul_add]

theorem trace_single_mul_single (a b c e : Fin n) :
    trace (Matrix.single a b (1 : ℂ) * Matrix.single c e 1) = if a = e ∧ b = c then 1 else 0 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  by_cases h1 : a = e <;> by_cases h2 : b = c <;> simp [h1, h2, ite_and, Finset.sum_ite_eq', eq_comm]

theorem sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem trace_hb_mul_hb (p q : Fin n × Fin n) : trace (hb p * hb q) = if p = q then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  obtain ⟨c, e⟩ := q
  have hs := sqrt_two_inv_sq
  simp only [hb]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 <;>
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_sub, trace_smul, trace_single_mul_single, smul_eq_mul, Prod.mk.injEq] at * <;> (simp only [Fin.ext_iff, Fin.lt_iff_val_lt_val] at * ; split_ifs at * <;> (try omega)) <;>
  (generalize ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = s at hs ⊢
   have hs2 : s ^ 2 = 1 / 2 := by rw [sq]; exact hs
   first | ring1 | (ring_nf; simp only [Complex.I_sq, hs2]; ring_nf))

theorem hb_linInd : LinearIndependent ℂ (hb (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h := congrArg (fun X => trace (X * hb q)) hg
  simpa [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, trace_hb_mul_hb] using h

def hbB (n : ℕ) : Module.Basis (Fin n × Fin n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank' hb hb_linInd (by simp [Module.finrank_matrix])

theorem hbB_apply (p : Fin n × Fin n) : hbB n p = hb p := by
  simp [hbB]

theorem hbB_repr (X : Mat n) (q : Fin n × Fin n) : (hbB n).repr X q = trace (X * hb q) := by
  conv_rhs => rw [← (hbB n).sum_repr X]
  simp [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, trace_smul, hbB_apply, trace_hb_mul_hb]

theorem det_of_trace (L : Mat n →ₗ[ℂ] Mat n) :
    (Matrix.of fun p q : Fin n × Fin n => trace (L (hb p) * hb q)).det = LinearMap.det L := by
  rw [← LinearMap.det_toMatrix (hbB n) L, ← Matrix.det_transpose (LinearMap.toMatrix (hbB n) (hbB n) L)]
  congr 1
  ext p q
  simp [LinearMap.toMatrix_apply, hbB_repr, hbB_apply]

def cjHom (U : Mat n) (hU : IsUnit U.det) : Mat n →+* Mat n where
  toFun X := U⁻¹ * X * U
  map_one' := by simp [Matrix.nonsing_inv_mul U hU]
  map_mul' X Y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U U⁻¹, Matrix.mul_nonsing_inv U hU, Matrix.one_mul]
  map_zero' := by simp
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]

theorem cjHom_apply (U : Mat n) (hU : IsUnit U.det) (X : Mat n) : cjHom U hU X = U⁻¹ * X * U := rfl

def cjEquiv (U : Mat n) (hU : IsUnit U.det) : Mat n ≃ₗ[ℂ] Mat n where
  toFun X := U⁻¹ * X * U
  invFun X := U * X * U⁻¹
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]
  left_inv X := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv U hU, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv U hU, Matrix.one_mul]
  right_inv X := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul U hU, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul U hU, Matrix.one_mul]

theorem isUnit_det_G (k : G n) : IsUnit (k.val).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp k.isUnit

theorem tw_val {k : G n} (hk : k ∈ KU n) (d : G n) : (tw k d).val = cjHom k.val (isUnit_det_G k) d.val := by
  have h : th k = k := hk
  rw [tw, h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, cjHom_apply]

end GlobalTheory.CompanionTheory.TopClass
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsUniformGenerators
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem exists_alg_of_twSecs : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ (n₁ : ℤ) (W : ∀ n : ℤ, Set Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ n e, W n ⊆ twSecs H n (S e)) → (∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W n, x - b ∈ twPow I H n P (e + 1)) → ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  intro A _ _ I X _ _ H hA P hP S hS n₁ W hW hgen
  have hH := hA.isLB
  let F : Set (Subobject P) := {B | (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ≤ S e}
  have h0 : (0 : Γ(GlobalTheory.twistZ P H n₁, ⊤)) ∈ twSecs H n₁ (S 0) := ⟨0, map_zero _⟩
  obtain ⟨b₀, hb₀, -⟩ := hgen n₁ le_rfl 0 0 h0
  have hF : F.Nonempty :=
    ⟨genSub hH n₁ b₀, GlobalTheory.T.generated_subsheaf_quasicoherent hH hP.1 n₁ b₀, fun e => GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem hH (S e) n₁ b₀ (hW n₁ e hb₀)⟩
  obtain ⟨M, ⟨hMq, hMS⟩, hMmax⟩ := GlobalTheory.T.coherent_noetherian_maximal_subsheaf hP F hF (fun B hB => hB.1)
  have hgenM : ∀ n, ∀ b ∈ W n, genSub hH n b ≤ M := by
    intro n b hb
    have hmem : M ⊔ genSub hH n b ∈ F :=
      ⟨(GlobalTheory.T.quasicoherent_sup_sections hP.1 M (genSub hH n b) hMq (GlobalTheory.T.generated_subsheaf_quasicoherent hH hP.1 n b)).1,
        fun e => sup_le (hMS e) (GlobalTheory.T.generated_subsheaf_le_of_twisted_section_mem hH (S e) n b (hW n e hb))⟩
    rw [← hMmax _ hmem le_sup_left]
    exact le_sup_right
  refine ⟨M, hMq, fun e => le_antisymm (sup_le (hMS e) (hS.pow_le e)) ?_⟩
  have hSe : IsCoherent (S e : X.Modules) := GlobalTheory.T.coherent_subobject_coherent hP (S e) (hS.qcoh e)
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.ample_twist_sections_generate_subsheaf hA (S e) hSe
  refine hn₀ (max n₀ n₁) (le_max_left _ _) _ fun x hx => ?_
  obtain ⟨b, hb, hxb⟩ := hgen (max n₀ n₁) (le_max_right _ _) e x hx
  rw [← add_sub_cancel b x]
  exact (GlobalTheory.T.generated_subsheaf_add_le_sup hH _ b (x - b)).trans (sup_le_sup (hgenM _ b hb) (GlobalTheory.T.generated_subsheaf_le_ideal_power I hH hP.1 _ _ _ hxb))

end GlobalTheory.CompanionTheory.GE.TwGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLiftingOfSections
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option maxHeartbeats 1000000 in

theorem exists_uniform_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (d : ℕ), 1 ≤ d → ∀ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))), VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ D : ℤ, D = d * t → ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D), SecMaps (pullPow (v e) D) σ (secPull σ' (β e)) := by
  intro R _ _ I Y β hβ hP N v hN d hd m s hs
  obtain ⟨g, ρ, hρ⟩ : ∃ (g : ℕ) (ρ : Fin g → R), Ideal.span (Set.range ρ) = I := by
    obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨S.card, fun k => (S.equivFin.symm k : R), ?_⟩
    rw [← hS]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    exact ⟨fun ⟨k, hk⟩ => hk ▸ (S.equivFin.symm k).2, fun hx => ⟨S.equivFin ⟨x, hx⟩, by simp⟩⟩
  subst hρ
  obtain ⟨D, hD0, hDβ, hDm, hDi, hDc, hDa⟩ :=
    GlobalTheory.T.thickening_very_ample_opens_exist R _ Y β hβ (pw (N 0) (d : ℤ)) m s (isLB_pw (hN 0).1 _) hs
  obtain ⟨sh, hsh0, hshp, hshu⟩ := GlobalTheory.T.formal_lift_very_ample_sections R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
  have hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R)
      (A := fun t => Tm _ Y N D (d : ℤ) e t S) fun j t => mulT _ Y N D (d : ℤ) e t S (sh e j S) :=
    fun e S i j t a => mulT_comm _ Y N D (d : ℤ) e t S (sh e i S) (sh e j S) a
  have hloc := GlobalTheory.T.formal_lift_sections_nonvanishing R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  have hDβ' : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S := fun e S => (hDβ e S).ge
  have h_pres : ∀ e t (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm _ Y N D (d : ℤ) (e + 1) t S),
      S.Nonempty → red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S' (resT _ Y N D (d : ℤ) hDm (e + 1) t h a) =
        resT _ Y N D (d : ℤ) hDm e t h (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S a) :=
    fun e t S S' h a _ => GlobalTheory.T.thickening_restriction_compatible_opens R _ Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
      (D (e + 1) S') (D e S) (D e S') (hDβ' e S) (hDβ' e S') (hDm (e + 1) S S' h)
      (hDm e S S' h) a
  have h_mp : ∀ j e t (S : Finset (Fin (m + 1))) (a : Tm _ Y N D (d : ℤ) (e + 1) t S), S.Nonempty →
      red _ Y N D β hβ v hN hDβ' ((d : ℤ) * (t + 1)) e S (mulT _ Y N D (d : ℤ) (e + 1) t S (sh (e + 1) j S) a) =
        mulT _ Y N D (d : ℤ) e t S (sh e j S) (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S a) := by
    intro j e t S a hS
    have h1 := GlobalTheory.T.thickening_cech_cover_compatible R _ Y β hβ N v hN (Fin (m + 1)) D hDβ' ((d : ℤ) * t)
      (d : ℤ) ((d : ℤ) * (t + 1)) (by ring) e S ((SecOnR.of _ _ _).symm a) (sh (e + 1) j S)
    rw [hshp e j S hS] at h1
    exact h1
  have h_mres : ∀ j e t (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm _ Y N D (d : ℤ) e t S), S.Nonempty →
      resT _ Y N D (d : ℤ) hDm e (t + 1) h (mulT _ Y N D (d : ℤ) e t S (sh e j S) a) -
        mulT _ Y N D (d : ℤ) e t S' (sh e j S') (resT _ Y N D (d : ℤ) hDm e t h a) ∈
          Ideal.span (Set.range ρ) • (⊤ : Submodule R (Tm _ Y N D (d : ℤ) e (t + 1) S')) :=
    fun j e t S S' h a hS => GlobalTheory.T.formal_lift_sections_generate R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
      sh hsh0 hshp hshu j e t S S' h a hS
  have h_G3 : ∀ e t (S : Finset (Fin (m + 1))), S.Nonempty →
      Function.Surjective (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S) ∧
        LinearMap.ker (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤ :=
    fun e t S hS => GlobalTheory.T.thickening_affine_preimage R _ Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1) S hS)
  have h_kill : ∀ e t (S : Finset (Fin (m + 1))), S.Nonempty →
      Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (Tm _ Y N D (d : ℤ) e t S)) = ⊥ :=
    fun e t S _ => GlobalTheory.T.ideal_power_annihilates_sections R _ Y e _ _
  have h_bij : ∀ i e t (S : Finset (Fin (m + 1))), i ∈ S → Function.Bijective (mulT _ Y N D (d : ℤ) e t S (sh e i S)) := by
    intro i e t S hi
    obtain ⟨y, hy⟩ := hshu e i S hi
    exact GlobalTheory.T.thickening_twisted_section_transition R _ Y β hβ N v hN (d : ℤ) (Fin (m + 1)) D e t S (sh e i S) y hy
  have h_one : ∀ e (i : Fin (m + 1)), red _ Y N D β hβ v hN hDβ' ((d : ℤ) * 0) e {i} (oneT _ Y N D (d : ℤ) (e + 1) {i}) =
      oneT _ Y N D (d : ℤ) e {i} :=
    fun e i => GlobalTheory.T.thickening_cech_restriction_commutes R _ Y β hβ N v hN (Fin (m + 1)) D hDβ' ((d : ℤ) * 0) (mul_zero _) e {i}
  have h_fin := GlobalTheory.T.formal_lift_closed_embedding R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.uniform_first_cohomology_kernels_exist (Fin (m + 1)) R g ρ (Tm _ Y N D (d : ℤ))
    (fun e t S S' h => resT _ Y N D (d : ℤ) hDm e t h)
    (fun e t S => red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S)
    (fun j e t S => mulT _ Y N D (d : ℤ) e t S (sh e j S))
    (fun e i => oneT _ Y N D (d : ℤ) e {i}) hc
    (fun e t S h a => SecOnR.restrict_self _ _ _)
    (fun e t S S' S'' h h' a => SecOnR.restrict_restrict _ _ _ _)
    h_pres h_mp h_mres (fun e t S hS => (h_G3 e t S hS).1) (fun e t S hS => (h_G3 e t S hS).2)
    h_kill h_bij hloc.1 hloc.2 h_one h_fin
  refine ⟨t₀.toNat, fun t ht D' hD' e σ => ?_⟩
  subst hD'
  exact GlobalTheory.T.formal_lift_projective_embedding_compatible R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa (t : ℤ) e
    (fun c hc0 hcoc => ht₀ t (by omega) e c hc0 hcoc) σ

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

