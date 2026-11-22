import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0123
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocal
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.MassProduct

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

theorem uniformiser_mem_jacobson (ϖ : 𝒪[F]) (h : Irreducible ϖ) (w : L.O)
    (hw : (w : E) = algebraMap F E (ϖ : F)) : w ∈ (⊥ : Ideal L.O).jacobson := by
  let f : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O
    (fun x => (L.O_def _).2 isIntegral_algebraMap)
  letI : Algebra 𝒪[F] L.O := f.toAlgebra
  haveI : IsScalarTower 𝒪[F] L.O E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsIntegral 𝒪[F] L.O := by
    refine ⟨fun x => ?_⟩
    have h1 : IsIntegral 𝒪[F] (x : E) := (L.O_def (x : E)).1 x.2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[F] L.O E) Subtype.val_injective).1 h1
  refine Ideal.mem_sInf.2 ?_
  rintro P ⟨-, hP⟩
  haveI := hP
  have hmax : (P.comap (algebraMap 𝒪[F] L.O)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  have hm : ϖ ∈ P.comap (algebraMap 𝒪[F] L.O) := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal _).2 h.not_isUnit
  have he : algebraMap 𝒪[F] L.O ϖ = w := by
    apply Subtype.ext
    rw [hw]
    rfl
  rw [Ideal.mem_comap, he] at hm
  exact hm

theorem stabilises_of_close {n : ℕ} (Λ : Submodule L.O (Fin n → E)) (hΛ : Λ.FG) (ϖ : 𝒪[F])
    (h : Irreducible ϖ) (m : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hm : ∀ x ∈ Λ, ∃ y ∈ Λ, m x - x = algebraMap F E (ϖ : F) • y) :
    m ∈ MulAction.stabilizer ((Fin n → E) ≃ₗ[E] (Fin n → E)) Λ := by
  have hO : algebraMap F E (ϖ : F) ∈ L.O := (L.O_def _).2 (by
    have : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E ϖ) := isIntegral_algebraMap
    exact this)
  let w : L.O := ⟨_, hO⟩
  have hw : w ∈ (⊥ : Ideal L.O).jacobson := uniformiser_mem_jacobson L ϖ h w rfl
  have hle : m • Λ ≤ Λ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := hm x hx
    have : m x = x + w • y := by
      rw [eq_add_of_sub_eq' e]
      rfl
    change m x ∈ Λ
    rw [this]
    exact Λ.add_mem hx (Λ.smul_mem w hy)
  have hge : Λ ≤ m • Λ := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {w}) hΛ
      ((Ideal.span_singleton_le_iff_mem _).2 hw) ?_
    intro x hx
    obtain ⟨y, hy, e⟩ := hm x hx
    have hx' : x = m x - w • y := by
      have : m x = x + w • y := by
        rw [eq_add_of_sub_eq' e]
        rfl
      rw [this]; abel
    rw [hx']
    refine Submodule.sub_mem_sup ?_ ?_
    · exact Submodule.smul_mem_pointwise_smul x m Λ hx
    · exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self w) hy
  exact MulAction.mem_stabilizer_iff.2 (le_antisymm hle hge)

end Local

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
variable (A : Places F E sig) (n : ℕ)

def extMap (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (p : HeightOneSpectrum (𝓞 F)) :
    (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep) :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose

theorem extMap_spec (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (p : HeightOneSpectrum (𝓞 F)) :
    A.Ext p g (extMap A n g p) :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose_spec.1

theorem extMap_unique {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} {p : HeightOneSpectrum (𝓞 F)}
    {g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)} (h : A.Ext p g g') :
    g' = extMap A n g p :=
  ((RatExt.rational_extend A n p).2.2.1 g).choose_spec.2 g' h

def extHom : ((Fin n → E) ≃ₗ[E] (Fin n → E)) →*
    ∀ p, (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep) where
  toFun g := extMap A n g
  map_one' := funext fun p => (extMap_unique A n (g := 1) (g' := 1) fun _ => rfl).symm
  map_mul' a b := funext fun p => (extMap_unique A n (g := a * b)
    (g' := extMap A n a p * extMap A n b p) (fun x => by
      change extMap A n a p (extMap A n b p (A.bc p x)) = A.bc p (a (b x))
      rw [extMap_spec A n b p x, extMap_spec A n a p (b x)])).symm

theorem comap_pi (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))) :
    (Subgroup.pi Set.univ K).comap (extHom A n) = A.rat K := by
  ext g
  constructor
  · intro h p
    exact ⟨extMap A n g p, (Subgroup.mem_pi _).1 h p (Set.mem_univ p), extMap_spec A n g p⟩
  · intro h
    refine (Subgroup.mem_pi _).2 fun p _ => ?_
    obtain ⟨g', hg, he⟩ := h p
    have e : extMap A n g p = g' := (extMap_unique A n he).symm
    change extMap A n g p ∈ K p
    rw [e]
    exact hg

end Global

theorem mass_eq_finprod : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k →
    ∀ Λ : G.Lt, Submodule.IsLattice E Λ →
    {p | (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) ≠ (G.S p).K0}.Finite ∧
      G.mu Λ = ∏ᶠ p, (G.S p).mu (A.lat p Λ) := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, hcoord⟩ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  have hstd := GlobalTheory.T.coordinateLattice_unique_term_almost_all_places A r k G hk
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hfin : {p | U p ≠ K p}.Finite := by
    refine (hstd.union hcoord).subset ?_
    intro p hp
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    obtain ⟨h1, h2⟩ := hcon
    apply hp
    change (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) = (G.S p).K0
    rw [h2]
    exact h1.2.2.1
  have hKSt : ∀ p, K p ≤ (G.S p).St := fun p x hx => hx.1.1
  have hUSt : ∀ p, U p ≤ (G.S p).St := fun p x hx => hx.1

  let c : ∀ p, ((A.loc p).Fp)ˣ := fun p =>
    if U p ≠ K p then
      haveI := (A.loc p).lf
      Units.mk0 (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp)
        (fun h0 => (G.S p).ϖ_irr.ne_zero (Subtype.ext h0))
    else 1
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite := by
    refine hfin.subset ?_
    intro p hp
    by_contra hcon
    apply hp
    have hu : U p = K p := not_not.1 hcon
    have h1 : c p = 1 := if_neg (not_not.2 hu)
    exact ⟨1, by rw [h1]; simp⟩
  let φ := extHom A (k + 2 * r + 1)
  have hdense : ∀ g, g ∈ Subgroup.pi Set.univ K ∨ g ∈ Subgroup.pi Set.univ U →
      ∃ γ, (φ γ)⁻¹ * g ∈ Subgroup.pi Set.univ K ⊓ Subgroup.pi Set.univ U := by
    intro g hg
    have hgSt : ∀ p, g p ∈ (G.S p).St := by
      intro p
      rcases hg with h | h
      · exact hKSt p ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
      · exact hUSt p ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
    have hgfin : {p | g p ∉ (G.S p).K0}.Finite := by
      rcases hg with h | h
      · refine Set.finite_empty.subset ?_
        intro p hp
        exact hp ((Subgroup.mem_pi _).1 h p (Set.mem_univ p))
      · refine hfin.subset ?_
        intro p hp he
        apply hp
        have := (Subgroup.mem_pi _).1 h p (Set.mem_univ p)
        rw [he] at this
        exact this
    obtain ⟨γ, -, hγ⟩ := GlobalTheory.T.exists_mem_St_approximating_local_elements A r k G Λ hΛ c hc g hgSt hgfin
    refine ⟨γ, ?_⟩
    have key : ∀ p, (g p)⁻¹ * φ γ p ∈ K p ⊓ U p := by
      intro p
      obtain ⟨h1, h2⟩ := hγ p (φ γ p) (extMap_spec A _ γ p)
      refine ⟨h1, ?_⟩
      by_cases he : U p = K p
      · rw [he]; exact h1
      · refine ⟨hKSt p h1, ?_⟩
        haveI := (A.loc p).lf
        have hcp : ((c p : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) := by
          have h3 : c p = Units.mk0 (((G.S p).ϖ : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp)
              (fun h0 => (G.S p).ϖ_irr.ne_zero (Subtype.ext h0)) := if_pos he
          rw [h3]
          rfl
        refine stabilises_of_close (A.L p) (A.lat p Λ) (hlat p).1 (G.S p).ϖ (G.S p).ϖ_irr _ ?_
        intro x hx
        obtain ⟨y, hy, e⟩ := h2 x hx
        refine ⟨y, hy, ?_⟩
        rw [← hcp]
        exact e
    have key2 : ∀ p, ((φ γ)⁻¹ * g) p ∈ K p ⊓ U p := by
      intro p
      have := (K p ⊓ U p).inv_mem (key p)
      simpa [mul_inv_rev] using this
    exact ⟨(Subgroup.mem_pi _).2 fun p _ => (key2 p).1, (Subgroup.mem_pi _).2 fun p _ => (key2 p).2⟩
  obtain ⟨hKU, hUK⟩ := GlobalTheory.T.relIndex_comap_pair_of_dense_image φ (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) hdense
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU' : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨-, -, hprod⟩ := GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod K U hKU' hidx
  refine ⟨hfin, ?_⟩
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (comap_pi A _ U).symm
  have hmu : G.mu Λ = invVol (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) := by
    unfold GFrames.mu invVol
    rw [e1, e2, hKU, hUK]
  rw [hmu, hprod]
  rfl

end GlobalTheory.HL.MassProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HolomorphicExtensionCompactRep
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace
open MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolExt

theorem differentiable_det (n : ℕ) :
    Differentiable ℂ fun y : Fin n → Fin n → ℂ => (Matrix.of y).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

theorem differentiable_adjugate (n : ℕ) (i j : Fin n) :
    Differentiable ℂ fun y : Fin n → Fin n → ℂ => (Matrix.of y).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  have : (fun y : Fin n → Fin n → ℂ => ((Matrix.of y).updateRow j (Pi.single i 1)).det) =
      (fun y : Fin n → Fin n → ℂ => (Matrix.of y).det) ∘ fun y => Function.update y j (Pi.single i 1) := rfl
  rw [this]
  refine (differentiable_det n).comp (differentiable_pi.2 fun a => ?_)
  by_cases h : a = j
  · subst h
    simp
  · simp only [Function.update_of_ne h]
    fun_prop

theorem differentiableOn_inv (n : ℕ) (i j : Fin n) :
    DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y)⁻¹ i j) {y | IsUnit (Matrix.of y)} := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine ((differentiable_det n).differentiableOn.inv fun y hy => ?_).mul
    (differentiable_adjugate n i j).differentiableOn
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hy).ne_zero

def peak {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := 1 + 2 * n + 2 * g.trace.re

theorem peak_coe {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ((peak g : ℝ) : ℂ) = 1 + 2 * n + g.trace + gᴴ.trace := by
  rw [Matrix.trace_conjTranspose, add_assoc, Complex.star_def, Complex.add_conj, peak]
  push_cast
  ring

theorem peak_pos {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) : 0 < peak g := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (g + 1)).trace_nonneg
  have h2 := (Complex.le_def.1 h).1
  simp only [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add, hg, Matrix.mul_one,
    Matrix.one_mul, trace_add, trace_one, trace_conjTranspose, Fintype.card_fin, Complex.add_re,
    Complex.natCast_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h2
  unfold peak
  linarith

theorem peak_lt {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) (h1 : g ≠ 1) :
    peak g < peak (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (g - 1)).trace_nonneg
  have hne : ((g - 1)ᴴ * (g - 1)).trace ≠ 0 := by
    rw [Ne, Matrix.trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero]
    exact h1
  have h2 := (Complex.lt_def.1 (lt_of_le_of_ne h hne.symm)).1
  simp only [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hg, Matrix.mul_one,
    Matrix.one_mul, trace_sub, trace_one, trace_conjTranspose, Fintype.card_fin, Complex.sub_re,
    Complex.natCast_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h2
  simp only [peak, trace_one, Fintype.card_fin, Complex.natCast_re]
  linarith

def intCLM {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    (μ : Measure K) [IsFiniteMeasure μ] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (p : K → B) (hp : Continuous p) : C(K, ℂ) →L[ℂ] B := GlobalTheory.IntegralAgainstMeasure.integralAgainst μ ⟨p, hp⟩

theorem exists_holomorphic_extension : ∀ (n : ℕ) (ε : Fin n → Bool) (B : Type) [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → B), π 1 = 1 → (∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, π (a * b) = π a * π b) → ContinuousOn π (Formalism.REAL.Kset ε) → ∃ τ : Matrix (Fin n) (Fin n) ℂ → B, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)} ∧ ∀ k ∈ Formalism.REAL.Kset ε, τ k = π k := by
  intro n ε B _ _ _ π h1 hmul hcont
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : TopologicalSpace.MetrizableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : TopologicalSpace.MetrizableSpace (KG ε) := hemb.metrizableSpace
  haveI : SecondCountableTopology (KG ε) := hemb.secondCountableTopology
  set μ := muK ε
  have hmem : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hun : ∀ x ∈ Kset ε, xᴴ * x = 1 := fun x hx => Unitary.star_mul_self_of_mem hx.1
  have hu : Continuous fun g : KG ε => toMK g := hemb.continuous
  have hb : Continuous fun g : KG ε => π (toMK g) := hcont.comp_continuous hu hmem
  have hc : Continuous fun g : KG ε => peak (toMK g) := by
    unfold peak
    fun_prop
  have hone : toMK (1 : KG ε) = 1 := rfl
  have hlim := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := μ) (s := Set.univ) (x₀ := (1 : KG ε)) (c := fun g : KG ε => peak (toMK g))
    (g := fun g : KG ε => π (toMK g)) isCompact_univ hc.continuousOn
    (fun y _ hy => peak_lt (hun _ (hmem y)) fun h => hy (hemb.injective h))
    (fun y _ => (peak_pos (hun _ (hmem y))).le) (peak_pos (hun _ (hmem 1))) (by simp) hb.continuousOn
  simp only [Measure.restrict_univ, hone, h1] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (Metric.ball_mem_nhds _ one_pos)).exists
  set c := ∫ g : KG ε, peak (toMK g) ^ N ∂μ
  set A := ∫ g : KG ε, peak (toMK g) ^ N • π (toMK g) ∂μ with hA
  have hint : Integrable (fun g : KG ε => peak (toMK g) ^ N • π (toMK g)) μ :=
    ((hc.pow N).smul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAu : ∃ A' : B, A * A' = 1 := by
    have e3 : ‖(1 : B) - c⁻¹ • A‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]
      exact hN
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one e3
    rw [sub_sub_cancel] at hu
    refine ⟨c⁻¹ • (↑u⁻¹ : B), ?_⟩
    rw [mul_smul_comm, ← smul_mul_assoc, ← hu, Units.mul_inv]
  obtain ⟨A', hA'⟩ := hAu
  have hform : ∀ x ∈ Kset ε, π x * A = ∫ g : KG ε, peak (xᴴ * toMK g) ^ N • π (toMK g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (fun g : KG ε => toMK g) := by
      rw [range_toMK]; exact hx
    have hz' : toMK z = x := hz
    have := (ContinuousLinearMap.mul ℂ B (π x)).integral_comp_comm hint
    rw [ContinuousLinearMap.mul_apply'] at this
    rw [hA, ← this,
      ← integral_mul_left_eq_self (fun g : KG ε => peak (xᴴ * toMK g) ^ N • π (toMK g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : toMK (z * g) = x * toMK g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hun x hx, Matrix.one_mul, hmul _ hx _ (hmem g), ContinuousLinearMap.mul_apply',
      mul_smul_comm]
  let e : Fin n → Fin n → C(KG ε, ℂ) := fun i j => ⟨fun g => toMK g i j, hu.matrix_elem i j⟩
  let F : Matrix (Fin n) (Fin n) ℂ → C(KG ε, ℂ) := fun y =>
    ((1 + 2 * n : ℂ) • (1 : C(KG ε, ℂ)) + ∑ i, ∑ j, y⁻¹ i j • e j i + ∑ i, ∑ j, y j i • star (e j i)) ^ N
  refine ⟨fun y => intCLM μ _ hb (F y) * A', ?_, fun k hk => ?_⟩
  · refine DifferentiableOn.mul_const ((intCLM μ _ hb).differentiable.comp_differentiableOn ?_) _
    refine DifferentiableOn.pow (DifferentiableOn.add (DifferentiableOn.add (differentiableOn_const _) ?_) ?_) N
    · exact DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (differentiableOn_inv n i j).smul_const _
    · refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        DifferentiableOn.smul_const ?_ _
      simp only [Matrix.of_apply]
      fun_prop
  · have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (hun k hk)
    have hI : intCLM μ _ hb (F k) = π k * A := by
      rw [hform k hk]
      show ∫ g, F k g • π (toMK g) ∂μ = _
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have : F k g = ((peak (kᴴ * toMK g) ^ N : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, peak_coe, conjTranspose_mul, conjTranspose_conjTranspose]
        simp [F, e, hinv, Matrix.trace, Matrix.mul_apply, mul_comm]
      simp only [this, Complex.coe_smul]
    show intCLM μ _ hb (F k) * A' = π k
    rw [hI, mul_assoc, hA', mul_one]

end GlobalTheory.HolExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepMemCyclotomicAdjoinStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOfFDRep_mem_cyclotomic_adjoin : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ → ∀ x, χ x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  first | exact @GlobalTheory.GLm.isChar_mem_adjoin_exp | exact GlobalTheory.GLm.isChar_mem_adjoin_exp | (intros; apply GlobalTheory.GLm.isChar_mem_adjoin_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClassFunctionBernsteinZelevinskyDerivativeStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClassFunction_bernsteinZelevinskyDerivative : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ), i < n → IsMirClass F → IsClass (der ψ i F) := by
  first | exact @GlobalTheory.GLm.DerClass.isClass_der | exact GlobalTheory.GLm.DerClass.isClass_der | (intros; apply GlobalTheory.GLm.DerClass.isClass_der <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIrrAndDenseOfIsFdegG
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem IsFdegG.dense_span_orbit {G : Type} [MeasurableSpace G] {μ : Measure G} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : G → (H →L[ℂ] H)} {d : ℝ} (h : IsFdegG μ σ d)
    (w : H) (hw : w ≠ 0) : Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  obtain ⟨hd, hint⟩ := h
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  rw [Submodule.mem_orthogonal] at hu

  have hzero : ∀ g, ⟪u, σ g w⟫_ℂ = 0 := fun g =>
    inner_eq_zero_symm.mp (hu (σ g w) (Submodule.subset_span ⟨g, rfl⟩))

  have key := (hint w u w u).2
  have hfun : (fun g => ⟪u, σ g w⟫_ℂ * star ⟪u, σ g w⟫_ℂ) = fun _ => (0 : ℂ) := by
    funext g
    simp [hzero g]
  rw [hfun, integral_zero] at key
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hw' : ⟪w, w⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hw
  have huu : ⟪u, u⟫_ℂ = 0 := by
    rcases div_eq_zero_iff.mp key.symm with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hw'
    · exact absurd h1 hd'
  exact inner_self_eq_zero.mp huu

theorem isIrr_and_dense_of_isFdegG : ∀ (G : Type) [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)) (d : ℝ), IsFdegG μ σ d → IsIrr σ ∧ ∀ w : H, w ≠ 0 → Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set H) := by
  intro G _ μ H _ _ _ σ d h
  refine ⟨?_, fun w hw => IsFdegG.dense_span_orbit h w hw⟩
  intro S hS hinv
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwS, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot

    have hsub : Submodule.span ℂ (Set.range fun g => σ g w) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hinv g w hwS
    have hcl : closure ((Submodule.span ℂ (Set.range fun g => σ g w) : Submodule ℂ H) : Set H) ⊆ (S : Set H) :=
      closure_minimal (fun y hy => hsub hy) hS
    rw [Submodule.eq_top_iff']
    intro x
    exact hcl (by rw [(IsFdegG.dense_span_orbit h w hw).closure_eq]; exact Set.mem_univ x)

end GlobalTheory.Dec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocallySelfDualOfHermitianLatticeOfLevelStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), TLat cm.sig J T f L → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∉ v.asIdeal → SelfDualAt cm.sig J v L := by
  first | exact @GlobalTheory.St.G.selfDualAt_of_tLat | exact GlobalTheory.St.G.selfDualAt_of_tLat | (intros; apply GlobalTheory.St.G.selfDualAt_of_tLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFunStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicConjInvariant_twistedTailMeanFun : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ), 1 ≤ m → m ≤ n → IsMirClass F → IsMirClass (tail ψ m F) := by
  first | exact @GlobalTheory.GLm.TailClass.isMirClass_tail | exact GlobalTheory.GLm.TailClass.isMirClass_tail | (intros; apply GlobalTheory.GLm.TailClass.isMirClass_tail <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrankStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRadical_span_prime_of_ncard_primesOver_eq_finrank : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E → (Ideal.span {(p : 𝓞 E)}).IsRadical := by
  first | exact @GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver | exact GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver | (intros; apply GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotypicTraceEqOfOneDoubleCosetStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotypic_trace_eq_of_one_double_coset : ∀ (G : Type) [Group G] [Fintype G] (H H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ), H₁ ≤ H → H₂ ≤ H → Nat.card H₁ = Nat.card H₂ → (∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b) → (∀ h ∈ H, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a) → (∀ h ∈ H, h ∉ H₂ → ∃ b b' : H₂, (b' : G) = h⁻¹ * b * h ∧ l₂ b' ≠ l₂ b) → ∀ φ : G → ℂ, IsClass φ → (Nat.card H₁ : ℂ)⁻¹ * ∑ a : H₁, ((l₁ a)⁻¹ : ℂˣ) * φ a = (Nat.card H₂ : ℂ)⁻¹ * ∑ b : H₂, ((l₂ b)⁻¹ : ℂˣ) * φ b := by
  first | exact @GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq | exact GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq | (intros; apply GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq <;> assumption)
end

