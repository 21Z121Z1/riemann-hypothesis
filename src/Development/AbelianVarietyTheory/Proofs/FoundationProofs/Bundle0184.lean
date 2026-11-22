import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerUnitsFiniteModPowersAtLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumHeckeTAdjoint
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTopologicalGeneratorTauTower
section
open GlobalTheory.K5 Polynomial IntermediateField

noncomputable section

namespace GlobalTheory.K5.TauGen

theorem not_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := GlobalTheory.T.q_not_pth_pow_in_closure_algebraic_padicInt

def geoF (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x})

theorem isOpen_setOf_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
    (x : Ω) (P : Ω → Prop) : IsOpen {σ : Ω ≃ₐ[F] Ω | P (σ x)} := by
  haveI : FiniteDimensional F F⟮x⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  have hU : IsOpen (((F⟮x⟯).fixingSubgroup : Subgroup (Ω ≃ₐ[F] Ω)) : Set (Ω ≃ₐ[F] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hV : IsOpen ((fun τ : Ω ≃ₐ[F] Ω => σ⁻¹ * τ) ⁻¹' ((F⟮x⟯).fixingSubgroup : Set (Ω ≃ₐ[F] Ω))) :=
    hU.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hV.mem_nhds ?_) ?_
  · show σ⁻¹ * σ ∈ (F⟮x⟯).fixingSubgroup
    rw [inv_mul_cancel]; exact one_mem _
  · intro τ hτ
    have h1 := (mem_fixingSubgroup_iff _ _).1 hτ x (mem_adjoin_simple_self F x)
    have h2 : τ x = σ x := by
      have : σ⁻¹ (τ x) = x := h1
      calc τ x = σ (σ⁻¹ (τ x)) := by simp
        _ = σ x := by rw [this]
    show P (τ x)
    rw [h2]; exact hσ

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ T : Tower p Ω, ∃ τ ∈ Ggeo p Ω, ∀ n, τ (T.qq n) = T.ζ n * T.qq n := by
  intro p hp hp2 Ω _ _ hΩ T
  haveI := hΩ.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo hΩ
  have hO : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ geoF p Ω := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hA : ∀ x : Ω, IsAlgZp p x → x ∈ geoF p Ω := fun x hx => Subfield.subset_closure (Or.inr hx)
  let F := geoF p Ω
  let φ : O0 p →+* F := (algebraMap (O0 p) Ω).codRestrict F hO
  have hφ : Function.Injective φ := fun a b h => hΩ.inj (congrArg Subtype.val h)
  have hcomp : (algebraMap F Ω).comp φ = algebraMap (O0 p) Ω := by ext a; rfl
  haveI hal : Algebra.IsAlgebraic F Ω := by
    constructor
    intro x
    obtain ⟨P, hP, hx⟩ := hΩ.alg.isAlgebraic x
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφ).2 hP, ?_⟩
    rw [aeval_def, eval₂_map, hcomp, ← aeval_def, hx]
  haveI : IsAlgClosure F Ω := ⟨inferInstance, hal⟩
  haveI : IsGalois F Ω := {}
  haveI : CompactSpace (Ω ≃ₐ[F] Ω) := inferInstance
  let q' : F := ⟨algebraMap (O0 p) Ω (qO p), hO _⟩
  have hirr : ∀ n, Irreducible (X ^ (p ^ n) - C q') := fun n =>
    X_pow_sub_C_irreducible_of_prime_pow hp.out hp2 n (fun b hb =>
      not_pow p Ω hΩ (b : Ω) b.2 (by rw [← SubmonoidClass.coe_pow, hb]))
  have hmin : ∀ n (y : Ω), y ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) → minpoly F y = X ^ (p ^ n) - C q' := by
    intro n y hy
    refine (minpoly.eq_of_irreducible_of_monic (hirr n) ?_ (monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero))).symm
    simp only [map_sub, map_pow, aeval_X, aeval_C, hy]
    exact sub_self _
  let S : ℕ → Set (Ω ≃ₐ[F] Ω) := fun n => {σ | σ (T.qq n) = T.ζ n * T.qq n}
  have hne : ∀ n, (S n).Nonempty := by
    intro n
    have h1 := hmin n (T.qq n) (Basic.qq_pow T n)
    have h2 := hmin n (T.ζ n * T.qq n) (by rw [mul_pow, (T.prim n).pow_eq_one, one_mul, Basic.qq_pow T n])
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) Ω).1 (h2.trans h1.symm)
    exact ⟨σ, hσ⟩
  have hdec : ∀ n, S (n + 1) ⊆ S n := by
    intro n σ hσ
    show σ (T.qq n) = T.ζ n * T.qq n
    have hσ' : σ (T.qq (n + 1)) = T.ζ (n + 1) * T.qq (n + 1) := hσ
    rw [← T.qpow n, map_pow, hσ', mul_pow, T.ζpow, T.qpow]
  have hcl : ∀ n, IsClosed (S n) := by
    intro n
    rw [← isOpen_compl_iff]
    exact isOpen_setOf_apply (F := F) (T.qq n) (fun y => ¬ y = T.ζ n * T.qq n)
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  let τ : Gal p Ω :=
    { σ.toRingEquiv with
      commutes' := fun a => σ.commutes (⟨algebraMap (O0 p) Ω a, hO a⟩ : F) }
  refine ⟨τ, fun x hx => σ.commutes (⟨x, hA x hx⟩ : F), fun n => hσ n⟩

end GlobalTheory.K5.TauGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationUniqueOnLthRootLevelFields
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.UniqRoot

theorem exists_finite_field {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (A : Set E) (hfin : A.Finite)
    (hA : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin F {t}) a) :
    ∃ (L : IntermediateField F E) (ht : t ∈ L), A ⊆ L ∧
      FiniteDimensional (IntermediateField.adjoin F {(⟨t, ht⟩ : L)}) L := by
  let K₀ : IntermediateField F E := IntermediateField.adjoin F {t}
  let L' : IntermediateField K₀ E := IntermediateField.adjoin K₀ A
  haveI : Finite A := hfin
  have hL' : FiniteDimensional K₀ L' := IntermediateField.finiteDimensional_adjoin fun a ha => (hA a ha).isIntegral
  let L : IntermediateField F E := L'.restrictScalars F
  have hK : ∀ x : K₀, (x : E) ∈ L := fun x => L'.algebraMap_mem x
  have ht : t ∈ L := hK ⟨t, IntermediateField.mem_adjoin_simple_self F t⟩
  refine ⟨L, ht, fun a ha => IntermediateField.subset_adjoin K₀ A ha, ?_⟩
  let K' : IntermediateField F L := IntermediateField.adjoin F {(⟨t, ht⟩ : L)}
  have hmap : K'.map L.val = K₀ := by
    simp only [K', K₀, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ x : K₀, (⟨x, hK x⟩ : L) ∈ K' := by
    intro x
    have hx : (x : E) ∈ K'.map L.val := by rw [hmap]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = ⟨x, hK x⟩ := Subtype.ext hyx
    exact this ▸ hy
  let φ : K₀ →+* K' :=
    { toFun := fun x => ⟨⟨x, hK x⟩, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra K₀ K' := φ.toAlgebra
  letI : Algebra K₀ L := (inferInstance : Algebra K₀ L')
  haveI : Module.Finite K₀ L := hL'
  haveI : IsScalarTower K₀ K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K₀ K' L

theorem valuation_eq_one_iff' {K : Type} [Field K] (W : ValuationSubring K) (x : K) :
    W.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ W ∧ x⁻¹ ∈ W := by
  rw [← W.valuation_le_one_iff, ← W.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨?_, h.le, by rw [h, inv_one]⟩
    rintro rfl
    simp at h
  · rintro ⟨h0, h1, h2⟩
    have hp : 0 < W.valuation x := zero_lt_iff.2 ((map_ne_zero _).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ hp).1 h2)

theorem gauss_comap {F E : Type} [Field F] [Field E] [Algebra F E] {t : E} (L : IntermediateField F E) (ht : t ∈ L)
    {V : ValuationSubring F} {W : ValuationSubring E} (h : Gauss t V W) :
    Gauss (⟨t, ht⟩ : L) V (W.comap (algebraMap L E)) := by
  refine ⟨fun a => ?_, fun P hP hu => ?_⟩
  · rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact h.1 a
  · have h1 := (valuation_eq_one_iff' _ _).1 (h.2 P hP hu)
    have e : algebraMap L E (Polynomial.aeval (⟨t, ht⟩ : L) P) = Polynomial.aeval t P :=
      (Polynomial.aeval_algHom_apply L.val (⟨t, ht⟩ : L) P).symm
    rw [valuation_eq_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, e]
    refine ⟨fun h0 => h1.1 ?_, h1.2⟩
    rw [← e, h0, map_zero]

theorem transcendental_j {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  intro h
  have hd := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible h.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one Ω X.jK hd
  have h1 := X.j_exp.1
  rw [← hc, AlgHom.commutes] at h1
  simp [HahnSeries.algebraMap_apply', HahnSeries.coeff_single] at h1

theorem gauss_unique_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring (AlgebraicClosure X.K), Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₁ → Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₂ → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), f ∈ X.Un l → Lev X M₀ f → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → ∀ x ∈ IntermediateField.adjoin (levF X M₀) {θ}, x ∈ W₁ ↔ x ∈ W₂ := by
  classical
  intro Ω _ _ _ ε X hj l M₀ hl hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have halgΩ : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by
    convert halgΩ
    exact Subsingleton.elim _ _
  obtain ⟨R, hR⟩ := GlobalTheory.KZ.FinLev.finite_mod_powers ε X ε.injective hj M₀ l hM hl.pos
  obtain ⟨T, -, hT⟩ := GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions ε X hj M₀ hM
  let E := AlgebraicClosure X.K
  let ι : X.K →ₐ[Ω] E := IsScalarTower.toAlgHom Ω X.K E
  let t : E := algebraMap X.K E X.jK
  have hmap : (IntermediateField.adjoin Ω {X.jK}).map ι = IntermediateField.adjoin Ω {t} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin Ω {X.jK}, ι c ∈ IntermediateField.adjoin Ω {t} :=
    fun c => hmap ▸ ⟨c, c.2, rfl⟩
  have halg : ∀ f : X.K, IsAlgebraic (IntermediateField.adjoin Ω {t}) (algebraMap X.K E f) := by
    intro f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* IntermediateField.adjoin Ω {t} :=
      (ι.toRingHom.comp (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)).codRestrict
        (IntermediateField.adjoin Ω {t}) hmem
    exact ((X.alg_j f).isIntegral.map_of_comp_eq φ (algebraMap X.K E) (RingHom.ext fun _ => rfl)).isAlgebraic
  let A : Set E := algebraMap X.K E '' (T : Set X.K) ∪
    ⋃ r ∈ (R : Set X.Kˣ), {y : E | y ^ l = algebraMap X.K E (r : X.K)}
  have hAfin : A.Finite := by
    refine (T.finite_toSet.image _).union (R.finite_toSet.biUnion fun r _ => ?_)
    refine (Polynomial.nthRoots l (algebraMap X.K E (r : X.K))).toFinset.finite_toSet.subset fun y hy => ?_
    simpa [Polynomial.mem_nthRoots hl.pos] using hy
  have hAalg : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin Ω {t}) a := by
    rintro a (⟨f, -, rfl⟩ | ha)
    · exact halg f
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq] at ha
      obtain ⟨r, -, hr⟩ := ha
      exact IsAlgebraic.of_pow hl.pos (hr ▸ halg r)
  obtain ⟨L, ht, hAL, hfin⟩ := exists_finite_field (F := Ω) t A hAfin hAalg
  have htr : Transcendental Ω (⟨t, ht⟩ : L) := by
    intro h
    have h1 : IsAlgebraic Ω (ι X.jK) := h.algHom L.val
    exact transcendental_j X ((isAlgebraic_algHom_iff ι ι.toRingHom.injective).1 h1)
  obtain ⟨S, hS⟩ := GlobalTheory.T.gauss_valuationSubring_unique_away_finset (F := Ω) (⟨t, ht⟩ : L) htr hfin
  have hlev : ∀ f : X.K, Lev X M₀ f → algebraMap X.K E f ∈ L := by
    intro f hf
    have hsp := hT f hf
    clear hf
    induction hsp using Submodule.span_induction with
    | mem x hx => exact hAL (Or.inl ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact L.add_mem hx hy
    | smul c x _ hx =>
      have hc : ι c ∈ L := (IntermediateField.adjoin_simple_le_iff.2 ht) (hmem c)
      have e : algebraMap X.K E (c • x) = ι c * algebraMap X.K E x := by
        rw [IntermediateField.smul_def, smul_eq_mul, map_mul]
        rfl
      rw [e]
      exact L.mul_mem hc hx
  have hlevF : levF X M₀ ≤ L := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hlev f hf
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ θ f hf hfl hθ x hx => ?_⟩
  have hW := hS q hq hqS V hV _ _ (gauss_comap L ht h₁) (gauss_comap L ht h₂)
  obtain ⟨r, hr, g, hg, c, hc, hfe⟩ := hR f hf hfl
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hl.pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne_zero] at hd
    exact hc hd.symm
  let u : E := algebraMap X.K E (g : X.K) * algebraMap Ω E d
  have hu0 : u ≠ 0 := mul_ne_zero ((map_ne_zero _).2 g.ne_zero) ((map_ne_zero _).2 hd0)
  have huL : u ∈ L := L.mul_mem (hlev g hg) (L.algebraMap_mem d)
  have hy : (θ / u) ^ l = algebraMap X.K E (r : X.K) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hu0), hθ, hfe, mul_pow, ← map_pow, ← map_pow, hd, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc]
  have hθL : θ ∈ L := by
    have h1 : θ / u ∈ L := hAL (Or.inr (Set.mem_biUnion (Finset.mem_coe.2 hr) hy))
    have := L.mul_mem h1 huL
    rwa [div_mul_cancel₀ _ hu0] at this
  have hxL : x ∈ L := by
    have hle : IntermediateField.adjoin (levF X M₀) {θ} ≤ IntermediateField.extendScalars hlevF :=
      IntermediateField.adjoin_simple_le_iff.2 hθL
    exact hle hx
  have := SetLike.ext_iff.1 hW ⟨x, hxL⟩
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at this
  exact this

end GlobalTheory.KZ.ES.UniqRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeff
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem tendsto_eulerProduct_LSeries_of_sq : ∀ (b : ℕ → ℂ) (s : ℝ), 0 < s → b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)) atTop (𝓝 (LSeries b ((1 + s : ℝ) : ℂ))) := by
  intro b s hs hb1 hmul hsum
  have hn : Summable (fun n : ℕ => ‖LSeries.term b ((1 + s : ℝ) : ℂ) n‖) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) :=
      Real.summable_one_div_nat_rpow.2 (by linarith)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hsum.add h1)
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · positivity
    · rw [Complex.ofReal_re, ← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (‖b n‖ - 1), norm_nonneg (b n)]
  refine EulerProduct.eulerProduct (f := LSeries.term b ((1 + s : ℝ) : ℂ)) ?_ ?_ hn ?_
  · simp [LSeries.term, hb1]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn0,
      LSeries.term_of_ne_zero (mul_ne_zero hm hn0), hmul m n hmn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, div_mul_div_comm]
  · simp

theorem prod_primesBelow_sq_le_tsum : ∀ (b : ℕ → ℂ) (s : ℝ), b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) ≤ ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro b s hb1 hmul hsum N
  have h0 : ∀ n : ℕ, 0 ≤ ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := fun n => by positivity
  have key := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) (by simp [hb1])
    (fun {m n} hmn => by
      simp only [hmul m n hmn, norm_mul, mul_pow, Nat.cast_mul]
      rw [Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm])
    (by simpa only [Real.norm_of_nonneg (h0 _)] using hsum) N
  rw [key]
  exact hsum.tsum_subtype_le _ _ h0

theorem global_positivity_ineq : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro M b ω s C hs hb1 hb0 hmul hbM hrec hC hsum X
  set f : ℕ → ℝ := fun n => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hf
  set Ssum := ∑' n : ℕ, f n
  set Lp : ℕ → ℂ := fun p => ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) with hLp
  set Rp : ℕ → ℝ := fun p => ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) with hRp
  set α : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ with hα
  set β : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ with hβ
  set A : ℕ → ℝ := fun p => if ¬ p ∣ M then ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) else 0 with hA
  have hA0 : ∀ p, 0 ≤ A p := fun p => by
    simp only [hA]; split_ifs <;> positivity

  have hα1 : ∀ p : ℕ, p.Prime → 1 ≤ α p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
    have h3 : 1 / (p : ℝ) ^ (1 + s) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hα]
    rw [one_le_inv₀ (by linarith)]; linarith
  have hβ1 : ∀ p : ℕ, p.Prime → 1 ≤ β p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (2 * (1 + s)) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (2 * (1 + s)) := by positivity
    have h3 : 1 / (p : ℝ) ^ (2 * (1 + s)) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hβ]
    rw [one_le_inv₀ (by linarith)]; linarith

  have hdiv : ∀ p : ℕ, p.Prime → p ∣ M → Lp p = 1 ∧ Rp p = 1 := by
    intro p hp hpM
    have hz : ∀ e : ℕ, e ≠ 0 → b (p ^ e) = 0 := by
      intro e he
      apply hbM
      intro hc
      have : p ∣ Nat.gcd (p ^ e) M := Nat.dvd_gcd (dvd_pow_self p he) hpM
      rw [hc] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    constructor
    · simp only [hLp]
      rw [tsum_eq_single 0]
      · simp [LSeries.term, hb1]
      · intro e he; simp [LSeries.term, hz e he]
    · simp only [hRp]
      rw [tsum_eq_single 0]
      · simp [hb1]
      · intro e he; simp [hz e he]
  have hRp0 : ∀ p, 0 ≤ Rp p := fun p => tsum_nonneg (fun e => by positivity)
  have hα0 : ∀ p : ℕ, p.Prime → 0 ≤ α p := fun p hp => le_trans zero_le_one (hα1 p hp)
  have hβ0 : ∀ p : ℕ, p.Prime → 0 ≤ β p := fun p hp => le_trans zero_le_one (hβ1 p hp)

  have hloc : ∀ p : ℕ, p.Prime → Real.exp (A p) ≤ α p * ‖Lp p‖ ^ 2 * Rp p * β p := by
    intro p hp
    by_cases hpM : p ∣ M
    · obtain ⟨h1, h2⟩ := hdiv p hp hpM
      simp only [hA, hpM, not_true_eq_false, if_false, Real.exp_zero, h1, h2, norm_one, one_pow, mul_one]
      nlinarith [hα1 p hp, hβ1 p hp]
    · have := GlobalTheory.T.local_positivity_eulerFactor_prime b ω s C p hs hp hb1 (hrec p 1 hp hpM).1 (fun r => (hrec p r hp hpM).2) hC
      simpa only [hA, hpM, not_false_eq_true, if_true] using this

  have hfin : ∀ N : ℕ, X ≤ N → Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by
    intro N hN
    have e1 : ∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) = ∑ p ∈ X.primesBelow, A p := by
      rw [Nat.primesBelow, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h1 : p.Prime <;> by_cases h2 : p ∣ M <;> simp [hA, h1, h2]
    have e2 : ∑ p ∈ X.primesBelow, A p ≤ ∑ p ∈ N.primesBelow, A p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesBelow_mono hN) (fun p _ _ => hA0 p)
    rw [e1]
    calc Real.exp (∑ p ∈ X.primesBelow, A p) ≤ Real.exp (∑ p ∈ N.primesBelow, A p) := Real.exp_le_exp.mpr e2
      _ = ∏ p ∈ N.primesBelow, Real.exp (A p) := Real.exp_sum _ _
      _ ≤ ∏ p ∈ N.primesBelow, (α p * ‖Lp p‖ ^ 2 * Rp p * β p) :=
          Finset.prod_le_prod (fun p _ => (Real.exp_pos _).le) (fun p hp => hloc p (Nat.prime_of_mem_primesBelow hp))
      _ = (∏ p ∈ N.primesBelow, α p) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * (∏ p ∈ N.primesBelow, Rp p) * (∏ p ∈ N.primesBelow, β p) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, norm_prod, Finset.prod_pow]
      _ ≤ (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum * 2 := by
          have a1 := GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le s hs N
          have a2 := GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le s hs.le N
          have a3 := prod_primesBelow_sq_le_tsum b s hb1 hmul hsum N
          have p1 : 0 ≤ ∏ p ∈ N.primesBelow, α p := Finset.prod_nonneg (fun p hp => hα0 p (Nat.prime_of_mem_primesBelow hp))
          have p2 : 0 ≤ ∏ p ∈ N.primesBelow, Rp p := Finset.prod_nonneg (fun p _ => hRp0 p)
          have p3 : 0 ≤ ∏ p ∈ N.primesBelow, β p := Finset.prod_nonneg (fun p hp => hβ0 p (Nat.prime_of_mem_primesBelow hp))
          gcongr
      _ = 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by ring
  have hlim := tendsto_eulerProduct_LSeries_of_sq b s hs hb1 hmul hsum
  have hcont : Tendsto (fun N : ℕ => 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum) atTop (𝓝 (2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * Ssum)) :=
    ((hlim.norm.pow 2).const_mul _).mul_const _
  exact ge_of_tendsto hcont (Filter.eventually_atTop.mpr ⟨X, hfin⟩)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodTupleProjectorIsProjCentral
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem conv_comm_of_classFun {G : Type} [Group G] [Fintype G] (e : G → ℂ) (he : ∀ x y, e (x * y) = e (y * x))
    (a : G → ℂ) : conv e a = conv a e := by
  funext x
  simp only [conv]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight]
  rw [mul_comm, he (y⁻¹ * x)⁻¹ x]
  congr 2
  group

theorem conv_finsetSum_finsetSum {G κ : Type} [Group G] [Fintype G] (s t : Finset κ) (a b : κ → G → ℂ) :
    conv (∑ i ∈ s, a i) (∑ j ∈ t, b j) = ∑ i ∈ s, ∑ j ∈ t, conv (a i) (b j) := by
  funext x
  simp only [conv, Finset.sum_apply, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem isProj_finsetSum {G κ : Type} [Group G] [Fintype G] (s : Finset κ) (a : κ → G → ℂ) (h : ∀ i ∈ s, IsProj (a i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → conv (a i) (a j) = 0) : IsProj (∑ i ∈ s, a i) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [conv_finsetSum_finsetSum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single_of_mem i hi fun j hj hne => ho i hi j hj hne.symm, (h i hi).1]
  · simp only [Finset.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i hi => (h i hi).2 x

theorem eGood_isProj_central : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m : ℕ) (ι : Type) [Fintype ι] (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), (∀ v, IsSeries (τ v)) → IsProj (eGood τ ch) ∧ ∀ a, conv (eGood τ ch) a = conv a (eGood τ ch) := by
  intro g _ N m ι _ τ ch hτ
  have hmem : ∀ F ∈ goodSet g N ch, ∀ v, F v ∈ sqSet g N := fun F hF =>
    (good_iff.1 (mem_goodSet_iff_good.1 hF)).1
  refine ⟨isProj_finsetSum _ _ (fun F hF => ?_) fun F hF F' hF' hne => ?_, conv_comm_of_classFun _ fun x y => ?_⟩
  · refine (tens_calculus ι (GG g N) (GG g N)).2.1 _ fun v => ?_
    obtain ⟨V, hV, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    rw [← hχ]
    exact (GlobalTheory.T.centralIdempotent_irreducible_character_props _ V).1
  · rw [conv_tens]
    obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
    obtain ⟨V, hV, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    obtain ⟨V', hV', hχ', -⟩ := (hτ v).2 _ (hmem F' hF' v)
    have h0 : conv (zc (τ v (F v))) (zc (τ v (F' v))) = 0 := by
      rw [← hχ, ← hχ']
      refine (GlobalTheory.T.centralIdempotent_irreducible_character_props _ V).2.2.1 V' ?_
      rw [hχ, hχ']
      exact fun h => hv ((hτ v).1 (hmem F hF v) (hmem F' hF' v) h)
    funext x
    exact Finset.prod_eq_zero (Finset.mem_univ v) (congrFun h0 (x v))
  · simp only [eGood, Finset.sum_apply, tens]
    refine Finset.sum_congr rfl fun F hF => Finset.prod_congr rfl fun v _ => ?_
    obtain ⟨V, -, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    simp only [zc, ← hχ, Pi.mul_apply, mul_inv_rev]
    rw [FDRep.char_mul_comm]

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCoboundaryTwistCochainStatement
section
open GlobalTheory.NeedB Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_carry_coboundary_twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  first | exact @GlobalTheory.NeedB.TwistCochain.twist_cochain | exact GlobalTheory.NeedB.TwistCochain.twist_cochain | (intros; apply GlobalTheory.NeedB.TwistCochain.twist_cochain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumHeckeTAdjointStatement
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_heckeT_adjoint : ∀ (N l q : ℕ) (k : ℤ) (σ σ' : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l q σ' → ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.heckeT k q σ ⇑f) (GlobalTheory.Hk.dia k σ' ⇑g) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (GlobalTheory.Hk.heckeT k q σ ⇑g) := by
  first | exact @GlobalTheory.Hk.pet_heckeT_adj | exact GlobalTheory.Hk.pet_heckeT_adj | (intros; apply GlobalTheory.Hk.pet_heckeT_adj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumSesquilinearHermitianStatement
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_sesquilinear_hermitian : ∀ (N l : ℕ) (k : ℤ), 0 < N → 0 < l → ∀ (f g h : CuspForm (GlobalTheory.Hk.lev N l) k) (c : ℂ), GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f (⇑g + c • ⇑h) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g + c * GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑h ∧ GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑g ⇑f = (starRingEnd ℂ) (GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g) := by
  first | exact @GlobalTheory.Hk.pet_sesq | exact GlobalTheory.Hk.pet_sesq | (intros; apply GlobalTheory.Hk.pet_sesq <;> assumption)
end

