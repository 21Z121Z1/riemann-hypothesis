import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodConjugateIntegral
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

noncomputable section

namespace GlobalTheory.LowerOps

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem act_of_mem_eigK {ρ : orderC c →+* Module.End O H} {σ : E →+* K} {x : K ⊗[O] H}
    (hx : x ∈ eigK ρ σ) (a : orderC c) : (ρ a).baseChange K x = σ a • x :=
  Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hx a)

theorem conj_ofF (a : OF E) :
    IsCMField.complexConj E ((ofF c a : orderC c) : E) = ((ofF c a : orderC c) : E) := by
  show IsCMField.complexConj E (algebraMap (OF E) E a) = algebraMap (OF E) E a
  rw [IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
  exact IsCMField.complexConj_apply_eq_self E _

theorem bar_ne_self (σ : E →+* K) : bar σ ≠ σ := by
  intro h
  apply IsCMField.complexConj_ne_one E
  ext x
  exact σ.injective (congrArg (fun τ : E →+* K => τ x) h)

theorem inK_mem_eigK {ρ : orderC c →+* Module.End O H} {σ : E →+* K} {y : H} (hy : y ∈ eigLat (K := K) ρ σ) :
    inK K H y ∈ eigK ρ σ := hy

theorem ext_of_eigLat [IsDomain O] [IsFractionRing O K] (ρ : orderC c →+* Module.End O H) (D : O) (hD : D ≠ 0)
    (hsum : ∀ h : H, D • h ∈ ⨆ σ : E →+* K, eigLat (K := K) ρ σ) (S T : Module.End K (K ⊗[O] H))
    (hST : ∀ σ : E →+* K, ∀ y ∈ eigLat (K := K) ρ σ, S (inK K H y) = T (inK K H y)) : S = T := by
  have hD' : algebraMap O K D ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hD
  have hsub : ∀ y ∈ ⨆ σ : E →+* K, eigLat (K := K) ρ σ, S (inK K H y) = T (inK K H y) := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem σ y hy => exact hST σ y hy
    | zero => simp
    | add y z _ _ hy hz => simp [map_add, hy, hz]
  have hH : ∀ h : H, S (inK K H h) = T (inK K H h) := by
    intro h
    have h1 : inK (O := O) K H (D • h) = algebraMap O K D • inK (O := O) K H h := by
      rw [map_smul, algebraMap_smul K D (inK K H h)]
    have h2 := hsub _ (hsum h)
    rw [h1, map_smul, map_smul] at h2
    exact smul_right_injective _ hD' h2
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul k h =>
    have : k ⊗ₜ[O] h = k • inK K H h := by simp [inK, TensorProduct.smul_tmul']
    rw [this, map_smul, map_smul, hH]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem lower_mem_eigK_bar {I : Type} {φ : I → E →+* K} {ρ : orderC c →+* Module.End O H} {e f : I → H}
    (hG : IsGens φ ρ e f) {i : I} {N : Module.End K (K ⊗[O] H)} (hN : IsLower ρ (φ i) (e i) (f i) N) {y : H}
    (hy : y ∈ eigLat (K := K) ρ (φ i)) : N (inK K H y) ∈ eigK ρ (bar (φ i)) := by
  rw [(hG i).1, Submodule.mem_span_singleton] at hy
  obtain ⟨r, rfl⟩ := hy
  have hf : inK K H (f i) ∈ eigK ρ (bar (φ i)) := by
    have : f i ∈ eigLat (K := K) ρ (bar (φ i)) := by
      rw [(hG i).2]; exact Submodule.mem_span_singleton_self _
    exact inK_mem_eigK this
  rw [map_smul, LinearMap.map_smul_of_tower, hN.1]
  exact Submodule.smul_of_tower_mem _ r hf

theorem lower_commute_and_mul_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i (a : OF E), Commute (N i) ((ρ (ofF c a)).baseChange K)) ∧ ∀ i j, N i * N j = 0 := by
  intro E _ _ _ c _ l _ O _ _ _ _ K _ _ _ _ _ D hD _ I _ φ hφ H _ _ ρ Fil B _ hEig e f hG N hN
  have hsum := hEig.2.2.1.2
  refine ⟨fun i a => ?_, fun i j => ?_⟩
  · show N i * (ρ (ofF c a)).baseChange K = (ρ (ofF c a)).baseChange K * N i
    apply ext_of_eigLat ρ D hD hsum
    intro σ y hy
    have hx := inK_mem_eigK (K := K) hy
    rw [Module.End.mul_apply, Module.End.mul_apply, act_of_mem_eigK hx, map_smul]
    by_cases hσ : σ = φ i
    · subst hσ
      have hm := lower_mem_eigK_bar hG (hN i) hy
      rw [act_of_mem_eigK hm]
      congr 1
      show _ = φ i (IsCMField.complexConj E ((ofF c a : orderC c) : E))
      rw [conj_ofF]
    · rw [(hN i).2 σ hσ _ hx, smul_zero, map_zero]
  · apply ext_of_eigLat ρ D hD hsum
    intro σ y hy
    have hx := inK_mem_eigK (K := K) hy
    rw [Module.End.mul_apply, LinearMap.zero_apply]
    by_cases hσ : σ = φ j
    · subst hσ
      have hm := lower_mem_eigK_bar hG (hN j) hy
      have hne : bar (φ j) ≠ φ i := by
        intro h
        obtain ⟨k, _, hk⟩ := hφ (bar (φ j))
        have hi := hk i (Or.inl h)
        have hj := hk j (Or.inr rfl)
        subst hi; subst hj
        exact bar_ne_self _ h
      exact (hN i).2 _ hne _ hm
    · rw [(hN j).2 σ hσ _ hx, map_zero]

end GlobalTheory.LowerOps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodDenominatorBound
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical

namespace GlobalTheory.PairingBound

section V
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem ord_mul' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : ord_vw O (a * b) = ord_vw O a + ord_vw O b := by
  unfold ord_vw
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb), neg_add]

theorem ord_alg_nonneg (x : O) (hx : x ≠ 0) : 0 ≤ ord_vw O (algebraMap O K x) := by
  have hx' : algebraMap O K x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hx
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hx'
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) ≤ 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact HeightOneSpectrum.intValuation_le_one _ x
  unfold ord_vw
  rw [← WithZero.exp_log h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  linarith

theorem ord_l_pos (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : 0 < ord_vw O (l : K) := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  unfold ord_vw
  rw [← WithZero.exp_log h2, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  linarith

theorem val_nonneg (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) (x : O) :
    0 ≤ val_vp O l (algebraMap O K x) := by
  unfold val_vp
  split_ifs with hx
  · exact le_top
  · have hx' : x ≠ 0 := by rintro rfl; exact hx (map_zero _)
    exact WithTop.coe_le_coe.2 (div_nonneg (by exact_mod_cast ord_alg_nonneg O x hx')
      (by exact_mod_cast (ord_l_pos O (K := K) l hl h).le))

theorem val_le_of_dvd (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) {x y : O} (hy : y ≠ 0)
    (hxy : x ∣ y) : val_vp O l (algebraMap O K x) ≤ val_vp O l (algebraMap O K y) := by
  obtain ⟨z, rfl⟩ := hxy
  have hx : x ≠ 0 := left_ne_zero_of_mul hy
  have hz : z ≠ 0 := right_ne_zero_of_mul hy
  have inj := IsFractionRing.injective O K
  have hx' : algebraMap O K x ≠ 0 := (map_ne_zero_iff _ inj).2 hx
  have hz' : algebraMap O K z ≠ 0 := (map_ne_zero_iff _ inj).2 hz
  have hy' : algebraMap O K (x * z) ≠ 0 := (map_ne_zero_iff _ inj).2 hy
  unfold val_vp
  rw [if_neg hx', if_neg hy', map_mul, ord_mul' O hx' hz']
  refine WithTop.coe_le_coe.2 (div_le_div_of_nonneg_right ?_ (by exact_mod_cast (ord_l_pos O (K := K) l hl h).le))
  push_cast
  linarith [(by exact_mod_cast ord_alg_nonneg O z hz : (0 : ℚ) ≤ ord_vw O (algebraMap O K z))]

end V

end GlobalTheory.PairingBound

namespace GlobalTheory.PairingBound

theorem pairing_val_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D) := by
  intro E _ _ _ c _ l hl O _ _ _ _ K _ _ _ hlm _ D hD _ I _ φ _ H _ _ ρ Fil B hLat hEig e f hGen i
  obtain ⟨hfree, -, -, -, -, -, hbij, halt, -⟩ := hLat
  obtain ⟨-, hsat, ⟨-, hsum⟩, -, horth⟩ := hEig
  obtain ⟨he, hf⟩ := hGen i
  haveI := hfree
  obtain ⟨-, ⟨g, hg0, hgs⟩, -, -, C, hC⟩ := hsat (φ i)
  have he0 : e i ≠ 0 := by
    intro h0
    rw [he, h0, Submodule.span_singleton_eq_bot.2 rfl] at hgs
    exact hg0 (Submodule.span_singleton_eq_bot.1 hgs.symm)
  have heL : e i ∈ eigLat ρ (φ i) := by rw [he]; exact Submodule.mem_span_singleton_self _
  rw [he] at hC
  let lam : H →ₗ[O] O := ((LinearEquiv.toSpanNonzeroSingleton O H (e i) he0).symm.toLinearMap).comp
    (Submodule.linearProjOfIsCompl _ C hC)
  have hlam : lam (e i) = 1 := by
    simp only [lam, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hp : (Submodule.linearProjOfIsCompl _ C hC) (e i) = ⟨e i, Submodule.mem_span_singleton_self _⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨e i, Submodule.mem_span_singleton_self _⟩
    rw [hp, LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  obtain ⟨h, hh⟩ := hbij.2 lam
  have hBeh : B (e i) h = -1 := by
    rw [← LinearMap.IsAlt.neg halt h (e i), hh, hlam]
  have hle : (⨆ σ : E →+* K, eigLat ρ σ) ≤ LinearMap.ker (B (e i)) ⊔ (O ∙ f i) := by
    refine iSup_le fun σ => ?_
    by_cases hσ : σ = bar (φ i)
    · subst hσ; rw [hf]; exact le_sup_right
    · refine le_sup_of_le_left fun y hy => ?_
      rw [LinearMap.mem_ker]
      have h0 := horth (φ i) σ hσ _ heL _ hy
      simp only [inK, TensorProduct.mk_apply, LinearMap.BilinForm.baseChange_tmul, mul_one, Algebra.smul_def]
        at h0
      exact (IsFractionRing.injective O K) (by rw [h0, map_zero])
  obtain ⟨k, hk, y, hy, hky⟩ := Submodule.mem_sup.1 (hle (hsum h))
  obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hdiv : B (e i) (f i) ∣ D := by
    have h1 := congrArg (B (e i)) hky
    rw [map_add, LinearMap.mem_ker.1 hk, zero_add, map_smul, map_smul, hBeh, smul_eq_mul, smul_eq_mul] at h1
    exact ⟨-u, by linear_combination h1⟩
  exact ⟨val_nonneg O l hl.ne_zero hlm _, val_le_of_dvd O l hl.ne_zero hlm hD hdiv⟩

end GlobalTheory.PairingBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodGaloisIntegral
section
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.CMFormBound

section Val

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem ord_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : ord_vw O (x * y) = ord_vw O x + ord_vw O y := by
  have hx' : (IsDiscreteValuationRing.maximalIdeal O).valuation K x ≠ 0 := by simpa using hx
  have hy' : (IsDiscreteValuationRing.maximalIdeal O).valuation K y ≠ 0 := by simpa using hy
  unfold ord_vw
  rw [map_mul, WithZero.log_mul hx' hy']
  ring

theorem ord_of_not_mem (x : O) (hx : x ∉ IsLocalRing.maximalIdeal O) : ord_vw O (algebraMap O K x) = 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (algebraMap O K x) = 1 :=
    le_antisymm ((IsDiscreteValuationRing.maximalIdeal O).valuation_le_one x)
      (not_lt.1 fun h => hx (((IsDiscreteValuationRing.maximalIdeal O).valuation_lt_one_iff_mem x).1 h))
  unfold ord_vw
  rw [h1, WithZero.log_one, neg_zero]

theorem ord_natCast_ne [CharZero O] (l : ℕ) (hl : l ≠ 0) (h : (l : O) ∈ IsLocalRing.maximalIdeal O) : ord_vw O (l : K) ≠ 0 := by
  have h0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap O K)]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (Nat.cast_ne_zero.2 hl)
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) < 1 := by
    rw [← map_natCast (algebraMap O K), HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).valuation K (l : K) ≠ 0 := by simpa using h0
  unfold ord_vw
  intro h4
  have := WithZero.exp_log h2
  rw [neg_eq_zero.1 h4, WithZero.exp_zero] at this
  exact h1.ne this.symm

theorem val_of_ne (l : ℕ) {x : K} (hx : x ≠ 0) :
    val_vp O l x = (((ord_vw O x : ℚ) / (ord_vw O (l : K) : ℚ) : ℚ) : WithTop ℚ) := by
  rw [val_vp, if_neg hx]

theorem val_mul (l : ℕ) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    val_vp O l (x * y) = val_vp O l x + val_vp O l y := by
  rw [val_of_ne O l hx, val_of_ne O l hy, val_of_ne O l (mul_ne_zero hx hy), ord_mul O hx hy,
    ← WithTop.coe_add]
  congr 1
  push_cast
  ring

end Val

theorem conj_sqrt (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (hd : d.Prime) (r : E)
    (hr : r ^ 2 = -(d : E)) : IsCMField.complexConj E r = -r := by
  have h1 : (IsCMField.complexConj E r) ^ 2 = r ^ 2 := by
    rw [← map_pow, hr, map_neg, map_natCast]
  have hne : IsCMField.complexConj E r ≠ r := by
    intro h
    let ψ : E →+* ℂ := Classical.choice inferInstance
    have h2 : conj (ψ r) = ψ r := by rw [← IsCMField.complexEmbedding_complexConj, h]
    have h3 : (ψ r) ^ 2 = -(d : ℂ) := by rw [← map_pow, hr, map_neg, map_natCast]
    obtain ⟨x, hx⟩ : ∃ x : ℝ, (x : ℂ) = ψ r := ⟨(ψ r).re, Complex.conj_eq_iff_re.1 h2⟩
    rw [← hx] at h3
    have h4 : x ^ 2 = -(d : ℝ) := by exact_mod_cast h3
    have h5 : (0 : ℝ) < d := by exact_mod_cast hd.pos
    nlinarith [sq_nonneg x]
  have h6 : (IsCMField.complexConj E r - r) * (IsCMField.complexConj E r + r) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h6 with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact eq_neg_of_add_eq_zero_left h

theorem eig_ext {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K] {H : Type} [AddCommGroup H] [Module O H]
    (ρ : orderC c →+* Module.End O H) (ρE : E →+* Module.End K (K ⊗[O] H))
    (hρE : ∀ a : orderC c, ρE a = (ρ a).baseChange K) (σ : E →+* K) (v : K ⊗[O] H) (hv : v ∈ eigK ρ σ)
    (a : E) : ρE a v = σ a • v := by
  have hS : ∀ b ∈ orderC c, ρE b v = σ b • v := by
    intro b hb
    have := Module.End.mem_eigenspace_iff.1 (Submodule.mem_iInf _ |>.1 hv ⟨b, hb⟩)
    rw [show b = ((⟨b, hb⟩ : orderC c) : E) from rfl, hρE]
    exact this
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  set N := algebraMap (OF E) (𝓞 E) n with hN
  have hmem : ∀ z : 𝓞 E, algebraMap (𝓞 E) E (N * z) ∈ orderC c := fun z =>
    Subring.subset_closure (Or.inr ⟨N * z, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hn), rfl⟩)
  have hy0 : algebraMap (𝓞 E) E y ≠ 0 := by
    simpa using nonZeroDivisors.ne_zero hy
  have hN0 : algebraMap (𝓞 E) E N ≠ 0 := by
    rw [hN, ← IsScalarTower.algebraMap_apply]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (OF E) E)).2 hn0
  set b := algebraMap (𝓞 E) E (N * y)
  have hb0 : b ≠ 0 := by simp only [b, map_mul]; exact mul_ne_zero hN0 hy0
  have hab : a * b = algebraMap (𝓞 E) E (N * x) := by
    simp only [b, map_mul, ← hxy]
    field_simp
  have h1 := hS b (hmem y)
  have h2 := hS (a * b) (hab ▸ hmem x)
  have h3 : ρE b⁻¹ v = (σ b)⁻¹ • v := by
    have h4 : v = σ b • ρE b⁻¹ v := by
      rw [← map_smul, ← h1, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hb0, map_one, Module.End.one_apply]
    have hσb : σ b ≠ 0 := (map_ne_zero σ).2 hb0
    conv_rhs => rw [h4, smul_smul, inv_mul_cancel₀ hσb, one_smul]
  have h5 : ρE a = ρE b⁻¹ * ρE (a * b) := by
    rw [← map_mul]; congr 1; field_simp
  rw [h5, Module.End.mul_apply, h2, map_smul, h3, smul_smul, map_mul, mul_assoc,
    mul_inv_cancel₀ ((map_ne_zero σ).2 hb0), mul_one]

end GlobalTheory.CMFormBound

namespace GlobalTheory.CMFormBound

theorem formClaims : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → (∀ i, 0 ≤ val_vp O l (algebraMap O K (B (e i) (f i))) ∧ val_vp O l (algebraMap O K (B (e i) (f i))) ≤ val_vp O l (algebraMap O K D)) → (∃! ρE : E →+* Module.End K (K ⊗[O] H), ∀ a : orderC c, ρE a = (ρ a).baseChange K) → FormClaims l φ ρ B D e f := by
  intro E _ _ _ c hc l hl O _ _ _ _ K _ _ _ hlm hcard D hD hCl I _ φ hφ H _ _ ρ Fil B hLat hEig e f hgens hB hρE
  refine ⟨hρE, ?_⟩
  intro ρE hρE' d r ξ hd hr hξ hξ0 hval
  have hconjr := conj_sqrt E d hd r hr
  have ha_real : IsCMField.complexConj E (ξ * r) = ξ * r := by
    rw [map_mul, hξ, hconjr, neg_mul_neg]
  have hr0 : r ≠ 0 := by
    rintro rfl
    have h0 : (d : E) = 0 := by
      rw [zero_pow two_ne_zero] at hr
      exact neg_eq_zero.1 hr.symm
    exact hd.ne_zero (by exact_mod_cast h0)
  have ha0 : ξ * r ≠ 0 := mul_ne_zero hξ0 hr0
  have hinv : ρE (ξ * r) * ρE (ξ * r)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ha0, map_one]
  have hinv' : ρE (ξ * r)⁻¹ * ρE (ξ * r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha0, map_one]
  refine ⟨⟨(IsCMField.complexConj_eq_self_iff E (ξ * r)).1 ha_real, ha0⟩, ?_, ?_⟩
  · refine ⟨(B.baseChange K).compl₂ (ρE (ξ * r)), ?_, ?_⟩
    · intro x y
      rw [LinearMap.compl₂_apply, ← Module.End.mul_apply, hinv, Module.End.one_apply]
    · intro BF' hBF'
      refine LinearMap.ext₂ fun x y => ?_
      rw [LinearMap.compl₂_apply, hBF' x (ρE (ξ * r) y), ← Module.End.mul_apply, hinv', Module.End.one_apply]
  · intro BF hBF i
    have hBFxy : ∀ x y, BF x y = B.baseChange K x (ρE (ξ * r) y) := by
      intro x y
      rw [hBF x (ρE (ξ * r) y), ← Module.End.mul_apply, hinv', Module.End.one_apply]
    have hfmem : inK K H (f i) ∈ eigK ρ (bar (φ i)) := by
      have : f i ∈ eigLat ρ (bar (φ i)) := by
        rw [(hgens i).2]
        exact Submodule.mem_span_singleton_self _
      exact this
    have heig := eig_ext hc ρ ρE hρE' (bar (φ i)) _ hfmem (ξ * r)
    have hbar : bar (φ i) (ξ * r) = φ i (ξ * r) := by
      show φ i (IsCMField.complexConj E (ξ * r)) = _
      rw [ha_real]
    have hK : B.baseChange K (inK K H (e i)) (inK K H (f i)) = algebraMap O K (B (e i) (f i)) := by
      simp [inK, LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
    have hval1 : BF (inK K H (e i)) (inK K H (f i)) = φ i (ξ * r) * algebraMap O K (B (e i) (f i)) := by
      rw [hBFxy, heig, hbar, LinearMap.map_smul, smul_eq_mul, hK]
    have hD0 : algebraMap O K D ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hD
    have hB0 : algebraMap O K (B (e i) (f i)) ≠ 0 := by
      intro h0
      have h1 := (hB i).2
      rw [h0, val_vp, if_pos rfl, val_of_ne O l hD0, top_le_iff] at h1
      exact WithTop.coe_ne_top h1
    have hφξ : φ i ξ ≠ 0 := (map_ne_zero _).2 hξ0
    have hφr : φ i r ≠ 0 := (map_ne_zero _).2 hr0
    have hF0 : BF (inK K H (e i)) (inK K H (f i)) ≠ 0 := by
      rw [hval1]
      exact mul_ne_zero ((map_ne_zero _).2 ha0) hB0
    have hlne : ord_vw O (l : K) ≠ 0 := ord_natCast_ne O l hl.ne_zero hlm
    have hvr : val_vp O l (φ i r) = (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
      have hsq : φ i r * φ i r = -1 * (d : K) := by
        rw [← map_mul, ← sq, hr, map_neg, map_natCast]; ring
      have hdK : (d : K) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hsq
        exact hφr (mul_self_eq_zero.1 hsq)
      have hm1 : ord_vw O ((-1 : K)) = 0 := by
        have := ord_of_not_mem O (K := K) (-1 : O) (by
          intro h; exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top
            ((Ideal.eq_top_iff_one _).2 (by simpa using (IsLocalRing.maximalIdeal O).neg_mem h)))
        simpa using this
      have hord := congrArg (ord_vw O) hsq
      rw [ord_mul O hφr hφr, ord_mul O (by norm_num) hdK, hm1, zero_add] at hord
      rw [val_of_ne O l hφr]
      by_cases hld : l = d
      · subst hld
        rw [if_pos rfl]
        congr 1
        have : (ord_vw O (φ i r) : ℚ) * 2 = ord_vw O ((l : ℕ) : K) := by exact_mod_cast (by linarith : ord_vw O (φ i r) * 2 = ord_vw O ((l : ℕ) : K))
        have hq : (ord_vw O ((l : ℕ) : K) : ℚ) ≠ 0 := by exact_mod_cast hlne
        field_simp
        linarith
      · rw [if_neg hld]
        have hdu : (d : O) ∉ IsLocalRing.maximalIdeal O := by
          intro hdm
          have hcop : IsCoprime (d : ℤ) (l : ℤ) :=
            Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hd hl).2 (Ne.symm hld))
          obtain ⟨u, w, huw⟩ := hcop
          have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
            have := congrArg (Int.cast : ℤ → O) huw
            push_cast at this
            rw [← this]
            exact add_mem (Ideal.mul_mem_left _ _ hdm) (Ideal.mul_mem_left _ _ hlm)
          exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1)
        have hd0 : ord_vw O ((d : ℕ) : K) = 0 := by
          have := ord_of_not_mem O (K := K) (d : O) hdu
          simpa using this
        rw [hd0] at hord
        have : ord_vw O (φ i r) = 0 := by linarith
        rw [this]
        simp
    have hvF : val_vp O l (BF (inK K H (e i)) (inK K H (f i))) =
        val_vp O l (algebraMap O K (B (e i) (f i))) + val_vp O l (φ i ξ) + val_vp O l (φ i r) := by
      rw [hval1, map_mul, val_mul O l (mul_ne_zero hφξ hφr) hB0, val_mul O l hφξ hφr]
      rw [add_comm, add_assoc]
    refine ⟨hval1, hF0, hvF, hvr, ?_⟩
    rw [hvF, hvr]
    calc val_vp O l (algebraMap O K (B (e i) (f i))) + val_vp O l (φ i ξ) + (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ)
        ≤ val_vp O l (algebraMap O K D) + 0 + (((if l = d then 1 / 2 else 0 : ℚ)) : WithTop ℚ) := by
          gcongr
          · exact (hB i).2
          · exact hval (φ i)
      _ = _ := by rw [add_zero]

end GlobalTheory.CMFormBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaDescentRestrictionEquivStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_descent_restriction_equiv : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → Function.Surjective (CoefMap.restrict F G).pull2 := by
  first | exact @GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma | exact GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma | (intros; apply GlobalTheory.CatCoh.Desc.pull2_surjective_of_comma <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaFirstOrderCocycleLiftStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_first_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict F G).pull2 → Function.Surjective (CoefMap.restrict F G).pull1 → (∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T)) → Function.Surjective (pullGlob1 (CoefMap.restrict F G)) → (∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) → Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.CechDR.pullHyp2_restrict_injective | exact GlobalTheory.CechDR.pullHyp2_restrict_injective | (intros; apply GlobalTheory.CechDR.pullHyp2_restrict_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaSecondOrderCocycleLiftStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_second_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict F G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) → (∀ κ : W1 F 2, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F 2 ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F 2 (G.map a) (θ' t)) → ∃ θ : W0 F 2, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F 2 φ (θ T)) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F 2 (G.map a) (η' t)) → ∃ η : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) → (∀ (T : C) (x : Om R (F.obj T) 3), (∀ t (u : T ⟶ G.obj t), pOm F 3 u x = 0) → x = 0) → Function.Surjective (pullHyp2 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.CechDR.pullHyp2_restrict_surjective | exact GlobalTheory.CechDR.pullHyp2_restrict_surjective | (intros; apply GlobalTheory.CechDR.pullHyp2_restrict_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleHigherFormsExtendAlongFunctorStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_higherForms_extend_along_functor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), (∀ (T : C) (x : (FormExtJ.omjExt F j).obj T), (∀ t (u : T ⟶ G.obj t), mp (FormExtJ.omjExt F j) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (FormExtJ.omjExt F j).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (FormExtJ.omjExt F j) (G.map a) (s t u)) → ∃ x : (FormExtJ.omjExt F j).obj T, ∀ t u, mp (FormExtJ.omjExt F j) u x = s t u) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F j (G.map a) (η' t)) → ∃ η : W0 F j, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F j φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) := by
  first | exact @GlobalTheory.compat_forms_extend | exact GlobalTheory.compat_forms_extend | (intros; apply GlobalTheory.compat_forms_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalHeightSuccDimStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_height_succ_dim : ∀ (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [FaithfulSMul k A] (d : ℕ), ringKrullDim (FractionRing k ⊗[k] A) = d → ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by
  first | exact @GlobalTheory.FibreMax.exists_isMaximal_height_ge | exact GlobalTheory.FibreMax.exists_isMaximal_height_ge | (intros; apply GlobalTheory.FibreMax.exists_isMaximal_height_ge <;> assumption)
end

