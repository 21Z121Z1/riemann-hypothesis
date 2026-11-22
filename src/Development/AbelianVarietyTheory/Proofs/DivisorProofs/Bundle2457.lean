import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPeriodConstantEqOfCardCmType
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.LatAlgebraic

theorem natAbs_discr_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    (discr F).natAbs = 1 := by
  have hb : (⊥ : Subalgebra ℚ F) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  let e : ℚ ≃ₐ[ℚ] F := (Algebra.botEquiv ℚ F).symm.trans ((Subalgebra.equivOfEq _ _ hb).trans Subalgebra.topEquiv)
  rw [← NumberField.discr_eq_discr_of_algEquiv (f := e), NumberField.discr_rat]
  rfl

theorem two_le_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
    have := Module.finrank_pos (R := ℚ) (M := maximalRealSubfield E)
    omega
  have hE := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, one_mul, natAbs_discr_of_finrank_one _ h1, one_pow] at hE
  have h2 : Module.finrank ℚ E = 2 := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, h1]
  have h3 := NumberField.abs_discr_gt_two (K := E) (by omega)
  have h4 : |(discr E : ℤ)| = 1 := by rw [Int.abs_eq_natAbs, hE]; rfl
  omega

theorem alg_id (c0 S0 X C Ω W cW P sgn p r : ℂ) (f t K : ℕ)
    (hS0 : S0 = C ^ t * X / (cW * (sgn * P) * W)) (hc0 : c0 = cW * P * (p / r) ^ K)
    (hΩ : Ω ≠ 0) (hp : p ≠ 0) (hr : r ≠ 0) (hW : W ≠ 0) (hcW : cW ≠ 0) (hP : P ≠ 0) (hsgn : sgn ≠ 0) :
    c0 * S0 / Ω ^ (t * f + 2 * K) = X * (C / Ω ^ f) ^ t * (sgn * (W * (Ω ^ 2 * r / p) ^ K))⁻¹ := by
  subst hS0 hc0
  have h1 : Ω ^ (t * f) ≠ 0 := pow_ne_zero _ hΩ
  have h2 : p ^ K ≠ 0 := pow_ne_zero _ hp
  have h3 : r ^ K ≠ 0 := pow_ne_zero _ hr
  field_simp
  simp only [div_pow, mul_pow, ← pow_mul, pow_add]
  field_simp
  ring

theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    {φ : I → E →+* ℂ} (h : IsCMType φ) : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := by
  have hreal : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ i)
    have e : i = j := (hk i (Or.inl rfl)).trans (hk j (Or.inr hij)).symm
    subst e
    have hr : ComplexEmbedding.IsReal (φ i) := ComplexEmbedding.isReal_iff.mpr hij.symm
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  have hbij : Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
    refine ⟨?_, ?_⟩
    · rintro (i | i) (j | j) hij
      · simp only [Sum.elim_inl] at hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij)]
      · exact absurd hij (hreal i j)
      · exact absurd hij.symm (hreal j i)
      · simp only [Sum.elim_inr] at hij
        have hij' : φ i = φ j := by
          simpa using congrArg ComplexEmbedding.conjugate hij
        obtain ⟨k, -, hk⟩ := h (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl hij')]
    · intro σ
      obtain ⟨k, hk, -⟩ := h σ
      rcases hk with hk | hk
      · exact ⟨Sum.inl k, hk.symm⟩
      · exact ⟨Sum.inr k, hk.symm⟩
  have h1 := Fintype.card_of_bijective hbij
  rw [Fintype.card_sum, NumberField.Embeddings.card E ℂ] at h1
  have h3 : Module.finrank ℚ E = 2 * Module.finrank ℚ (maximalRealSubfield E) := by
    rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]
  omega

theorem gamma_nat_add (k n : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + n) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range n, ((k : ℝ) + j) := by
  induction n with
  | zero =>
    have : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
      rw [Nat.cast_sub hk]; ring
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    rw [this, Real.Gamma_nat_eq_factorial]
  | succ n ih =>
    have hpos : (k : ℝ) + n ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one hpos, ih]
    ring

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) :
    ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ i, Multiset.replicate (κ i) i).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum', Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Multiset.count_replicate]
    simp [hj]
  · simp

theorem cmPeriodConstant_eq_of_card_cmType {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (d s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) :
    C0 E d (2 * s) κ = GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) *
      (∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) * (2 * Real.pi / Real.sqrt d) ^ (∑ i, κ i) := by
  have hk : 1 ≤ 2 * s := by omega
  rw [cmValueConst_eq, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt, Finset.prod_congr rfl (fun i _ => gamma_nat_add (2 * s) (κ i) hk),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  ring

theorem risingFactor_eq {I : Type} [Fintype I] (k : ℕ) (κ : I → ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor k κ =
      (-1) ^ (∑ i, κ i) * (((∏ i, ∏ j ∈ Finset.range (κ i), ((k : ℝ) + j)) : ℝ) : ℂ) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  push_cast
  rfl

theorem latAlg : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → EisRule → JetCore → ModelAlg → LatAlg := by
  intro hZ hSt hEis hJet hMod
  intro K _ _ d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ s 𝔣 Q hDat κ y S hS
  classical
  obtain ⟨hUn, hCM, hφι, hs, h𝔣, hQ⟩ := hDat
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hΩ0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)
  obtain ⟨⟨z, hz⟩, -⟩ := hZ E s hs
  obtain ⟨𝔠, X₀, δ₀, N, T, hAdm, hOver, hCalg, hA⟩ :=
    hMod K d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hCM hφι (condQ 𝔣 Q) y hc0
  let R₀ : Subring ℂ := (algebraicClosure ℚ ℂ).toSubring
  obtain ⟨r, hr⟩ := hEis E hf2 𝔠 s hs z hz R₀ 1 (one_mem _) (fun C => by
    show _ ∈ algebraicClosure ℚ ℂ
    exact mul_mem (one_mem _) (SubfieldClass.ratCast_mem _ _))
  obtain ⟨ε, hε⟩ := hJet
  let ι₀ : R₀ →+* Qb :=
    { toFun := fun a => ⟨a.1, a.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  letI : Algebra R₀ Qb := ι₀.toAlgebra
  obtain ⟨x, hx⟩ := hε E I 𝔠 hf2 R₀ s r hs Qb X₀ δ₀ N hAdm κ
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  have hxe := hx (algebraMap Qb ℂ) (fun a => rfl) φ (condQ 𝔣 Q) y 1 hCM hc0 (hr I φ (condQ 𝔣 Q) y hCM hc0) T hOver g u hg hu
  have hcard := card_eq_finrank hCM
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hε0 : ((ε : ℤ) : ℂ) ≠ 0 := by exact_mod_cast ε.ne_zero
  have hW : ∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (mul_ne_zero hε0 (hA i).1)
  have hcW : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt
      have h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
      exact mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos h1 _)
    exact_mod_cast this.ne'
  have hP : (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity
    exact_mod_cast this.ne'
  have hrF : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor (2 * s) κ ≠ 0 := by
    rw [risingFactor_eq]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hP
  have hS0 : S 0 = T.C ^ (2 * s) * algebraMap Qb ℂ x /
      ((GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) * GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.risingFactor (2 * s) κ *
        ∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i) := by
    rw [hxe, hDg]
    field_simp
  have hB : ∏ i, (((ε : ℤ) : ℂ) * (T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))) ^ κ i =
      (∏ i, (((ε : ℤ) : ℂ) * T.A i) ^ κ i) * (Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ))) ^ (∑ i, κ i) := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [← mul_pow]; ring
  have key : GlobalTheory.ToricTransport.coordIn E d s κ Ω₀ (S 0) =
      algebraMap Qb ℂ x * (T.C / Ω₀ ^ Fintype.card I) ^ (2 * s) *
        ((-1) ^ (∑ i, κ i) * ∏ i, (((ε : ℤ) : ℂ) * (T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * (Real.pi : ℂ)))) ^ κ i)⁻¹ := by
    have hC0 : ((C0 E d (2 * s) κ : ℝ) : ℂ) = (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) *
        (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ (∑ i, κ i) := by
      rw [cmPeriodConstant_eq_of_card_cmType hcard d s hs κ]; push_cast; ring
    rw [risingFactor_eq] at hS0
    rw [GlobalTheory.ToricTransport.coordIn, hB]
    exact alg_id _ _ _ _ _ _ _ _ _ _ _ (Fintype.card I) (2 * s) (∑ i, κ i) hS0 hC0 hΩ0
      (mul_ne_zero two_ne_zero hpi) hsd hW hcW hP (pow_ne_zero _ (by norm_num))
  rw [key, ← mem_algebraicClosure_iff]
  have mem : ∀ w : ℂ, IsAlgebraic ℚ w → w ∈ algebraicClosure ℚ ℂ := fun w h => mem_algebraicClosure_iff.2 h
  refine mul_mem (mul_mem x.2 (pow_mem (mem _ hCalg) _)) (inv_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _)
    (prod_mem fun i _ => pow_mem (mul_mem (intCast_mem _ _) (mem _ (hA i).2)) _)))

end GlobalTheory.LatAlgebraic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmSkewIdealFractionalIdeal
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.AntiInvFrac

theorem fracId_of_antiInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E) (ξ : E), ξ ≠ 0 → bar ξ = -ξ →
    (∀ m ∈ M, bar m = -m) → IsUnit M → ∃ 𝔠 : FracId (FR E), ∀ a : FR E, a ∈ 𝔠.elt ↔ (a : E) * ξ ∈ M := by
  intro E _ _ _ M ξ hξ hbξ hM hU
  let f : FR E →ₗ[OF E] E :=
    { toFun := fun a ↦ (a : E) * ξ
      map_add' := fun a b ↦ by push_cast; ring
      map_smul' := fun r a ↦ by
        simp only [RingHom.id_apply, Algebra.smul_def]
        rw [IsScalarTower.algebraMap_apply (OF E) (FR E) E]
        rw [show ∀ x : FR E, algebraMap (FR E) E x = (x : E) from fun _ ↦ rfl]
        push_cast; ring }
  have hf : Function.Injective f := fun a b h ↦ by
    have h' : (a : E) * ξ = (b : E) * ξ := h
    exact Subtype.ext (mul_right_cancel₀ hξ h')
  let S : Submodule (OF E) (FR E) := M.comap f
  have hle : M ≤ LinearMap.range f := fun m hm ↦ by
    have hfix : bar (m / ξ) = m / ξ := by
      simp only [bar, map_div₀] at hbξ ⊢
      rw [show IsCMField.complexConj E m = -m from hM m hm, hbξ, neg_div_neg_eq]
    refine ⟨⟨m / ξ, (IsCMField.complexConj_eq_self_iff E _).1 hfix⟩, ?_⟩
    show (m / ξ) * ξ = m
    exact div_mul_cancel₀ m hξ
  have hmap : S.map f = M := by
    rw [Submodule.map_comap_eq, inf_eq_right.2 hle]
  have hMfg : M.FG := Submodule.fg_of_isUnit hU
  have hSfg : S.FG := Submodule.fg_of_fg_map_injective f hf (hmap ▸ hMfg)
  have hM0 : M ≠ ⊥ := by
    intro h
    have : IsUnit (0 : Submodule (OF E) E) := by rw [← Submodule.zero_eq_bot] at h; rw [← h]; exact hU
    exact not_isUnit_zero this
  have hS0 : S ≠ ⊥ := by
    intro h
    apply hM0
    rw [← hmap, h, Submodule.map_bot]
  let I : FractionalIdeal (nonZeroDivisors (𝓞 (FR E))) (FR E) := ⟨S, FractionalIdeal.isFractional_of_fg hSfg⟩
  have hI : I ≠ 0 := by
    intro h
    apply hS0
    have := congrArg (fun J : FractionalIdeal (nonZeroDivisors (𝓞 (FR E))) (FR E) ↦ (J : Submodule (𝓞 (FR E)) (FR E))) h
    simpa [I] using this
  refine ⟨Units.mk0 I hI, fun a ↦ ?_⟩
  show a ∈ S ↔ _
  rfl

end GlobalTheory.AntiInvFrac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTraceFormImaginaryPart
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

namespace GlobalTheory.CMTrace

theorem sum_embeddings_cmType {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (g : (E →+* ℂ) → ℂ) :
    ∑ σ : E →+* ℂ, g σ = ∑ i, (g (φ i) + g (ComplexEmbedding.conjugate (φ i))) := by
  have hnr : ∀ i, ComplexEmbedding.conjugate (φ i) ≠ φ i := fun i h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (φ i)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  let f : I ⊕ I → (E →+* ℂ) := Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))
  have hf : Function.Bijective f := by
    constructor
    · rintro (i | i) (j | j) h
      · simp only [f, Sum.elim_inl] at h
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl h)]
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at h
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        have hi := hk i (Or.inl rfl)
        have hj := hk j (Or.inr h)
        subst hi; subst hj
        exact absurd h.symm (hnr _)
      · simp only [f, Sum.elim_inl, Sum.elim_inr] at h
        obtain ⟨k, _, hk⟩ := hφ (φ j)
        have hi := hk i (Or.inr h.symm)
        have hj := hk j (Or.inl rfl)
        subst hi; subst hj
        exact absurd h (hnr _)
      · simp only [f, Sum.elim_inr] at h
        have h' : φ i = φ j := by
          have := congrArg ComplexEmbedding.conjugate h
          simpa using this
        obtain ⟨k, _, hk⟩ := hφ (φ i)
        rw [hk i (Or.inl rfl), hk j (Or.inl h')]
    · intro σ
      obtain ⟨i, hi, _⟩ := hφ σ
      rcases hi with h | h
      · exact ⟨Sum.inl i, h.symm⟩
      · exact ⟨Sum.inr i, h.symm⟩
  rw [← Fintype.sum_bijective f hf (g ∘ f) g (fun _ => rfl), Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

theorem trace_eq_sum_re {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) (w : E) :
    ((Algebra.trace ℚ E w : ℚ) : ℝ) = ∑ i, 2 * (φ i w).re := by
  have h1 : ((Algebra.trace ℚ E w : ℚ) : ℂ) = ∑ σ : E →ₐ[ℚ] ℂ, σ w := by
    rw [← trace_eq_sum_embeddings (K := ℚ) (L := E) (E := ℂ)]
    simp
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ w = ∑ σ : E →+* ℂ, σ w :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun _ => rfl))
  have h3 := sum_embeddings_cmType φ hφ (fun σ => σ w)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h1, h2, h3]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]
  push_cast; ring

end GlobalTheory.CMTrace

open GlobalTheory.CMTrace in
theorem GlobalTheory.trace_riemannForm_eq_im : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (t₁ : E) (ρ : ℝ), (∀ i, φ i t₁ = -Complex.I * ((ρ / 2 : ℝ) : ℂ)) →
    ∀ (a : FR E) (x y : E), ((Algebra.trace ℚ E ((a : E) * t₁ * x * bar y) : ℚ) : ℝ) =
      (∑ j, (φ (e j) (a : E) * (ρ : ℂ)) * φ (e j) x * starRingEnd ℂ (φ (e j) y)).im := by
  intro E _ _ _ I _ φ hφ n e t₁ ρ ht a x y
  rw [trace_eq_sum_re φ hφ, Complex.im_sum, Equiv.sum_comp e (fun i => ((φ i (a : E) * (ρ : ℂ)) * φ i x * starRingEnd ℂ (φ i y)).im)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ha : starRingEnd ℂ (φ i (a : E)) = φ i (a : E) := by
    rw [← IsCMField.complexEmbedding_complexConj]
    congr 1
    exact (IsCMField.complexConj E).commutes a
  have hre : φ i (a : E) = ((φ i (a : E)).re : ℂ) := (Complex.conj_eq_iff_re.1 ha).symm
  have hb : φ i (bar y) = starRingEnd ℂ (φ i y) := IsCMField.complexEmbedding_complexConj E (φ i) y
  rw [map_mul, map_mul, map_mul, hb, ht i, hre]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeRealEmbeddingEquiv
section
open NumberField GlobalTheory.CMVal GlobalTheory.LatJet GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex (latMod polMod dualLat TrInt bar)

noncomputable section

namespace GlobalTheory.CMEquiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isReal_res (σ : E →+* ℂ) : ComplexEmbedding.IsReal (σ.comp (maximalRealSubfield E).subtype) := by
  ext x
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, Subfield.subtype_apply]
  rw [← IsCMField.complexEmbedding_complexConj, (IsCMField.complexConj_eq_self_iff E _).2 x.2]

def res (σ : E →+* ℂ) : FR E →+* ℝ := (isReal_res σ).embedding

theorem res_apply (σ : E →+* ℂ) (x : FR E) : ((res σ x : ℝ) : ℂ) = σ (x : E) :=
  ComplexEmbedding.IsReal.coe_embedding_apply _ x

theorem exists_ext (ψ : FR E →+* ℂ) : ∃ σ : E →+* ℂ, ∀ x : FR E, σ (x : E) = ψ x := by
  letI : Algebra (FR E) ℂ := ψ.toAlgebra
  let f : E →ₐ[FR E] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun x => f.commutes x⟩

theorem eq_or_eq_conj (σ σ' : E →+* ℂ) (h : ∀ x : FR E, σ' (x : E) = σ (x : E)) :
    σ' = σ ∨ σ' = ComplexEmbedding.conjugate σ := by
  set c := IsCMField.complexConj E with hc
  obtain ⟨y, hy⟩ : ∃ y, c y ≠ y := by
    by_contra! H
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext H)
  have cc : ∀ z, c (c z) = z := IsCMField.complexConj_apply_apply E
  set α := y - c y with hα
  have hα0 : α ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hcα : c α = -α := by rw [hα, map_sub, cc]; ring
  have mem : ∀ z, c z = z → σ' z = σ z := fun z hz =>
    h ⟨z, (IsCMField.complexConj_eq_self_iff E z).1 hz⟩
  have hsq : σ' α ^ 2 = σ α ^ 2 := by
    rw [← map_pow, ← map_pow]; exact mem _ (by rw [map_pow, hcα]; ring)
  have dec : ∀ z, ∃ a b, c a = a ∧ c b = b ∧ z = a + b * α ∧ c z = a - b * α := by
    intro z
    refine ⟨(z + c z) / 2, (z - c z) / (2 * α), ?_, ?_, ?_, ?_⟩
    · rw [map_div₀, map_add, cc, map_ofNat]; ring
    · rw [map_div₀, map_sub, cc, map_mul, map_ofNat, hcα]
      field_simp
      ring
    · field_simp; ring
    · field_simp; ring
  have hsq' : (σ' α - σ α) * (σ' α + σ α) = 0 := by linear_combination hsq
  rcases mul_eq_zero.1 hsq' with h1 | h1
  · left
    ext z
    obtain ⟨a, b, ha, hb, hz, -⟩ := dec z
    rw [hz, map_add, map_add, map_mul, map_mul, mem a ha, mem b hb, sub_eq_zero.1 h1]
  · right
    ext z
    obtain ⟨a, b, ha, hb, hz, hcz⟩ := dec z
    rw [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj, ← hc, hcz, hz,
      map_add, map_sub, map_mul, map_mul, mem a ha, mem b hb, eq_neg_of_add_eq_zero_left h1]
    ring

theorem cmType_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) :
    ∃ (e : Fin (Module.finrank ℚ (FR E)) ≃ I) (e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ)),
      ∀ j (x : FR E), ((e' j x : ℝ) : ℂ) = φ (e j) (x : E) := by
  have hRC : Function.Bijective (fun τ : FR E →+* ℝ => Complex.ofRealHom.comp τ) := by
    constructor
    · intro τ τ' hτ
      ext x
      exact Complex.ofReal_injective (RingHom.congr_fun hτ x)
    · intro ψ
      obtain ⟨σ, hσ⟩ := exists_ext ψ
      refine ⟨res σ, RingHom.ext fun x => ?_⟩
      simp only [RingHom.coe_comp, Function.comp_apply, Complex.ofRealHom_eq_coe]
      rw [res_apply, hσ]
  let eRC := Equiv.ofBijective _ hRC
  let e' : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ) :=
    (Fintype.equivFinOfCardEq (Embeddings.card (FR E) ℂ)).symm.trans eRC.symm
  have hb : Function.Bijective (fun i => res (φ i)) := by
    constructor
    · intro i j hij
      have hx : ∀ x : FR E, φ j (x : E) = φ i (x : E) := fun x => by
        rw [← res_apply, ← res_apply]
        exact congrArg (fun τ : FR E →+* ℝ => ((τ x : ℝ) : ℂ)) hij.symm
      obtain ⟨k, -, hk⟩ := hφ (φ j)
      exact (hk i (eq_or_eq_conj (φ i) (φ j) hx)).trans (hk j (Or.inl rfl)).symm
    · intro τ
      obtain ⟨σ, hσ⟩ := exists_ext (Complex.ofRealHom.comp τ)
      obtain ⟨i, hi, -⟩ := hφ σ
      refine ⟨i, RingHom.ext fun x => Complex.ofReal_injective ?_⟩
      rw [res_apply]
      rcases hi with h | h
      · rw [← h, hσ]; rfl
      · have h' : φ i = ComplexEmbedding.conjugate σ := by
          ext z
          rw [ComplexEmbedding.conjugate_coe_eq, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
        rw [h', ComplexEmbedding.conjugate_coe_eq, hσ]
        simp
  let b := Equiv.ofBijective _ hb
  refine ⟨e'.trans b.symm, e', fun j x => ?_⟩
  have hj : res (φ ((e'.trans b.symm) j)) = e' j := b.apply_symm_apply (e' j)
  rw [← hj, res_apply]

end GlobalTheory.CMEquiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOnePointMinimalPrime
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

theorem GlobalTheory.primeIdealOf_minimal_of_coheight_eq_one : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U) (z : X) (hz : z ∈ U), Order.coheight z = 1 → (hU.primeIdealOf ⟨z, hz⟩).asIdeal ≠ ⊥ ∧ ∀ Q : Ideal Γ(X, U), Q.IsPrime → Q ≠ ⊥ → Q ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal → Q = (hU.primeIdealOf ⟨z, hz⟩).asIdeal := by
  intro X _ U hU z hz h
  haveI : Nonempty U := ⟨⟨z, hz⟩⟩
  letI := X.presheaf.algebra_section_stalk (⟨z, hz⟩ : U)
  haveI := hU.isLocalization_stalk ⟨z, hz⟩
  have hc : (hU.primeIdealOf ⟨z, hz⟩).asIdeal.height = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨z, hz⟩).asIdeal
      (X.presheaf.stalk z)
    rw [ringKrullDim_stalk_eq_coheight, h] at this
    exact_mod_cast this.symm
  refine ⟨fun e => ?_, fun Q hQ hQ0 hQP => ?_⟩
  · rw [e, Ideal.height_bot] at hc
    exact zero_ne_one hc
  · by_contra hne
    haveI : (⊥ : Ideal Γ(X, U)).IsPrime := Ideal.isPrime_bot
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQ0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hQP hne)
    rw [Ideal.height_bot, zero_add] at h1
    rw [hc] at h2
    have h4 : (1 : ℕ∞) + 1 ≤ Q.height + 1 := by gcongr
    have h3 : (1 : ℕ∞) + 1 ≤ 1 := h4.trans h2
    exact absurd h3 (by decide)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemesStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductorSquare_flat_baseChange_schemes : ∀ (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (X X' Z : Scheme.{0}) (u : X ⟶ Sp R) (p : X' ⟶ X) (u' : X' ⟶ Sp R') (i : Z ⟶ X) (v : Z ⟶ Sp (R ⧸ c)), Flat u → IsPullback p u' u (spMap (algebraMap R R')) → IsPullback i v u (spMap (Ideal.Quotient.mk c)) → GlobalTheory.Pinch.Cond p i := by
  first | exact @GlobalTheory.Pinch.FlatSq.cond_of_flat | exact GlobalTheory.Pinch.FlatSq.cond_of_flat | (intros; apply GlobalTheory.Pinch.FlatSq.cond_of_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparisonStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_eq_deRham_of_smoothLift_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  first | exact @GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift | exact GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift | (intros; apply GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift <;> assumption)
end

