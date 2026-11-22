import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelLogCoords
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.SiegLog

theorem supp_fin {R : Type} [Ring R] (θ : ℤ → ℤ) (f : ℤ → R) (h : ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → θ k = 0) :
    (Function.support (fun k : ℤ => (θ k : R) * f k)).Finite := by
  obtain ⟨B, hB⟩ := h
  refine (Set.finite_Icc (-(B : ℤ)) B).subset fun k hk => ?_
  by_contra hc
  apply hk
  have : (B : ℤ) < |k| := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hc
    rcases hc with hc | hc
    · rw [abs_of_neg (by omega)]; omega
    · rw [abs_of_pos (by omega)]; omega
  simp [hB k this]

end GlobalTheory.SiegLog

namespace GlobalTheory.SiegLog

theorem siegel_logCoords : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (A : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ∀ (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ (T : GlobalTheory.K5.Tower p Ωl) (j : Ω →+* Ωl), IsCusp ε A T j → ∀ (L : ℕ) (ψ : O0 p →+* Ωl) (io : KT X (p ^ L) →+* Ωl), 1 ≤ L → IsReb T L ψ → IsIo X A T j L ψ io → ∀ ι : On p L →ₐ[O0 p] Ωl, IsEmb T L ι →
  ∀ (N c : ℕ) (A₁ a₂ g : ℤ), a₂ ≡ N * g [ZMOD (p : ℤ) ^ L] → (N : ℤ) ∣ a₂ → 0 < N → Nat.Coprime N p → 1 < c → Nat.Coprime c (6 * N * p) → ¬ (((N * p ^ L : ℕ) : ℤ) ∣ A₁) →
  ∀ y : KT X (p ^ L), (y : X.K) = sgN X c N (N * p ^ L) (A₁, a₂) →
  ∃ (w : (On p L)ˣ) (α β : On p L) (z z' : Ωl), IsDlog p L (w : On p L) α β ∧ ι w = io y ∧ Ev ψ (fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0) z z' ∧
    Cong p L (ι α) (-(A₁ : Ωl) * z) ∧ Cong p L ((p : Ωl) * ι β) (-(p : Ωl) * (g : Ωl) * z) := by
  intro Ω _ _ _ ε X hj p _ hp2 A hpA Ωl _ _ hclo T j hcusp L ψ io hL hreb hio ι hemb N c A₁ a₂ g ha₂ hNa hN hNp hc hc6 hNA y hy
  obtain ⟨θ, hB, hr0, hcong, hexp, hder, hsm, hunit⟩ := GlobalTheory.T.siegelUnitAtScaledArgument_twoVariableExpansion ε X hj p hp2 L N c A₁ a₂ g hL ha₂ hNa hN hNp hc hc6 hNA
  rw [← hy] at hexp hder hunit
  have hζ : j (zt ε p L) = T.ζ L := hcusp.root L
  have hzA : zt ε p L ∈ A := (hcusp.int _).2 (by rw [hζ]; exact GlobalTheory.KumDlog.int_zeta T L)
  have hzA' : (zt ε p L)⁻¹ ∈ A := (hcusp.int _).2 (by rw [map_inv₀, hζ]; exact GlobalTheory.KumDlog.int_zeta_inv T L)
  have hzpow : ∀ m : ℤ, zt ε p L ^ m ∈ A := by
    intro m
    rcases m with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact pow_mem hzA m
    · rw [zpow_negSucc, ← inv_pow]; exact pow_mem hzA' _
  have hpL : 0 < p ^ L := pow_pos (Fact.out : p.Prime).pos L
  have hcoef : ∀ s : ℚ, (X.exp (y : X.K)).coeff s ∈ A ∧
      (X.exp (y : X.K)).coeff s ∈ IntermediateField.adjoin ℚ (({zt ε p L} : Finset Ω) : Set Ω) := by
    intro s
    by_cases hs : (X.exp (y : X.K)).coeff s = 0
    · rw [hs]; exact ⟨zero_mem _, zero_mem _⟩
    have hden := ((KTExp.mem_KT_iff ε X (p ^ L) hpL (y : X.K)).1 y.2) s hs
    have hsr : s = (((s * ((p ^ L : ℕ) : ℚ)).num : ℤ) : ℚ) / (p : ℚ) ^ L := by
      have e := Rat.coe_int_num_of_den_eq_one hden
      have hp0 : (p : ℚ) ^ L ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
      rw [e, Nat.cast_pow, mul_div_assoc, div_self hp0, mul_one]
    rw [hsr, hexp]
    constructor
    · refine finsum_induction (· ∈ A) (zero_mem _) (fun _ _ => add_mem) fun k => ?_
      exact mul_mem (intCast_mem _ _) (hzpow _)
    · refine finsum_induction (· ∈ IntermediateField.adjoin ℚ (({zt ε p L} : Finset Ω) : Set Ω)) (zero_mem _)
        (fun _ _ => add_mem) fun k => ?_
      refine mul_mem (intCast_mem _ _) (zpow_mem (IntermediateField.subset_adjoin _ _ ?_) _)
      simp
  obtain ⟨x', hEv⟩ := hio.ev y {zt ε p L} hcoef
  obtain ⟨r0, hr0'⟩ := hr0
  set cU : ℤ → Ωl := fun r => j ((X.exp (y : X.K)).coeff ((r : ℚ) / (p : ℚ) ^ L)) with hcU
  set cE : ℤ → Ωl := fun r : ℤ => if 0 ≤ r then j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) else 0 with hcE
  have hjexp : ∀ r, cU r = ∑ᶠ k : ℤ, (θ k r : Ωl) * T.ζ L ^ (g * k) := by
    intro r
    simp only [hcU, hexp r]
    rw [map_finsum j (supp_fin (fun k => θ k r) (fun k => zt ε p L ^ (g * k)) (hB r))]
    simp only [map_mul, map_intCast, map_zpow₀, hζ]
  have hcE0 : ∀ r : ℤ, r < 0 → cE r = 0 := by
    intro r hr
    simp [hcE, not_le.2 hr]
  have hcEmem : ∀ r : ℤ, cE r ∈ Subring.closure {T.ζ L} := by
    intro r
    simp only [hcE]
    split_ifs
    · have h1 : j (smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ r.toNat) ∈ (Subring.closure {zt ε p L}).map j := Subring.mem_map.2 ⟨_, hsm r.toNat, rfl⟩
      rwa [RingHom.map_closure, Set.image_singleton, hζ] at h1
    · exact zero_mem _
  have hjder : ∀ r : ℤ, ∑ᶠ k : ℤ, ((k * θ k r : ℤ) : Ωl) * T.ζ L ^ (g * k) = -∑ᶠ i : ℤ, cE i * cU (r - i) := by
    intro r
    have hfin : (Function.support (fun i : ℤ => (if 0 ≤ i then smF c 1 (N * p ^ L) (eOm ε (1 / ((N * p ^ L : ℕ) : ℚ))) A₁ a₂ i.toNat else 0) *
        (X.exp (y : X.K)).coeff (((r - i : ℤ) : ℚ) / (p : ℚ) ^ L))).Finite := by
      refine (Set.finite_Icc 0 (r - r0)).subset fun i hi => ?_
      rw [Function.mem_support] at hi
      constructor
      · by_contra h0
        apply hi
        rw [if_neg h0, zero_mul]
      · by_contra h1
        apply hi
        have h2 : ∀ k, θ k (r - i) = 0 := fun k => hr0' k _ (by omega)
        rw [hexp (r - i)]
        simp [h2]
    have hB' : ∃ B : ℕ, ∀ k : ℤ, (B : ℤ) < |k| → k * θ k r = 0 := by
      obtain ⟨B, hb⟩ := hB r
      exact ⟨B, fun k hk => by rw [hb k hk, mul_zero]⟩
    have h := congrArg j (hder r)
    rw [map_neg, map_finsum j (supp_fin (fun k => k * θ k r) (fun k => zt ε p L ^ (g * k)) hB'), map_finsum j hfin] at h
    simp only [map_mul, map_intCast, map_zpow₀, hζ] at h
    rw [h]
    congr 1
    refine finsum_congr fun i => ?_
    simp only [hcE, hcU]
    split_ifs <;> simp
  have hzi : ∀ m : ℤ, IsInt p ((T.ζ L) ^ m) := by
    intro m
    rcases m with m | m
    · rw [Int.ofNat_eq_coe, zpow_natCast]; exact GlobalTheory.KumDlog.int_pow (GlobalTheory.KumDlog.int_zeta T L) m
    · rw [zpow_negSucc, ← inv_pow]; exact GlobalTheory.KumDlog.int_pow (GlobalTheory.KumDlog.int_zeta_inv T L) _
  obtain ⟨r, m, hrm⟩ := hunit
  have hcu : cU r ≠ 0 ∧ IsInt p (cU r)⁻¹ := by
    have hz0 : (T.ζ L) ^ m ≠ 0 := zpow_ne_zero _ (GlobalTheory.KumDlog.zeta_ne T L)
    rcases hrm with hrm | hrm
    · simp only [hcU, hrm, map_zpow₀, hζ]
      exact ⟨hz0, by rw [← zpow_neg]; exact hzi _⟩
    · simp only [hcU, hrm, map_neg, map_zpow₀, hζ]
      exact ⟨neg_ne_zero.2 hz0, by rw [inv_neg, ← zpow_neg]; exact GlobalTheory.KumDlog.int_neg (hzi _)⟩
  obtain ⟨hx0, hxi⟩ := (GlobalTheory.T.evalSeries_cong_iff_coeff_and_isUnit p Ωl hclo T L ψ hreb 0 cU (io y) x' hEv).2 ⟨r, hcu.1, hcu.2⟩
  exact GlobalTheory.T.logCoords_unit_value_twoVariableIntegralExpansion p Ωl hclo T L ψ ι hL hreb hemb A₁ g θ cU cE (io y) x' hB ⟨r0, hr0'⟩ hcong hjexp hjder hcE0 hcEmem hEv hx0 hxi

end GlobalTheory.SiegLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumPairingGramMatrixValuesAndDefinite
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat

open Classical in

theorem blockForm_apply {F C I : Type} [CommRing F] [Fintype C] [Fintype I] {N : ℕ} (e : Fin N ≃ C × I)
    (M : Matrix I I F) (x y : Fin N → F) :
    x ⬝ᵥ (Matrix.of fun a b => if (e a).1 = (e b).1 then M (e a).2 (e b).2 else 0) *ᵥ y =
      ∑ c, (fun i => x (e.symm (c, i))) ⬝ᵥ M *ᵥ (fun i => y (e.symm (c, i))) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

open Classical in

theorem blockForm_posDef {C I : Type} [Fintype C] [Fintype I] {N : ℕ} (e : Fin N ≃ C × I)
    (M : Matrix I I ℂ) (hM : M.PosDef) :
    (Matrix.of fun a b => if (e a).1 = (e b).1 then M (e a).2 (e b).2 else 0).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    by_cases h : (e a).1 = (e b).1
    · rw [if_pos h, if_pos h.symm]
      exact hM.isHermitian.apply _ _
    · rw [if_neg h, if_neg (fun h' => h h'.symm), star_zero]
  · intro x hx
    rw [blockForm_apply]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hx
    refine Finset.sum_pos' (fun c _ => ?_) ⟨(e a).1, Finset.mem_univ _, ?_⟩
    · exact hM.posSemidef.dotProduct_mulVec_nonneg (fun i => x (e.symm (c, i)))
    · refine hM.dotProduct_mulVec_pos (x := fun i => x (e.symm ((e a).1, i))) ?_
      intro h0
      apply ha
      simpa using congrFun h0 (e a).2

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem IsDefGram.isUnit_det {n : ℕ} {G : Matrix (Fin n) (Fin n) K} (h : IsDefGram G) : IsUnit G.det := by
  obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have h1 := (h.2.2 φ).det_pos
  have h2 : (G.map φ).det = φ G.det := (RingHom.map_det φ G).symm
  rw [h2] at h1
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, map_zero] at h1
  exact lt_irrefl _ h1

theorem map_inv_of_isUnit {F F' : Type} [Field F] [Field F'] {n : ℕ} (φ : F →+* F') (G : Matrix (Fin n) (Fin n) F)
    (h : IsUnit G.det) : (G⁻¹).map φ = (G.map φ)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ (map_zero φ) (map_one φ)]

theorem IsDefGram.inv_transpose {n : ℕ} {G : Matrix (Fin n) (Fin n) K} (h : IsDefGram G) : IsDefGram (G⁻¹)ᵀ := by
  have hu := h.isUnit_det
  refine ⟨?_, ?_, fun φ => ?_⟩
  · have h1 : (G⁻¹)ᴴ = G⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, h.1]
    ext a b
    have := congrFun (congrFun h1 b) a
    simpa [Matrix.conjTranspose_apply] using this
  · intro a b
    set G0 : Matrix (Fin n) (Fin n) (cmMax K) := Matrix.of fun a b => ⟨G a b, h.2.1 a b⟩ with hG0
    have e0 : G = G0.map (cmMax K).subtype := by ext a b; rfl
    have hu0 : IsUnit G0.det := by
      refine isUnit_iff_ne_zero.mpr fun h0 => hu.ne_zero ?_
      have h2 : (G0.map (cmMax K).subtype).det = (cmMax K).subtype G0.det := (RingHom.map_det _ G0).symm
      rw [e0, h2, h0, map_zero]
    rw [Matrix.transpose_apply, e0, ← map_inv_of_isUnit _ _ hu0, Matrix.map_apply]
    exact (G0⁻¹ b a).2
  · rw [Matrix.transpose_map, map_inv_of_isUnit _ _ hu]
    exact (h.2.2 φ).inv.transpose

omit [NumberField K] in

theorem pairK_equivFun_symm {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K)
    (u v : VVIdx lam → K) :
    pairK lam G ((bVV K lam).equivFun.symm u) ((bVV K lam).equivFun.symm v) =
      star u ⬝ᵥ (Matrix.of fun i j => pairK lam G (bVV K lam i) (bVV K lam j)) *ᵥ v := by
  simp only [Module.Basis.equivFun_symm_apply, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum,
    LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Pi.star_apply, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sumGram_spec : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, IsDefGram (G τ)) → ∀ (C : Type) [Fintype C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam), (∀ x y : Fin N → K, star x ⬝ᵥ sumGram lam e G *ᵥ y = ∑ c, pairK lam G (valAt lam e c x) (valAt lam e c y)) ∧ IsDefGram (sumGram lam e G) ∧ IsDefGram ((sumGram lam e G)⁻¹)ᵀ ∧ (∀ τ, IsUnit (G τ).det) := by
  intro K _ _ _ ι _ n lam G hG C _ N e
  have hdef : IsDefGram (sumGram lam e G) := by
    refine ⟨?_, ?_, fun φ => ?_⟩
    · ext a b
      simp only [sumGram, Matrix.conjTranspose_apply, Matrix.of_apply]
      by_cases h : (e a).1 = (e b).1
      · rw [if_pos h, if_pos h.symm]
        exact (pairSymm K ι n lam G fun τ => (hG τ).1).eq _ _
      · rw [if_neg h, if_neg (fun h' => h h'.symm), star_zero]
    · intro a b
      simp only [sumGram, Matrix.of_apply]
      split_ifs
      · exact pairingRational_holds K ι n lam _ G (fun τ => (hG τ).2.1) _ _
      · exact zero_mem _
    · have h1 := blockForm_posDef e _ (pairingPositive_holds K ι n lam G φ fun τ => (hG τ).2.2 φ)
      convert h1 using 1
      ext a b
      simp only [sumGram, Matrix.of_apply, Matrix.map_apply]
      split_ifs
      · rfl
      · exact map_zero φ
  refine ⟨fun x y => ?_, hdef, hdef.inv_transpose, fun τ => (hG τ).isUnit_det⟩
  have h1 := blockForm_apply e (Matrix.of fun i j => pairK lam G (bVV K lam i) (bVV K lam j)) (star x) y
  refine Eq.trans h1 (Finset.sum_congr rfl fun c _ => ?_)
  exact (pairK_equivFun_symm lam G (fun i => x (e.symm (c, i))) (fun i => y (e.symm (c, i)))).symm

end GlobalTheory.TestLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdge
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZEdge

theorem isUnit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h2 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h2
  rw [ZMod.natCast_self, mul_zero, add_zero] at h2
  exact ⟨⟨(d : ZMod L), (u : ZMod L), by rw [mul_comm]; exact h2, h2⟩, rfl⟩

theorem changeLevel_int {n m : ℕ} (χ : DirichletCharacter ℂ n) (h : n ∣ m) (d : ℤ) (hd : IsUnit (d : ZMod m)) :
    DirichletCharacter.changeLevel h χ (d : ZMod m) = χ (d : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h hd.unit
  simp only [IsUnit.unit_spec] at this
  rw [this, ZMod.cast_intCast h]

theorem chi_neg_one (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (hk : Odd k) (hg : Prim k N χ g) :
    χ (-1) = -1 := by
  by_contra hne
  have hinv := hg.cf.1.2 (-1) (by simp)
  have hq : ∀ τ : ℍ, qs g τ = 0 := by
    intro τ
    have h1 := hinv τ
    have hs : (-1 : SL(2, ℤ)) • τ = τ := by rw [ModularGroup.SL_neg_smul, one_smul]
    rw [hs] at h1
    simp [ch, hk.neg_one_pow] at h1
    have h3 : qs g τ * (1 + χ (-1)) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd (by linear_combination h) hne
  have hq0 : qs g = qs 0 := by
    funext τ; rw [hq τ]; simp [qs]
  have hp0 : PolyB (0 : ℕ → ℂ) := ⟨0, 0, by simp⟩
  have := GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth g 0 hg.cf.1.1 hp0 hq0
  have h1 := hg.one
  rw [this] at h1
  simp at h1

end GlobalTheory.EisM.ZEdge

namespace GlobalTheory.EisM.ZEdge

theorem multiplier_agree (N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) :
    ∀ d : ℤ, IsCoprime d ((N * M ^ 2 : ℕ) : ℤ) →
      ch χ d * ch φ d ^ 2 = ch (DirichletCharacter.changeLevel (dvd_mul_right N (M ^ 2)) χ *
        (DirichletCharacter.changeLevel (Dvd.intro_left _ (pow_two M).symm |>.trans (dvd_mul_left _ N)) φ) ^ 2) d := by
  intro d hd
  have hu := isUnit_of_isCoprime hd
  simp only [ch, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  rw [changeLevel_int χ _ d hu, changeLevel_int φ _ d hu]

theorem exists_entire (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ)
    (hk : 1 ≤ k) (hN : 0 < N) (hM : 0 < M) (hg : CF k N (ch χ) g) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re →
      LSeries (fun n => φ n * g n) s = Λ s := by
  have ht := GlobalTheory.T.isCuspFormCoeffSeq_dirichletTwist_level_mul_sq k N M χ φ g hM hg
  have hmf := (GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * M ^ 2) _).2.2.2.1 _ _ (multiplier_agree N M χ φ) ht.1
  obtain ⟨Λ, h1, h2⟩ := GlobalTheory.T.cuspForm_lseries_extends_entire k (N * M ^ 2) (N * M ^ 2) _ _ hk (by positivity) dvd_rfl ⟨hmf, ht.2⟩
  exact ⟨Λ, h1, fun s hs => (h2 s hs).2⟩

theorem norm_b_sq (e n : ℕ) {M : ℕ} (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) :
    ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e) := by
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_pow, mul_pow, ← pow_mul, mul_comm e 2, mul_div_assoc]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) (DirichletCharacter.norm_le_one φ _))

theorem term_le (e n : ℕ) (s : ℝ) (hs : 0 < s) {M : ℕ} (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) :
    ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [show ((0 : ℕ) : ℝ) = 0 from Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by positivity), div_zero, div_zero]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc _ ≤ (‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e)) / (n : ℝ) ^ (1 + s) :=
          div_le_div_of_nonneg_right (norm_b_sq e n φ g) (by positivity)
      _ = _ := by
          rw [div_div]; congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_add hn']; congr 1; push_cast; ring

theorem lseries_shift (e : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    LSeries (fun n => a n / (n : ℂ) ^ e) z = LSeries a (z + e) := by
  unfold LSeries; congr 1; funext n
  simp only [LSeries.term]
  split_ifs with h
  · rfl
  · rw [cpow_add _ _ (Nat.cast_ne_zero.2 h), cpow_natCast, div_div, mul_comm]

end GlobalTheory.EisM.ZEdge

namespace GlobalTheory.EisM.ZEdge

theorem b_props (e N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ)
    (hN : 0 < N) (hg : Prim (2 * e + 1) N χ g) (hχ : χ (-1) = -1) (hg0 : g 0 = 0) :
    let b : ℕ → ℂ := fun n => φ n * g n / (n : ℂ) ^ e
    let ω : ℕ → ℂ := fun p => χ p * φ p ^ 2
    b 1 = 1 ∧ b 0 = 0 ∧ (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) ∧
    (∀ n, ¬ n.Coprime (N * M) → b n = 0) ∧
    (∀ p r : ℕ, p.Prime → ¬ p ∣ N * M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) ∧
    (∀ p : ℕ, p.Prime → ¬ p ∣ N * M → (p : ZMod (N * M)) = -1 → (b p).re = 0) := by
  intro b ω
  obtain ⟨hmul, hrec, -⟩ := GlobalTheory.T.depletedCuspEigenform_heckeRelations (2 * e + 1) N χ g (by omega) hN hg
  refine ⟨by simp [b, hg.one], by simp [b, hg0], ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    simp only [b, Nat.cast_mul, map_mul, hmul m n hmn, mul_pow]
    ring
  · intro n hn
    simp only [b]
    by_cases hnN : n.Coprime N
    · have hnM : ¬ n.Coprime M := fun h => hn (Nat.Coprime.mul_right hnN h)
      rw [MulChar.map_nonunit φ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul, zero_div]
    · rw [hg.zero n hnN, mul_zero, zero_div]
  · intro p r hp hpd
    have hpN : ¬ p ∣ N := fun h => hpd (dvd_mul_of_dvd_left h M)
    have huN : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    refine ⟨?_, ?_⟩
    · simp only [ω, norm_mul, norm_pow]
      have h1 := DirichletCharacter.unit_norm_eq_one χ huN.unit
      simp only [IsUnit.unit_spec] at h1
      rw [h1, one_mul]
      have hpM : ¬ p ∣ M := fun h => hpd (dvd_mul_of_dvd_right h N)
      have huM : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      have h2 := DirichletCharacter.unit_norm_eq_one φ huM.unit
      simp only [IsUnit.unit_spec] at h2
      rw [h2, one_pow]
    · simp only [b, Nat.cast_pow, map_pow, hrec p r hp hpN, ω]
      rw [show 2 * e + 1 - 1 = 2 * e by omega]
      field_simp
      ring
  · intro p hp hpd hpm
    have hpN : ¬ p ∣ N := fun h => hpd (dvd_mul_of_dvd_left h M)
    have hcN : (p : ZMod N) = -1 := by
      have := congrArg (ZMod.castHom (dvd_mul_right N M) (ZMod N)) hpm
      simpa using this
    have hcM : (p : ZMod M) = -1 := by
      have := congrArg (ZMod.castHom (dvd_mul_left M N) (ZMod M)) hpm
      simpa using this
    have hreal := GlobalTheory.T.depletedCuspEigenform_eigenvalue_eq_char_mul_conj (2 * e + 1) N p χ g (by omega) hN hg hp hpN
    simp only [ch, Int.cast_natCast, hcN, hχ] at hreal
    have hre : (g p).re = 0 := by
      have := congrArg Complex.re hreal
      simp at this
      linarith
    have hφ : φ (-1) = 1 ∨ φ (-1) = -1 := by
      have h2 : φ (-1) ^ 2 = 1 := by rw [← map_pow]; simp
      have h3 : (φ (-1) - 1) * (φ (-1) + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · left; linear_combination h
      · right; linear_combination h
    simp only [b, hcM]
    rw [← Nat.cast_pow, Complex.div_natCast_re]
    rcases hφ with h | h <;> simp [h, hre]

end GlobalTheory.EisM.ZEdge

theorem GlobalTheory.EisM.twisted_lvalue_ne_zero_edge : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) (w : ℝ), Odd k → 0 < N → 0 < M → Prim k N χ g → ((k : ℝ) + 1) / 2 ≤ w → χ (-1) = -1 ∧ ∃ v : ℂ, v ≠ 0 ∧ Tendsto (fun s : ℝ => LSeries (fun n => φ n * g n) ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  intro k N M χ φ g w hk hN hM hg hw
  have hχ := GlobalTheory.EisM.ZEdge.chi_neg_one k N χ g hk hg
  refine ⟨hχ, ?_⟩
  obtain ⟨e, rfl⟩ := hk
  obtain ⟨Λ, hΛd, hΛ⟩ := GlobalTheory.EisM.ZEdge.exists_entire (2 * e + 1) N M χ φ g (by omega) hN hM hg.cf
  obtain ⟨hg0, ⟨C1, hC1⟩, hsum, ⟨C2, hC2⟩⟩ := GlobalTheory.T.rankin_mean_square_cuspForm (2 * e + 1) N (ch χ) g (by omega) hg.cf
  obtain ⟨hb1, hb0, hbm, hbz, hbr, hbre⟩ := GlobalTheory.EisM.ZEdge.b_props e N M χ φ g hN hg hχ hg0
  have hkw : (e : ℝ) + 1 ≤ w := by push_cast at hw; linarith
  have hne : Λ w ≠ 0 := by
    have key := GlobalTheory.T.lseries_ne_zero_re_ge_one_of_positivity (N * M) (fun n => φ n * g n / (n : ℂ) ^ e) (fun p => χ p * φ p ^ 2) (max C1 C2)
      (fun z => Λ (z + e)) (by positivity) hb1 hb0 hbm hbz hbr ?_ ?_ ?_ hbre ?_ ?_ (w - e) (by linarith)
    · have hc : (((w - e : ℝ)) : ℂ) + (e : ℂ) = (w : ℂ) := by push_cast; ring
      simpa [hc] using key
    · intro n
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [hg0]
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        calc ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e) := GlobalTheory.EisM.ZEdge.norm_b_sq e n φ g
          _ ≤ C1 * (n : ℝ) ^ (2 * e + 1) / (n : ℝ) ^ (2 * e) := div_le_div_of_nonneg_right (hC1 n) (by positivity)
          _ = C1 * n := by field_simp; ring
          _ ≤ max C1 C2 * n := mul_le_mul_of_nonneg_right (le_max_left _ _) hn'.le
    · intro s hs
      exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g) (hsum s hs)
    · intro s hs hs1
      calc s * ∑' n : ℕ, ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 / (n : ℝ) ^ (1 + s)
          ≤ s * ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) := by
            apply mul_le_mul_of_nonneg_left _ hs.le
            exact Summable.tsum_le_tsum (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g)
              (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g) (hsum s hs)) (hsum s hs)
        _ ≤ C2 := hC2 s hs hs1
        _ ≤ max C1 C2 := le_max_right _ _
    · exact hΛd.comp (differentiable_id.add_const _)
    · intro s hs
      show LSeries (fun n => φ n * g n / (n : ℂ) ^ e) _ = Λ (_ + e)
      rw [GlobalTheory.EisM.ZEdge.lseries_shift e (fun n => φ n * g n)]
      apply hΛ
      simp
      push_cast
      linarith
  refine ⟨Λ w, hne, ?_⟩
  have hc : Tendsto (fun s : ℝ => Λ ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (Λ w)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun s : ℝ => Λ ((w + s : ℝ) : ℂ)) :=
      hΛd.continuous.comp (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))
    simpa using this.tendsto 0
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hΛ]
  simp
  push_cast
  have : (0 : ℝ) < s := hs
  linarith
end

