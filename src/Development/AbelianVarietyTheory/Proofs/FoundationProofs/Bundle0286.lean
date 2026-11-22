import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0281
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaKillsFplusDiscreteForm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThKill

theorem cgA_natCast {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (l n a b : ℕ)
    (h : ((a : ℕ) : ZMod (l ^ n)) = ((b : ℕ) : ZMod (l ^ n))) : CgA A l n (a : Ω) (b : Ω) := by
  have h' : ((a : ℤ) : ZMod (l ^ n)) = ((b : ℤ) : ZMod (l ^ n)) := by exact_mod_cast h
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
  obtain ⟨k, hk⟩ := h'
  refine ⟨((-k : ℤ) : Ω), intCast_mem A (-k), ?_⟩
  have hk' : ((b : ℤ) : Ω) - ((a : ℤ) : Ω) = ((l : ℤ) : Ω) ^ n * (k : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hk
    push_cast at this ⊢
    linear_combination this
  push_cast at hk' ⊢
  linear_combination -hk'

theorem cgA_trans {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ} {x y z : Ω}
    (h1 : CgA A l n x y) (h2 : CgA A l n y z) : CgA A l n x z := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, add_mem ha hb, by linear_combination e1 + e2⟩

theorem cgA_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {l n : ℕ} {x y t : Ω}
    (h : CgA A l n x y) (ht : t ∈ A) : CgA A l n (x * t) (y * t) := by
  obtain ⟨a, ha, e⟩ := h
  exact ⟨a * t, mul_mem ha ht, by linear_combination t * e⟩

theorem gamma1_le_of_dvd {N M : ℕ} (h : N ∣ M) :
    CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ ⊢
  obtain ⟨h1, h2, h3⟩ := hγ
  have key : ∀ x y : ℤ, ((x : ZMod M)) = (y : ZMod M) → (x : ZMod N) = (y : ZMod N) := by
    intro x y hxy
    have := congrArg (ZMod.castHom h (ZMod N)) hxy
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · simpa using key _ 1 (by simpa using h1)
  · simpa using key _ 1 (by simpa using h2)
  · simpa using key _ 0 (by simpa using h3)

theorem isThB_level_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω)
    (N M l n : ℕ) [Fact l.Prime] (b : X.Fn l) (φ : HahnSeries ℚ Ω) (h : IsThB X A N l n b φ) :
    IsThB X A (N * M) l n b φ := by
  obtain ⟨f, hI, hc, hδ, hD⟩ := h
  have hle : CongruenceSubgroup.Gamma1 (N * M * l ^ n) ≤ CongruenceSubgroup.Gamma1 (N * l ^ n) :=
    gamma1_le_of_dvd ⟨M, by ring⟩
  refine ⟨f, fun γ hγ => hI γ (hle hγ), hc, fun δ hδ' hneg => ?_, hD⟩
  obtain ⟨g, hg, e⟩ := hδ δ (gamma1_le_of_dvd (dvd_mul_right N M) hδ') hneg
  exact ⟨g, fun γ hγ => hg γ (hle hγ), e⟩

theorem B_level_mul {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N M l w : ℕ) [Fact l.Prime] :
    X.B N l w ≤ X.B (N * M) l w := by
  apply Submodule.span_mono
  rintro b ⟨hp, hg⟩
  refine ⟨hp, fun γ hγ => hg γ ?_⟩
  rw [Gam, Subgroup.mem_inf] at hγ ⊢
  exact ⟨gamma1_le_of_dvd (dvd_mul_right N M) hγ.1, hγ.2⟩

theorem auxiliaryLevel_coprime_ge_five (l N : ℕ) [hl : Fact l.Prime] (hN : 1 ≤ N) (hlN : ¬ l ∣ N) :
    5 ≤ N * (if l = 5 then 7 else 5) ∧ ¬ l ∣ N * (if l = 5 then 7 else 5) := by
  refine ⟨?_, ?_⟩
  · split_ifs <;> nlinarith
  · intro h
    rcases (Nat.Prime.dvd_mul hl.out).1 h with h' | h'
    · exact hlN h'
    · split_ifs at h' with h5
      · subst h5; norm_num at h'
      · have := (Nat.prime_dvd_prime_iff_eq hl.out (by norm_num)).1 h'
        exact h5 this

theorem discrete (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (hj : ∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) (hA : A.valuation (l : Ω) < 1) (hl2 : l ≠ 2)
    (N : ℕ) (hN : 1 ≤ N) (hlN : ¬ l ∣ N) (w : ℕ) (hw : Odd w) (F : Finset Ω) :
    ∃ c : ℕ, ∀ v : X.Fn l, v ∈ X.B N l w →
      (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s v = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • v) →
      ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n v φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨c, hc⟩ := GlobalTheory.T.integral_tate_inertia_cyclotomic_twist_torsion l Ω A hA (w + 1) (by omega) F
  refine ⟨c, fun v hv hgal n φ hφ r => ?_⟩
  have hφA : ∀ r, φ.coeff r ∈ A := by
    obtain ⟨f, -, -, -, hDl⟩ := hφ
    exact hDl.1
  refine hc n (φ.coeff r) (hφA r) (fun s hs hF => ?_)
  have hsA : ∀ x, x ∈ A ↔ s x ∈ A := fun x => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs) x).symm
  set u : ℤ_[l] := (cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1) with hu
  have h1 := GlobalTheory.isThB_galB Ω ε X A N l n w s ((ValuationSubring.mem_nonunits_iff A).2 hA) hsA v hv φ hφ
  rw [hgal s hs hF] at h1
  have h2 := GlobalTheory.ThAdd.isThB_add Ω ε X A N l n w v v ((ValuationSubring.mem_nonunits_iff A).2 hA) hv hv u 0 φ φ hφ hφ
  rw [zero_smul, add_zero] at h2
  have huv : u • v ∈ X.B N l w := Submodule.smul_mem _ u hv
  obtain ⟨hN5, hlN5⟩ := auxiliaryLevel_coprime_ge_five l N hN hlN
  have h3 := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A _ l hj hl2 hlN5 hN5 ((ValuationSubring.mem_nonunits_iff A).2 hA) n w hw (u • v)
    (B_level_mul X N _ l w huv) _ _ (isThB_level_mul X A N _ l n _ _ h1) (isThB_level_mul X A N _ l n _ _ h2) r

  have h0 : ((0 : ℤ_[l]).appr n : ℕ) = 0 := by
    have hlt := PadicInt.appr_lt (0 : ℤ_[l]) n
    have hk : ((PadicInt.toZModPow n (0 : ℤ_[l]) : ZMod (l ^ n))) = 0 := map_zero _
    have hk' : (((0 : ℤ_[l]).appr n : ℕ) : ZMod (l ^ n)) = 0 := hk
    rw [ZMod.natCast_eq_zero_iff] at hk'
    exact Nat.eq_zero_of_dvd_of_lt hk' hlt
  rw [h0] at h3
  have e : ((((u.appr n : ℕ)) : Ω) • φ + ((0 : ℕ) : Ω) • φ).coeff r = ((u.appr n : ℕ) : Ω) * φ.coeff r := by simp
  have e' : (HahnSeries.map φ (s : Ω →+* Ω)).coeff r = s (φ.coeff r) := rfl
  rw [e, e'] at h3
  have hcg : CgA A l n ((u.appr n : ℕ) : Ω) ((((cycMod ℚ Ω l n s : ZMod (l ^ n)).val ^ (w + 1) : ℕ) : Ω)) :=
    cgA_natCast A l n _ _ (by
      have e1 : (((u.appr n : ℕ)) : ZMod (l ^ n)) = PadicInt.toZModPow n u := rfl
      rw [e1, hu, map_pow]
      push_cast
      congr 1
      simp [cycMod])
  rw [Nat.cast_pow] at hcg
  exact cgA_trans h3 (cgA_mul hcg (hφA r))

theorem th_kills_Fplus_discrete : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω),
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → A.valuation (l : Ω) < 1 → ∀ (N w : ℕ) (F : Finset Ω), l ≠ 2 → ¬ l ∣ N → 1 ≤ N → Odd w → ∃ c : ℕ, ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → X.galB l s b = ((cycZ ℚ Ω l s : ℤ_[l]) ^ (w + 1)) • b) →
  ∀ (n : ℕ) (φ : HahnSeries ℚ Ω), IsThB X A N l n b φ → ∀ r, CgA A l n ((l : Ω) ^ c * φ.coeff r) 0 := by
  intro l _ Ω _ _ _ ε X A hj hA N w F hl2 hlN hN hw
  exact discrete l Ω ε X A hj hA hl2 N hN hlN w hw F

end GlobalTheory.ThKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeDiamondAction
section
open scoped MatrixGroups
open Matrix GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

noncomputable section

namespace GlobalTheory.CyclotomicQExpansion.ThnEx

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem toGQ_coe (σ : SL(2, ℤ)) : toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL σ := by
  have h : (0 : ℤ) < (σ : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  unfold toGQ
  rw [dif_pos h]
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [ofSL]

theorem kmap_SL_A (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (σ : SL(2, ℤ)) :
    ∀ a ∈ X.A l, X.kmap l (X.sl (toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv a ∈ X.A l := by
  apply KmapA.kmap_mem_A
  intro W hW
  refine ⟨fun c => ?_, ?_⟩
  · rw [ValuationSubring.mem_comap]
    change X.sl _ (algebraMap Ω X.K c) ∈ W
    rw [AlgEquiv.commutes]; exact hW.1 c
  · rw [ValuationSubring.mem_comap]
    change X.sl _ X.jK ∈ W
    rw [toGQ_coe, X.j_inv]; exact hW.2

private theorem exists_isDiam_of_coprime {N l d : ℕ} (hNl : Nat.Coprime N l) (hd : Nat.Coprime d N) :
    ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  obtain ⟨e, heN, hel⟩ := Nat.chineseRemainder hNl d 1
  have hcop : Nat.Coprime e (N * l) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq heN]; exact hd
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hel]; simp
  have hbez := Nat.gcd_eq_gcd_ab e (N * l)
  rw [hcop.gcd_eq_one] at hbez
  refine ⟨⟨!![Nat.gcdA e (N * l), -Nat.gcdB e (N * l); ((N * l : ℕ) : ℤ), (e : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; push_cast at hbez ⊢; linear_combination -hbez
  · refine Subgroup.mem_inf.mpr ⟨CongruenceSubgroup.Gamma0_mem.mpr ?_, CongruenceSubgroup.Gamma0_mem.mpr ?_⟩
    · simp
    · simp
  · simp only [en]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Int.cast_natCast]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr heN

private theorem conj_mem_Gamma1_of_mem_Gamma0 {N : ℕ} {σ γ : SL(2, ℤ)} (hσ : σ ∈ CongruenceSubgroup.Gamma0 N)
    (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hγ
  have hg0 : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma0 N :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ hγ0) (Subgroup.inv_mem _ hσ)
  have h1 : (⟨γ, hγ0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem]
    exact (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have h2 : (⟨σ * γ * σ⁻¹, hg0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N :=
    (CongruenceSubgroup.Gamma0Map N).normal_ker.conj_mem _ h1 ⟨σ, hσ⟩
  exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h2)

private theorem kmap_kmap_eq_kmap_trans (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ ψ : X.K ≃+* X.K) (x : X.Khat l) :
    X.kmap l ψ (X.kmap l φ x) = X.kmap l (φ.trans ψ) x := by
  unfold Tower.kmap
  simp only [LinearMap.coe_restrictScalars]
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp]
  rfl

private theorem act_act_eq_act_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (σ τ : SL(2, ℤ)) (b : X.Fn l) :
    X.act l (τ : Matrix (Fin 2) (Fin 2) ℤ) (X.act l (σ : Matrix (Fin 2) (Fin 2) ℤ) b) =
      X.act l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) b := by
  funext u
  change X.kmap l (X.sl (toGQ (τ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.sl (toGQ (σ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
        (b (mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ (mZl l (τ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u)))) =
    X.kmap l (X.sl (toGQ ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (b (mZl l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u))
  have hm : mZl l ((σ * τ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      mZl l (σ : Matrix (Fin 2) (Fin 2) ℤ) * mZl l (τ : Matrix (Fin 2) (Fin 2) ℤ) := by
    simp only [mZl, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]
  have hs : (X.sl (ofSL σ * ofSL τ)).toRingEquiv =
      (X.sl (ofSL σ)).toRingEquiv.trans (X.sl (ofSL τ)).toRingEquiv := by
    ext f; exact X.sl_mul _ _ f
  rw [kmap_kmap_eq_kmap_trans, toGQ_coe, toGQ_coe, toGQ_coe, map_mul, Matrix.mulVec_mulVec, hm, hs]

theorem diam_BSet (X : Tower Ω ε) (N l w d : ℕ) [Fact l.Prime] (hN : 0 < N) (hNl : Nat.Coprime N l)
    (hd : Nat.Coprime d N) (b : X.Fn l) (hb : b ∈ X.BSet N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.BSet N l w := by
  have hσ : IsDiam N l d (sgD N l d) := Classical.epsilon_spec (exists_isDiam_of_coprime hNl hd)
  obtain ⟨hpol, hinv⟩ := hb
  refine ⟨GlobalTheory.T.intMatrixAction_mem_homogeneousPolyFunctions X l w _ (kmap_SL_A X l (sgD N l d)) b hpol, ?_⟩
  intro γ hγ
  obtain ⟨hσN, hσl⟩ := Subgroup.mem_inf.mp hσ.1
  obtain ⟨hγN, hγl⟩ := Subgroup.mem_inf.mp hγ
  have hconj : sgD N l d * γ * (sgD N l d)⁻¹ ∈ Gam N l :=
    Subgroup.mem_inf.mpr ⟨conj_mem_Gamma1_of_mem_Gamma0 hσN hγN,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hσl hγl) (Subgroup.inv_mem _ hσl)⟩
  have hswap : sgD N l d * γ = sgD N l d * γ * (sgD N l d)⁻¹ * sgD N l d :=
    (inv_mul_cancel_right _ _).symm
  rw [act_act_eq_act_mul X l _ _ b, hswap, ← act_act_eq_act_mul X l (sgD N l d * γ * (sgD N l d)⁻¹) (sgD N l d) b,
    hinv _ hconj]

theorem diam_B (X : Tower Ω ε) (N l w d : ℕ) [Fact l.Prime] (hN : 0 < N) (hNl : Nat.Coprime N l)
    (hd : Nat.Coprime d N) (b : X.Fn l) (hb : b ∈ X.B N l w) :
    X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b ∈ X.B N l w := by
  have hle : X.B N l w ≤ (X.B N l w).comap (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ)) :=
    Submodule.span_le.mpr (fun x hx => Submodule.subset_span (diam_BSet X N l w d hN hNl hd x hx))
  exact hle hb

end GlobalTheory.CyclotomicQExpansion.ThnEx

namespace GlobalTheory.CyclotomicQExpansion

theorem thN_isThB : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime],
    (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
    ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
    IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) (thN X A N l n d b) ∧
      IsLat 1 (thN X A N l n d b) := by
  intro Ω _ _ _ ε X A N l _ hj hl2 hlN hN hlA n w d hw hd b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : l.Prime := Fact.out
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hl).mpr hlN).symm
  have hb' := ThnEx.diam_B X N l w d (by omega) hNl hd b hb
  exact thN_spec X A N l n d b (GlobalTheory.T.exists_cuspFunctional_oddWeight_oddPrime Ω ε X A N l (IsAlgClosure.isAlgebraic (R := ℚ)) hj hl2 hlN (by omega) hlA n w hw _ hb')

end GlobalTheory.CyclotomicQExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeTriplesDistributive
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.DistLa

variable {D : D7} {N N' : ℕ}

theorem La_map (T : Tor D) (f : VC D N N' →ₗ[ℂ] VC D N N')
    (g : Matrix (Fin N') (Fin N) D.host.E →ₗ[D.host.E] Matrix (Fin N') (Fin N) D.host.E)
    (hfg : ∀ A, f (embV D T A) = embV D T (g A)) {L M : Lat D N} {L' M' : Lat D N'}
    (hg : ∀ A : Matrix (Fin N') (Fin N) D.host.E, (∀ x ∈ L, A.mulVec x ∈ L') → ∀ x ∈ M, (g A).mulVec x ∈ M')
    {z : VC D N N'} (hz : z ∈ La D T L L') : f z ∈ La D T M M' := by
  have h1 : ∀ A ∈ homL D L L', g A ∈ homL D M M' := by
    intro A hA
    have : homL D L L' ≤ (homL D M M').comap (g.restrictScalars (𝓞 D.host.E)) :=
      Submodule.span_le.2 fun B hB => Submodule.subset_span (hg B hB)
    exact this hA
  have h2 : ∀ A ∈ YYl D L L', g A ∈ YYl D M M' := by
    intro A hA
    have : YYl D L L' ≤ (YYl D M M').comap (g.restrictScalars (𝓞 D.host.E)) := by
      refine Submodule.span_le.2 ?_
      rintro B ⟨a, ha, C, hC, rfl⟩
      exact Submodule.subset_span ⟨a, ha, g C, h1 C hC, map_smul g a C⟩
    exact this hA
  have h3 : La D T L L' ≤ (La D T M M').comap f.toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, hA, rfl⟩
    refine AddSubgroup.subset_closure ⟨w, hw, g A, h2 A hA, ?_⟩
    show f (w • embV D T A) = _
    rw [map_smul, hfg]
  exact h3 hz

def lft (P : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ i j => ∑ k, embT D τ (P i k) * z τ k j
  map_add' x y := by
    funext τ i j; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

def rgt (P : Matrix (Fin N) (Fin N) D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun z := fun τ i j => ∑ k, z τ i k * embT D τ (P k j)
  map_add' x y := by
    funext τ i j; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext τ i j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem lft_add (P : Matrix (Fin N') (Fin N') D.host.E) (z : VC D N N') : lft P z + lft (1 - P) z = z := by
  funext τ i j
  show ∑ k, embT D τ (P i k) * z τ k j + ∑ k, embT D τ ((1 - P) i k) * z τ k j = z τ i j
  rw [← Finset.sum_add_distrib]
  simp only [← add_mul, ← map_add, Matrix.sub_apply, add_sub_cancel, Matrix.one_apply]
  simp [apply_ite]

theorem rgt_add (P : Matrix (Fin N) (Fin N) D.host.E) (z : VC D N N') : rgt P z + rgt (1 - P) z = z := by
  funext τ i j
  show ∑ k, z τ i k * embT D τ (P k j) + ∑ k, z τ i k * embT D τ ((1 - P) k j) = z τ i j
  rw [← Finset.sum_add_distrib]
  simp only [← mul_add, ← map_add, Matrix.sub_apply, add_sub_cancel, Matrix.one_apply]
  simp [apply_ite]

theorem lft_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N') (Fin N') D.host.E) {L : Lat D N}
    {L' M' : Lat D N'} (hP : ∀ v ∈ L', P.mulVec v ∈ M') {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') :
    lft P z ∈ La D (tor0 D cc δ) L M' := by
  refine La_map _ (lft P)
    { toFun := fun A => P * A, map_add' := fun A B => Matrix.mul_add P A B,
      map_smul' := fun c A => Matrix.mul_smul P c A } ?_ ?_ hz
  · intro A
    funext τ i j
    show ∑ k, embT D τ (P i k) * embT D τ (A k j) = embT D τ ((P * A) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul]
  · intro A hA x hx
    show (P * A).mulVec x ∈ M'
    rw [← Matrix.mulVec_mulVec]
    exact hP _ (hA x hx)

theorem rgt_mem (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (P : Matrix (Fin N) (Fin N) D.host.E) {L M : Lat D N}
    {L' : Lat D N'} (hP : ∀ v ∈ M, P.mulVec v ∈ L) {z : VC D N N'} (hz : z ∈ La D (tor0 D cc δ) L L') :
    rgt P z ∈ La D (tor0 D cc δ) M L' := by
  refine La_map _ (rgt P)
    { toFun := fun A => A * P, map_add' := fun A B => Matrix.add_mul A B P,
      map_smul' := fun c A => Matrix.smul_mul c A P } ?_ ?_ hz
  · intro A
    funext τ i j
    show ∑ k, embT D τ (A i k) * embT D τ (P k j) = embT D τ ((A * P) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul]
  · intro A hA x hx
    show (A * P).mulVec x ∈ L'
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hP x hx)

theorem one_sub_mulVec {n : ℕ} (P : Matrix (Fin n) (Fin n) D.host.E) (v : Fin n → D.host.E) :
    (1 - P).mulVec v = v - P.mulVec v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]

theorem bet_proj {n : ℕ} {L₁ L₂ L₃ : Lat D n} (hb : Bet D L₁ L₂ L₃) {P : Matrix (Fin n) (Fin n) D.host.E}
    (h1 : ∀ v ∈ L₁ ⊔ L₃, P.mulVec v ∈ L₁) (h2 : ∀ v ∈ L₃, P.mulVec v ∈ L₃)
    (h3 : ∀ v ∈ L₁, v - P.mulVec v ∈ L₃) (v : Fin n → D.host.E) (hv : v ∈ L₂) :
    P.mulVec v ∈ L₁ ∧ P.mulVec v ∈ L₂ ∧ v - P.mulVec v ∈ L₃ := by
  obtain ⟨a, ⟨ha1, ha2⟩, b, ⟨hb2, hb3⟩, rfl⟩ := Submodule.mem_sup.1 (hb.1 hv)
  have pa := h1 a (Submodule.mem_sup_left ha1)
  have pb := h1 b (Submodule.mem_sup_right hb3)
  rw [Matrix.mulVec_add]
  refine ⟨L₁.add_mem pa pb, L₂.add_mem ?_ (hb.2 ⟨pb, h2 b hb3⟩), ?_⟩
  · have := L₂.sub_mem ha2 (hb.2 ⟨L₁.sub_mem ha1 pa, h3 a ha1⟩)
    rwa [sub_sub_cancel] at this
  · rw [add_sub_add_comm]
    exact L₃.add_mem (h3 a ha1) (L₃.sub_mem hb3 (h2 b hb3))

theorem dist_La : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), (∀ (L : Lat D N) (L₁ L₂ L₃ : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L L₁) (La D (tor0 D cc δ) L L₂) (La D (tor0 D cc δ) L L₃)) ∧ (∀ (L₁ L₂ L₃ : Lat D N) (L' : Lat D N'), SD D L₁ → SD D L₃ → Bet D L₁ L₂ L₃ → Dist (La D (tor0 D cc δ) L₁ L') (La D (tor0 D cc δ) L₂ L') (La D (tor0 D cc δ) L₃ L')) ∧ ∀ (L₀ L : Lat D N) (L₀' L' : Lat D N'), SD D L₀' → SD D L' → Dist (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L₀ L') (La D (tor0 D cc δ) L L') := by
  intro D cc δ N N'
  refine ⟨?_, ?_, ?_⟩
  · intro L L₁ L₂ L₃ s1 s3 hb x hx y _ _
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N' L₁ L₃ s1 s3
    have k := bet_proj hb h1 h2 h3
    rw [← lft_add P x]
    refine add_mem (AddSubgroup.mem_sup_left ⟨lft_mem cc δ P (fun v hv => (k v hv).1) hx,
      lft_mem cc δ P (fun v hv => (k v hv).2.1) hx⟩) (AddSubgroup.mem_sup_right
        ⟨lft_mem cc δ _ (fun v hv => ?_) hx, lft_mem cc δ _ (fun v hv => ?_) hx⟩)
    · rw [one_sub_mulVec]; exact L₂.sub_mem hv (k v hv).2.1
    · rw [one_sub_mulVec]; exact (k v hv).2.2
  · intro L₁ L₂ L₃ L' s1 s3 hb x hx y _ _
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N L₁ L₃ s1 s3
    have k := bet_proj hb h1 h2 h3
    rw [← rgt_add P x, add_comm]
    refine add_mem (AddSubgroup.mem_sup_left ⟨rgt_mem cc δ _ (fun v hv => ?_) hx,
      rgt_mem cc δ _ (fun v hv => ?_) hx⟩) (AddSubgroup.mem_sup_right
        ⟨rgt_mem cc δ P (fun v hv => (k v hv).2.1) hx,
          rgt_mem cc δ P (fun v hv => hb.2 ⟨h1 v (Submodule.mem_sup_right hv), h2 v hv⟩) hx⟩)
    · rw [one_sub_mulVec]; exact hb.2 ⟨L₁.sub_mem hv (h1 v (Submodule.mem_sup_left hv)), h3 v hv⟩
    · rw [one_sub_mulVec]; exact L₂.sub_mem hv (k v hv).2.1
  · intro L₀ L L₀' L' s1 s3 x hx y hy hu
    obtain ⟨P, h1, h2, h3⟩ := GlobalTheory.T.exists_matrix_projection_selfDual_lattices D N' L₀' L' s1 s3
    have q1 : ∀ v ∈ L₀', (1 - P).mulVec v ∈ L₀' := fun v hv => by
      rw [one_sub_mulVec]; exact L₀'.sub_mem hv (h1 v (Submodule.mem_sup_left hv))
    have q2 : ∀ v ∈ L₀', (1 - P).mulVec v ∈ L' := fun v hv => by
      rw [one_sub_mulVec]; exact h3 v hv
    have q3 : ∀ v ∈ L', (1 - P).mulVec v ∈ L' := fun v hv => by
      rw [one_sub_mulVec]; exact L'.sub_mem hv (h2 v hv)
    have e : x = lft P x + lft (1 - P) (x + y) - lft (1 - P) y := by
      rw [map_add, ← add_assoc, lft_add, add_sub_cancel_right]
    have e2 : lft (1 - P) y = lft (1 - P) (x + y) - lft (1 - P) x := by
      rw [map_add, add_sub_cancel_left]
    rw [e]
    refine sub_mem (AddSubgroup.mem_sup_left (add_mem
      ⟨lft_mem cc δ P (fun v hv => h1 v (Submodule.mem_sup_right hv)) hx, lft_mem cc δ P h2 hx⟩
      ⟨lft_mem cc δ _ q1 hu, lft_mem cc δ _ q2 hu⟩)) (AddSubgroup.mem_sup_right ⟨?_, lft_mem cc δ _ q3 hy⟩)
    rw [e2]
    exact AddSubgroup.sub_mem _ (lft_mem cc δ _ q2 hu) (lft_mem cc δ _ q3 hx)

end GlobalTheory.DistLa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionMapCarriesTorusLatticesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionMap_carries_torus_lattices : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → (∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ n : ℕ, 0 < n → (∀ x x' y y', AdpB D (tor0 D cc δ) M ρ b n x x' → AdpB D (tor0 D cc δ) M ρ b n y y' → AdpB D (tor0 D cc δ) M ρ b n (x - y) (x' - y')) ∧ (∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → ∃ t', AdpB D (tor0 D cc δ) M ρ b n t t') ∧ ∀ (k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D (tor0 D cc δ) Y, ∃ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ (∀ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, ∃ x ∈ LaS D (tor0 D cc δ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ ∀ x x', AdpB D (tor0 D cc δ) M ρ b n x x' → (x ∈ LaS D (tor0 D cc δ) Y ↔ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y) := by
  first | exact @GlobalTheory.ThetaConj.adpB_lattices | exact GlobalTheory.ThetaConj.adpB_lattices | (intros; apply GlobalTheory.ThetaConj.adpB_lattices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionTranslateMemThetaPullbackSpanStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionTranslate_mem_thetaPullbackSpan : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ F ∈ Tr D (tor0 D cc δ) b, ∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → U D (tor0 D cc δ) t F ∈ Tr D (tor0 D cc δ) b := by
  first | exact @GlobalTheory.TorsionTranslate.translate_mem | exact GlobalTheory.TorsionTranslate.translate_mem | (intros; apply GlobalTheory.TorsionTranslate.translate_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateLevelFourStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.U_pullB_ne_zero_and_invariant_four_smul : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → Differentiable ℂ (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∧ ∃ t : VC D N N', 2 • t ∈ LaB D (tor0 D cc δ) b ∧ U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) 0 ≠ 0 ∧ ∀ ω ∈ LaB D (tor0 D cc δ) b, U D (tor0 D cc δ) (4 • ω) (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) = U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) := by
  first | exact @GlobalTheory.OddThetaTranslate.translate_level_four | exact GlobalTheory.OddThetaTranslate.translate_level_four | (intros; apply GlobalTheory.OddThetaTranslate.translate_level_four <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientSStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace : NabDelLoc ∧ NabDelFree ∧ NabLeVV := by
  first | exact @GlobalTheory.TransLoc.nabDelLoc_free_leVV | exact GlobalTheory.TransLoc.nabDelLoc_free_leVV | (intros; apply GlobalTheory.TransLoc.nabDelLoc_free_leVV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformisesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_formalGroupLog_uniformises : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  first | exact @GlobalTheory.WpForm.wp_flog | exact GlobalTheory.WpForm.wp_flog | (intros; apply GlobalTheory.WpForm.wp_flog <;> assumption)
end

