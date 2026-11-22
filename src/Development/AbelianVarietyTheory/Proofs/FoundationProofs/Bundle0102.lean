import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem exp_gal (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.exp (X.gal s f) = HahnSeries.map (X.exp f) (s : Ω →+* Ω) := by
  ext r; simp [X.gal_exp]

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  rw [exp_gal, AlgHom.commutes, AlgHom.commutes]
  ext r
  have hC : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.single 0 c := fun c => by
    rw [HahnSeries.algebraMap_apply']
    simp [PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]
  simp only [HahnSeries.map_coeff, hC, HahnSeries.coeff_single]
  split_ifs <;> simp

theorem map_mul_gal (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x * y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) * HahnSeries.map y (s : Ω →+* Ω) :=
  HahnSeries.map_mul (s : Ω →+* Ω).toNonUnitalRingHom

theorem map_sub_gal (s : Ω ≃ₐ[ℚ] Ω) (x y : HahnSeries ℚ Ω) :
    HahnSeries.map (x - y) (s : Ω →+* Ω) = HahnSeries.map x (s : Ω →+* Ω) - HahnSeries.map y (s : Ω →+* Ω) := by
  ext r; simp

theorem theta_map (s : Ω ≃ₐ[ℚ] Ω) (q : ℚ) (φ : HahnSeries ℚ Ω) :
    theta q (HahnSeries.map φ (s : Ω →+* Ω)) = HahnSeries.map (theta q φ) (s : Ω →+* Ω) := by
  ext r; simp [theta]

theorem cgA_map (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hA : ∀ x, x ∈ A ↔ s x ∈ A) (l n : ℕ) (x y : Ω)
    (h : CgA A l n x y) : CgA A l n (s x) (s y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨s z, (hA z).1 hz, by rw [← map_sub, e, map_mul, map_pow, map_natCast]⟩

theorem prim_map (A : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hA : ∀ x, x ∈ A ↔ s x ∈ A) (φ : HahnSeries ℚ Ω)
    (h : Prim A φ) : Prim A (HahnSeries.map φ (s : Ω →+* Ω)) := by
  obtain ⟨h1, r, hr, hu⟩ := h
  refine ⟨fun r => by simpa using (hA _).1 (h1 r), r, by simpa using hr, ?_⟩
  simpa [← map_inv₀] using (hA _).1 hu

theorem exists_root [IsAlgClosed Ω] (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (hM : 0 < M) :
    ∃ (ζ : Ω) (d e : ℤ), IsPrimitiveRoot ζ M ∧ s ζ = ζ ^ d ∧ (d : ZMod M) * e = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (M : Ω) := ⟨Nat.cast_ne_zero.2 hM.ne'⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hs : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hs.pow_eq_one
  have hc : i.Coprime M := (hζ.pow_iff_coprime hM i).1 (hi ▸ hs)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  refine ⟨ζ, i, u, hζ, by rw [zpow_natCast, hi], ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod M)) huv
  push_cast at this
  rw [ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact_mod_cast this

theorem recip_zmod (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (hM : 0 < M) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) (ζ : Ω) (hζ : IsPrimitiveRoot ζ M)
    (d e : ℤ) (hd : s ζ = ζ ^ d) (hde : (d : ZMod M) * e = 1) (δ δ' : SL(2, ℤ))
    (h00 : (en δ' 0 0 : ZMod M) = en δ 0 0) (h01 : (en δ' 0 1 : ZMod M) = e * en δ 0 1)
    (h10 : (en δ' 1 0 : ZMod M) = d * en δ 1 0) (h11 : (en δ' 1 1 : ZMod M) = en δ 1 1) :
    X.gal s (X.sl (ofSL δ') f) = X.sl (ofSL δ) (X.gal s f) := by
  apply X.recip M f hM hf ζ hζ s d hd δ' δ
  refine ⟨h00.symm, ?_, h10.symm, h11.symm⟩
  rw [h01, ← mul_assoc, hde, one_mul]

theorem inv_gal [IsAlgClosed Ω] (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M : ℕ) (f : X.K)
    (hf : Inv X (CongruenceSubgroup.Gamma1 M) f) : Inv X (CongruenceSubgroup.Gamma1 M) (X.gal s f) := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨M1, hM1, hlev, h00, h11, h10⟩ : ∃ M1 : ℕ, 0 < M1 ∧
      (∀ g ∈ CongruenceSubgroup.Gamma M1, X.sl (ofSL g) f = f) ∧
      ((en γ 0 0 : ℤ) : ZMod M1) = 1 ∧ ((en γ 1 1 : ℤ) : ZMod M1) = 1 ∧ ((en γ 1 0 : ℤ) : ZMod M1) = 0 := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      obtain ⟨M0, h0, hl⟩ := X.level f
      obtain ⟨a, b, c⟩ := hγ
      have a' : en γ 0 0 = 1 := by simpa [en] using a
      have b' : en γ 1 1 = 1 := by simpa [en] using b
      have c' : en γ 1 0 = 0 := by simpa [en] using c
      exact ⟨M0, h0, hl, by simp [a'], by simp [b'], by simp [c']⟩
    · refine ⟨M, h, fun g hg => hf g ?_, hγ⟩
      rw [CongruenceSubgroup.Gamma_mem] at hg
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
  obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M1 hM1
  have hT : ModularGroup.T ^ (e * en γ 0 1) ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
  have key := recip_zmod X s M1 hM1 f hlev ζ hζ d e hd hde γ (ModularGroup.T ^ (e * en γ 0 1))
    (by simp [en, ModularGroup.coe_T_zpow]; exact h00.symm) (by simp [en, ModularGroup.coe_T_zpow])
    (by simp [en, ModularGroup.coe_T_zpow]; rw [show (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M1) = 0 from h10, mul_zero])
    (by simp [en, ModularGroup.coe_T_zpow]; exact h11.symm)
  rw [hf _ hT] at key
  exact key.symm

end GlobalTheory.ThGal

namespace GlobalTheory.ThGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cast_of_dvd {a b : ℕ} (h : a ∣ b) (x y : ℤ) (hxy : (x : ZMod b) = y) : (x : ZMod a) = y :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub x y a).2
    (dvd_trans (Int.natCast_dvd_natCast.2 h) ((ZMod.intCast_eq_intCast_iff_dvd_sub x y b).1 hxy))

theorem exists_twist [IsAlgClosed Ω] (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (N l n : ℕ) (hl : 0 < l) (f : X.K)
    (hf : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) f) (δ : SL(2, ℤ))
    (h1 : δ ∈ CongruenceSubgroup.Gamma1 N) (h2 : -δ ∈ CongruenceSubgroup.Gamma (l ^ n)) :
    ∃ δ' : SL(2, ℤ), δ' ∈ CongruenceSubgroup.Gamma1 N ∧ -δ' ∈ CongruenceSubgroup.Gamma (l ^ n) ∧
      X.gal s (X.sl (ofSL δ') f) = X.sl (ofSL δ) (X.gal s f) := by
  rw [CongruenceSubgroup.Gamma1_mem] at h1
  rw [CongruenceSubgroup.Gamma_mem] at h2
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg] at h2
  obtain ⟨g00, g01, g10, g11⟩ := h2
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    obtain ⟨M0, h0, hlev⟩ := X.level f
    obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M0 h0
    obtain ⟨a, b, c⟩ := h1
    have a' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by simpa using a
    have b' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by simpa using b
    have c' : (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by simpa using c
    refine ⟨ModularGroup.T ^ (e * en δ 0 1), ?_, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T_zpow]
    · rw [CongruenceSubgroup.Gamma_mem]
      rw [a'] at g00
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, ModularGroup.coe_T_zpow, en]
      refine ⟨by simpa using g00, ?_, by simp, by simpa using g00⟩
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_neg, Int.cast_mul]
      rw [mul_comm, ← neg_mul, g01, zero_mul]
    · apply recip_zmod X s M0 h0 f hlev ζ hζ d e hd hde δ
      · simp [en, ModularGroup.coe_T_zpow, a']
      · simp [en, ModularGroup.coe_T_zpow]
      · simp [en, ModularGroup.coe_T_zpow, c']
      · simp [en, ModularGroup.coe_T_zpow, b']
  · set M1 := N * l ^ n with hM1def
    have hM1 : 0 < M1 := Nat.mul_pos hN (pow_pos hl n)
    have hlev : ∀ g ∈ CongruenceSubgroup.Gamma M1, X.sl (ofSL g) f = f := by
      intro g hg
      apply hf g
      rw [CongruenceSubgroup.Gamma_mem] at hg
      rw [CongruenceSubgroup.Gamma1_mem]
      exact ⟨hg.1, hg.2.2.2, hg.2.2.1⟩
    obtain ⟨ζ, d, e, hζ, hd, hde⟩ := exists_root s M1 hM1
    let m : Matrix (Fin 2) (Fin 2) (ZMod M1) :=
      !![(en δ 0 0 : ZMod M1), e * en δ 0 1; d * en δ 1 0, en δ 1 1]
    have hm : m.det = 1 := by
      rw [Matrix.det_fin_two_of]
      have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
        have := δ.det_coe; rw [Matrix.det_fin_two] at this; exact this
      have := congrArg (fun z : ℤ => (z : ZMod M1)) hdet
      push_cast at this
      linear_combination this - ((en δ 0 1 : ZMod M1) * en δ 1 0) * hde
    obtain ⟨δ', hδ'⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M1 ⟨m, hm⟩
    have he : ∀ i j, (((δ' : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M1) = m i j := fun i j => by
      have := congrArg (fun g : SL(2, ZMod M1) => (g : Matrix (Fin 2) (Fin 2) (ZMod M1)) i j) hδ'
      simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this
    have e00 : (en δ' 0 0 : ZMod M1) = en δ 0 0 := he 0 0
    have e01 : (en δ' 0 1 : ZMod M1) = ((e * en δ 0 1 : ℤ) : ZMod M1) := by rw [Int.cast_mul]; exact he 0 1
    have e10 : (en δ' 1 0 : ZMod M1) = ((d * en δ 1 0 : ℤ) : ZMod M1) := by rw [Int.cast_mul]; exact he 1 0
    have e11 : (en δ' 1 1 : ZMod M1) = en δ 1 1 := he 1 1
    have dN : N ∣ M1 := Dvd.intro _ rfl
    have dl : l ^ n ∣ M1 := Dvd.intro_left _ rfl
    refine ⟨δ', ?_, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]
      obtain ⟨a, b, c⟩ := h1
      refine ⟨?_, ?_, ?_⟩
      · exact (cast_of_dvd dN _ _ e00).trans a
      · exact (cast_of_dvd dN _ _ e11).trans b
      · refine (cast_of_dvd dN _ _ e10).trans ?_
        rw [Int.cast_mul, show ((en δ 1 0 : ℤ) : ZMod N) = 0 from c, mul_zero]
    · rw [CongruenceSubgroup.Gamma_mem]
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod (l ^ n)) = en δ 0 0 from cast_of_dvd dl _ _ e00]
        exact g00
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod (l ^ n)) = ((e * en δ 0 1 : ℤ) : ZMod (l ^ n)) from
          cast_of_dvd dl _ _ e01]
        push_cast; rw [← mul_neg]; rw [show -((en δ 0 1 : ℤ) : ZMod (l ^ n)) = 0 from g01, mul_zero]
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod (l ^ n)) = ((d * en δ 1 0 : ℤ) : ZMod (l ^ n)) from
          cast_of_dvd dl _ _ e10]
        push_cast; rw [← mul_neg]; rw [show -((en δ 1 0 : ℤ) : ZMod (l ^ n)) = 0 from g10, mul_zero]
      · rw [show (((δ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod (l ^ n)) = en δ 1 1 from cast_of_dvd dl _ _ e11]
        exact g11
    · exact recip_zmod X s M1 hM1 f hlev ζ hζ d e hd hde δ δ' e00 (by rw [e01]; push_cast; rfl)
        (by rw [e10]; push_cast; rfl) e11

end GlobalTheory.ThGal

namespace GlobalTheory

open GlobalTheory.KZ GlobalTheory.Glue

theorem isThB_galB : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w : ℕ) (s : Ω ≃ₐ[ℚ] Ω), (l : Ω) ∈ A.nonunits → (∀ x, x ∈ A ↔ s x ∈ A) → ∀ b : X.Fn l, b ∈ X.B N l w → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n (X.galB l s b) (HahnSeries.map φ (s : Ω →+* Ω)) := by
  intro Ω _ _ _ ε X A N l _ n w s _ hA b _ φ hb
  obtain ⟨f, hfI, hcls, hδ, hdl⟩ := hb
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
  refine ⟨Units.map (X.gal s).toMonoidHom f, ?_, ?_, ?_, ?_⟩
  · rw [hf]; exact ThGal.inv_gal X s _ _ hfI
  · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
        (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
      funext i; fin_cases i <;> simp
    have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
        (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
    rw [hu] at hg
    rw [AdicCompletion.eval_apply] at hcls
    rw [hg, AdicCompletion.eval_apply, Tower.kmap]
    erw [AdicCompletion.map_val_apply]
    rw [hcls]
    simp [Tower.cls, LinearMap.reduceModIdeal_apply]
  · intro δ hδ1 hδ2
    obtain ⟨δ', h1, h2, hrec⟩ := ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
    obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
    refine ⟨X.gal s g, ThGal.inv_gal X s _ _ hg, ?_⟩
    rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · obtain ⟨hφ, a, c, κ, hκ, hfa, ha, hc, hcg⟩ := hdl
    refine ⟨fun r => by simpa using (hA _).1 (hφ r), X.gal s a, X.gal s c, s κ, by simpa using hκ, ?_, ?_, ?_, ?_⟩
    · rw [hf, ← ThGal.gal_algebraMap, ← map_mul, ← map_mul, hfa]
    · rw [ThGal.exp_gal]; exact ThGal.prim_map A s hA _ ha
    · rw [ThGal.exp_gal]; exact ThGal.prim_map A s hA _ hc
    · intro r
      rw [ThGal.exp_gal, ThGal.exp_gal, ← ThGal.map_mul_gal, ← ThGal.map_mul_gal, ThGal.theta_map, ThGal.theta_map,
        ← ThGal.map_mul_gal, ← ThGal.map_mul_gal, ← ThGal.map_sub_gal, HahnSeries.map_coeff, HahnSeries.map_coeff]
      exact ThGal.cgA_map A s hA l n _ _ (hcg r)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionUpperTriangularAction
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.DlUp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem sub_coeff (ε : Ω →+* ℂ) {a b d : ℚ} (h : 0 < a / d) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε a b d φ).coeff s = eOm ε ((a / d)⁻¹ * s * b / d) * φ.coeff ((a / d)⁻¹ * s) := by
  have hs : s = (OrderIso.mulLeft₀ (a / d) h).toOrderEmbedding ((a / d)⁻¹ * s) := by
    show s = (a / d) * ((a / d)⁻¹ * s)
    rw [mul_inv_cancel_left₀ h.ne']
  unfold sub scale
  rw [dif_pos h]
  conv_lhs => rw [hs]
  rw [HahnSeries.embDomain_coeff]
  rfl

theorem theta_one (φ : HahnSeries ℚ Ω) : theta 1 φ = qD φ := by
  ext r
  simp [theta, qD, cm]

theorem mem_of_pow_eq_one (A : ValuationSubring Ω) {y : Ω} {k : ℕ} (hk : k ≠ 0) (hy : y ^ k = 1) : y ∈ A := by
  rw [← A.valuation_le_one_iff]
  by_contra hlt
  push_neg at hlt
  have h := one_lt_pow' hlt hk
  rw [← map_pow, hy, map_one] at h
  exact lt_irrefl _ h

theorem eOm_pow [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) : eOm ε x ^ x.den = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hy : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have h' : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x.num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * h'
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  haveI : NeZero x.den := ⟨x.den_nz⟩
  haveI : NeZero (x.den : Ω) := ⟨Nat.cast_ne_zero.2 x.den_nz⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos x.den Ω x.den_pos))
  have hζ : IsPrimitiveRoot z x.den := Polynomial.isRoot_cyclotomic_iff.1 hz
  have hεζ : IsPrimitiveRoot (ε z) x.den := hζ.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := hεζ.eq_pow_of_pow_eq_one hy
  have hrange : ∃ w, ε w = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := ⟨z ^ i, by rw [map_pow, hi]⟩
  have hε : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := Function.invFun_eq hrange
  apply ε.injective
  rw [map_pow, hε, hy, map_one]

theorem eOm_unit [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (x : ℚ) :
    eOm ε x ≠ 0 ∧ eOm ε x ∈ A ∧ (eOm ε x)⁻¹ ∈ A := by
  have h := eOm_pow ε x
  refine ⟨fun h0 => ?_, mem_of_pow_eq_one A x.den_nz h, mem_of_pow_eq_one A x.den_nz (by rw [inv_pow, h, inv_one])⟩
  rw [h0, zero_pow x.den_nz] at h
  exact zero_ne_one h

theorem prim_sub [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) {a b d : ℚ} (h : 0 < a / d)
    {ψ : HahnSeries ℚ Ω} (hψ : Prim A ψ) : Prim A (sub ε a b d ψ) := by
  obtain ⟨h1, r, hr0, hr⟩ := hψ
  refine ⟨fun s => ?_, (a / d) * r, ?_, ?_⟩
  · rw [sub_coeff ε h]; exact mul_mem (eOm_unit ε A _).2.1 (h1 _)
  · rw [sub_coeff ε h, inv_mul_cancel_left₀ h.ne']; exact mul_ne_zero (eOm_unit ε A _).1 hr0
  · rw [sub_coeff ε h, inv_mul_cancel_left₀ h.ne', mul_inv]; exact mul_mem (eOm_unit ε A _).2.2 hr

theorem isDl_sl_upper : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ) (g : GQ), ent g 1 0 = 0 → 0 < ent g 0 0 → 0 < ent g 1 1 → algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) ∈ A →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A l n 1 f φ →
    IsDl X A l n 1 (X.sl g f) (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ) := by
  intro Ω _ _ _ ε X A N l _ n g h10 ha hd hc f φ hdl
  obtain ⟨hφ, a₀, b₀, κ, hκ, hfb, hPa, hPb, hcg⟩ := hdl
  have hpos : 0 < ent g 0 0 / ent g 1 1 := div_pos ha hd
  have hexp : ∀ u, X.exp (X.sl g u) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp u) :=
    fun u => GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst Ω ε X g h10 u
  have hmul := GlobalTheory.T.substUpperTriangularHahn_mul_and_one Ω ε (ent g 0 0) (ent g 0 1) (ent g 1 1) hpos
  have hqd := GlobalTheory.T.hahnSeriesQDerivative_substUpperTriangular Ω ε (ent g 0 0) (ent g 0 1) (ent g 1 1) hpos
  have hco := sub_coeff ε (b := ent g 0 1) hpos
  have hss : ∀ ψ χ : HahnSeries ℚ Ω, sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (ψ - χ) =
      sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) ψ - sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) χ := by
    intro ψ χ; ext s; simp [hco, mul_sub]
  simp only [theta_one] at hcg
  refine ⟨?_, X.sl g a₀, X.sl g b₀, κ, hκ, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hco, smul_eq_mul]
    exact mul_mem hc (mul_mem (eOm_unit ε A _).2.1 (hφ _))
  · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
  · rw [hexp]; exact prim_sub ε A hpos hPa
  · rw [hexp]; exact prim_sub ε A hpos hPb
  · intro s
    simp only [theta_one]
    rw [hexp, hexp, hqd, hqd]
    have e1 : HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ *
        sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp a₀) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp b₀) =
        HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) *
          sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (φ * X.exp a₀ * X.exp b₀) := by
      rw [(hmul _ _).1, (hmul _ _).1]; ring
    have e2 : HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp a₀)) *
        sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp b₀) - sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp a₀) *
        (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp b₀))) =
        HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) *
          sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp a₀) * X.exp b₀ - X.exp a₀ * qD (X.exp b₀)) := by
      rw [hss, (hmul _ _).1, (hmul _ _).1]; ring
    rw [e1, e2]
    obtain ⟨z, hz, hzeq⟩ := hcg ((ent g 0 0 / ent g 1 1)⁻¹ * s)
    refine ⟨algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) *
      eOm ε ((ent g 0 0 / ent g 1 1)⁻¹ * s * ent g 0 1 / ent g 1 1) * z,
      mul_mem (mul_mem hc (eOm_unit ε A _).2.1) hz, ?_⟩
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul, hco, hco,
      smul_eq_mul, smul_eq_mul, ← mul_sub, ← mul_sub, hzeq]
    ring

end GlobalTheory.DlUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPrimitiveRootEOmLevel
section
noncomputable section

namespace GlobalTheory.Glue.Roots

open GlobalTheory.KZ GlobalTheory.K5

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem eOm_pow (ε : Ω →+* ℂ) (x : ℚ) (n : ℕ) : eOm ε x ^ n = eOm ε (n * x) := by
  apply ε.injective
  rw [map_pow, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem isPrimitiveRoot_eOm_inv (ε : Ω →+* ℂ) {n : ℕ} (hn : n ≠ 0) :
    IsPrimitiveRoot (eOm ε (1 / (n : ℚ))) n := by
  apply IsPrimitiveRoot.of_map_of_injective (f := ε) _ ε.injective
  rw [eOm_spec ε ε.injective]
  convert Complex.isPrimitiveRoot_exp n hn using 2
  push_cast; ring

theorem isPrimitiveRoot_zt (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (zt ε l m) (l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (pow_ne_zero m hl)
  rwa [Nat.cast_pow] at h

theorem zt_add_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m k : ℕ) :
    zt ε l (m + k) ^ l ^ k = zt ε l m := by
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
  rw [zt, zt, eOm_pow]
  congr 1; push_cast; field_simp; ring

theorem zt_succ_pow (ε : Ω →+* ℂ) {l : ℕ} (hl : l ≠ 0) (m : ℕ) :
    zt ε l (m + 1) ^ l = zt ε l m := by
  simpa using zt_add_pow ε hl m 1

theorem eOm_level_pow (ε : Ω →+* ℂ) {N : ℕ} (hN : N ≠ 0) (l m : ℕ) :
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = zt ε l m := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  rw [zt, eOm_pow]
  congr 1
  rw [one_div, one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN', one_mul]

theorem isPrimitiveRoot_eOm_level (ε : Ω →+* ℂ) {N l : ℕ} (hN : N ≠ 0) (hl : l ≠ 0) (m : ℕ) :
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) := by
  have h := isPrimitiveRoot_eOm_inv ε (mul_ne_zero hN (pow_ne_zero m hl))
  rwa [Nat.cast_mul, Nat.cast_pow] at h

theorem eOm_isPrimitiveRoot_compatible : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Function.Injective ε →
    ∀ (l : ℕ), l.Prime → ∀ (N : ℕ), 0 < N → ∀ m : ℕ,
    IsPrimitiveRoot (eOm ε (1 / (l : ℚ) ^ m)) (l ^ m) ∧ eOm ε (1 / (l : ℚ) ^ (m + 1)) ^ l = eOm ε (1 / (l : ℚ) ^ m) ∧
    IsPrimitiveRoot (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) (N * l ^ m) ∧
    eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ N = eOm ε (1 / (l : ℚ) ^ m) := by
  intro Ω _ _ _ ε _ l hl N hN m
  have hl0 : l ≠ 0 := hl.ne_zero
  have hN0 : N ≠ 0 := hN.ne'
  exact ⟨isPrimitiveRoot_zt ε hl0 m, zt_succ_pow ε hl0 m, isPrimitiveRoot_eOm_level ε hN0 hl0 m, eOm_level_pow ε hN0 l m⟩

end GlobalTheory.Glue.Roots
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiag
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES

open GlobalTheory.KroneckerCongruence in

theorem kron_frob_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a →
    SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  intro Ω _ _ _ ε X q hq V s hs a ha r
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hε : Function.Injective ε := ε.injective
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hs.1)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs.2 x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs.2 x x.2).2.2
  set c := X.exp a with hc
  have hdq : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hA : (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a)).coeff r = c.coeff (r / q) := by
    have h := X.exp_upper (toGQ !![(q : ℤ), 0; 0, 1]) (by rw [ent_toGQ _ hdq]; simp) a (r / q)
    rw [ent_toGQ _ hdq, ent_toGQ _ hdq, ent_toGQ _ hdq] at h
    simp [eOm_zero hε, hq0] at h
    rw [← h]
  set B := X.exp (X.gal s.symm a) with hB
  have hBc : ∀ t, B.coeff t = s.symm (c.coeff t) := fun t => by rw [hB, X.gal_exp]
  have hBV : ∀ t, B.coeff t ∈ V := fun t => by rw [hBc]; exact (hs.2 _ (ha t)).2.1
  have hBq : X.exp ((X.gal s.symm a) ^ q) = hahnSeriesCoeffRingHomMap V.subtype (liftV V B hBV ^ q) := by
    rw [map_pow, map_pow, map_liftV]
  set y : V := (liftV V B hBV ^ q).coeff r with hy_def
  have hy : (X.exp ((X.gal s.symm a) ^ q)).coeff r = (y : Ω) := by rw [hBq, hahnSeriesCoeffRingHomMap_coeff]; rfl
  have hρy : ρ y = ρ ⟨c.coeff (r / q), ha _⟩ := by
    have h1 : ρ y = (hahnSeriesCoeffRingHomMap ρ (liftV V B hBV ^ q)).coeff r := by rw [hahnSeriesCoeffRingHomMap_coeff]
    rw [h1, map_pow, coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff]
    have h2 : (liftV V B hBV).coeff (r / q) = ⟨s.symm (c.coeff (r / q)), (hs.2 _ (ha _)).2.1⟩ :=
      Subtype.ext (hBc _)
    rw [h2, ← hfrob]
    congr 1
    apply Subtype.ext
    simp
  rw [map_sub, HahnSeries.coeff_sub, hA, hy]
  have hmem : c.coeff (r / q) - (y : Ω) = ((⟨c.coeff (r / q), ha _⟩ - y : V) : Ω) := rfl
  rw [hmem, ValuationSubring.mem_nonunits_iff, ← hρ0, map_sub, hρy, sub_self]

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingPrincipalMinorMulModConductorStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingPrincipalMinor_mul_mod_conductor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ m : Fin n, ¬ Triv (ψ m / nxt ψ m) 1 → (∀ a ∈ grp ψ, valuation k (minor a m) = 1) ∧ ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, Triv (ψ m / nxt ψ m) (minor (a * b) m - minor a m * minor b m) := by
  first | exact @GlobalTheory.PsType.minor_mul_mod | exact GlobalTheory.PsType.minor_mul_mod | (intros; apply GlobalTheory.PsType.minor_mul_mod <;> assumption)
end

