import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsPolynomialModularJOfHasQExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemGammaOfMul
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.HeckeLev

def rep (M q : ℕ) (γ : SL(2, ℤ)) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]
  | some j => !![1, ((j : ℕ) : ℤ) * (M : ℤ); 0, (q : ℤ)]

theorem det_rep (M q : ℕ) (γ : SL(2, ℤ)) (o : Option (Fin q)) : (rep M q γ o).det = q := by
  cases o with
  | none => simp [rep, Matrix.det_mul, Matrix.det_fin_two]
  | some j => simp [rep, Matrix.det_fin_two]

abbrev red (M : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  (Int.castRingHom (ZMod M)).mapMatrix m

theorem red_mul (M : ℕ) (m m' : Matrix (Fin 2) (Fin 2) ℤ) : red M (m * m') = red M m * red M m' :=
  RingHom.map_mul _ _ _

theorem red_rep {M q : ℕ} {γ : SL(2, ℤ)} (hγ : DiagMod M q γ) (o : Option (Fin q)) :
    red M (rep M q γ o) = !![1, 0; 0, (q : ZMod M)] := by
  obtain ⟨h01, h10, h11⟩ := hγ
  simp only [en] at h01 h10 h11
  cases o with
  | some j =>
    ext i k; fin_cases i <;> fin_cases k <;> simp [rep, red]
  | none =>
    have hdet : (γ 0 0 : ZMod M) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this
      have := congrArg (fun z : ℤ => (z : ZMod M)) this; push_cast at this; exact this
    rw [h01, h10, h11] at hdet
    ext i k; fin_cases i <;> fin_cases k <;>
      simp [rep, red, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h11] <;> linear_combination hdet

theorem mem_Gamma_of_mul {M q : ℕ} (hqM : Nat.Coprime q M) (δ : SL(2, ℤ)) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (hm : red M m = !![1, 0; 0, (q : ZMod M)]) (h : red M ((δ : Matrix (Fin 2) (Fin 2) ℤ) * m) = !![1, 0; 0, (q : ZMod M)]) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  have hu : IsUnit (!![1, 0; 0, (q : ZMod M)] : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    simpa using (ZMod.unitOfCoprime q hqM).isUnit
  have h2 : red M (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (q : ZMod M)] = !![1, 0; 0, (q : ZMod M)] := by
    rw [← hm]; exact (RingHom.map_mul _ _ _).symm.trans (h.trans hm.symm)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  exact hu.mul_right_cancel (h2.trans (one_mul _).symm)

theorem map_rep {M q : ℕ} (hq : q.Prime) (hqM : Nat.Coprime q M) {γ : SL(2, ℤ)} (hγ : DiagMod M q γ)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma M) (o : Option (Fin q)) :
    ∃ o', ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma M ∧
      rep M q γ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o' := by
  set m := rep M q γ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) with hmdef
  have hm : m.det = q := by
    rw [hmdef, Matrix.det_mul, det_rep, Matrix.SpecialLinearGroup.det_coe, mul_one]
  have hδ1 : red M (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [CongruenceSubgroup.Gamma_mem'] at hδ
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod M) => (x : Matrix (Fin 2) (Fin 2) (ZMod M))) hδ
    simpa using this
  have hred : red M m = !![1, 0; 0, (q : ZMod M)] := by
    rw [hmdef, red_mul, hδ1, Matrix.mul_one, red_rep hγ]

  have fin : ∀ o' (g : Matrix (Fin 2) (Fin 2) ℤ), g * rep M q γ o' = m →
      ∃ g' : SL(2, ℤ), g' ∈ CongruenceSubgroup.Gamma M ∧ m = (g' : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o' := by
    intro o' g he
    have hd : g.det = 1 := by
      have := congrArg Matrix.det he
      rw [Matrix.det_mul, det_rep, hm] at this
      have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      exact mul_right_cancel₀ hq' (this.trans (one_mul _).symm)
    refine ⟨⟨g, hd⟩, ?_, he.symm⟩
    exact mem_Gamma_of_mul hqM _ (rep M q γ o') (red_rep hγ o') (by rw [show ((⟨g, hd⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = g from rfl, he, hred])
  rcases GlobalTheory.cosetPrimeDet q hq m hm with ⟨g, hg⟩ | ⟨k, hk, g, hg⟩
  · have hs : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨g', hg', he⟩ := fin none (g * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) (by
      rw [← hg]; show _ * ((γ : Matrix (Fin 2) (Fin 2) ℤ) * _) = _
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hs, Matrix.one_mul])
    exact ⟨none, g', hg', he⟩
  ·
    have hMq : IsCoprime (M : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM.symm
    obtain ⟨u, v, huv⟩ := hMq
    haveI := Fact.mk hq
    set j : ℕ := ((k : ZMod q) * (u : ZMod q)).val with hj
    have hjq : j < q := ZMod.val_lt _
    have hdiv : (q : ℤ) ∣ (j : ℤ) * M - k := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hj, ZMod.natCast_zmod_val]
      have := congrArg (fun z : ℤ => (z : ZMod q)) huv
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, add_zero] at this
      linear_combination (k : ZMod q) * this
    obtain ⟨t, ht⟩ := hdiv
    obtain ⟨g', hg', he⟩ := fin (some ⟨j, hjq⟩) (g * !![1, -t; 0, 1]) (by
      rw [← hg, Matrix.mul_assoc]; congr 1
      ext a b; fin_cases a <;> fin_cases b <;> simp [rep] <;> linear_combination ht)
    exact ⟨some ⟨j, hjq⟩, g', hg', he⟩

theorem rep_distinct {M q : ℕ} (hq : q.Prime) (hqM : Nat.Coprime q M) (γ : SL(2, ℤ)) (o o' : Option (Fin q))
    (h : SL(2, ℤ)) (H : (h : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o = rep M q γ o') : o = o' := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2; rw [Matrix.det_fin_two] at this; exact this
  have nd : ¬ (q : ℤ) ∣ 1 := by
    intro hd
    have : q ∣ 1 := by exact_mod_cast hd
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some k =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00
      exact nd ⟨h 0 0 * γ 0 0 + h 0 1 * γ 1 0, by linear_combination -e00⟩
  | some j =>
    cases o' with
    | none =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      have e10 := congrFun (congrFun H 1) 0
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
      exact nd ⟨γ 0 0 * h 1 1 - h 0 1 * γ 1 0, by rw [e00, e10] at hdet; linear_combination -hdet⟩
    | some k =>
      have e00 := congrFun (congrFun H 0) 0
      have e01 := congrFun (congrFun H 0) 1
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
      rw [e00] at e01
      have hdv : (q : ℤ) ∣ ((k : ℕ) - (j : ℕ) : ℤ) * M := ⟨h 0 1, by linear_combination -e01⟩
      have hc : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM
      have h2 := hc.dvd_of_dvd_mul_right hdv
      have hj := j.2
      have hk := k.2
      congr 1
      apply Fin.ext
      obtain ⟨c, hc⟩ := h2
      have hj' : ((j : ℕ) : ℤ) < q := by exact_mod_cast hj
      have hk' : ((k : ℕ) : ℤ) < q := by exact_mod_cast hk
      have hj0 : (0 : ℤ) ≤ (j : ℕ) := by positivity
      have hk0 : (0 : ℤ) ≤ (k : ℕ) := by positivity
      have hc0 : c = 0 := by
        rcases lt_trichotomy c 0 with hlt | heq | hgt
        · nlinarith
        · exact heq
        · nlinarith
      rw [hc0, mul_zero] at hc
      exact_mod_cast (by linarith : ((j : ℕ) : ℤ) = (k : ℕ))

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem prod_sl_inv (X : Tower Ω ε) (M : ℕ) {ι : Type} [Fintype ι]
    (r : ι → Matrix (Fin 2) (Fin 2) ℤ) (hr : ∀ i, 0 < (r i).det) (δ : SL(2, ℤ))
    (hmap : ∀ i, ∃ i', ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma M ∧
      r i * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * r i')
    (hdis : ∀ i i' (h : SL(2, ℤ)), (h : Matrix (Fin 2) (Fin 2) ℤ) * r i = r i' → i = i')
    (f : X.K) (hf : Lev X M f) :
    X.sl (ofSL δ) (∏ i, X.sl (toGQ (r i)) f) = ∏ i, X.sl (toGQ (r i)) f := by
  choose s g hg he using hmap
  have hdet1 : ∀ h : SL(2, ℤ), 0 < (h : Matrix (Fin 2) (Fin 2) ℤ).det := fun h => by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  have hinj : Function.Injective s := by
    intro i1 i2 h12
    have hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hg2 : (((g i2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g i2 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    symm
    apply hdis i2 i1 (g i1 * (g i2)⁻¹)
    have e1 := he i1
    have e2 := he i2
    rw [h12] at e1
    have a1 : r i1 = (g i1 : Matrix (Fin 2) (Fin 2) ℤ) * r (s i2) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← e1, Matrix.mul_assoc, hδ, Matrix.mul_one]
    have a2 : r i2 = (g i2 : Matrix (Fin 2) (Fin 2) ℤ) * r (s i2) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← e2, Matrix.mul_assoc, hδ, Matrix.mul_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, a1]
    conv_lhs => rw [a2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ (g i2 : Matrix (Fin 2) (Fin 2) ℤ), hg2, Matrix.one_mul]
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  rw [map_prod]
  have step : ∀ i, X.sl (ofSL δ) (X.sl (toGQ (r i)) f) = X.sl (toGQ (r (s i))) f := by
    intro i
    rw [← X.sl_mul, ← MobLaws.toGQ_SL, ← MobLaws.toGQ_mul _ _ (hr i) (hdet1 δ), he i,
      MobLaws.toGQ_mul _ _ (hdet1 (g i)) (hr (s i)), X.sl_mul, MobLaws.toGQ_SL, hf _ (hg i)]
  simp only [step]
  exact Equiv.prod_comp (Equiv.ofBijective s hbij) (fun i => X.sl (toGQ (r i)) f)

end GlobalTheory.KZ.ES.HeckeLev

namespace GlobalTheory.KZ.ES

theorem lev_heckeProd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ) (f : X.K) (γ : SL(2, ℤ)), 0 < M → q.Prime → Nat.Coprime q M → Lev X M f → DiagMod M q γ →
    Lev X M (Nq X M q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  intro Ω _ _ _ ε X M q f γ _ hq hqM hf hγ δ hδ
  have e : Nq X M q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f =
      ∏ o : Option (Fin q), X.sl (toGQ (HeckeLev.rep M q γ o)) f := by
    rw [Fintype.prod_option, mul_comm, Nq, Finset.prod_range]
    rfl
  rw [e]
  exact HeckeLev.prod_sl_inv X M (HeckeLev.rep M q γ)
    (fun o => by rw [HeckeLev.det_rep]; exact_mod_cast hq.pos) δ
    (HeckeLev.map_rep hq hqM hγ δ hδ) (HeckeLev.rep_distinct hq hqM γ) f hf

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponents
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.KTExp

theorem exists_prim_root_of_isAlgClosed (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n : ℕ) (hn : 0 < n) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne')
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).1 hζ⟩

theorem map_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ)
    (x : ℚ) : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hε : Function.Injective ε := ε.injective
  unfold eOm
  apply Function.invFun_eq
  obtain ⟨ζ, hζ⟩ := exists_prim_root_of_isAlgClosed Ω x.den x.den_pos
  have hζ' : IsPrimitiveRoot (ε ζ) x.den := hζ.map_of_injective hε
  haveI : NeZero x.den := ⟨x.den_nz⟩
  have hpow : (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨x.num, ?_⟩
    have hx : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    calc (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x : ℂ) * x.den) * (2 * Real.pi * Complex.I) := by ring
      _ = _ := by rw [hx]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem eOm_eq_one_iff {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    eOm ε x = 1 ↔ x.den = 1 := by
  have hε : Function.Injective ε := ε.injective
  rw [← hε.eq_iff, map_one, map_eOm, Complex.exp_eq_one_iff]
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  constructor
  · rintro ⟨n, hn⟩
    have h3 : ((x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
      apply mul_left_cancel₀ hne
      push_cast
      rw [hn]; ring
    have : x = n := by exact_mod_cast h3
    rw [this]; rfl
  · intro h
    refine ⟨x.num, ?_⟩
    have : x = (x.num : ℚ) := by
      exact ((Rat.den_eq_one_iff x).1 h).symm
    rw [this]; push_cast; simp; ring

theorem ent_T_pow (L : ℕ) :
    ent (ofSL (ModularGroup.T ^ L)) 0 0 = 1 ∧ ent (ofSL (ModularGroup.T ^ L)) 0 1 = L ∧
    ent (ofSL (ModularGroup.T ^ L)) 1 0 = 0 ∧ ent (ofSL (ModularGroup.T ^ L)) 1 1 = 1 := by
  have h : ((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (L : ℤ); 0, 1] := by
    rw [← zpow_natCast, ModularGroup.coe_T_zpow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · change (((ModularGroup.T ^ L : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) _ _ = _
    rw [h]; simp

end GlobalTheory.Glue.KTExp

namespace GlobalTheory.Glue.KTExp

theorem mem_KT_iff : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (L : ℕ), 0 < L → ∀ f : X.K, (f ∈ KT X L ↔ ∀ r : ℚ, (X.exp f).coeff r ≠ 0 → (r * L).den = 1) := by
  intro Ω _ _ _ ε X L _ f
  obtain ⟨h00, h01, h10, h11⟩ := ent_T_pow L
  have key : ∀ r : ℚ, (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = eOm ε (r * L) * (X.exp f).coeff r := by
    intro r
    have := X.exp_upper (ofSL (ModularGroup.T ^ L)) h10 f r
    rwa [h00, h01, h11, mul_one, div_one, div_one] at this
  have hmem : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := by
    unfold KT
    rw [RingHom.mem_eqLocusField]
    rfl
  rw [hmem]
  constructor
  · intro h r hr
    have k := key r
    rw [h] at k
    have h1 : eOm ε (r * L) = 1 := by
      have : (1 - eOm ε (r * L)) * (X.exp f).coeff r = 0 := by rw [sub_mul, one_mul, ← k, sub_self]
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hr)).symm
    exact (eOm_eq_one_iff ε _).1 h1
  · intro h
    apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
    ext r
    change (X.exp (X.sl (ofSL (ModularGroup.T ^ L)) f)).coeff r = (X.exp f).coeff r
    rw [key r]
    by_cases hr : (X.exp f).coeff r = 0
    · rw [hr, mul_zero]
    · rw [(eOm_eq_one_iff ε _).2 (h r hr), one_mul]

end GlobalTheory.Glue.KTExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantDivQIntegerQExpansions
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

private theorem qParam_one_eq (τ : ℍ) :
    Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * τ) := by
  simp [Function.Periodic.qParam]

private theorem disc_vadd (τ : ℍ) :
    ModularForm.discriminant ((1 : ℝ) +ᵥ τ) = ModularForm.discriminant τ := by
  have h := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
    one_mem_strictPeriods_SL (τ : ℂ)
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at h
  have e : UpperHalfPlane.ofComplex ((τ : ℂ) + ((1 : ℝ) : ℂ)) = (1 : ℝ) +ᵥ τ := by
    ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using τ.im_pos)]
    simp [add_comm]
  rw [e] at h
  simpa [CuspForm.coe_discriminant] using h

private theorem qParam_ne (τ : ℍ) : Function.Periodic.qParam 1 (τ : ℂ) ≠ 0 :=
  Function.Periodic.qParam_ne_zero _

theorem dd_div_q_and_q_div_dd :
    (∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => DD τ / Complex.exp (2 * Real.pi * Complex.I * τ))
      fun n => (c n : ℂ)) ∧
    ∃ c : ℕ → ℤ, c 0 = 1 ∧ HasQ 1 (fun τ => Complex.exp (2 * Real.pi * Complex.I * τ) / DD τ)
      fun n => (c n : ℂ) := by
  obtain ⟨U, hU0, hU⟩ := GlobalTheory.exists_hasQExpansion_discriminant
  have hu : GlobalTheory.HasQExpansion 1 (fun τ ↦ ModularForm.discriminant τ / Function.Periodic.qParam 1 τ)
      (PowerSeries.map (Int.castRingHom ℂ) U) :=
    .of_qParam_mul (hU.congr fun τ ↦ by field_simp [qParam_ne τ])
  have hcast : ∀ (V : PowerSeries ℤ) (g : ℍ → ℂ),
      GlobalTheory.HasQExpansion 1 g (PowerSeries.map (Int.castRingHom ℂ) V) →
        HasQ 1 g fun n => ((PowerSeries.coeff n V : ℤ) : ℂ) := by
    intro V g hg
    have := (hasQ_coeff_iff_hasQExpansion 1 g _).mpr (by exact_mod_cast hg)
    simpa [PowerSeries.coeff_map] using this
  refine ⟨⟨fun n => PowerSeries.coeff n U, hU0, ?_⟩, ?_⟩
  · have := hcast U _ hu
    convert this using 2 with τ
    rw [qParam_one_eq]; rfl

  set f : ℍ → ℂ := fun τ ↦ Function.Periodic.qParam 1 τ / ModularForm.discriminant τ with hf
  have hper : ∀ τ : ℍ, f ((1 : ℝ) +ᵥ τ) = f τ := fun τ ↦ by
    simp only [hf, GlobalTheory.qParam_one_vadd, disc_vadd]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
    ((GlobalTheory.HasQExpansion.qParam 1).mdifferentiable one_pos).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty f := by
    have ht := (tendsto_const_nhds (x := (1 : ℂ))).div (hu.tendsto one_pos)
      (by simp [PowerSeries.coeff_map, hU0])
    have : f = fun τ ↦ 1 / (ModularForm.discriminant τ / Function.Periodic.qParam 1 τ) := by
      funext τ; simp only [hf]; field_simp
    rw [this]
    exact ht.isBigO_one ℝ
  have h1 := GlobalTheory.HasQExpansion.of_periodic one_pos
    (GlobalTheory.periodic_comp_ofComplex_of_vadd hper) hhol hbdd
  have h2 := (h1.mul hu).unique one_pos ((GlobalTheory.HasQExpansion.const 1 (1 : ℂ)).congr fun τ ↦ by
    simp only [hf]; field_simp [qParam_ne τ, ModularForm.discriminant_ne_zero τ])
  have hUV : U * U.invOfUnit 1 = 1 := PowerSeries.mul_invOfUnit U 1 (by simpa using hU0)
  have h3 : UpperHalfPlane.qExpansion 1 f =
      PowerSeries.map (Int.castRingHom ℂ) (U.invOfUnit 1) := by
    have e := congrArg (· * PowerSeries.map (Int.castRingHom ℂ) (U.invOfUnit 1)) h2
    simp only [mul_assoc, ← map_mul, hUV, map_one, mul_one, one_mul] at e
    exact e
  refine ⟨fun n => PowerSeries.coeff n (U.invOfUnit 1), ?_, ?_⟩
  · simp
  · have := hcast _ _ (h3 ▸ h1)
    convert this using 2 with τ
    simp only [hf, qParam_one_eq]; rfl

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldClearDenominators
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem clear_denominators : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (P : Polynomial T.K), P ≠ 0 → ∃ (p : ℕ → GlobalTheory.FN.ring ε.range) (u : T.K), u ≠ 0 ∧ p P.natDegree ≠ 0 ∧
      ∀ i, T.io (p i) = u * P.coeff i := by
  intro Ω _ _ _ ε T P hP
  classical
  choose a b hb hab using T.io_surj
  set S := Finset.range (P.natDegree + 1) with hS
  have hbne : ∀ f, T.io (b f) ≠ 0 := fun f h => hb f (T.io_inj (by rw [h, map_zero]))
  refine ⟨fun i => if i ∈ S then a (P.coeff i) * ∏ j ∈ S.erase i, b (P.coeff j) else 0,
    T.io (∏ j ∈ S, b (P.coeff j)), ?_, ?_, ?_⟩
  · rw [map_prod]; exact Finset.prod_ne_zero_iff.mpr fun j _ => hbne _
  · have hmem : P.natDegree ∈ S := by simp [hS]
    intro h
    simp only [hmem, if_true] at h
    have h2 := congrArg T.io h
    rw [map_zero, map_mul, ← hab, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hmem] at h2
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hP (Polynomial.leadingCoeff_eq_zero.mp h3)
    · exact (Finset.prod_ne_zero_iff.mpr fun j _ => hbne _) h3
  · intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      rw [map_mul, ← hab, map_prod, map_prod, mul_assoc, Finset.mul_prod_erase S (fun j => T.io (b (P.coeff j))) hi, mul_comm]
    · simp only [hi, if_false, map_zero]
      have : P.natDegree < i := by simp [hS] at hi; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, mul_zero]

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionSlTwoIntInvariantStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_function_slTwoInt_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → ∀ γ : SL(2, ℤ), ∀ z ∈ Hs, φ (mob (ofSL γ) z) = φ z := by
  first | exact @GlobalTheory.KZ.InvFun.fun_inv | exact GlobalTheory.KZ.InvFun.fun_inv | (intros; apply GlobalTheory.KZ.InvFun.fun_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponentialStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n) → ∃ B t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z - ε ((X.exp h).coeff 0)‖ ≤ B * Real.exp (-(2 * Real.pi * (z.im - t))) := by
  first | exact @GlobalTheory.KZ.ExpBound.bound_at_infinity | exact GlobalTheory.KZ.ExpBound.bound_at_infinity | (intros; apply GlobalTheory.KZ.ExpBound.bound_at_infinity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerRootOfInvariantTInvariantStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_rootOfInvariant_T_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ), l.Prime → l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (u : X.K), u ≠ 0 → Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)) → (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) → X.sl (ofSL ModularGroup.T) u = u := by
  first | exact @GlobalTheory.TInv.sl_T_eq | exact GlobalTheory.TInv.sl_T_eq | (intros; apply GlobalTheory.TInv.sl_T_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialEqOfUpperUnipotentDoubleCosetStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_eq_of_upperUnipotent_double_coset : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (w w' u u' : GG g N), (∃ σ : Equiv.Perm (Fin N), ∀ a b, w.val a b ≠ 0 → a = σ b) → (∃ σ : Equiv.Perm (Fin N), ∀ a b, w'.val a b ≠ 0 → a = σ b) → IsUp g N u → IsUp g N u' → u * w = w' * u' → w = w' := by
  first | exact @GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset | exact GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset | (intros; apply GlobalTheory.BadShare.monomial_eq_of_unipotent_double_coset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongr
section
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

theorem normOp_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r →
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  intro R _ p hp σ hF h₁ h₂ r k hk hu he
  obtain ⟨b, hb⟩ := exists_basis_one_add_X_pow R p hF.complete
  exact normOp_congr_of_basis R p b hb h₁ h₂ r k hk hu he

end GlobalTheory.Col
end

