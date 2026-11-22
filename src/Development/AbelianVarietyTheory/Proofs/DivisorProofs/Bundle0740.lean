import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.GlobalFields.WeilGroups.QuasiCharacterDecomposition
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0723
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFormalLogSubSmulIntegral
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.QLog

theorem in_frob_formalLog_sub_smul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σB : B →+* B)
    (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σB b)) →
    (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B), constantCoeff g = 1 →
    In (⊤ : Ideal B) (frob p s (formalLog (map (algebraMap B Q) g)) -
      (p : Q) • formalLog (map (algebraMap B Q) g)) := by
  intro p _ B O Q _ _ _ _ _ θ hF σB s hs hσ d g hg
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hXB : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) := HasSubst.X_pow hp
  have hXQ : HasSubst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p) := HasSubst.X_pow hp
  have hX0 : ∀ i : Fin d, constantCoeff ((X i : MvPowerSeries (Fin d) B) ^ p) = 0 := fun i => by
    simp [hp]
  set v := subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) with hv
  have hv1 : constantCoeff v = 1 := by
    rw [hv, constantCoeff_subst_of_zero hXB hX0]
    simp [hg]
  have hgp1 : constantCoeff (g ^ p) = 1 := by simp [hg]
  obtain ⟨u, hu⟩ := isUnit_iff_constantCoeff.mpr (hgp1 ▸ isUnit_one : IsUnit (constantCoeff (g ^ p)))
  set k : MvPowerSeries (Fin d) B := ↑u⁻¹ with hk
  have hgk : g ^ p * k = 1 := by rw [hk, ← hu, Units.mul_inv]
  have hk1 : constantCoeff k = 1 := by
    have := congrArg constantCoeff hgk
    rwa [map_mul, hgp1, one_mul, map_one] at this

  have hc := fun α => GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p p B σB hσ d g α
  choose r hr using hc
  set R : MvPowerSeries (Fin d) B := fun α => r α with hR
  have hvR : v - g ^ p = C (p : B) * R := by
    ext α
    rw [coeff_C_mul, hr α]
    rfl
  set h := v * k with hh
  have hh1 : constantCoeff h = 1 := by rw [hh, map_mul, hv1, hk1, one_mul]
  have hhv : h * g ^ p = v := by rw [hh, mul_assoc, mul_comm k, hgk, mul_one]
  have hhJ : ∀ α, coeff α (h - 1) ∈ Ideal.span {(p : B)} := by
    intro α
    have : h - 1 = C (p : B) * (R * k) := by
      rw [hh, ← hgk, ← sub_mul, hvR, mul_assoc]
    rw [this, coeff_C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hJ : ∀ x ∈ Ideal.span {(p : B)}, ∃ y ∈ Ideal.span {(p : B)}, x ^ p = p * y := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine ⟨(p : B) ^ (p - 1) * a ^ p,
      Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (by omega)), ?_⟩
    rw [mul_pow, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ p), mul_comm]
  have hlog := GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF _ hJ (Fin d) h hh1 hhJ

  set ι := algebraMap B Q with hι
  have hG1 : constantCoeff (map ι g) = 1 := by simp [hg]
  have hmapG : map s (map ι g) = map ι (map σB g) := by
    ext α
    simp [coeff_map, hs]
  have hmapv : map ι v = subst (fun i : Fin d => (X i : MvPowerSeries (Fin d) Q) ^ p)
      (map ι (map σB g)) := by
    rw [hv, map_subst hXB]
    congr 1
    funext i
    simp
  have hσG1 : constantCoeff (map ι (map σB g)) = 1 := by simp [hg]
  have key : frob p s (formalLog (map ι g)) - (p : Q) • formalLog (map ι g) =
      formalLog (map ι h) := by
    rw [frob, map_formalLog s hG1, hmapG, subst_formalLog hXQ hσG1, ← hmapv, ← hhv, map_mul,
      map_pow, formalLog_mul (by simp [hh1]) (by simp [hg]), formalLog_pow p hG1,
      Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
  rw [key]
  intro α
  obtain ⟨b, -, hb⟩ := hlog α
  exact ⟨b, trivial, hb⟩

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitRootPolynomialFactorization
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel.RootPolyFactor

open GlobalTheory.GoodCharsCompare

theorem card_sigma_cyc {r : ℕ} (b : Fin r → Fin r) :
    Fintype.card (Σ c : Cyc b, Fin (cycLen b c)) = r := by
  have e : (Σ c : Cyc b, {i : Fin r // b i = c.1}) ≃ Fin r :=
    { toFun := fun y => y.2.1
      invFun := fun i => ⟨⟨b i, i, rfl⟩, i, rfl⟩
      left_inv := by
        rintro ⟨⟨c, hc⟩, i, hi⟩
        cases hi
        rfl
      right_inv := fun i => rfl }
  have := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_sigma] at this
  rw [Fintype.card_sigma]
  simpa using this

theorem rootsBar_prod {p : ℕ} [Fact p.Prime] {ι : Type} (s : Finset ι) (φ : ι → (ZMod p)[X])
    (h : ∀ c, (φ c).Monic) {z : Fbar p} :
    z ∈ Formalism.CyclotomicNorms.rootsBar (∏ c ∈ s, φ c) ↔ ∃ c ∈ s, z ∈ Formalism.CyclotomicNorms.rootsBar (φ c) := by
  rw [mem_rootsBar (monic_prod_of_monic _ _ fun c _ => h c).ne_zero, map_prod, Finset.prod_eq_zero_iff]
  simp only [mem_rootsBar (h _).ne_zero]

theorem dg_eq {p : ℕ} [Fact p.Prime] {r : ℕ} {b : Fin r → Fin r} {x : Cyc b → Fbar p}
    (hx : ∀ c, x c ^ (p ^ cycLen b c - 1) = 1) (hinj : Function.Injective (rootElt x)) (c : Cyc b) :
    dg (x c) = cycLen b c := by
  obtain ⟨k, hk⟩ := exists_dg_mul (cycLen_pos b c) (hx c)
  have h0 := cycLen_pos b c
  have hle : dg (x c) ≤ cycLen b c := Nat.le_of_dvd h0 ⟨k, hk⟩
  by_contra hne
  have hlt : dg (x c) < cycLen b c := lt_of_le_of_ne hle hne
  have := @hinj ⟨c, ⟨dg (x c), hlt⟩⟩ ⟨c, ⟨0, h0⟩⟩ (by
    show x c ^ p ^ dg (x c) = x c ^ p ^ 0
    rw [(frobenius_orbit_degreeOverPrimeFieldFbar (x c)).1, pow_zero, pow_one])
  have h2 := congrArg (fun y : (Σ c : Cyc b, Fin (cycLen b c)) => (y.2 : ℕ)) this
  exact (dg_pos (x c)).ne' h2

theorem mem_roots_lt {p : ℕ} [Fact p.Prime] {y z : Fbar p} :
    z ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) y) ↔ ∃ i < dg y, y ^ p ^ i = z := by
  classical
  rw [← Multiset.mem_toFinset, roots_minpoly]
  simp

theorem rootPoly_factor : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) (b : Fin r → Fin r) (x : Cyc b → Fbar p) (f : (ZMod p)[X]), IsRootPoly x f → f.natDegree = r ∧ f.coeff 0 ≠ 0 ∧ (Squarefree f ↔ Function.Injective (rootElt x)) ∧ (Squarefree f → (∀ c, (minpoly (ZMod p) (x c)).natDegree = cycLen b c) ∧ Function.Injective (fun c => minpoly (ZMod p) (x c)) ∧ f = ∏ c, minpoly (ZMod p) (x c)) := by
  intro p _ r b x f ⟨hx, hm, hr⟩
  have hdeg : f.natDegree = r := by
    rw [← card_rootsBar, hr, Multiset.card_map, ← Finset.card_def, Finset.card_univ, card_sigma_cyc]
  have hsq : Squarefree f ↔ Function.Injective (rootElt x) := by
    rw [squarefree_iff hm.ne_zero, hr, Multiset.nodup_map_iff_inj_on Finset.univ.nodup]
    simp [Function.Injective]
  refine ⟨hdeg, ?_, hsq, fun hs => ?_⟩
  · rw [coeff_zero_iff hm.ne_zero, hr, Multiset.mem_map]
    rintro ⟨⟨c, i⟩, -, h⟩
    have h1 : x c = 0 := eq_zero_of_pow_eq_zero h
    have := hx c
    rw [h1, zero_pow (g_pow_sub_pos (cycLen_pos b c)).ne'] at this
    exact zero_ne_one this
  · have hinj := hsq.1 hs
    have hd := dg_eq hx hinj
    refine ⟨hd, fun c c' h => ?_, ?_⟩
    · have h1 : x c' ∈ Formalism.CyclotomicNorms.rootsBar (minpoly (ZMod p) (x c)) := by
        rw [show minpoly (ZMod p) (x c) = minpoly (ZMod p) (x c') from h]
        exact mem_roots_minpoly.2 ⟨0, by simp⟩
      obtain ⟨i, hi, e⟩ := mem_roots_lt.1 h1
      have := @hinj ⟨c, ⟨i, hd c ▸ hi⟩⟩ ⟨c', ⟨0, cycLen_pos b c'⟩⟩ (by
        show x c ^ p ^ i = x c' ^ p ^ 0
        rw [e, pow_zero, pow_one])
      exact congrArg Sigma.fst this
    · have hmon : ∀ c, (minpoly (ZMod p) (x c)).Monic := fun c => minpoly.monic (isInt _)
      have hP := monic_prod_of_monic Finset.univ _ fun c _ => hmon c
      apply eq_of_rootsBar hm hP
      apply Multiset.eq_of_le_of_card_le
      · rw [Multiset.le_iff_subset ((squarefree_iff hm.ne_zero).1 hs)]
        intro z hz
        rw [hr, Multiset.mem_map] at hz
        obtain ⟨⟨c, i⟩, -, rfl⟩ := hz
        exact (rootsBar_prod _ _ hmon).2 ⟨c, Finset.mem_univ _, mem_roots_minpoly.2 ⟨i, rfl⟩⟩
      · rw [card_rootsBar, card_rootsBar, hdeg, natDegree_prod_of_monic _ _ fun c _ => hmon c]
        have := card_sigma_cyc b
        rw [Fintype.card_sigma] at this
        simp only [Fintype.card_fin] at this
        exact ((Finset.sum_congr rfl fun c _ => hd c).trans this).le

end GlobalTheory.ParamLabel.RootPolyFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFamilyOfRealised
section
noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial NumberField Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison GlobalTheory.IndefiniteRowSideFullHecke.TameCharacterTorusValues Formalism.MainNotions.PrimeDegreeVariant

section Conclusion

variable {K G : Type} [Field K] [Group G]

def ConclFinset (emb : K →+* ℂ) (Y : Set (G → ℂ)) : Prop :=
  ∃ Xg : Finset (G → K), (∀ ch, ch ∈ Y ↔ ∃ c ∈ Xg, ∀ t, ch t = emb (c t)) ∧ (∀ c ∈ Xg, IsAbsIrrChar c) ∧
    ∃ T : GoodSet K G, ∀ c, c ∈ Xg ↔ ∃ s : T.S, ∀ t, c t = LinearMap.trace K (T.W s) (T.tau s t)

def ConclRange (σ : K →+* ℂ) (Y : Set (G → ℂ)) : Prop :=
  (∀ Θ ∈ Y, ∃ ΘK : G → K, (∀ t, σ (ΘK t) = Θ t) ∧ IsAbsIrrChar ΘK) ∧
    ∃ T : GoodSet K G, (Set.range fun (s : T.S) (t : G) => σ (LinearMap.trace K (T.W s) (T.tau s t))) = Y

theorem ConclRange.mono {σ : K →+* ℂ} {Y Y' : Set (G → ℂ)} (h : ConclRange σ Y) (hY : Y' ⊆ Y) : ConclRange σ Y' := by
  classical
  obtain ⟨h1, T, rfl⟩ := h
  let T' : GoodSet K G :=
    { S := {s : T.S // (fun t => σ (LinearMap.trace K (T.W s) (T.tau s t))) ∈ Y'}
      W := fun s => T.W s.1
      tau := fun s => T.tau s.1
      irr := fun s => T.irr s.1
      inj := fun s s' e => Subtype.ext (T.inj e) }
  refine ⟨fun Θ hΘ => h1 Θ (hY hΘ), T', Set.ext fun Θ => ⟨?_, fun hΘ => ?_⟩⟩
  · rintro ⟨s, rfl⟩
    exact s.2
  · obtain ⟨s, rfl⟩ := hY hΘ
    exact ⟨⟨s, hΘ⟩, rfl⟩

end Conclusion

section OnePrime

variable {g : ℕ} [Fact g.Prime] {P : Type} {r m : ℕ}

def FullGood (ω : P → Fbar g →*₀ ℂ) (η : P → Fin m → (ZMod g)ˣ → ℂ) (τ : P → GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (f : P → (ZMod g)[X]) (c : P → Fin m → (ZMod g)ˣ), (∀ v j, IsTameLabel (ω v) (η v j) (c v j)) ∧
    IsGood r g f (fun v (js : Fin m × Bool) => if js.2 then c v js.1 else (c v js.1)⁻¹) ∧
    ∀ v, IndefiniteRowSideFullHecke.CuspValueComparison.IsTypeChar (ω v) (f v) (τ v)

def TorusGood (ι : P → (Fbar g)ˣ →* ℂˣ) (η : P → Fin m × Bool → (ZMod g)ˣ → ℂ)
    (τ : P → GL (Fin r) (ZMod g) → ℂ) : Prop :=
  ∃ (f : P → (ZMod g)[X]) (c : P → Fin m × Bool → (ZMod g)ˣ), (∀ v j, IsCharLabel (ι v) (η v j) (c v j)) ∧
    IsGood r g f c ∧ ∀ v, IndefiniteRowSideFullHecke.TameCharacterTorusValues.IsTypeChar (ι v) (f v) (τ v)

theorem FullGood.change {ω ω' : P → Fbar g →*₀ ℂ} (hω : ∀ v, Function.Injective (ω v))
    (hω' : ∀ v, Function.Injective (ω' v)) {η : P → Fin m → (ZMod g)ˣ → ℂ} {τ : P → GL (Fin r) (ZMod g) → ℂ}
    (h : FullGood ω' η τ) : FullGood ω η τ := by
  obtain ⟨f, c, h1, h2, h3⟩ := h
  choose β hβ using fun v => exists_beta (hω v) (hω' v)
  choose f' hf' using fun v => exists_tr (β v) _ (f v) (h2.1 v).1 rfl
  choose c' hc' using fun v j => exists_unit_of_pow (y := β v (algebraMap (ZMod g) (Fbar g) (c v j)))
    (by rw [← map_pow, unit_pow, map_one])
  refine ⟨f', c', fun v j z => ?_, isGood_tr β hf' (fun v js => ?_) h2,
    fun v => isTypeChar_tr (hβ v) (h2.1 v).2.2 (hf' v) (h3 v)⟩
  · rw [h1 v j z, hβ v 1 one_pos _ _ (unit_pow _) (unit_pow _), hc']
  · split_ifs
    · exact hc' v js.1
    · rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, map_inv₀, hc']

theorem FullGood.reindex {P' : Type} (e : P' ≃ P) {ω : P → Fbar g →*₀ ℂ} {η : P → Fin m → (ZMod g)ˣ → ℂ}
    {τ : P → GL (Fin r) (ZMod g) → ℂ} (h : FullGood ω η τ) :
    FullGood (fun v => ω (e v)) (fun v => η (e v)) (fun v => τ (e v)) := by
  obtain ⟨f, c, h0, ⟨h1, h2, h3, h4, h5, v, h6⟩, h7⟩ := h
  refine ⟨fun v => f (e v), fun v => c (e v), fun v => h0 _, ⟨fun v => h1 _, fun v => h2 _,
    fun l hl hb v => h3 l hl hb _, fun l hl hb v => h4 l hl hb _, fun a ha hb => ?_, e.symm v, by simpa using h6⟩,
    fun v => h7 _⟩
  obtain ⟨v, hv⟩ := h5 a ha hb
  exact ⟨e.symm v, by simpa using hv⟩

theorem TorusGood.full (H : CuspidalCharacterFormula) {ι : P → (Fbar g)ˣ →* ℂˣ} {ω : P → Fbar g →*₀ ℂ}
    (hι : ∀ v, Function.Injective (ι v))
    (hω : ∀ v, Function.Injective (ω v)) {η : P → Fin m → (ZMod g)ˣ → ℂ} {η' : P → Fin m × Bool → (ZMod g)ˣ → ℂ}
    (ht : ∀ v j, η' v (j, true) = η v j) (hf : ∀ v j, η' v (j, false) = fun z => (η v j z)⁻¹)
    {τ : P → GL (Fin r) (ZMod g) → ℂ} (h : TorusGood ι η' τ) : FullGood ω η τ := by
  choose ω' hω' he using fun v => exists_ext (hι v)
  obtain ⟨f, c, h1, h2, h3⟩ := h
  have a1 : ∀ v j, IsTameLabel (ω' v) (η v j) (c v (j, true)) := fun v j => ht v j ▸ (label_iff (he v) _ _).1 (h1 v _)
  refine FullGood.change hω hω' ⟨f, fun v j => c v (j, true), a1, ?_,
    fun v => typeChar_full_of_torus H (hω' v) (he v) (h3 v)⟩
  convert h2 using 3 with v js
  obtain ⟨j, _ | _⟩ := js
  · exact label_unique (hω' v) (label_inv (a1 v j)) (hf v j ▸ (label_iff (he v) _ _).1 (h1 v _))
  · rfl

end OnePrime

section Global

variable {E : Type} [Field E] [NumberField E] [StarRing E] {gp : Fin 2 → ℕ} [∀ i, Fact (gp i).Prime]
  {pb : Fin 2 → 𝓞 E} {K : Type} [Field K]

def placeEquiv (hT : IsTypeDatum gp pb) (i : Fin 2) : PlacesOver pb i ≃ ↥(primesOf (pb i)) where
  toFun v := ⟨v.1.1, mem_primesOf.2 ⟨pb_ne_zero hT i, v.2⟩⟩
  invFun v := ⟨toBoth hT i v, (mem_primesOf.1 v.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def eta (hT : IsTypeDatum gp pb) (m : ℕ) (σ : K →+* ℂ) (χ : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* Kˣ) (i : Fin 2)
    (v : ↥(primesOf (pb i))) (j : Fin m) (z : (ZMod (gp i))ˣ) : ℂ :=
  σ (χ (j.val + 1) v.1 (Units.map ((resIso hT i v : ZMod (gp i) →+* kP v.1) : ZMod (gp i) →* kP v.1) z) : Kˣ)

end Global

end GlobalTheory.GoodCharsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
section
set_option autoImplicit false

namespace GlobalTheory.Published

theorem grothendieckDeformation_of_lifting (P : AbelianDeRham) (L : AbelianLifting) :
    GrothendieckDeformation :=
  fun R _ I κ hκ R₀ _ π hπ hI ↦
    ⟨GrothendieckMessing.canonical_of_abelianDeRham P hκ hπ hI, L R I κ hκ R₀ π hπ hI⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeDividedPowerLiftTower
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqLift

theorem dual_eq_sum_of_ker {R R₁ : Type} [CommRing R] [CommRing R₁] (ρ : R →+* R₁) {P : Type*}
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P] (x : Module.Dual R P)
    (hx : ∀ c, ρ (x c) = 0) :
    ∃ (n : ℕ) (j : Fin n → R) (d : Fin n → Module.Dual R P), (∀ k, ρ (j k) = 0) ∧
      x = ∑ k, j k • d k := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun k ↦ x (f (Pi.single k 1)), fun k ↦ (LinearMap.proj k) ∘ₗ s, fun k ↦ hx _, ?_⟩
  ext c
  have e1 : s c = ∑ k, s c k • (Pi.single k (1 : R) : Fin n → R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  have e2 : x c = x (f (s c)) := by rw [← LinearMap.comp_apply f s, hs, LinearMap.id_apply]
  rw [e2, e1, map_sum, map_sum]
  simp [mul_comm]

theorem isAdmissible_reduce : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ F : Submodule R (HdR A), IsAdmissible h F → ∃ F₁ : Submodule R₁ (HdR A₁), IsAdmissible h₁ F₁ ∧
      ∀ y : HdR A₁, y ∈ F₁ ↔ ∃ x ∈ F, (redMor h₂).Corr x y := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ hs g A₀ _ A₁ _ A _ i₁ i₂ i h₁ h₂ h hi hA hg F hF
  obtain ⟨PF, -, PB, -, -⟩ := P
  letI : Algebra R R₁ := ρ.toAlgebra
  have hbc : (AbelianDeRham.bcMor h₂).IsBC := (PB R A g hA hg R₁ A₁ i₂ h₂).1
  obtain ⟨hfin, hproj, -⟩ := PF.prim hA hg

  have hPs : Function.Surjective (redMor h₂).pull := by
    intro c₁
    obtain ⟨z, rfl⟩ := hbc.2 c₁
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | tmul r c =>
      obtain ⟨r', rfl⟩ := hs.surj r
      exact ⟨r' • c, by rw [liftSemi_tmul, LinearMap.map_smulₛₗ]⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  have hex : ∀ x : HdR A, ∃ y : HdR A₁, (redMor h₂).Corr x y := fun x ↦ hbc.exists x
  have huniq : ∀ {x : HdR A} {y y' : HdR A₁}, (redMor h₂).Corr x y → (redMor h₂).Corr x y' → y = y' := by
    intro x y y' e e'
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [e c, e' c]
  have hlift : ∀ y : HdR A₁, ∃ x : HdR A, (redMor h₂).Corr x y := by
    intro y
    let l : primDR A →ₗ[R] R₁ :=
      { toFun c := y ((redMor h₂).pull c)
        map_add' := by simp
        map_smul' r c := by rw [LinearMap.map_smulₛₗ, map_smul]; rfl }
    obtain ⟨x, hx⟩ := Module.projective_lifting_property (Algebra.linearMap R R₁) l hs.surj
    exact ⟨x, fun c ↦ (LinearMap.congr_fun hx c).symm⟩
  let S : Submodule R (HdR A) → Submodule R₁ (HdR A₁) := fun F ↦
    { carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
      add_mem' := by
        rintro a b ⟨x, hx, ex⟩ ⟨x', hx', ex'⟩
        exact ⟨x + x', F.add_mem hx hx', fun c ↦ by simp [ex c, ex' c]⟩
      zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
      smul_mem' := by
        rintro r₁ y ⟨x, hx, ex⟩
        obtain ⟨r, rfl⟩ := hs.surj r₁
        exact ⟨r • x, F.smul_mem r hx, fun c ↦ by simp [ex c]⟩ }
  have comp : ∀ c, (redMor h₁).pull ((redMor h₂).pull c) = (redMor h).pull c :=
    fun c ↦ GrpMor.pull_pull (redMor h₂) (redMor h₁) (redMor h) (fun r ↦ RingHom.congr_fun hs.comp r) hi c
  obtain ⟨⟨N, hN⟩, hFil⟩ := hF
  refine ⟨S F, ⟨⟨S N, ⟨?_, ?_⟩⟩, fun y ↦ ?_⟩, fun y ↦ Iff.rfl⟩
  · refine Submodule.disjoint_def.2 fun y ⟨f, hf, ef⟩ ⟨n, hn, en⟩ ↦ ?_
    have hx : ∀ c, ρ ((f - n) c) = 0 := fun c ↦ by
      rw [LinearMap.sub_apply, map_sub, ← ef c, ← en c, sub_self]
    obtain ⟨k, j, d, hj, hsum⟩ := dual_eq_sum_of_ker ρ (f - n) hx
    have hfp : f = (Submodule.linearProjOfIsCompl F N hN (f - n) : HdR A) := by
      have e1 : Submodule.linearProjOfIsCompl F N hN f = ⟨f, hf⟩ :=
        Submodule.linearProjOfIsCompl_apply_left hN ⟨f, hf⟩
      have e2 : Submodule.linearProjOfIsCompl F N hN n = 0 :=
        (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hN).2 hn
      rw [map_sub, e1, e2, sub_zero]
    refine LinearMap.ext fun c₁ ↦ ?_
    obtain ⟨c, rfl⟩ := hPs c₁
    rw [ef c, hfp, hsum]
    simp [map_sum, Submodule.coe_sum, hj]
  · refine codisjoint_iff_le_sup.2 fun y _ ↦ ?_
    obtain ⟨x, ex⟩ := hlift y
    obtain ⟨f, hf, n, hn, rfl⟩ := Submodule.mem_sup.1 (hN.sup_eq_top ▸ Submodule.mem_top : x ∈ F ⊔ N)
    obtain ⟨yf, ef⟩ := hex f
    obtain ⟨yn, en⟩ := hex n
    refine Submodule.mem_sup.2 ⟨yf, ⟨f, hf, ef⟩, yn, ⟨n, hn, en⟩, huniq (fun c ↦ ?_) ex⟩
    rw [LinearMap.add_apply, LinearMap.add_apply, ef c, en c, map_add]
  · rw [hFil y]
    constructor
    · rintro ⟨x, hx, e⟩
      obtain ⟨x₁, e₁⟩ := hex x
      refine ⟨x₁, ⟨x, hx, e₁⟩, fun c₁ ↦ ?_⟩
      obtain ⟨c, rfl⟩ := hPs c₁
      rw [comp, e c, e₁ c]
      exact (RingHom.congr_fun hs.comp _).symm
    · rintro ⟨x₁, ⟨x, hx, e₁⟩, e⟩
      exact ⟨x, hx, fun c ↦ by rw [← comp, e, e₁ c]; exact RingHom.congr_fun hs.comp _⟩

end GlobalTheory.SqLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterAbsoluteValuePower
section
open NumberField IsDedekindDomain Formalism.L2.Host

noncomputable section

namespace GlobalTheory.HeckeNormPow

def toQC {K : Type} [Field K] [NumberField K] (χ : HChar K) : GroundTheory.Global.QuasiCharacter K where
  toMonoidHom := QuotientGroup.lift _ χ.1 (by
    rintro _ ⟨a, rfl⟩
    exact χ.2.2 a)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 χ.2.1

theorem norm_val_eq_rpow : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), ∃ s : ℝ,
    ∀ w : HeightOneSpectrum (𝓞 K), ‖((χ.val w : ℂˣ) : ℂ)‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ s := by
  intro K _ _ χ
  refine ⟨-(toQC χ).exponent, fun w => ?_⟩
  have h1 := (toQC χ).norm_apply
    (GroundTheory.Global.IdeleClassGroup.mk K (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w))))
  rw [GroundTheory.Global.IdeleClassGroup.ideleModule_mk,
    GroundTheory.Global.ideleModule_finiteEmbedding_of_uniformizer (unif_spec w)] at h1
  have h2 : ((χ.val w : ℂˣ) : ℂ) = (((toQC χ) (GroundTheory.Global.IdeleClassGroup.mk K
      (GroundTheory.Global.IdeleGroup.finiteEmbedding w (atFin w (unif w)))) : ℂˣ) : ℂ) := rfl
  rw [h2, h1, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]

end GlobalTheory.HeckeNormPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLNeZeroNat
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal

theorem IsHeckeL.ne_zero_nat {E : Type} [Field E] [NumberField E] {χ : HChar E} {Λ : ℂ → ℂ} (hu : IsUnitary χ)
    (hΛ : IsHeckeL χ Λ) {s : ℕ} (hs : 1 ≤ s) : Λ s ≠ 0 := by
  rcases hs.eq_or_lt with rfl | h
  · obtain ⟨Z, hZd, hZ⟩ := GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire E
    rw [Nat.cast_one]
    exact GlobalTheory.eulerProduct_ne_zero_one_of_entire _ _ (GlobalTheory.HeckeOne.cf χ) GlobalTheory.HeckeOne.two_le_N
      (GlobalTheory.HeckeOne.norm_cf hu) GlobalTheory.HeckeOne.sumN GlobalTheory.HeckeOne.nonemptyN Z Λ hZd hΛ.1 hZ
      fun s hs => (hΛ.2 s hs).unique (GlobalTheory.HeckeOne.hasProd_exp hu hs)
  · have hs' : 1 < (s : ℂ).re := by
      rw [Complex.natCast_re]; exact_mod_cast h
    rw [(hΛ.2 _ hs').unique (GlobalTheory.HeckeOne.hasProd_exp hu hs')]
    exact Complex.exp_ne_zero _

theorem heckeL_ne_zero_nat : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (m : I → ℤ) (χ : HChar E), IsCMType φ → IsUnitary χ → HasInf χ φ m → (∃ i, m i ≠ 0) → ∃ Λ, IsHeckeL χ Λ) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (m : I → ℤ) (χ : HChar E) (Λ : ℂ → ℂ) (s : ℕ), IsUnitary χ → HasInf χ φ m → (∀ i, 0 < m i) → IsHeckeL χ Λ → 1 ≤ s → Λ s ≠ 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hu _ _ hΛ hs => hΛ.ne_zero_nat hu hs

end GlobalTheory.CMVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeJetSplitDirectionAddStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeJet_split_direction_add : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t v : ℂ) (κ : Emb F → ℕ), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → jet k (split 𝔞 𝔟 x) κ τ (c + v) t = ∑ μ ∈ Finset.Iic κ, ((∏ i, rco k (κ i) (μ i) : ℤ) : ℂ) * v ^ (∑ i, (κ i - μ i)) * jet k (split 𝔞 𝔟 x) μ τ c t := by
  first | exact @GlobalTheory.HilbFam.jet_split_add | exact GlobalTheory.HilbFam.jet_split_add | (intros; apply GlobalTheory.HilbFam.jet_split_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultipleStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) := by
  first | exact @GlobalTheory.NMulHom.isHom_nmul | exact GlobalTheory.NMulHom.isHom_nmul | (intros; apply GlobalTheory.NMulHom.isHom_nmul <;> assumption)
end

