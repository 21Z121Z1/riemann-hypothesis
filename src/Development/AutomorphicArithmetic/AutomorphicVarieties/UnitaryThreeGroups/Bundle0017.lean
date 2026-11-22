import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsIsKroneckerCharOfDiscr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0011
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0032
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0044
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0012

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsGaloisCyclotomicNegOneTrivialOnEtaPsi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem cycMod_cc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {σ : G ℚ Ω}
    (h : IsConjOm σ.toRingEquiv) : cycMod ℚ Ω l 1 σ = -1 := by
  obtain ⟨j, hj⟩ := h
  have hlp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hlp.ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  have hζl : ζ ^ l = 1 := hζ.pow_eq_one
  have hσζ : σ.toRingEquiv ζ = ζ⁻¹ := by
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (n := l)
      (by rw [← map_pow, hζl, map_one]) hlp.ne_zero
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
    simp
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ (n := 1) (by rw [pow_one]; exact hζl)
  have hval : ((cycMod ℚ Ω l 1 σ : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)) =
      PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv).val := rfl
  set a : ZMod (l ^ 1) := PadicInt.toZModPow 1 (cyclotomicCharacter Ω l σ.toRingEquiv).val with ha
  haveI : NeZero (l ^ 1) := ⟨by simp [hlp.ne_zero]⟩
  have hlt : a.val < l := by simpa using ZMod.val_lt a
  have hinv : ζ⁻¹ = ζ ^ (l - 1) := by
    rw [eq_comm, inv_eq_of_mul_eq_one_right]
    rw [← pow_succ', Nat.sub_add_cancel hlp.one_le, hζl]
  have hav : a.val = l - 1 := by
    apply hζ.pow_inj hlt (Nat.sub_lt hlp.pos one_pos)
    rw [← hspec, hσζ, hinv]
  apply Units.ext
  rw [hval, ← ZMod.natCast_zmod_val a, hav, Units.val_neg, Units.val_one, eq_neg_iff_add_eq_zero]
  have h0 : ((l : ℕ) : ZMod (l ^ 1)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    simp
  rw [← h0, ← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hlp.one_le]

theorem UpperTheory.exists_galois_cyclotomic_neg_one_trivial_on_eta_psi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
          {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
          ∃ g : G ℚ Ω, D.η g = 1 ∧ barChar c.O D.Ψ g = 1 ∧ cycMod ℚ Ω l 1 g = -1 := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  obtain ⟨-, hηcc, hΨcc, -⟩ := dat_facts D
  have hcyc_cc : cycMod ℚ Ω l 1 D.cc = -1 := by
    apply cycMod_cc l
    obtain ⟨φ, hφ⟩ := D.conj
    exact ⟨φ, hφ⟩
  have hgd := D.gd.eta
  rw [← D.η_ker] at hgd
  obtain ⟨h, hmem, hnot⟩ := SetLike.not_le_iff_exists.mp hgd
  obtain ⟨hh1, hh2⟩ := Subgroup.mem_inf.mp hmem
  rw [MonoidHom.mem_ker] at hh1 hh2 hnot
  have hηh : D.η h = -1 := (Int.units_eq_one_or _).resolve_left hnot
  obtain ⟨⟨w, hw, -⟩, hall⟩ := omT Ω l c
  have hwk : w.ker = (cycMod ℚ Ω l 1).ker := (hall w hw).1
  have hwh : w h = 1 := by
    rw [← MonoidHom.mem_ker, hwk, MonoidHom.mem_ker]
    exact hh1
  obtain ⟨b, -, -, hcong⟩ := (psiBar Ω l c w hw N ψ).1
  have hΨh : barChar c.O D.Ψ h = 1 := by
    have hm := hcong e h
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, hwh, hh2, one_pow, mul_one, Units.val_one] at hm
    apply Units.ext
    show (residue c.O) ((D.Ψ h : (c.O)ˣ) : c.O) = ((1 : (ResidueField c.O)ˣ) : ResidueField c.O)
    rw [Units.val_one, ← map_one (residue c.O), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hm
  refine ⟨D.cc * h, ?_, ?_, ?_⟩
  · rw [map_mul, hηcc, hηh]
    rfl
  · rw [map_mul, hΨh, mul_one]
    simp only [barChar, MonoidHom.coe_comp, Function.comp_apply, hΨcc, map_one]
  · rw [map_mul, hcyc_cc, hh1, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MemGalOfQuadraticOfFixesDiscrRootsOfUnity
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base

private theorem UpperTheory.exists_fixed_square_root_odd {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (g : Ω →+* Ω) (n : ℕ) :
    Odd n → (∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ) →
      ∃ m : ℤ, m.natAbs = n ∧ m % 4 = 1 ∧ ∃ s : Ω, s ^ 2 = m ∧ g s = s := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hg
    by_cases h1 : n = 1
    · subst h1
      exact ⟨1, rfl, rfl, 1, by norm_num, map_one g⟩
    · set p := n.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime h1
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      rw [← hp_def] at hk
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hk
        obtain ⟨a, ha⟩ := hn
        omega
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · obtain ⟨a, ha⟩ := hn
          rw [h, mul_zero] at hk
          omega
        · exact h
      have hkn : k < n := by
        rw [hk]
        have := hp.two_le
        nlinarith
      have hkodd : Odd k := (Nat.odd_mul.mp (hk ▸ hn)).2
      obtain ⟨m', hm'abs, hm'4, s', hs'sq, hgs'⟩ :=
        ih k hkn hkodd (fun ζ hζ => hg ζ (by rw [hk, pow_mul', hζ, one_pow]))
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : NeZero (p : Ω) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
      obtain ⟨⟨x, hx⟩, hall⟩ := CF.gauss Ω p ζ hp2 hζ
      have hgz : g ζ = ζ ^ 1 := by
        rw [pow_one]
        exact hg ζ (by rw [hk, pow_mul, hζ.pow_eq_one, one_pow])
      have hgx : g x = x := by
        have := (hall x hx).2 g 1 hgz
        simpa [legendreSym.at_one] using this
      have hps : (CF.pStar p).natAbs = p := by
        simp [CF.pStar, Int.natAbs_mul, Int.natAbs_pow]
      have hp4 : CF.pStar p % 4 = 1 := by
        obtain ⟨a, ha⟩ := hp.odd_of_ne_two hp2
        clear_value p
        rcases Nat.even_or_odd a with ⟨c, hc⟩ | ⟨c, hc⟩
        · have e : p / 2 = 2 * c := by omega
          have hpz : (p : ℤ) = 4 * c + 1 := by omega
          rw [CF.pStar, e, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
        · have e : p / 2 = 2 * c + 1 := by omega
          have hpz : (p : ℤ) = 4 * c + 3 := by omega
          rw [CF.pStar, e, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, hpz]
          omega
      refine ⟨CF.pStar p * m', ?_, ?_, x * s', ?_, ?_⟩
      · rw [Int.natAbs_mul, hps, hm'abs, hk]
      · rw [Int.mul_emod, hp4, hm'4]
        rfl
      · rw [mul_pow, hx, hs'sq]
        push_cast
        ring
      · rw [map_mul, hgx, hgs']

theorem UpperTheory.mem_galOf_quadratic_of_fixes_discr_roots_of_unity :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω], Module.finrank ℚ K = 2 → Odd (discr K).natAbs → ∀ g : G ℚ Ω, (∀ ζ : Ω, ζ ^ (discr K).natAbs = 1 → g ζ = ζ) → g ∈ galOf ℚ K Ω := by
  intro Ω _ _ _ K _ _ _ hK hodd g hg
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨m, hmabs, hm4, s, hs, hgs⟩ :=
    UpperTheory.exists_fixed_square_root_odd (g : Ω →+* Ω) (discr K).natAbs hodd (fun ζ h => by simpa using hg ζ h)
  have hd4 : discr K % 4 = 1 := by
    have h2 : Odd (discr K) := Int.natAbs_odd.mp hodd
    rcases GlobalTheory.QuadraticZeta.discr_mod_four hK with h | h
    · obtain ⟨c, hc⟩ := h2
      omega
    · exact h
  have hm : m = discr K := by
    rcases Int.natAbs_eq_natAbs_iff.mp hmabs with h | h
    · exact h
    · rw [h] at hm4
      omega
  subst hm
  have hgs' : g s = s := by simpa using hgs
  obtain ⟨b, t, n, hb0, hb1, hd⟩ := GlobalTheory.QuadraticZeta.exists_basis hK
  set θ : Ω := algebraMap K Ω ((b 1 : 𝓞 K) : K) with hθ
  have hθ2 : θ ^ 2 = t * θ - n := by
    have := congrArg (fun z : 𝓞 K => algebraMap K Ω (z : K)) hb1
    simpa [hθ] using this
  have hy : (2 * θ - t) ^ 2 = s ^ 2 := by
    rw [hs, hd]
    push_cast
    linear_combination 4 * hθ2
  have hgθ : g θ = θ := by
    have hgy : g (2 * θ - t) = 2 * θ - t := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
      · rw [h, hgs']
      · rw [h, map_neg, hgs']
    have e : 2 * g θ - t = 2 * θ - t := by
      rw [← hgy, map_sub, map_mul, map_ofNat, map_intCast]
    linear_combination (1 / 2 : Ω) * e
  have hint : ∀ a : 𝓞 K, g (algebraMap K Ω (a : K)) = algebraMap K Ω (a : K) := by
    intro a
    have e : algebraMap K Ω (a : K) = ((b.repr a 0 : ℤ) : Ω) + ((b.repr a 1 : ℤ) : Ω) * θ := by
      conv_lhs => rw [GlobalTheory.QuadraticZeta.eq_coord b hb0 a]
      simp [hθ]
    rw [e, map_add, map_mul, map_intCast, map_intCast, hgθ]
  change ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x
  intro x
  obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  rw [map_div₀, map_div₀]
  exact congrArg₂ (· / ·) (hint a) (hint c)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PowEqOneOfUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private def ball {F : Type} [NormedField F] [IsUltrametricDist F] (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) : Subgroup Fˣ where
  carrier := {u | ‖(u : F) - 1‖ < ε}
  one_mem' := by simpa using h0
  mul_mem' {a b} ha hb := by
    have ha' : ‖(a : F) - 1‖ < ε := ha
    have hb' : ‖(b : F) - 1‖ < ε := hb
    show ‖((a * b : Fˣ) : F) - 1‖ < ε
    have e : ((a * b : Fˣ) : F) - 1 = ((a : F) - 1) * ((b : F) - 1) + (((a : F) - 1) + ((b : F) - 1)) := by
      rw [Units.val_mul]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_
      ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha' hb')))
    rw [norm_mul]
    nlinarith [norm_nonneg ((a : F) - 1), norm_nonneg ((b : F) - 1)]
  inv_mem' {a} ha := by
    have ha' : ‖(a : F) - 1‖ < ε := ha
    show ‖((a⁻¹ : Fˣ) : F) - 1‖ < ε
    have hn : ‖(a : F)‖ = 1 := by
      have h2 : ‖(a : F) - 1‖ < ‖(1 : F)‖ := by rw [norm_one]; exact ha'.trans_le h1
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne
      rw [sub_add_cancel, max_eq_right h2.le, norm_one] at this
      exact this
    have e : (a : F) * (((a⁻¹ : Fˣ) : F) - 1) = -((a : F) - 1) := by
      rw [mul_sub, Units.mul_inv]; ring
    have := congrArg norm e
    rw [norm_mul, hn, one_mul, norm_neg] at this
    rwa [this]

private theorem eq_one_of_pow {F : Type} [NormedField F] [IsUltrametricDist F] (x : F) (hx : ‖x - 1‖ < 1) (h : ℕ)
    (hh : ‖(h : F)‖ = 1) (e : x ^ h = 1) : x = 1 := by
  have hn : ‖x‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (x - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le hx.le le_rfl)
  have h1 : ∀ n : ℕ, ‖x ^ n - 1‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : x ^ (n + 1) - 1 = x * (x ^ n - 1) + (x - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hx)
      rw [norm_mul]
      nlinarith [norm_nonneg x, norm_nonneg (x ^ n - 1)]
  have h2 : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, x ^ i - n‖ < 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : ∑ i ∈ Finset.range (n + 1), x ^ i - ((n + 1 : ℕ) : F) =
          (∑ i ∈ Finset.range n, x ^ i - n) + (x ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ih (h1 n))
  have h3 := geom_sum_mul x h
  rw [e, sub_self, mul_eq_zero] at h3
  rcases h3 with h3 | h3
  · have := h2 h
    rw [h3, zero_sub, norm_neg, hh] at this
    exact absurd this (lt_irrefl _)
  · exact sub_eq_zero.1 h3

private theorem pow_eq_one_of_unr {K Ω F : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [IsTotallyComplex K] [NormedField F] [IsUltrametricDist F] (κ : G K Ω →* Fˣ) (hc : Continuous fun g => (κ g : F))
    (hI : ∀ (A : ValuationSubring Ω), ∀ g ∈ Ine (F := K) A, κ g = 1) (g : G K Ω) : (κ g : F) ^ classNumber K = 1 := by
  have key : ∀ (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1), ‖(κ g : F) ^ classNumber K - 1‖ < ε := by
    intro ε h0 h1
    let χ := (QuotientGroup.mk' (ball (F := F) ε h0 h1)).comp κ
    have hχ : ∀ x, x ∈ χ.ker ↔ ‖(κ x : F) - 1‖ < ε := fun x => QuotientGroup.eq_one_iff (κ x)
    have hle := Kum.artKer K Ω _ χ ?_ ?_ ?_
    · have hg : g ^ classNumber K ∈ (Kum.artCl K Ω).ker := by
        rw [MonoidHom.mem_ker, map_pow, classNumber]
        exact pow_card_eq_one
      have := (hχ _).1 (hle hg)
      rwa [map_pow, Units.val_pow_eq_pow_val] at this
    · have : (χ.ker : Set (G K Ω)) = {x | ‖(κ x : F) - 1‖ < ε} := Set.ext hχ
      rw [this]
      exact isOpen_lt (hc.sub continuous_const).norm continuous_const
    · intro A x hx
      rw [hχ, hI A x hx]
      simpa using h0
    · rintro c ⟨j, hj⟩
      exfalso
      have hE : ComplexEmbedding.IsReal (j.comp (algebraMap K Ω)) := by
        rw [ComplexEmbedding.isReal_iff]
        ext y
        rw [ComplexEmbedding.conjugate_coe_eq]
        exact (hj (algebraMap K Ω y)).symm.trans (congrArg j (c.commutes y))
      exact IsTotallyComplex.complexEmbedding_not_isReal _ hE
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  by_contra hne
  have hpos := not_le.1 hne
  exact absurd (key _ (lt_min hpos one_pos) (min_le_right _ _)) (not_lt.2 (min_le_left _ _))

theorem UpperTheory.V.U3.char_eq_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (κ : D.η.ker →* (PadicAlgCl l)ˣ),
      Continuous (fun g => (κ g : PadicAlgCl l)) → (∀ g, ‖(κ g : PadicAlgCl l) - 1‖ < 1) →
      (∀ (A : ValuationSubring Ω) (g : D.η.ker), (g : G ℚ Ω) ∈ Ine (F := ℚ) A → κ g = 1) → κ = 1 := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D κ hc h1 hI
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI := D.gd.imag
  let ι : G K Ω →* D.η.ker := (galEmb ℚ K Ω).codRestrict D.η.ker fun s => D.η_ker ▸ galEmb_mem ℚ K Ω s
  have hι : Continuous ι := (galEmbTop ℚ K Ω).1.continuous.subtype_mk _
  have hp := pow_eq_one_of_unr (κ.comp ι) (hc.comp hι) fun A g hg =>
    hI A (ι g) (by
      rw [← ((galEmbFam ℚ K Ω l).1 A).2] at hg
      exact hg)
  have hh : ‖((classNumber K : ℕ) : PadicAlgCl l)‖ = 1 := by
    have hnd : ¬ l ∣ classNumber K := fun h => D.gd.l_cop (h.mul_left _)
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd
  refine MonoidHom.ext fun g => ?_
  have hg : g.1 ∈ (galEmb ℚ K Ω).range := by
    rw [range_galEmb, ← D.η_ker]
    exact g.2
  obtain ⟨s, hs⟩ := hg
  have e : ι s = g := Subtype.ext hs
  have := hp s
  rw [MonoidHom.comp_apply, e] at this
  exact Units.ext (eq_one_of_pow _ (h1 g) _ hh this)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtInertiaAway
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_sum_lt' {F ι : Type} [NormedField F] [IsUltrametricDist F] (s : Finset ι) (f : ι → F) {C : ℝ}
    (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C :=
  _root_.UpperTheory.Reformulated.B.Qe17.norm_sum_lt s f hC h

private theorem det_ne_zero' {F : Type} [NormedField F] [IsUltrametricDist F] {m : ℕ} (t : F) (ht : ‖t‖ = 1)
    (E : Matrix (Fin m) (Fin m) F) (hE : ∀ a b, ‖E a b‖ < 1) : (t • (1 : Matrix (Fin m) (Fin m) F) + E).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.Qi6.det_ne_zero t ht E hE

private theorem conj_of_close {F Γ : Type} [NormedField F] [IsUltrametricDist F] [Group Γ] [Fintype Γ] {m : ℕ}
    (hΓ : ‖(Fintype.card Γ : F)‖ = 1) (ρ ρ₀ : Γ →* GL (Fin m) F)
    (hi : ∀ g a b, ‖(ρ g : Matrix (Fin m) (Fin m) F) a b‖ ≤ 1)
    (hc : ∀ g a b, ‖(ρ g : Matrix (Fin m) (Fin m) F) a b - (ρ₀ g : Matrix (Fin m) (Fin m) F) a b‖ < 1) :
    ∃ M : GL (Fin m) F, ∀ g, (M : Matrix (Fin m) (Fin m) F) * ρ g = ρ₀ g * M := by
  have hi₀ : ∀ g a b, ‖(ρ₀ g : Matrix (Fin m) (Fin m) F) a b‖ ≤ 1 := fun g a b => by
    have e : (ρ₀ g : Matrix (Fin m) (Fin m) F) a b = (ρ g : Matrix (Fin m) (Fin m) F) a b +
      -((ρ g : Matrix (Fin m) (Fin m) F) a b - (ρ₀ g : Matrix (Fin m) (Fin m) F) a b) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hi g a b) (by rw [norm_neg]; exact (hc g a b).le))
  set M : Matrix (Fin m) (Fin m) F := ∑ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ρ g with hM
  have hsplit : M = (Fintype.card Γ : F) • (1 : Matrix (Fin m) (Fin m) F) +
      ∑ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ((ρ g : Matrix (Fin m) (Fin m) F) - ρ₀ g) := by
    have e : ∀ g, (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ρ g =
        1 + (ρ₀ g⁻¹ : Matrix (Fin m) (Fin m) F) * ((ρ g : Matrix (Fin m) (Fin m) F) - ρ₀ g) := fun g => by
      rw [Matrix.mul_sub, ← Units.val_mul (ρ₀ g⁻¹) (ρ₀ g), ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      abel
    rw [hM, Finset.sum_congr rfl fun g _ => e g, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Nat.cast_smul_eq_nsmul]
  have hdet : M.det ≠ 0 := by
    rw [hsplit]
    refine det_ne_zero' _ hΓ _ fun a b => ?_
    rw [Matrix.sum_apply]
    refine norm_sum_lt' _ _ one_pos fun g _ => ?_
    rw [Matrix.mul_apply]
    refine norm_sum_lt' _ _ one_pos fun k _ => ?_
    rw [norm_mul, Matrix.sub_apply]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hi₀ _ _ _) (norm_nonneg _) (hc g k b)
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, fun h => ?_⟩
  show M * _ = _ * M
  rw [hM, Finset.sum_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  simp only [Equiv.coe_mulRight]
  rw [← Matrix.mul_assoc, ← Units.val_mul (ρ₀ h), ← map_mul, map_mul ρ, Units.val_mul, ← Matrix.mul_assoc]
  congr 4
  group

theorem UpperTheory.V.U3.pt_inertia_away :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r),
      ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∃ M : GL (Fin 3) (PadicAlgCl l), ∀ g ∈ Ine (F := ℚ) A, D.η g = 1 →
        (M : Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) * (r g).mat = (r0 D.η D.ΨQ g).mat * M := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ D U g₁ _ r h A hA
  obtain ⟨-, -, -, -, -, hk0, -, -, -, hK, -⟩ := dat_facts D
  let H : Subgroup (G ℚ Ω) := Ine (F := ℚ) A ⊓ D.η.ker
  let i : H →* D.η.ker := Subgroup.inclusion inf_le_right
  let χ : H →* c.Oˣ := (Chr.dirG ℚ Ω ψ).comp H.subtype
  let ρ : H →* GL (Fin 3) (PadicAlgCl l) := (glPart D.η r h.mult).comp i
  let ρ₀ : H →* GL (Fin 3) (PadicAlgCl l) := (glPart D.η (r0 D.η D.ΨQ) (hasSimilitudeFactor_diagonalRepr _ _)).comp i
  have hkill : ∀ g : H, g ∈ χ.ker → (g : G ℚ Ω) ∈ D.Kill := fun g hg => (hK g).2 ⟨A, hA, g.2.1, g.2.2, hg⟩
  have hρ : χ.ker ≤ ρ.ker := fun g hg => by
    show (r g).left = 1
    rw [h.kill g (hkill g hg)]; rfl
  have hρ₀ : χ.ker ≤ ρ₀.ker := fun g hg => by
    show tor _ (D.ΨQ g) = 1
    have h1 : tor _ (D.Ψ g) = 1 := congrArg SemidirectProduct.left (hk0 g (hkill g hg))
    have h2 : D.Ψ g = 1 := by
      have : (tor _ (D.Ψ g) : Matrix (Fin 3) (Fin 3) c.O) 0 0 = 1 := by rw [h1]; simp
      rw [tor_val] at this
      apply Units.ext
      simpa [wt1] using this
    have h3 : D.ΨQ g = 1 := by
      unfold Dat.ΨQ
      rw [MonoidHom.comp_apply, h2, map_one]
    rw [h3, map_one]
  have hfin : Finite χ.range := by
    have : χ.range ≤ ψ.toUnitHom.range := by
      rintro _ ⟨g, rfl⟩
      exact ⟨_, rfl⟩
    have h2 : Finite ψ.toUnitHom.range := Finite.of_surjective _ ψ.toUnitHom.rangeRestrict_surjective
    exact Finite.of_injective _ (Subgroup.inclusion_injective this)
  have hfinQ : Finite (H ⧸ χ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange χ).symm.toEquiv
  letI : Fintype (H ⧸ χ.ker) := Fintype.ofFinite _
  have hpow : ∀ x : H ⧸ χ.ker, x ^ orderOf ψ = 1 := fun x => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, MonoidHom.mem_ker, map_pow]
    apply Units.ext
    show ((ψ.toUnitHom (Chr.cls ℚ Ω N g) ^ orderOf ψ : c.Oˣ) : c.O) = 1
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]
  have hnd : ¬ l ∣ Fintype.card (H ⧸ χ.ker) := fun hd => by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
    exact D.gd.ord (hx.symm.dvd.trans (orderOf_dvd_of_pow_eq_one (hpow x)))
  have hnorm : ‖(Fintype.card (H ⧸ χ.ker) : PadicAlgCl l)‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd hl.out).2 hnd)
  obtain ⟨M, hM⟩ := conj_of_close hnorm (QuotientGroup.lift _ ρ hρ) (QuotientGroup.lift _ ρ₀ hρ₀)
    (fun x a b => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact h.int g a b)
    (fun x a b => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact h.red g a b)
  exact ⟨M, fun g hg hη => hM (QuotientGroup.mk (⟨g, hg, hη⟩ : H))⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ULocEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem phiCond_quot {Γ : Type} [Group Γ] [TopologicalSpace Γ] (l : ℕ) (M : Subgroup Γ) [M.Normal]
    (h : PhiCond Γ l) : PhiCond (Γ ⧸ M) l := by
  intro H hH
  have hc : Continuous (QuotientGroup.mk' M) := QuotientGroup.continuous_mk
  haveI := h (H.comap (QuotientGroup.mk' M)) (hH.preimage hc)
  let π : H.comap (QuotientGroup.mk' M) →* H := (QuotientGroup.mk' M).subgroupComap H
  have hπ : Continuous π := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective π :=
    MonoidHom.subgroupComap_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective M)
  refine Finite.of_injective (β := {φ : H.comap (QuotientGroup.mk' M) →* Multiplicative (ZMod l) //
    IsOpen (φ.ker : Set (H.comap (QuotientGroup.mk' M)))}) (fun φ => ⟨φ.1.comp π, φ.2.preimage hπ⟩) ?_
  intro φ φ' e
  exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

private theorem exists_univ_loc (hP : Loc.LocalPublishedTheorems) (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (η : GQ l →* ℤˣ) (Ψ : GQ l →* Oˣ)
    (hη : IsLocallyConstant η) (hΨ : IsLocallyConstant (barChar O Ψ)) : Nonempty (Univ (GCond.noCondition O η Ψ)) := by
  haveI : IsAdicComplete (maximalIdeal O) O := (dvrFacts l O).2.2.2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] O) := (dvrFacts l O).2.2.1
  haveI : Finite (ResidueField O) := by
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue O), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ_[l] O)]
    refine map_nonunit _ _ ?_
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  haveI : IsGalois ℚ_[l] (Om l) := IsAlgClosure.isGalois _ _
  haveI : (Subgroup.normalClosure (∅ : Set (GQ l))).topologicalClosure.Normal :=
    Subgroup.is_normal_topologicalClosure _
  obtain ⟨U⟩ := exists_univ l η Ψ hη hΨ ∅ (fun g hg => hg.elim) _ rfl
    (phiCond_quot l _ fun H hH => Loc.phiCond hP l l H hH)
  refine ⟨{ R := U.R, r := U.r, rep := fun R' _ _ _ => ⟨fun _ => trivial, fun r' _ => ?_⟩ }⟩
  exact (U.rep R').2 r' fun g hg => hg.elim

theorem UpperTheory.V.U3.exists_uLoc :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ), Nonempty D.ULoc := by
  intro hC Ω _ _ _ K _ _ _ l hl c N _ e ψ D
  obtain ⟨-, -, -, hη, hΨ, -⟩ := dat_facts D
  exact exists_univ_loc hC.loc l c.O _ _ (hη.comp_continuous D.ι_cont) (hΨ.comp_continuous D.ι_cont)
end

