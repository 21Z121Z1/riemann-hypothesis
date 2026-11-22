import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0080
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSupportedIdele
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation
open TensorProduct Formalism.UG Formalism.UG.P

noncomputable section

namespace GlobalTheory.SuppIdele

section Base

variable {F : Type} [Field F] [NumberField F]

theorem exists_int_mul (a : 𝓞 F) (ha : a ≠ 0) (z : FiniteAdeleRing (𝓞 F) F)
    (hz : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (z w) ≤ w.intValuation a) :
    ∃ x ∈ intAd F, z = (a : F) • x := by
  have ha' : (a : F) ≠ 0 := by simpa using ha
  refine ⟨(a : F)⁻¹ • z, fun w => ?_, by rw [smul_smul, mul_inv_cancel₀ ha', one_smul]⟩
  rw [afsplit_smul_apply, HeightOneSpectrum.mem_adicCompletionIntegers, Algebra.smul_def, map_mul, map_inv₀, map_inv₀]
  have h1 : Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)
  rw [h1, inv_mul_le_iff₀ (zero_lt_iff.2 (w.intValuation_ne_zero a ha)), mul_one]
  exact hz w

theorem val_algebraMap (w : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (w.adicCompletion F) (a : F)) = w.intValuation a := by
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (a : F)

theorem intVal_eq_one (w : HeightOneSpectrum (𝓞 F)) {a : 𝓞 F} (h : a ∉ w.asIdeal) : w.intValuation a = 1 :=
  le_antisymm (w.intValuation_le_one a) (not_lt.1 fun h' => h ((w.intValuation_lt_one_iff_mem a).1 h'))

theorem exists_notMem {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) : ∃ c ∈ w.asIdeal, c ∉ v.asIdeal := by
  by_contra H
  push Not at H
  exact h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top H))

theorem eps_dvd (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ x ∈ intAd F, afsplitI v 1 = (c : F) • x := by
  refine exists_int_mul c (by rintro rfl; exact hc (zero_mem _)) _ fun w => ?_
  by_cases h : w = v
  · subst h
    rw [afsplitI_self, map_one, intVal_eq_one w hc]
  · rw [afsplitI_ne v w h, map_zero]
    exact zero_le

theorem one_sub_eps (v : HeightOneSpectrum (𝓞 F)) :
    ∃ a ∈ v.asIdeal ^ 2, ∃ r ∈ v.asIdeal ^ 2, ∃ x ∈ intAd F,
      1 - afsplitI v 1 = (a : F) • x + (r : F) • (1 - afsplitI v 1) := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (pow_ne_zero 2 v.ne_bot)
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime (I := Ideal.span {a}) (by simpa using ha0) v.asIdeal
  have hc : IsCoprime (v.asIdeal ^ 2) Q := (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left
  obtain ⟨r, hr, q, hq, hrq⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨x, hx, hxe⟩ := exists_int_mul a ha0 ((q : F) • (1 - afsplitI v 1)) fun w => by
    rw [afsplit_smul_apply, afsplit_sub_apply, afsplit_one_apply]
    by_cases h : w = v
    · subst h
      rw [afsplitI_self, sub_self, smul_zero, map_zero]
      exact zero_le
    · rw [afsplitI_ne v w h, sub_zero, Algebra.smul_def, mul_one, val_algebraMap]
      obtain ⟨t, ht, htw⟩ := exists_notMem (Ne.symm h)
      have hm := Ideal.mul_mem_mul (Ideal.pow_mem_pow ht
        (Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})))) hq
      rw [← hI, Ideal.mem_span_singleton'] at hm
      obtain ⟨s, hs⟩ := hm
      have := congrArg w.intValuation hs
      rw [map_mul, map_mul, map_pow, intVal_eq_one w htw, one_pow, one_mul] at this
      rw [← this]
      exact mul_le_of_le_one_left' (w.intValuation_le_one s)
  refine ⟨a, ha, r, hr, x, hx, ?_⟩
  rw [← hxe, ← add_smul]
  have : (q : F) + (r : F) = 1 := by
    rw [add_comm]; exact_mod_cast congrArg (fun t : 𝓞 F => (t : F)) hrq
  rw [this, one_smul]

end Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (E) in

def ofInt (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ intAd F) : RInt F E :=
  ⟨(1 : E) ⊗ₜ[F] x, Subring.subset_closure (Or.inr ⟨⟨x, hx⟩, rfl⟩)⟩

theorem coe_toRInt (b : 𝓞 E) : (toRInt F E b : AfE F E) = (b : E) ⊗ₜ[F] 1 := rfl

theorem tmul_smul_eq (a : 𝓞 F) (x : FiniteAdeleRing (𝓞 F) F) (hx : x ∈ intAd F) :
    (1 : E) ⊗ₜ[F] ((a : F) • x) = ((toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx : RInt F E) : AfE F E) := by
  rw [Subring.coe_mul, coe_toRInt, ofInt, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rfl

theorem eps_int (v : HeightOneSpectrum (𝓞 F)) : afsplitI v 1 ∈ intAd F := afsplitI_mem_intAd v 1 (one_mem _)

theorem exists_crt (I Q : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hQ : Q ≠ ⊥) (h : IsCoprime I Q) (b : 𝓞 E) :
    ∃ b' : 𝓞 E, b' ≠ 0 ∧ b' - b ∈ I ∧ b' - 1 ∈ Q := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 h
  have h1 : b * q + p - b ∈ I := by
    have : b * q + p - b = (1 - b) * p := by linear_combination b * hpq
    rw [this]; exact I.mul_mem_left _ hp
  have h2 : b * q + p - 1 ∈ Q := by
    have : b * q + p - 1 = (b - 1) * q := by linear_combination hpq
    rw [this]; exact Q.mul_mem_left _ hq
  by_cases h0 : b * q + p = 0
  · obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mul_ne_zero hI hQ)
    rw [h0] at h1 h2
    refine ⟨t, ht0, ?_, ?_⟩
    · have h3 : t ∈ I := Ideal.mul_le_inf ht |>.1
      rw [show t - b = t + (0 - b) by ring]
      exact I.add_mem h3 h1
    · have h3 : t ∈ Q := Ideal.mul_le_inf ht |>.2
      rw [show t - 1 = t + (0 - 1) by ring]
      exact Q.add_mem h3 h2
  · exact ⟨_, h0, h1, h2⟩

theorem exists_supported_idele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 E)
    (hPv : P.asIdeal.under (𝓞 F) = v.asIdeal) :
    ∃ (y : (AfE F E)ˣ) (y₀ : RInt F E), (y₀ : AfE F E) = (y : AfE F E) ∧ y ∈ suppAt E v ∧
      y₀ - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) ∧
      ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → y₀ - 1 ∈ P'.asIdeal.map (toRInt F E) := by
  haveI := P.isMaximal
  have hv0 : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact v.ne_bot
  obtain ⟨Q, hQ, hI⟩ := Ideal.eq_prime_pow_mul_coprime hv0 P.asIdeal
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    exact hv0 (by rw [hI, Ideal.mul_bot])
  obtain ⟨b', hb0, hb1, hb2⟩ := exists_crt (P.asIdeal ^ 2) Q (pow_ne_zero 2 P.ne_bot) hQ0
    (Ideal.isCoprime_iff_sup_eq.2 hQ).pow_left b
  have hb0' : (b' : E) ≠ 0 := by simpa using hb0
  set e : RInt F E := ofInt E (afsplitI v 1) (eps_int v) with he
  have hee : (e : AfE F E) = afsplitEps E v := rfl
  set ι := inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) with hι
  have hid := afsplit_eps_idem (E := E) v
  have hinv : ι b' * ι (b' : E)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hb0', map_one]
  have hmul : (1 + (ι b' - 1) * afsplitEps E v) * (1 + (ι (b' : E)⁻¹ - 1) * afsplitEps E v) = 1 := by
    linear_combination (ι b' - 1) * (ι (b' : E)⁻¹ - 1) * hid + afsplitEps E v * hinv
  refine ⟨⟨_, _, hmul, by rw [mul_comm, hmul]⟩, 1 + (toRInt F E b' - 1) * e, rfl, ?_, ?_, ?_⟩
  · simp only [Formalism.L2.DIV.suppAt, Subgroup.mem_iInf, MonoidHom.mem_ker]
    intro w hw
    apply Units.ext
    show prV (E := E) w (1 + (ι b' - 1) * afsplitEps E v) = 1
    rw [map_add, map_mul, afsplit_prV_eps_ne v w hw, mul_zero, add_zero, map_one]
  · obtain ⟨a, ha, r, hr, x, hx, hxe⟩ := one_sub_eps v
    have hle : ∀ c ∈ v.asIdeal ^ 2, toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
      intro c hc
      apply Ideal.mem_map_of_mem
      have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hc
      rw [Ideal.map_pow] at h1
      refine Ideal.pow_right_mono ?_ 2 h1
      rw [← hPv]; exact Ideal.map_comap_le
    have hx' : 1 - afsplitI v 1 ∈ intAd F := sub_mem (one_mem _) (eps_int v)
    have h1 : 1 - e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) a) * ofInt E x hx +
        toRInt F E (algebraMap (𝓞 F) (𝓞 E) r) * ofInt E _ hx' := by
      apply Subtype.ext
      rw [Subring.coe_add, ← tmul_smul_eq, ← tmul_smul_eq, ← TensorProduct.tmul_add, ← hxe, TensorProduct.tmul_sub]
      rfl
    have h2 : 1 - e ∈ (P.asIdeal ^ 2).map (toRInt F E) := by
      rw [h1]
      exact add_mem (Ideal.mul_mem_right _ _ (hle a ha)) (Ideal.mul_mem_right _ _ (hle r hr))
    have h3 : 1 + (toRInt F E b' - 1) * e - toRInt F E b = toRInt F E (b' - b) + (1 - toRInt F E b') * (1 - e) := by
      rw [map_sub]; ring
    rw [h3]
    exact add_mem (Ideal.mem_map_of_mem _ hb1) (Ideal.mul_mem_left _ _ h2)
  · intro P' hP'
    rw [add_sub_cancel_left]
    by_cases hle : v.asIdeal.map (algebraMap (𝓞 F) (𝓞 E)) ≤ P'.asIdeal
    · rw [hI] at hle
      have hQP : Q ≤ P'.asIdeal := by
        rcases P'.isPrime.mul_le.1 hle with h | h
        · haveI := P'.isPrime
          exact absurd (HeightOneSpectrum.ext (P.isMaximal.eq_of_le P'.isPrime.ne_top
            (Ideal.IsPrime.le_of_pow_le h))).symm hP'
        · exact h
      have := Ideal.mem_map_of_mem (toRInt F E) (hQP hb2)
      rw [map_sub, map_one] at this
      exact Ideal.mul_mem_right _ _ this
    · have hc : ∃ c : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) c ∈ P'.asIdeal ∧ c ∉ v.asIdeal := by
        by_contra H
        push Not at H
        haveI := P'.isMaximal
        have hm : (P'.asIdeal.under (𝓞 F)).IsMaximal := inferInstance
        apply hle
        rw [← hm.eq_of_le v.isPrime.ne_top (fun c hc => H c hc)]
        exact Ideal.map_comap_le
      obtain ⟨c, hc1, hc2⟩ := hc
      obtain ⟨x, hx, hxe⟩ := eps_dvd v c hc2
      have h1 : e = toRInt F E (algebraMap (𝓞 F) (𝓞 E) c) * ofInt E x hx := by
        apply Subtype.ext
        rw [← tmul_smul_eq, ← hxe]
        rfl
      rw [h1]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc1))

end GlobalTheory.SuppIdele
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfLeAbsNodeSubMid
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lowsFar_poly {y n t N l k d : ℝ} (hy : 28 ≤ y) (hn0 : 0 ≤ n) (ht0 : 0 ≤ t) (hN0 : 0 ≤ N) (hl0 : 0 ≤ l)
    (hk0 : 0 ≤ k) (hd0 : 0 ≤ d) (hn : n ≤ y) (ht : t ≤ y) (hN : N ≤ y) (hl : l ≤ y) (hk : k ≤ y) (hd : d ≤ 2 * y) :
    2 * (n * t ^ 2 * (N + t) * l ^ 2 + k * n ^ 2 * (k * (4 * d) + t + l)) + t / 2 + 3 ≤ y ^ 7 := by
  have hy0 : 0 ≤ y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have h1 : n * t ^ 2 * (N + t) * l ^ 2 ≤ y * y ^ 2 * (y + y) * y ^ 2 := by gcongr
  have h2 : k * n ^ 2 * (k * (4 * d) + t + l) ≤ y * y ^ 2 * (y * (4 * (2 * y)) + y + y) := by gcongr
  have e1 : y * y ^ 2 * (y + y) * y ^ 2 = 2 * y ^ 6 := by ring
  have e2 : y * y ^ 2 * (y * (4 * (2 * y)) + y + y) = 8 * y ^ 5 + 2 * y ^ 4 := by ring
  have p5 : y ^ 5 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p4 : y ^ 4 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p1 : y ^ 1 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have p7 : 28 * y ^ 6 ≤ y ^ 7 := by
    calc 28 * y ^ 6 ≤ y * y ^ 6 := by gcongr
      _ = y ^ 7 := by ring
  rw [pow_one] at p1
  linarith

theorem half_le_abs_node_sub_mid (b : ℝ) (i j : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    H ≤ |(b + i * (2 * H)) - (b + j * (2 * H) + 2 * H / 2)| := by
  rcases Nat.lt_or_ge j i with h | h
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
    exact le_abs.2 (Or.inl (by nlinarith))
  · have : (i : ℝ) ≤ j := by exact_mod_cast h
    exact le_abs.2 (Or.inr (by nlinarith))

theorem szRow_lowsFar : SzRow (fun C D L => (∀ τ (i j : Fin D.R.m),
    2 * L.sc.b / lStar L + (D.R.t : ℝ) / 2 + 3 ≤ |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)|)) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨402, fun cD hcD => ⟨cD * 7, fun ch hch => ⟨max x1 28, fun D L he hx V τ i j => ?_⟩⟩⟩
  have hx28 : 28 ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hx1' : 1 ≤ L.sc.x := by linarith
  obtain ⟨hf, -, hr, hkr, -, hLx, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ :=
    hx1 L.sc D.R he (le_trans (le_max_left _ _) hx) V.ranks
  have up : ∀ a : ℝ, a ≤ 402 → L.sc.x ^ a ≤ L.sc.x ^ cD := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx1' (le_trans ha hcD)
  have hxy : L.sc.x ≤ L.sc.x ^ cD := by simpa using up 1 (by norm_num)
  have hn : (D.R.n : ℝ) ≤ L.sc.x ^ cD := by
    have : (D.R.n : ℝ) ≤ D.R.f := by
      unfold Ranks.f; exact_mod_cast (by omega)
    exact this.trans (hf.trans (up _ (by norm_num)))
  have hk : (D.R.k : ℝ) ≤ L.sc.x ^ cD := by
    have : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact this.trans (hr.trans (up _ (by norm_num)))
  have hd : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have key := lowsFar_poly (y := L.sc.x ^ cD) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hn
    (ht.trans (up _ (by norm_num))) (hN.trans (up _ (by norm_num))) (hLx.trans hxy) hk hd
  have h7 : (L.sc.x ^ cD) ^ 7 ≤ (⌈L.sc.x ^ ch⌉₊ : ℝ) := by
    refine le_trans ?_ (Nat.le_ceil _)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hx1' (by simpa using hch)
  obtain ⟨-, -, ⟨b1, hb, -⟩, -⟩ := V.hc
  have hdist := half_le_abs_node_sub_mid (b1 τ : ℝ) i.1 j.1 (⌈L.sc.x ^ ch⌉₊ : ℝ) (Nat.cast_nonneg _)
  have heq : (((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ) =
      ((b1 τ : ℝ) + i.1 * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ))) -
        ((b1 τ : ℝ) + j.1 * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) + 2 * (⌈L.sc.x ^ ch⌉₊ : ℝ) / 2) := by
    rw [(hb τ j).2, (hb τ i).1, (hb τ j).1]
    unfold h0v
    push_cast
    ring
  rw [heq]
  refine le_trans ?_ (key.trans (h7.trans hdist))
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hm : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega)
  have hS : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, V.Del_eq]; push_cast; ring
  unfold lStar
  rw [hS]
  set Λ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * ((D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) + D.R.t + L.sc.L) with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have : 0 ≤ L.sc.L := by linarith
    positivity
  have : 2 * L.sc.b / ((D.R.m : ℝ) * L.sc.b / Λ) ≤ 2 * Λ := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hΛ0 hb0.le]
  linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeisenbergCocycleFormIntegralSelfDual
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.CocInt

variable {X : Fields} (A : Amb X) {a b : ℕ}

theorem hv_apply {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc z w = (sc : ℂ) * ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) := rfl

theorem hv_swap {ι : Type} [Fintype ι] (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = (starRingEnd ℂ) (HV sc z w) := by
  simp only [hv_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem emb_apply (x : HomE X.E a b) (τ : X.Tau) (i : Fin b) (j : Fin a) :
    emb A x τ i j = A.δ * X.embC A.σ₀ τ (x (Pi.single j 1) i) := rfl

theorem hv_smul (hX : X.Ok) (r : X.E) (x y : HomE X.E a b) :
    HV A.sc (emb A (r • x)) (emb A y) = HV A.sc (emb A x) (emb A (star r • y)) := by
  rw [hv_apply, hv_apply]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [emb_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul, hX.conjE, Complex.conj_conj]
  ring

theorem emb_add (x y : HomE X.E a b) : emb A (x + y) = emb A x + emb A y := map_add (embH _ _) x y

theorem coc_add_left (x y z : HomE X.E a b) : coc A (x + y) z = coc A x z + coc A y z := by
  simp only [coc, imH, altE, emb_add, map_add, LinearMap.add_apply, Complex.add_re, Complex.add_im]
  ring

theorem coc_zero_left (z : HomE X.E a b) : coc A 0 z = 0 := by
  have := coc_add_left A 0 0 z
  rw [add_zero] at this
  linarith

theorem emb_injective (hX : X.Ok) (hδ : A.δ ≠ 0) : Function.Injective (emb A : HomE X.E a b → _) := by
  intro x y h
  obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
  funext i
  have := congrFun (congrFun (congrFun h τ) i) j
  rw [emb_apply, emb_apply] at this
  simpa using (X.embC A.σ₀ τ).injective (mul_left_cancel₀ hδ this)

variable {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

theorem emb_mem {x : HomE X.E a b} (hx : x ∈ per A N N') : emb A x ∈ LamC (X.embC A.σ₀) A.δ A.AA N N' :=
  ⟨x, hx, rfl⟩

theorem mem_per_iff (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') (x : HomE X.E a b) :
    x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n := by
  constructor
  · intro hx y hy
    have h1 := emb_mem A hx
    rw [← hL.1] at h1
    exact h1 _ (emb_mem A hy)
  · intro h
    have h1 : emb A x ∈ dualLat (HV A.sc) (LamC (X.embC A.σ₀) A.δ A.AA N N') := by
      rintro _ ⟨y, hy, rfl⟩
      exact h y hy
    rw [hL.1] at h1
    obtain ⟨x', hx', e⟩ := h1
    rwa [← emb_injective A hX hδ (a₁ := x') e]

theorem coc_int (hX : X.Ok) (hδ : A.δ ≠ 0) (hL : LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') {x y : HomE X.E a b}
    (hx : x ∈ per A N N') (hy : y ∈ per A N N') : ∃ n : ℤ, coc A x y = n := by
  obtain ⟨m, hm⟩ := (mem_per_iff A hX hδ hL x).1 hx y hy
  have h := hL.2.2 _ (emb_mem A hx) _ (emb_mem A hy)
  simp only [alV, alphaQ, Formalism.L2.Th1.H.qOf] at h
  rw [← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨n + m, ?_⟩
  have h2 := congrArg Complex.im hn
  have h3 : (HV A.sc (emb A y) (emb A x)).re = (HV A.sc (emb A x) (emb A y)).re := by
    rw [hv_swap]; simp
  simp only [imH] at hm
  simp only [map_add, LinearMap.add_apply, Complex.add_re, h3, hm] at h2
  simp at h2
  simp only [coc, imH, hm]
  push_cast
  apply mul_left_cancel₀ Real.pi_ne_zero
  linarith

theorem cocycle_integral : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), X.Ok → A.δ ≠ 0 → LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N' → (∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y)) ∧ (∀ x : HomE X.E a b, x ∈ per A N N' ↔ ∀ y ∈ per A N N', ∃ n : ℤ, imH A x y = n) ∧ ∀ x y : HomE X.E a b, (∀ Q : HeightOneSpectrum (𝓞 X.E), ∃ k : X.E, k ≠ 0 ∧ k⁻¹ • x ∈ localization₂ Q.asIdeal (per A N N') ∧ star k • y ∈ localization₂ (conjPrime₂ Q).asIdeal (per A N N')) → ∃ n : ℤ, coc A x y = n := by
  intro X A a b N N' hX hδ hL
  have h1 : ∀ (r : X.E) (x y : HomE X.E a b), coc A (r • x) y = coc A x (star r • y) ∧ imH A (r • x) y = imH A x (star r • y) := by
    intro r x y
    simp only [coc, imH, altE, hv_smul A hX, and_self]
  refine ⟨h1, mem_per_iff A hX hδ hL, fun x y h => ?_⟩
  let I : Ideal (𝓞 X.E) :=
    { carrier := {r | ∀ s : 𝓞 X.E, ∃ n : ℤ, coc A ((s * r) • x) y = n}
      zero_mem' := fun s => ⟨0, by simp [coc_zero_left]⟩
      add_mem' := fun {r r'} hr hr' s => by
        obtain ⟨n, hn⟩ := hr s
        obtain ⟨m, hm⟩ := hr' s
        exact ⟨n + m, by rw [mul_add, add_smul, coc_add_left, hn, hm, Int.cast_add]⟩
      smul_mem' := fun c r hr s => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hr _ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 X.E) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField X.E)⟩
    obtain ⟨k, hk, hx, hy⟩ := h Q
    obtain ⟨u, hu, hx⟩ := (mem_locP _ _ _).1 hx
    obtain ⟨v, hv, hy⟩ := (mem_locP _ _ _).1 hy
    have hmem : u * cO X.E v ∈ I := by
      intro s
      obtain ⟨n, hn⟩ := coc_int A hX hδ hL (Submodule.smul_mem _ s hx) hy
      refine ⟨n, ?_⟩
      rw [← hn]
      have e1 : (s * (u * cO X.E v)) • x = (star (algebraMap (𝓞 X.E) X.E v) * k) • (s • u • k⁻¹ • x) := by
        rw [← algebraMap_smul X.E s, ← algebraMap_smul X.E u, ← algebraMap_smul X.E (s * _), smul_smul, smul_smul, smul_smul,
          map_mul, map_mul, algebraMap_cO]
        congr 1
        field_simp
      rw [e1, (h1 _ _ _).1, star_mul', star_star, mul_smul, algebraMap_smul]
    rcases hM.isPrime.mem_or_mem (hle hmem) with h' | h'
    · exact hu h'
    · exact hv h'
  have : (1 : 𝓞 X.E) ∈ I := hI ▸ Submodule.mem_top
  simpa using this 1

end GlobalTheory.MomT.CocInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatSumReindexOfLeSup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory

theorem latSum_reindex_of_le_sup (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (D C As B : Submodule (𝓞 E) W) (f g : W → ℂ) (hCD : C ≤ D) (hB : ∀ t ∈ As, t ∈ B ↔ t ∈ C) (hD : D ≤ As ⊔ C)
    (hfg : ∀ x ∈ D, ∀ t ∈ As, t - x ∈ C → f x = g t) (hg : ∀ t ∈ As, t ∉ D → g t = 0) :
    latSum D C f = latSum As B g := by
  classical
  unfold latSum
  set r : (↥D ⧸ C.comap D.subtype) → ↥D :=
    Function.surjInv (Submodule.Quotient.mk_surjective (C.comap D.subtype)) with hr
  set s : (↥As ⧸ B.comap As.subtype) → ↥As :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap As.subtype)) with hs
  have hr' : ∀ z, Submodule.Quotient.mk (r z) = z := fun z => Function.surjInv_eq _ z
  have hs' : ∀ z, Submodule.Quotient.mk (s z) = z := fun z => Function.surjInv_eq _ z
  have hex : ∀ x : ↥D, ∃ t : ↥As, (t : W) - x ∈ C := by
    intro x
    obtain ⟨a, ha, c, hc, h⟩ := Submodule.mem_sup.1 (hD x.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    have : a - (x : W) = -c := by rw [← h]; abel
    simpa [this] using hc
  choose τ hτ using hex
  have keyA : ∀ t u : ↥As, (Submodule.Quotient.mk t : ↥As ⧸ B.comap As.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ C := by
    intro t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    exact hB _ (t - u).2
  have keyD : ∀ t u : ↥D, (Submodule.Quotient.mk t : ↥D ⧸ C.comap D.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ C := by
    intro t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    rfl
  let φ : (↥D ⧸ C.comap D.subtype) → (↥As ⧸ B.comap As.subtype) := fun z => Submodule.Quotient.mk (τ (r z))
  have hφ : ∀ z, (s (φ z) : W) - r z ∈ C := by
    intro z
    have h1 : (s (φ z) : W) - τ (r z) ∈ C := (keyA _ _).1 (hs' _)
    have := C.add_mem h1 (hτ (r z))
    simpa using this
  have hinj : Function.Injective φ := by
    intro z w h
    rw [← hr' z, ← hr' w, keyD]
    have h1 := hφ z
    have h2 := hφ w
    rw [h] at h1
    have := C.sub_mem h2 h1
    simpa using this
  have e1 : ∑ᶠ z, f (r z : W) = ∑ᶠ z, (fun y => g (s y : W)) (φ z) :=
    finsum_congr fun z => hfg _ (r z).2 _ (s (φ z)).2 (hφ z)
  rw [e1, ← finsum_mem_range (f := fun y => g (s y : W)) hinj, ← finsum_mem_univ (fun y => g (s y : W))]
  apply finsum_mem_inter_support_eq'
  intro y hy
  simp only [Set.mem_univ, iff_true]
  have hyD : (s y : W) ∈ D := by
    by_contra h
    exact hy (hg _ (s y).2 h)
  refine ⟨Submodule.Quotient.mk ⟨_, hyD⟩, ?_⟩
  have h1 := hφ (Submodule.Quotient.mk ⟨_, hyD⟩)
  have h2 : (r (Submodule.Quotient.mk ⟨_, hyD⟩) : W) - s y ∈ C := (keyD _ ⟨_, hyD⟩).1 (hr' _)
  have h3 := C.add_mem h1 h2
  have h4 := (keyA (s (φ (Submodule.Quotient.mk ⟨_, hyD⟩))) (s y)).2 (by simpa using h3)
  rwa [hs', hs'] at h4

end GlobalTheory
end

