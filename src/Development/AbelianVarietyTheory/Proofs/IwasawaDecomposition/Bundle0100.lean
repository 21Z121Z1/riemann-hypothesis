import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import ReciprocityTheory.Automorphisms.Bundle0001
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumFactorial
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogKer

theorem exists_sum_factorial {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (l : ℕ) (hl : 0 < l)
    (hA : IsAdicComplete (Ideal.span {(l : A)}) A) (γ : ℕ → R) :
    ∃ Y : A, ∀ r n : ℕ, l ^ r ≤ n → ∃ w : A,
      Y = f (∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : R) * γ k) + (l : A) ^ r * w := by
  obtain ⟨Y, hY⟩ := LogEx.exists_sum (l : A) (fun k => f ((-1) ^ k * ((k.factorial : ℕ) : R) * γ k))
    (fun r => l ^ r) (fun a b hab => Nat.pow_le_pow_right hl hab) (fun r k hk => by
      obtain ⟨m, hm⟩ := Nat.dvd_factorial (pow_pos hl r) hk
      refine ⟨f ((-1) ^ k * (m : R) * γ k), ?_⟩
      simp only [hm, map_mul, map_natCast, Nat.cast_mul, Nat.cast_pow, map_pow]
      ring)
  refine ⟨Y, fun r n hn => ?_⟩
  obtain ⟨w, hw⟩ := hY r n hn
  exact ⟨w, by rw [map_sum, ← hw]; ring⟩

theorem sum_eq {P : Type} [CommRing P] (u γ : ℕ → P) (x : P) (hu : ∀ k : ℕ, ((k + 1 : ℕ) : P) * u k = 1)
    (hγ : ∀ k : ℕ, (((k + 1).factorial : ℕ) : P) * γ k = x ^ (k + 1)) (n : ℕ) :
    ∑ k ∈ Finset.range n, (-1) ^ k * ((k.factorial : ℕ) : P) * γ k =
      ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hγ k, Nat.factorial_succ, Nat.cast_mul]
  linear_combination (-((-1) ^ k * ((k.factorial : ℕ) : P) * γ k)) * hu k

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris

theorem exists_log : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ z : Per.Ainf l, Per.θ l z = 0 → ∃ Y : Per.Acris l, ∀ n : ℕ, ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * Per.ev l n (j Y) = Ideal.Quotient.mk _ (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1)) := by
  intro l _ j hj z hz
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  have hγ : ∀ k : ℕ, ∃ γ : Per.Acris0 l, (((k + 1).factorial : ℕ) : Per.AinfP l) * (γ : Per.AinfP l) =
      (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := fun k => by
    obtain ⟨d, hd⟩ := (hf (k + 1)).exists_right_inv
    have h : (((k + 1).factorial : ℕ) : Per.AinfP l) *
        (d * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1)) =
        (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := by rw [← mul_assoc, hd, one_mul]
    exact ⟨⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l z (k + 1) _ hz h⟩, h⟩
  choose γ hγ using hγ
  have hmem : algebraMap (Per.Ainf l) (Per.AinfP l) z ∈ Per.kerP l :=
    GlobalTheory.RingIface.alg_mem_kerP l hz
  obtain ⟨Y, hY⟩ := exists_sum_factorial (algebraMap (Per.Acris0 l) (Per.Acris l)) l
    (Fact.out : l.Prime).pos (acris_basic l).1 γ
  refine ⟨Y, fun n => ?_⟩
  have hs : ∀ m : ℕ, ((∑ k ∈ Finset.range m, (-1) ^ k * ((k.factorial : ℕ) : Per.Acris0 l) * γ k :
      Per.Acris0 l) : Per.AinfP l) =
      ∑ k ∈ Finset.range m, (-1) ^ k * u k * (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) := by
    intro m
    rw [← sum_eq u (fun k => (γ k : Per.AinfP l)) _ hu hγ m]
    change (Per.Acris0 l).val _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_pow, map_natCast, map_neg, map_one]
    rfl
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) z) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l j hj).2.2 n Y (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨w, hw⟩ := hY r (max (l ^ r) n) (le_max_left _ _)
    refine ⟨_, w, 0, hw, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, LogFun.ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      hs, LogFun.partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (LogFun.partial_sub_mem _ u _ hmem (le_max_right _ _)))
  rw [key, LogFun.ev_alg, ← map_natCast (Ideal.Quotient.mk (Per.kerP l ^ n)), ← map_mul, hc]

end GlobalTheory.MemLoc.LogKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTameLocOfResidue
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem tame_valued_int (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) = v.valuation L (algebraMap (𝓞 L) L a) :=
  ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L a)

theorem tame_valued_lt_one_iff (a : 𝓞 L) :
    Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 ↔ a ∈ v.asIdeal := by
  rw [tame_valued_int,
    HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem tame_mk_eq {u : v.adicCompletion L} {a b : 𝓞 L}
    (ha : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1)
    (hb : Valued.v (u - algebraMap (𝓞 L) (v.adicCompletion L) b) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  rw [Ideal.Quotient.eq, ← tame_valued_lt_one_iff, map_sub]
  have e : algebraMap (𝓞 L) (v.adicCompletion L) a - algebraMap (𝓞 L) (v.adicCompletion L) b =
      (u - algebraMap (𝓞 L) (v.adicCompletion L) b) - (u - algebraMap (𝓞 L) (v.adicCompletion L) a) := by
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hb ha)

def unitPart : (v.adicCompletion L)ˣ →* (v.adicCompletion L)ˣ where
  toFun x := x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp), zpow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem isUnitAt_unitPart (x : (v.adicCompletion L)ˣ) : IsUnitAt v (unitPart v x) := by
  have h : Valued.v ((atFin v (unif v) : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
      WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  show Valued.v ((x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) :
    (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, h, ← WithZero.exp_zsmul]
  nth_rewrite 1 [← WithZero.exp_log hx]
  rw [← WithZero.exp_add]
  simp

theorem unitPart_of_isUnitAt {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) : unitPart v x = x := by
  have h : Valued.v (x : v.adicCompletion L) = 1 := hx
  show x * atFin v (unif v) ^ WithZero.log (Valued.v (x : v.adicCompletion L)) = x
  rw [h]
  simp

theorem exists_unitPart_approx (x : (v.adicCompletion L)ˣ) : ∃ a : 𝓞 L,
    Valued.v ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1 :=
  ReciprocityTheory.Aut.adic_exists_approx v _ (le_of_eq (isUnitAt_unitPart v x))

def resPart : (v.adicCompletion L)ˣ →* 𝓞 L ⧸ v.asIdeal where
  toFun x := Ideal.Quotient.mk v.asIdeal (exists_unitPart_approx v x).choose
  map_one' := by
    refine tame_mk_eq v (b := 1) (exists_unitPart_approx v 1).choose_spec ?_
    simp
  map_mul' x y := by
    rw [← map_mul]
    refine tame_mk_eq v (exists_unitPart_approx v (x * y)).choose_spec ?_
    have hx := (exists_unitPart_approx v x).choose_spec
    have hy := (exists_unitPart_approx v y).choose_spec
    set a := (exists_unitPart_approx v x).choose
    set b := (exists_unitPart_approx v y).choose
    have hu : Valued.v (unitPart v x : v.adicCompletion L) = 1 := isUnitAt_unitPart v x
    have hb : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) b) ≤ 1 := by
      rw [tame_valued_int]
      exact v.valuation_le_one b
    have e : (unitPart v (x * y) : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a * b) =
        (unitPart v x : v.adicCompletion L) *
          ((unitPart v y : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) b) +
        ((unitPart v x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) *
          algebraMap (𝓞 L) (v.adicCompletion L) b := by
      rw [map_mul, map_mul, Units.val_mul]
      ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rwa [map_mul, hu, one_mul]
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hb) hx

theorem resPart_eq {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) {a : 𝓞 L}
    (ha : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) a) < 1) :
    resPart v x = Ideal.Quotient.mk v.asIdeal a := by
  refine tame_mk_eq v (exists_unitPart_approx v x).choose_spec ?_
  rwa [unitPart_of_isUnitAt v hx]

open Classical in

theorem exists_tameLoc_of_residue : ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (θ0 : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ), ∃ θ : (v.adicCompletion L)ˣ →* ℂˣ, TameLoc v θ ∧ (∀ (k : Lˣ) (y : 𝓞 L) (b : (𝓞 L ⧸ v.asIdeal)ˣ), (k : L) = (y : L) → (b : 𝓞 L ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal y → θ (atFin v k) = θ0 b) ∧ ∀ x, IsUnitAt v x → ∃ b, θ x = θ0 b := by
  intro L _ _ v θ0
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  refine ⟨θ0.comp (resPart v).toHomUnits, ⟨fun x => ?_, fun x hx h1 => ?_⟩, fun k y b hk hb => ?_,
    fun x _ => ⟨_, rfl⟩⟩
  · have hf : IsOfFinOrder ((θ0 ((resPart v).toHomUnits x) : ℂˣ) : ℂ) :=
      ((Units.coeHom ℂ).comp θ0).isOfFinOrder (isOfFinOrder_of_finite _)
    exact hf.norm_eq_one
  · have e : (resPart v).toHomUnits x = 1 := by
      apply Units.ext
      show resPart v x = Ideal.Quotient.mk v.asIdeal 1
      refine resPart_eq v hx ?_
      rw [map_one]
      refine lt_of_le_of_lt h1 ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    rw [MonoidHom.comp_apply, e, map_one]
  · have ek : ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) =
        algebraMap (𝓞 L) (v.adicCompletion L) y := by
      show algebraMap L (v.adicCompletion L) (k : L) = _
      rw [hk]
      rfl
    have hy : y ∉ v.asIdeal := by
      intro hy
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hy] at hb
      haveI := v.isPrime
      exact b.ne_zero hb
    have hu : IsUnitAt v (atFin v k) := by
      show Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1
      rw [ek]
      refine le_antisymm ?_ (not_lt.1 fun h => hy ((tame_valued_lt_one_iff v y).1 h))
      rw [tame_valued_int]
      exact v.valuation_le_one y
    have e : (resPart v).toHomUnits (atFin v k) = b := by
      apply Units.ext
      show resPart v (atFin v k) = _
      rw [hb]
      refine resPart_eq v hu ?_
      rw [ek, sub_self, map_zero]
      exact zero_lt_one
    rw [MonoidHom.comp_apply, e]

end GlobalTheory.Mem.Chr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Filter Topology

namespace GlobalTheory.HalfIntChars

theorem emb_mul_indep {L I : Type} [Field L] [CharZero L] [Fintype I] (σ : I → L →+* ℂ) (hσ : Function.Injective σ)
    (m : I → ℤ) (h : ∀ k : L, k ≠ 0 → ∏ i, σ i k ^ m i = 1) : m = 0 := by
  classical
  have key : ∀ x : L, ∑ i, (m i : ℂ) * σ i x = 0 := by
    intro x
    let f : ℂ → ℂ := fun t => ∏ i, (1 + t * σ i x) ^ m i
    have hd : ∀ i ∈ (Finset.univ : Finset I),
        HasDerivAt (fun t : ℂ => (1 + t * σ i x) ^ m i) ((m i : ℂ) * σ i x) 0 := by
      intro i _
      have h1 : HasDerivAt (fun t : ℂ => 1 + t * σ i x) (σ i x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ i x)).const_add 1
      have h2 := (hasDerivAt_zpow (m i) ((fun t : ℂ => 1 + t * σ i x) 0) (Or.inl (by simp))).comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hf : HasDerivAt f (∑ i, (m i : ℂ) * σ i x) 0 := by
      have := HasDerivAt.fun_finset_prod hd
      simpa [f] using this
    have hs := hasDerivAt_iff_tendsto_slope.1 hf
    have hu : Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ), Eventually.of_forall fun n => ?_⟩
      exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
    have hfin : ∀ᶠ n : ℕ in atTop, (1 + (1 / ((n : L) + 1)) * x) ≠ 0 := by
      rw [← Nat.cofinite_eq_atTop]
      refine Set.Subsingleton.finite ?_
      intro a ha b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb
      have ha1 : ((a : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero a
      have hb1 : ((b : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero b
      field_simp at ha hb
      have : (a : L) = b := by linear_combination ha - hb
      exact_mod_cast this
    have h0 : Tendsto (fun n : ℕ => slope f 0 ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hfin.mono fun n hn => ?_)
      have h1 := h _ hn
      have h2 : f ((1 : ℂ) / ((n : ℂ) + 1)) = 1 := by
        refine Eq.trans ?_ h1; simp [f]
      have h3 : f 0 = 1 := by simp [f]
      simp only [slope, h2, h3, vsub_self, smul_zero]
    exact tendsto_nhds_unique (hs.comp hu) h0
  have li := (linearIndependent_monoidHom L ℂ).comp (fun i => (σ i : L →* ℂ))
    (fun i j hij => hσ (RingHom.coe_monoidHom_injective hij))
  have := Fintype.linearIndependent_iff.1 li (fun i => (m i : ℂ)) (by
    funext x
    simpa [Finset.sum_apply] using key x)
  funext i
  exact_mod_cast this i

theorem unit_sq (z : ℂ) (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h3 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  field_simp
  rw [← h3]

theorem hasInf_unique {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ) (h1 : Function.Injective φ)
    (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) {χ : HChar L} {n n' : I → ℤ} (h : χ.HasInf φ n) (h' : χ.HasInf φ n') :
    n = n' := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := emb_mul_indep σ hσ (Sum.elim (n - n') (n' - n)) (fun k hk => by
    have e := (h (Units.mk0 k hk)).symm.trans (h' (Units.mk0 k hk))
    simp only [Units.val_mk0] at e
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have hu : ∀ i, φ i k / ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := fun i =>
      div_ne_zero (hne i) (by exact_mod_cast norm_ne_zero_iff.2 (hne i))
    have e2 : ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ (n i - n' i) = 1 := by
      simp_rw [zpow_sub₀ (hu _)]
      rw [Finset.prod_div_distrib, e, div_self]
      exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hu i)
    have e3 := congrArg (· ^ 2) e2
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (n i - n' i), zpow_mul, zpow_natCast, unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg, neg_sub])
  funext i
  have := congrFun this (Sum.inl i)
  simpa [sub_eq_zero] using this

theorem hasInfQ_mul {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ χ' : HChar L} {a a' : I → ℚ}
    (h : χ.HasInfQ φ a) (h' : χ'.HasInfQ φ a') : (χ * χ').HasInfQ φ (a + a') := by
  obtain ⟨n, hn, h⟩ := h
  obtain ⟨n', hn', h'⟩ := h'
  refine ⟨n + n', fun i => by simp [hn, hn', mul_add], fun k => ?_⟩
  rw [HChar.inf_mul, Units.val_mul, h k, h' k, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hne : φ i k ≠ 0 := by simp
  rw [Pi.add_apply, zpow_add₀ (div_ne_zero hne (by exact_mod_cast norm_ne_zero_iff.2 hne))]

theorem hasInfQ_inv {L I : Type} [Field L] [NumberField L] [Fintype I] {φ : I → L →+* ℂ} {χ : HChar L} {a : I → ℚ}
    (h : χ.HasInfQ φ a) : (χ⁻¹).HasInfQ φ (-a) := by
  obtain ⟨n, hn, h⟩ := h
  refine ⟨-n, fun i => by simp [hn], fun k => ?_⟩
  rw [HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp

theorem embPsi_inj {R : Ranks} (H : Formalism.BasicNotions.Host R) : Function.Injective (embPsi H) := fun _ _ h =>
  Subtype.ext ((factEmb R H).1.1 h)

theorem embPsi_ne_conj {R : Ranks} (H : Formalism.BasicNotions.Host R) (i j : R.Psi) :
    embPsi H i ≠ (starRingEnd ℂ).comp (embPsi H j) := by
  intro h
  have hi : embPsi H i (H.sqd) = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) :=
    ((factEmb R H).2 _).2 i.2
  have hj : embPsi H j (H.sqd) = Complex.I * ((Real.sqrt H.d : ℝ) : ℂ) :=
    ((factEmb R H).2 _).2 j.2
  rw [h, RingHom.comp_apply, hj, map_mul, Complex.conj_I, Complex.conj_ofReal] at hi
  have h0 : ((Real.sqrt H.d : ℝ) : ℂ) = 0 := by
    have : (2 * Complex.I) * ((Real.sqrt H.d : ℝ) : ℂ) = 0 := by linear_combination -hi
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hd : 0 < H.d := H.hyp.2.1.pos
  have : (0 : ℝ) < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact this.ne' (by exact_mod_cast h0)

def halfInt {R : Ranks} (H : Formalism.BasicNotions.Host R) : Subgroup (HChar H.E) where
  carrier := {χ | χ.IsUnitary ∧ ∃ a : R.Psi → ℚ, χ.HasInfQ (embPsi H) a}
  one_mem' := ⟨isClsF_one.unitary, 0, 0, fun _ => by simp, fun k => by
    show ((1 : ℂˣ) : ℂ) = _
    simp⟩
  mul_mem' := fun ⟨h, a, ha⟩ ⟨h', a', ha'⟩ => ⟨h.mul h', a + a', hasInfQ_mul ha ha'⟩
  inv_mem' := fun ⟨h, a, ha⟩ => ⟨h.inv, -a, hasInfQ_inv ha⟩

open Classical in

theorem exists_unitary_rational_infType_subgroup_and_infType_unique : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), (∃ G : Subgroup (HChar H.E), ∀ χ, χ ∈ G ↔ χ.IsUnitary ∧ ∃ a : R.Psi → ℚ, χ.HasInfQ (embPsi H) a) ∧ ∀ (χ : HChar H.E) (a b : R.Psi → ℚ), χ.HasInfQ (embPsi H) a → χ.HasInfQ (embPsi H) b → a = b := by
  intro R H
  refine ⟨⟨halfInt H, fun _ => Iff.rfl⟩, ?_⟩
  rintro χ a b ⟨n, hn, h⟩ ⟨n', hn', h'⟩
  obtain rfl := hasInf_unique _ (embPsi_inj H) (embPsi_ne_conj H) h h'
  funext i
  have := (hn i).symm.trans (hn' i)
  linarith

end GlobalTheory.HalfIntChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FgSpanTopOfLatticeCompatibleSemilinear
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem oLatTie_fg_span_top : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (σ : K →+* ℂ) {O : Type} [CommRing O] {φO : O →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] (M : Formalism.BasicNotions.Rows.OLat O φO W) (j : (Fin n → K) →ₛₗ[σ] W) (N : Submodule (𝓞 K) (Fin n → K)), (LinearIndependent ℂ fun i => j (Pi.single i 1)) → Formalism.L2.DIV.OLatTie σ M j N → N.FG ∧ Submodule.span K (N : Set (Fin n → K)) = ⊤ := by
  intro K _ _ _ n σ O _ φO W _ _ M j N hli hT
  classical
  obtain ⟨hgen, hmem⟩ := hT
  have hj : ∀ x, j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
    intro x
    conv_lhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ]
    simp
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [hj] at hx
    have h0 := Fintype.linearIndependent_iff.1 hli _ hx
    funext i
    exact σ.injective (by simpa using h0 i)
  have hgen' : ∀ v, ∃ x, v ∈ M.gen → j x = v := by
    intro v
    by_cases hv : v ∈ M.gen
    · obtain ⟨x, hx⟩ := hgen v hv
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose pre hpre using hgen'
  have hN : N = Submodule.span (𝓞 K) (pre '' (M.gen : Set W)) := by
    ext x
    rw [hmem, Submodule.mem_span_image_finset_iff_exists_fun']
    refine exists_congr fun a => ?_
    have : ∑ v ∈ M.gen, σ ((a v : 𝓞 K) : K) • v = j (∑ v ∈ M.gen, a v • pre v) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul K (a v) (pre v), map_smulₛₗ, hpre v hv]
    rw [this]
    exact ⟨fun h => (hinj h).symm, fun h => congrArg j h.symm⟩
  refine ⟨hN ▸ Submodule.fg_span ((M.gen.finite_toSet).image pre), ?_⟩
  rw [hN]
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  let B := Module.Basis.span hli
  let F0 := B.constr ℂ (fun i => σ (f (Pi.single i 1)))
  obtain ⟨F, hFF⟩ := LinearMap.exists_extend F0
  have hFe : ∀ i, F (j (Pi.single i 1)) = σ (f (Pi.single i 1)) := by
    intro i
    have h1 : (B i : W) = j (Pi.single i 1) := by simp [B, Module.Basis.span_apply hli i]
    rw [← h1]
    have h2 := LinearMap.congr_fun hFF (B i)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h2]
    simp [F0]
  have hF : ∀ x, F (j x) = σ (f x) := by
    intro x
    rw [hj, map_sum]
    conv_rhs => rw [← (Pi.basisFun K (Fin n)).sum_repr x]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFe]
    simp
  have hF0 : F = 0 := by
    apply LinearMap.ext_on M.span_top
    intro v hv
    rw [← hpre v hv, hF]
    have : f (pre v) ∈ (⊥ : Submodule K K) := by
      rw [← hf]
      exact Submodule.mem_map_of_mem
        (Submodule.subset_span (Submodule.subset_span ⟨v, hv, rfl⟩))
    rw [(Submodule.mem_bot K).1 this]
    simp
  apply hf0
  refine LinearMap.ext fun x => σ.injective ?_
  rw [← hF, hF0]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionFlattenStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linComb_pow_section_flatten : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))), ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  first | exact @GlobalTheory.linComb_pow_pow_sec | exact GlobalTheory.linComb_pow_pow_sec | (intros; apply GlobalTheory.linComb_pow_pow_sec <;> assumption)
end

