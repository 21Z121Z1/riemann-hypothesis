import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0613
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0615
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPAdicArcBase
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.ArcBaseFactor

theorem exists_extend {S K O' : Type} [CommRing S] [IsDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    [CommRing O'] [Nontrivial O'] (b : S →+* O') (V : ValuationSubring K) (hS : ∀ x : S, algebraMap S K x ∈ V)
    (h : ∀ v ∈ V, ∃ a s : S, IsUnit (b s) ∧ v * algebraMap S K s = algebraMap S K a) :
    ∃ b' : V →+* O', ∀ x : S, b' ⟨algebraMap S K x, hS x⟩ = b x := by
  let M : Submonoid S := (IsUnit.submonoid O').comap b
  have hM : M ≤ nonZeroDivisors S := by
    intro s hs
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rintro rfl
    have : IsUnit (b 0) := hs
    simp at this
  have hK : ∀ s : M, IsUnit (algebraMap S K s) := fun s =>
    IsUnit.mk0 _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hM s.2))
  let g : Localization M →+* O' := IsLocalization.lift (M := M) (g := b) (fun s => s.2)
  let φ : Localization M →+* K := IsLocalization.lift (M := M) (g := algebraMap S K) hK
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun z hz => ?_
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M z
    have h1 : algebraMap S K a = 0 := by
      have := IsLocalization.lift_mk'_spec (S := Localization M) (M := M) (g := algebraMap S K) (hg := hK) a (0 : K) s
      have h2 : φ (IsLocalization.mk' (Localization M) a s) = 0 := hz
      exact (this.1 h2).trans (by simp)
    have h3 : a = 0 := (IsFractionRing.injective S K) (by simpa using h1)
    simp [h3]
  let e : Localization M ≃+* φ.range := RingEquiv.ofBijective φ.rangeRestrict
    ⟨fun x y hxy => hφ (congrArg Subtype.val hxy), φ.rangeRestrict_surjective⟩
  have hV : ∀ v : V, (v : K) ∈ φ.range := by
    intro v
    obtain ⟨a, s, hs, hv⟩ := h v v.2
    have hs' : s ∈ M := hs
    refine ⟨IsLocalization.mk' (Localization M) a (⟨s, hs'⟩ : M), ?_⟩
    have := IsLocalization.lift_mk'_spec (S := Localization M) (M := M) (g := algebraMap S K) (hg := hK) a (v : K) ⟨s, hs'⟩
    exact this.2 (by simpa [mul_comm] using hv.symm)
  let ι : V →+* φ.range := RingHom.codRestrict V.subtype φ.range hV
  refine ⟨g.comp (e.symm.toRingHom.comp ι), fun x => ?_⟩
  have h5 : e.symm (ι ⟨algebraMap S K x, hS x⟩) = algebraMap S (Localization M) x := by
    rw [RingEquiv.symm_apply_eq]
    apply Subtype.ext
    change algebraMap S K x = φ (algebraMap S (Localization M) x)
    simp [φ, IsLocalization.lift_eq]
  change g (e.symm (ι ⟨algebraMap S K x, hS x⟩)) = b x
  rw [h5]
  exact IsLocalization.lift_eq _ _

theorem exists_fraction {S K : Type} [CommRing S] [IsDedekindDomain S] [Field K] [Algebra S K] [IsFractionRing S K]
    (V : ValuationSubring K) (hS : ∀ x : S, algebraMap S K x ∈ V) (P : Ideal S) [hp : P.IsPrime] (hP : P ≠ ⊥)
    (hV : ∀ x ∈ P, V.valuation (algebraMap S K x) < 1) (v : K) (hv : v ∈ V) :
    ∃ a s : S, s ∉ P ∧ v * algebraMap S K s = algebraMap S K a := by
  have hmax : P.IsMaximal := hp.isMaximal hP
  have hle : ∀ x : S, V.valuation (algebraMap S K x) ≤ 1 := fun x => (V.valuation_le_one_iff _).2 (hS x)
  have hunit : ∀ s, s ∉ P → V.valuation (algebraMap S K s) = 1 := by
    intro s hs
    obtain ⟨t, r, hr, htr⟩ := hmax.exists_inv hs
    have h1 : V.valuation (algebraMap S K (t * s)) = 1 := by
      have h2 : t * s = 1 - r := by rw [← htr]; ring
      rw [h2, map_sub, map_one]
      exact Valuation.map_one_sub_of_lt _ (hV r hr)
    rw [map_mul, map_mul] at h1
    refine le_antisymm (hle s) ?_
    calc (1 : _) = V.valuation (algebraMap S K t) * V.valuation (algebraMap S K s) := h1.symm
      _ ≤ 1 * V.valuation (algebraMap S K s) := by gcongr; exact hle t
      _ = _ := one_mul _
  let A := Localization.AtPrime P
  haveI : IsDiscreteValuationRing A := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP A
  have hinj : Function.Injective (algebraMap S A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) v
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyK : algebraMap S K y ≠ 0 := by
    simpa using (IsFractionRing.injective S K).ne hy0
  obtain ⟨c, hc⟩ := PreValuationRing.cond (algebraMap S A x) (algebraMap S A y)
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl c
  have hsK : algebraMap S K s ≠ 0 := by
    have : (s : S) ≠ 0 := fun h0 => s.2 (h0 ▸ P.zero_mem)
    simpa using (IsFractionRing.injective S K).ne this
  have hK1 : ∀ {a s : S}, x * a = y * s → algebraMap S K x / algebraMap S K y * algebraMap S K a = algebraMap S K s := by
    intro a s h
    have h' : algebraMap S K x * algebraMap S K a = algebraMap S K y * algebraMap S K s := by
      rw [← map_mul, ← map_mul, h]
    field_simp
    exact h'
  have hK2 : ∀ {a s : S}, y * a = x * s → algebraMap S K x / algebraMap S K y * algebraMap S K s = algebraMap S K a := by
    intro a s h
    have h' : algebraMap S K y * algebraMap S K a = algebraMap S K x * algebraMap S K s := by
      rw [← map_mul, ← map_mul, h]
    field_simp
    exact h'.symm
  rcases hc with hc | hc
  · have h1 : x * a = y * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    by_cases ha : a ∈ P
    · exfalso
      have h2 : algebraMap S K x / algebraMap S K y * algebraMap S K a = algebraMap S K s := hK1 h1
      have h3 := congrArg V.valuation h2
      rw [map_mul, hunit _ s.2] at h3
      have h4 : V.valuation (algebraMap S K x / algebraMap S K y) ≤ 1 := (V.valuation_le_one_iff _).2 hv
      have h5 := hV a ha
      have h6 : V.valuation (algebraMap S K x / algebraMap S K y) * V.valuation (algebraMap S K a) <
          1 := lt_of_le_of_lt (mul_le_of_le_one_left' h4) h5
      exact h6.ne h3
    · exact ⟨s, a, ha, hK1 h1⟩
  · have h1 : y * a = x * s := by
      apply hinj
      rw [map_mul, map_mul, ← hc, mul_assoc, IsLocalization.mk'_spec]
    exact ⟨a, s, s.2, hK2 h1⟩

theorem exists_place (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by
  have hne : (Ideal.span {(p : (⊥ : Subring ℂ))}) ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    obtain ⟨n, hn⟩ := Subring.mem_bot.1 v.2
    have h1 : ((p : ℤ) * n : ℤ) = 1 := by
      have := congrArg Subtype.val hv
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [← hn] at this
      exact_mod_cast this
    have := Int.isUnit_iff_natAbs_eq.1 (IsUnit.of_mul_eq_one _ h1)
    simp at this
    exact hp.one_lt.ne' this
  obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  exact ⟨W, hW ⟨p, Ideal.mem_span_singleton_self _, by simp⟩⟩

theorem valuation_comap_lt_one {K : Type} [Field K] (i : K →+* ℂ) (W : ValuationSubring ℂ) (z : K)
    (hz : i z ∈ W.nonunits) : (W.comap i).valuation z < 1 := by
  by_cases h0 : z = 0
  · simp [h0]
  by_contra hn
  have hn' := not_lt.1 hn
  have h1 : (W.comap i).valuation z⁻¹ ≤ 1 := by
    rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn'
  have h2 : z⁻¹ ∈ W.comap i := ((W.comap i).valuation_le_one_iff _).1 h1
  have h3 : (i z)⁻¹ ∈ W := by simpa using h2
  have h4 : W.valuation (i z)⁻¹ ≤ 1 := (W.valuation_le_one_iff _).2 h3
  have h5 : W.valuation (i z) < 1 := W.mem_nonunits_iff.1 hz
  rw [map_inv₀] at h4
  have h6 : W.valuation (i z) ≠ 0 := by simpa using h0
  exact absurd h5 (not_lt.2 ((inv_le_one₀ (zero_lt_iff.2 h6)).1 h4))

theorem ringOfIntegers_mem {K : Type} [Field K] (i : K →+* ℂ) (W : ValuationSubring ℂ) (x : 𝓞 K) :
    algebraMap (𝓞 K) K x ∈ W.comap i := by
  have h : IsIntegral ℤ (i (x : K)) := (RingOfIntegers.isIntegral_coe x).map i.toIntAlgHom
  have h' : IsIntegral W (i (x : K)) := h.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h'
  change i (x : K) ∈ W
  have hy' : (y : ℂ) = i (x : K) := hy
  rw [← hy']; exact y.2

theorem exists_prime_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] (n : ℕ) (hn : n ≠ 0)
    (h : (n : R) ∈ P) : ∃ q : ℕ, q.Prime ∧ (q : R) ∈ P := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h))
    obtain ⟨q, hq, m, rfl⟩ := Nat.exists_prime_and_dvd h1
    rw [Nat.cast_mul] at h
    rcases hP.mem_or_mem h with h | h
    · exact ⟨q, hq, h⟩
    · have hm : m ≠ 0 := right_ne_zero_of_mul hn
      exact ih m (lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm) hq.one_lt) hm h

theorem exists_factor (K : Type) [Field K] [NumberField K] (i : K →+* ℂ) {O' : Type} [CommRing O'] [IsDomain O']
    [CharZero O'] (b : 𝓞 K →+* O') (ϖ : O') (hO : IsArcBase O' ϖ) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (bV : 𝓞 K →+* W.comap i)
      (b' : W.comap i →+* O'), (∀ x, ((bV x : W.comap i) : K) = (x : K)) ∧ b'.comp bV = b := by
  suffices H : ∃ (p : ℕ) (W : ValuationSubring ℂ), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      ∀ hS : (∀ x : 𝓞 K, algebraMap (𝓞 K) K x ∈ W.comap i),
        ∃ b' : W.comap i →+* O', ∀ x, b' ⟨algebraMap (𝓞 K) K x, hS x⟩ = b x by
    obtain ⟨p, W, hp, hW, h⟩ := H
    have hS : ∀ x : 𝓞 K, algebraMap (𝓞 K) K x ∈ W.comap i := fun x => ringOfIntegers_mem i W x
    obtain ⟨b', hb'⟩ := h hS
    exact ⟨p, W, hp, hW, RingHom.codRestrict (algebraMap (𝓞 K) K) (W.comap i) hS, b', fun x => rfl, RingHom.ext hb'⟩
  by_cases hU : ∀ n : ℕ, n ≠ 0 → IsUnit (n : O')
  · obtain ⟨W, hW⟩ := exists_place 2 Nat.prime_two
    refine ⟨2, W, Nat.prime_two, hW, fun hS => exists_extend b (W.comap i) hS fun v _ => ?_⟩
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) v
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hyK : algebraMap (𝓞 K) K y ≠ 0 := by
      simpa using (IsFractionRing.injective (𝓞 K) K).ne hy0
    refine ⟨x, y, ?_, by field_simp⟩
    have hN : ((Ideal.absNorm (Ideal.span {y}) : ℕ) : 𝓞 K) ∈ Ideal.span {y} := Ideal.absNorm_mem _
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hN
    have hN0 : Ideal.absNorm (Ideal.span {y}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hy0
    have h1 := hU _ hN0
    rw [← map_natCast b, ← hz, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  · push_neg at hU
    obtain ⟨n, hn, hnu⟩ := hU
    rcases hO with ⟨hf, -⟩ | ⟨hd, -, -⟩
    · exfalso
      obtain ⟨c, hc⟩ := hf.mul_inv_cancel (Nat.cast_ne_zero.2 hn : (n : O') ≠ 0)
      exact hnu (IsUnit.of_mul_eq_one _ hc)
    haveI := hd
    have hnm : (n : O') ∈ maximalIdeal O' := (mem_maximalIdeal _).2 hnu
    obtain ⟨q, hq, hqm⟩ := exists_prime_mem (maximalIdeal O') n hn hnm
    let P : Ideal (𝓞 K) := (maximalIdeal O').comap b
    haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
    have hqP : (q : 𝓞 K) ∈ P := by
      change b (q : 𝓞 K) ∈ maximalIdeal O'
      simpa using hqm
    have hP : P ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.mem_bot] at hqP
      exact hq.ne_zero (by exact_mod_cast hqP)
    let f : 𝓞 K →+* ℂ := i.comp (algebraMap (𝓞 K) K)
    have hfi : Function.Injective f := i.injective.comp (IsFractionRing.injective (𝓞 K) K)
    have hne : P.map f.rangeRestrict ≠ ⊤ := by
      intro ht
      have h1 : (1 : f.range) ∈ P.map f.rangeRestrict := ht ▸ Submodule.mem_top
      obtain ⟨x, hx, hx1⟩ := (Ideal.mem_map_iff_of_surjective _ f.rangeRestrict_surjective).1 h1
      have hx2 : x = 1 := hfi (by simpa using congrArg Subtype.val hx1)
      exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 (hx2 ▸ hx))
    obtain ⟨W, -, hW⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
    have hPW : ∀ x ∈ P, f x ∈ W.nonunits := fun x hx =>
      hW ⟨f.rangeRestrict x, Ideal.mem_map_of_mem _ hx, rfl⟩
    refine ⟨q, W, hq, by simpa [f] using hPW _ hqP, fun hS => exists_extend b (W.comap i) hS fun v hv => ?_⟩
    obtain ⟨a, s, hs, hvs⟩ := exists_fraction (W.comap i) hS P hP
      (fun x hx => valuation_comap_lt_one i W _ (hPW x hx)) v hv
    refine ⟨a, s, ?_, hvs⟩
    by_contra hn'
    exact hs ((mem_maximalIdeal _).2 hn')

theorem factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O' : Type)
    [CommRing O'] [IsDomain O'] [CharZero O'] (b : 𝓞 c.F →+* O') (ϖ : O'), IsArcBase O' ϖ →
    ∃ (p : ℕ) (W : ValuationSubring ℂ) (_ : p.Prime) (_ : (p : ℂ) ∈ W.nonunits) (bV : 𝓞 c.F →+* c.V W)
      (b' : c.V W →+* O'), (∀ x, ((bV x : c.V W) : c.F) = (x : c.F)) ∧ b'.comp bV = b := by
  intro E _ _ _ H l c O' _ _ _ b ϖ hO
  haveI := c.fin
  haveI : NumberField c.F := ⟨⟩
  exact exists_factor c.F c.F.val.toRingHom b ϖ hO

end GlobalTheory.ArcBaseFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealBilinFormEqSumAdditiveImageIntForms
section
open GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem exists_toReal_span_fintype {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ) : ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (Q : κ → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  let H := Module.Free.chooseBasis ℚ ℝ
  let S : Finset (Module.Free.ChooseBasisIndex ℚ ℝ) :=
    Finset.univ.biUnion fun p : Module.Free.ChooseBasisIndex ℤ L × Module.Free.ChooseBasisIndex ℤ L =>
      (H.repr (B (b p.1) (b p.2))).support
  let f : S × Module.Free.ChooseBasisIndex ℤ L × Module.Free.ChooseBasisIndex ℤ L → ℚ :=
    fun t => H.repr (B (b t.2.1) (b t.2.2)) t.1
  obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose m hm using hn
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
  have hm' : ∀ t, (m t : ℚ) = D * f t := fun t => by simpa [Submonoid.smul_def] using hm t
  let Q : S → LinearMap.BilinForm ℤ L := fun s => Matrix.toLinearMap₂ b b (fun i k => m (s, i, k))
  let g : S → ℝ →+ ℝ := fun s => (D : ℝ) • ((Rat.castHom ℝ).toAddMonoidHom.comp (H.coord s).toAddMonoidHom)
  have hQb : ∀ s i k, (Q s (b i) (b k) : ℝ) = D * (H.repr (B (b i) (b k)) s : ℝ) := fun s i k => by
    have h1 : Q s (b i) (b k) = m (s, i, k) := Matrix.toLinearMap₂_apply_basis _ _ _ _ _
    rw [h1]
    have := hm' (s, i, k)
    simp only [f] at this
    exact_mod_cast this
  have hQ : ∀ s y z, (Q s y z : ℝ) = g s (B y z) := by
    intro s
    have : toReal (Q s) = B.compr₂ (g s).toIntLinearMap := by
      refine LinearMap.ext_basis b b fun i k => ?_
      rw [toReal_apply, hQb]
      simp [g, H]
    intro y z
    simpa using LinearMap.congr_fun₂ this y z
  refine ⟨S, inferInstance, fun s => H s / D, Q, ?_, fun s => ⟨g s, hQ s⟩⟩
  refine LinearMap.ext_basis b b fun i k => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, hQb, smul_eq_mul]
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD'
  have key : ∀ h r : ℝ, h / D * (D * r) = r * h := fun h r => by field_simp
  have e1 : ∀ x : S, H x / D * (D * (H.repr (B (b i) (b k)) x : ℝ)) = H.repr (B (b i) (b k)) x • H x := fun x => by
    rw [Rat.smul_def]; exact key _ _
  rw [Finset.sum_congr rfl fun x _ => e1 x]
  rw [Finset.sum_coe_sort S (fun x => H.repr (B (b i) (b k)) x • H x)]
  conv_lhs => rw [← H.linearCombination_repr (B (b i) (b k))]
  rw [Finsupp.linearCombination_apply]
  refine Finsupp.sum_of_support_subset _ ?_ (fun (x : Module.Free.ChooseBasisIndex ℚ ℝ) (a : ℚ) => a • H x)
    fun x _ => zero_smul ℚ (H x)
  intro x hx
  exact Finset.mem_biUnion.2 ⟨(i, k), Finset.mem_univ _, hx⟩

theorem exists_sum_toReal_additive_images : ∀ {L : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (B : L →ₗ[ℤ] L →ₗ[ℤ] ℝ), ∃ (n : ℕ) (w : Fin n → ℝ) (Q : Fin n → LinearMap.BilinForm ℤ L),
      B = ∑ j, w j • toReal (Q j) ∧ ∀ j, ∃ g : ℝ →+ ℝ, ∀ y z, (Q j y z : ℝ) = g (B y z) := by
  intro L _ _ _ B
  obtain ⟨κ, _, w, Q, h1, h2⟩ := exists_toReal_span_fintype B
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun j => w (e.symm j), fun j => Q (e.symm j), ?_, fun j => h2 _⟩
  rw [h1]
  exact (e.symm.sum_comp fun s => w s • toReal (Q s)).symm

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRescaleUniformisationRigidification
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigRescale

open GlobalTheory GlobalTheory.ArchMetricCompare

theorem exists_rescale_rig : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (rig : LB.Gen (L.pull (eSec A))), L.IsLB → rig.IsGen → ∃ (u' : HolUnif A L g) (lam : ℂ), lam ≠ 0 ∧ u'.ex = u.ex ∧ u'.Λ = u.Λ ∧ u'.IsRig rig ∧ ∀ i z, u'.fr i z = lam * u.fr i z := by
  intro A _ L g u rig hL hr
  have h0 : (u.ex 0).left = eSec A := by
    rw [(u.ker 0).2 u.Λ.zero_mem, Hom.one_def]
    simp [eSec]
  obtain ⟨j₀, hj₀⟩ := exists_chart_at hL (u.ex 0).left
  have hj₀' : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U (fun _ => j₀) := by
    exact (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) (fun _ => j₀)).2 (by rw [Category.id_comp, ← h0]; exact hj₀)
  have hr₀ := valAt'_unit_ne_zero _ hj₀' (rig.s (fun _ => j₀))
  have hf₀ : u.fr j₀ 0 ≠ 0 := u.fr_ne j₀ 0 hj₀
  set r₀ := valAt' (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U (fun _ => j₀)) (rig.s (fun _ => j₀)).val with hr₀def
  let u' : HolUnif A L g :=
    { u with
      fr := fun i z => r₀ / u.fr j₀ 0 * u.fr i z
      fr_hol := fun i => (u.fr_hol i).const_mul _
      fr_ne := fun i z h => mul_ne_zero (div_ne_zero hr₀ hf₀) (u.fr_ne i z h)
      fr_compat := fun i j z h => by
        show r₀ / u.fr j₀ 0 * u.fr i z = _ * (r₀ / u.fr j₀ 0 * u.fr j z)
        rw [u.fr_compat i j z h]; ring }
  refine ⟨u', r₀ / u.fr j₀ 0, div_ne_zero hr₀ hf₀, rfl, rfl, ?_, fun _ _ => rfl⟩
  intro j hj
  have hj1 : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ (L.pull (eSec A)).U j := fun p _ => hj trivial
  have hm : ⊤ ≤ (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) ⁻¹ᵁ ((L.pull (eSec A)).U j ⊓ (L.pull (eSec A)).U (fun _ => j₀)) :=
    (top_le_preimage_inf _ _ _).2 ⟨hj1, hj₀'⟩
  have hz : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U j₀) := by
    rw [top_le_preimage_inf, h0]
    exact ⟨by simpa only [Category.id_comp] using (le_pull_iff L (eSec A) (𝟙 (Sp ℂ)) j).1 hj1, by rw [← h0]; exact hj₀⟩
  have e := congrArg (fun a => valAt' (𝟙 (Sp ℂ)) _ (Units.val a)) (hr j (fun _ => j₀))
  simp only [Units.val_mul] at e
  rw [valAt'_mul] at e
  have e1 := (valAt'_res _ inf_le_left _ hm).symm.trans (e.trans (congrArg _ (valAt'_res _ inf_le_right _ hm)))
  have hg := val_pull_g L (eSec A) (𝟙 (Sp ℂ)) j (fun _ => j₀) hm
  rw [Category.id_comp] at hg
  have hc := u.fr_compat (j PUnit.unit) j₀ 0 hz
  rw [h0] at hc
  show r₀ / u.fr j₀ 0 * u.fr (j PUnit.unit) 0 = _
  rw [e1, hg, hc, ← hr₀def]
  field_simp

end GlobalTheory.RigRescale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsScfEmbeddingDvd
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad.Pull

open Cardinal

theorem exists_scf_embedding_dvd :
    ∀ (p : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], p.Prime → (p : V) ∈ IsLocalRing.maximalIdeal V → Cardinal.mk V ≤ Cardinal.continuum → ∃ (C : SCF p) (φ : V →+* ↥(intO ↥C.S)), Function.Injective φ ∧ ∀ a b : V, ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ ≤ ‖((φ b : ↥(intO ↥C.S)) : ↥C.S)‖ → b ∣ a := by
  intro p V _ _ _ _ hp hpm hV
  let K := FractionRing V
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    GlobalTheory.exists_complete_isAlgClosed_of_isDiscreteValuationRing V K hp0 hpm
      (inv_pos.2 (zero_lt_one.trans h1)) (inv_lt_one_of_one_lt₀ h1)
  have hK : #K ≤ 𝔠 :=
    (IsLocalization.cardinalMk_le (nonZeroDivisors V)).trans hV
  have hx : 1 < ‖algebraMap K C (algebraMap V K p)⁻¹‖ := by
    rw [map_inv₀, norm_inv, hCp, inv_inv]; exact h1
  obtain ⟨L, hKL, hcl, hac, hL⟩ := GlobalTheory.SmallClosedField.exists_small_closed_subfield hK hx
  letI : NontriviallyNormedField L :=
    { (inferInstance : NormedField L) with non_trivial := ⟨⟨_, hKL _⟩, hx⟩ }
  haveI : CompleteSpace L := hcl.completeSpace_coe
  haveI : CharZero K := charZero_of_injective_ringHom (IsFractionRing.injective V K)
  let i : K →+* L := (algebraMap K C).codRestrict L hKL
  have hi : ∀ y, ‖i y‖ = ‖algebraMap K C y‖ := fun _ => rfl
  haveI : CharZero L := charZero_of_injective_ringHom i.injective
  have hLp : ‖(p : L)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast i, hi, ← map_natCast (algebraMap V K), hCp]
  obtain ⟨D, e, he⟩ := GlobalTheory.SmallClosedField.exists_scf_isometry hLp hL
  let g : V →+* D.S := (e.comp i).comp (algebraMap V K)
  have hg : ∀ a : V, ‖g a‖ = ‖algebraMap K C (algebraMap V K a)‖ := fun a => by
    simp only [g, RingHom.comp_apply, he, hi]
  have hle : ∀ a : V, g a ∈ intO D.S := fun a => by
    change ‖g a‖ ≤ 1
    rw [hg]; exact (hC _).2 ⟨a, rfl⟩
  refine ⟨D, g.codRestrict _ hle, fun a b hab => ?_, fun a b hab => ?_⟩
  · have h := congrArg Subtype.val hab
    exact IsFractionRing.injective V K (i.injective (e.injective h))
  · change ‖g a‖ ≤ ‖g b‖ at hab
    rw [hg, hg] at hab
    by_cases hb : b = 0
    · subst hb
      have : algebraMap K C (algebraMap V K a) = 0 := by
        rw [map_zero, map_zero, norm_zero] at hab
        exact norm_le_zero_iff.1 hab
      rw [(map_eq_zero_iff _ (algebraMap K C).injective).1 this |>
        (map_eq_zero_iff _ (IsFractionRing.injective V K)).1]
    · have hb' : algebraMap V K b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hb
      have hbC : 0 < ‖algebraMap K C (algebraMap V K b)‖ :=
        norm_pos_iff.2 ((map_ne_zero_iff _ (algebraMap K C).injective).2 hb')
      obtain ⟨c, hc⟩ := (hC (algebraMap V K a / algebraMap V K b)).1 (by
        rw [map_div₀, norm_div]; exact div_le_one_of_le₀ hab hbC.le)
      refine ⟨c, IsFractionRing.injective V K ?_⟩
      rw [map_mul, hc, mul_div_cancel₀ _ hb']

end GlobalTheory.ShFam.Pad.Pull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelZeroLogConstantStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromModel_zero_log_constant : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (a : F) (n : ℕ), a ≠ 0 → n ≠ 0 → FromModel Y 0 (fun _ => 1) (fun _ e _ => Real.log (e.w (algebraMap F (AlgebraicClosure F) a)) / n) := by
  first | exact @GlobalTheory.LineNorm.fromModel_const | exact GlobalTheory.LineNorm.fromModel_const | (intros; apply GlobalTheory.LineNorm.fromModel_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesian
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenericFibrePoint

theorem fibre_map_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y yF x φ hgp hL
  have hsq : φ ≫ Y.t.G.hom = (x.P.A.hom ≫ yF) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    rw [hgp.1.w, Category.assoc]; rfl
  let φ' : x.P.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift φ (x.P.A.hom ≫ yF) hsq
  have h1 : φ' ≫ Y.m.φ = φ := Y.m.cart.1.lift_fst _ _ _
  have h2 : φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF := Y.m.cart.1.lift_snd _ _ _
  have hn : IsGrpPullback x.P.A Y.t.G (yF ≫ (Y.jQ ≫ pullback.fst _ _)) (φ' ≫ Y.m.φ) := by
    rw [h1]; exact hgp
  have hc : IsGrpPullback x.P.A Y.oF.t.G yF φ' := IsGrpPullback.cancel Y.m.cart hn h2
  refine ⟨φ', h1, h2, hc.comp Y.m0.toSABMap.cart, ?_⟩
  obtain ⟨w, hw, -⟩ := Y.m.lin
  obtain ⟨w0, hw0, -⟩ := Y.m0.toSABMap.lin
  have k : LBIso (Y.t.PP.L.pull Y.m.φ) (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) :=
    LBIso.trans (pull_isLB Y.t.PP.isLB _) Y.oF.t.PP.isLB (pull_isLB Xo.univ.t.PP.isLB _)
      (LBIso.symm ⟨w, hw⟩) ⟨w0, hw0⟩
  have k' : LBIso (Y.t.PP.L.pull φ) (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) :=
    GlobalTheory.Spread.lbIso_pull_comp φ' h1.symm rfl k
  exact LBIso.trans x.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL k'

end GlobalTheory.GenericFibrePoint
end

