import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
import ReciprocityTheory.DualLattices.Bundle0008
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0005
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0007
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0005
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelRankAlgebraicBound
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspace
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwLift

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FixedByAutomorphismsMemFieldStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_by_automorphisms_mem_field : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussSumValuationTeichmuller
section
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem val_one_sub_pow_le {K : Type} [Field K] (v : Valuation K NNReal) {x : K} (hx : v x = 1)
    (i : ℕ) : v (1 - x ^ i) ≤ v (1 - x) := by
  have h : 1 - x ^ i = (1 - x) * ∑ j ∈ Finset.range i, x ^ j := (mul_neg_geom_sum x i).symm
  rw [h, map_mul]
  refine mul_le_of_le_one_right' ?_
  exact v.map_sum_le (fun j _ => by rw [map_pow, hx, one_pow])

theorem val_eq_one_of_pow_eq_one {K : Type} [Field K] (v : Valuation K NNReal) {x : K} {n : ℕ}
    (hn : n ≠ 0) (hx : x ^ n = 1) : v x = 1 := by
  have h : v x ^ n = 1 := by rw [← map_pow, hx, map_one]
  exact (pow_left_inj₀ zero_le zero_le_one hn).mp (by simpa using h)

theorem val_sub_one_pow {K : Type} [Field K] (v : Valuation K NNReal) (p : ℕ) [Fact p.Prime]
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ (p - 1) = v (p : K) := by
  have hp : p.Prime := Fact.out
  have hprod : (p : K) = ∏ μ ∈ primitiveRoots p K, (1 - μ) := by
    rw [← Polynomial.eval_one_cyclotomic_prime (R := K) (p := p),
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]
    simp
  have hval : ∀ μ ∈ primitiveRoots p K, v (1 - μ) = v (1 - ζ) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hζ.pow_eq_one
    refine le_antisymm (val_one_sub_pow_le v (val_eq_one_of_pow_eq_one v hp.ne_zero
      hζ.pow_eq_one) i) ?_
    conv_lhs => rw [← hj]
    exact val_one_sub_pow_le v (val_eq_one_of_pow_eq_one v hp.ne_zero hμ'.pow_eq_one) j
  rw [hprod, map_prod, Finset.prod_congr rfl hval, Finset.prod_const, hζ.card_primitiveRoots,
    Nat.totient_prime hp, Valuation.map_sub_swap]

theorem exists_mulShift_eq {F K : Type} [Field F] [Fintype F] [Field K] (ψ₀ ψ : AddChar F K)
    (h₀ : ψ₀ ≠ 1) : ∃ c, ψ = AddChar.mulShift ψ₀ c :=
  _root_.UpperTheory.Reformulated.B.Yde4.main ψ₀ ψ h₀

def ltOneIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) hx

theorem mem_ltOneIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (r : R) :
    r ∈ ltOneIdeal v R hv ↔ v (algebraMap R C r) < 1 := Iff.rfl

theorem ltOneIdeal_isPrime {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : (ltOneIdeal v R hv).IsPrime := by
  rw [Ideal.isPrime_iff]
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have h1 : (1 : R) ∈ ltOneIdeal v R hv := h ▸ Submodule.mem_top
    rw [mem_ltOneIdeal] at h1
    simp at h1
  · rw [mem_ltOneIdeal, map_mul, map_mul] at hab
    by_contra hcon
    push Not at hcon
    simp only [mem_ltOneIdeal, not_lt] at hcon
    have ha : v (algebraMap R C a) = 1 := le_antisymm (hv.map_le_one a) hcon.1
    have hb : v (algebraMap R C b) = 1 := le_antisymm (hv.map_le_one b) hcon.2
    simp [ha, hb] at hab

theorem gauss_value : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → Fintype.card F ≠ 2 → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → ∀ ψ : AddChar F C, ψ ≠ 1 → v (∑ a, algebraMap R C (σ⁻¹ a) * ψ a) ^ (p - 1) = v (p : C) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hcard hF σ hσ ψ hψ
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : IsDomain R := hv.hom_inj.isDomain (algebraMap R C)
  haveI hprime : (ltOneIdeal v R hv).IsPrime := ltOneIdeal_isPrime v R hv

  have hpm : (p : R) ∈ ltOneIdeal v R hv := by
    rw [mem_ltOneIdeal, map_natCast]; exact hp
  have hspan : Ideal.span {(p : R)} ≤ ltOneIdeal v R hv :=
    (Ideal.span_singleton_le_iff_mem _).mpr hpm
  let ι : F →+* R ⧸ ltOneIdeal v R hv :=
    { toFun := fun a => Ideal.Quotient.mk _ (σ a)
      map_one' := by simp
      map_mul' := fun a b => by simp
      map_zero' := by simp [MulChar.map_zero]
      map_add' := fun a b => by
        rw [← map_add, Ideal.Quotient.eq]
        have := hspan (hσ a b)
        rwa [sub_sub] at this }

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  have hvζ : v ζ = 1 := val_eq_one_of_pow_eq_one v hpp.ne_zero hζ.pow_eq_one
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hvζ.le
  have hzp : z ^ p = 1 := hv.hom_inj (by rw [map_pow, hζ.pow_eq_one, map_one])
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨y, hym, hy⟩ := ReciprocityTheory.PGsh.gaussCongruence p F R (ltOneIdeal v R hv) ι σ z hF hzp
    (fun a => rfl)

  let ψ₀ : AddChar F C := (AddChar.zmodChar p hζ.pow_eq_one).compAddMonoidHom
    (Algebra.trace (ZMod p) F).toAddMonoidHom
  have hψ₀ : ∀ a, ψ₀ a = algebraMap R C z ^ (Algebra.trace (ZMod p) F a).val := fun a => rfl
  have hψ₀1 : ψ₀ ≠ 1 := by
    haveI : Module.Finite (ZMod p) F := Module.Finite.of_finite
    obtain ⟨b, hb⟩ := Algebra.trace_surjective (ZMod p) F 1
    intro h
    have h1 : ψ₀ b = 1 := by rw [h]; simp
    rw [hψ₀] at h1
    have hb0 : (Algebra.trace (ZMod p) F b).val ≠ 0 := by
      rw [hb, Ne, ZMod.val_eq_zero]
      exact one_ne_zero
    exact hζ.pow_ne_one_of_pos_of_lt hb0 (ZMod.val_lt _) h1
  obtain ⟨c, rfl⟩ := exists_mulShift_eq ψ₀ ψ hψ₀1
  have hc : c ≠ 0 := by
    rintro rfl
    exact hψ (AddChar.mulShift_zero _)
  have hσc : σ c * σ⁻¹ c = 1 := by
    rw [MulChar.inv_apply', ← map_mul, mul_inv_cancel₀ hc, map_one]
  have hsum : ∑ a, algebraMap R C (σ⁻¹ a) * AddChar.mulShift ψ₀ c a =
      algebraMap R C (σ c) * ∑ b, algebraMap R C (σ⁻¹ b) * ψ₀ b := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft₀ c hc) _ _ (fun a => ?_)
    simp only [Equiv.mulLeft₀_apply, AddChar.mulShift_apply, map_mul, ← mul_assoc]
    rw [← map_mul, hσc, map_one, one_mul]
  have hvσ : v (algebraMap R C (σ c)) = 1 := by
    have h1 : v (algebraMap R C (σ c)) * v (algebraMap R C (σ⁻¹ c)) = 1 := by
      rw [← map_mul, ← map_mul, hσc, map_one, map_one]
    refine le_antisymm (hv.map_le_one _) ?_
    calc (1 : NNReal) = v (algebraMap R C (σ c)) * v (algebraMap R C (σ⁻¹ c)) := h1.symm
      _ ≤ v (algebraMap R C (σ c)) := mul_le_of_le_one_right' (hv.map_le_one _)
  have hG : ∑ b, algebraMap R C (σ⁻¹ b) * ψ₀ b =
      (algebraMap R C z - 1) * (algebraMap R C y - 1) := by
    have := congrArg (algebraMap R C) hy
    simp only [map_sum, map_mul, map_pow, map_sub, map_one] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => by rw [hψ₀]
  have hvy : v (algebraMap R C y - 1) = 1 := by
    have h : v (algebraMap R C y) < v (1 : C) := by
      rw [map_one]; exact hym
    rw [Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left v h, map_one]
  rw [hsum, hG, map_mul, map_mul, hvσ, hvy, one_mul, mul_one]
  exact val_sub_one_pow v p hζ

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharactersStatement
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_contains_characters : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsIntegrallyClosed R] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ χ : T →* Rˣ, (fun t => ((χ t : Rˣ) : R)) ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.char_mem_hopfOrder <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariantStatement
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_translation_invariant : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder | exact GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate.translate_mem_of_isHopfOrder <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KernelRankBoundNormValuation
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem lemF_algebra : ∀ (E : Type) [Field E] [NumberField E] (k W : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] [AddCommGroup W] [Module k W] [FiniteDimensional k W] (r : ℕ) (ρ : 𝓞 E →+* Module.End k W), (∀ a : 𝓞 E, (ρ a).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ r) → (∀ a : 𝓞 E, a ≠ 0 → Module.finrank k (LinearMap.ker (ρ a)) ≤ r * padicValNat p (Algebra.norm ℤ a).natAbs) → ∃ x : Fin r → W, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ρ (RingOfIntegers.basis E q.2) (x q.1)) = ⊤ :=
  @PositivityTheory.Xgn.kernel_rank_algebraic_bound

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBasisAdaptedToSubspaceStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_basis_adapted_to_subspace : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] (i : C.I) (n : ℕ) (b : Module.Basis (Fin n) K V) (L : AddSubgroup V) (W : Submodule K V), IsLatOf C i b L → ∃ (bW : Module.Basis (Fin (Module.finrank K W)) K W) (bQ : Module.Basis (Fin (Module.finrank K (V ⧸ W))) K (V ⧸ W)) (b' : Module.Basis (Fin (Module.finrank K W + Module.finrank K (V ⧸ W))) K V), IsLatOf C i b' L ∧ IsLatOf C i bW (L.comap W.subtype.toAddMonoidHom) ∧ IsLatOf C i bQ (L.map W.mkQ.toAddMonoidHom) ∧ (∀ j, b' (Fin.castAdd _ j) = bW j) ∧ ∀ j, W.mkQ (b' (Fin.natAdd _ j)) = bQ j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted | exact GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.LatAdapted.exists_adapted <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeKernelRankBoundNormStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_kernel_rank_bound_norm : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (a : 𝓞 E), a ≠ 0 → Module.finrank k (LinearMap.ker (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ))) ≤ Module.finrank (𝓞 E) Λ * padicValNat p (Algebra.norm ℤ a).natAbs ∧ (LinearMap.baseChange k ((LinearMap.lsmul (𝓞 E) Λ a).restrictScalars ℤ)).charpoly = ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom k)) ^ Module.finrank (𝓞 E) Λ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly | exact GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.free_extension_kernel_bound_charpoly <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem locFree_map_equiv (R : Subalgebra o Ω) {E E' : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E'] [Module Ω E'] (e : E ≃ₗ[Ω] E') {r : ℕ} {L : AddSubgroup E}
    (h : LocFree R r L) : LocFree R r (L.map e.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hst, k, f, c, hf, hc, hs, hl⟩ := h
  refine ⟨?_, k, f, c, hf, hc, hs, fun l => ?_⟩
  · rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨a • x, hst a ha x hx, by simp⟩
  · obtain ⟨b, hb, hsp, hiff⟩ := hl l
    refine ⟨fun q => e (b q), hb.map' e.toLinearMap (LinearEquiv.ker e), ?_, fun v => ?_⟩
    · have : Set.range (fun q => e (b q)) = e.toLinearMap '' Set.range b := by
        rw [← Set.range_comp]; rfl
      rw [this, ← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top]
      exact e.surjective
    · have key : ∀ n : ℕ, f l ^ n • v ∈ L.map e.toLinearMap.toAddMonoidHom ↔
          f l ^ n • e.symm v ∈ L := by
        intro n
        constructor
        · rintro ⟨x, hx, hxe⟩
          have : x = f l ^ n • e.symm v := by
            apply e.injective
            rw [map_smul, e.apply_symm_apply]
            exact hxe
          rwa [← this]
        · intro hx
          exact ⟨_, hx, by simp⟩
      simp only [key]
      rw [hiff (e.symm v)]
      constructor
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        have := congrArg e hv
        simpa [map_sum] using this
      · rintro ⟨a, ha, hv⟩
        refine ⟨a, ha, ?_⟩
        rw [hv]
        simp [map_sum]

theorem mem_stdLat (R : Subalgebra o Ω) {ι : Type} {v : ι → Ω} :
    v ∈ stdLat R ι ↔ ∀ j, v j ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem locFree_stdLat (R : Subalgebra o Ω) (m : ℕ) : LocFree R m (stdLat R (Fin m)) := by
  classical
  refine ⟨fun a ha e he => ?_, 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem,
    by simp, fun _ => ?_⟩
  · rw [mem_stdLat] at he ⊢
    intro j
    simpa using R.mul_mem ha (he j)
  · refine ⟨fun q => (Pi.basisFun Ω (Fin m)) q, (Pi.basisFun Ω (Fin m)).linearIndependent,
      (Pi.basisFun Ω (Fin m)).span_eq, fun e => ?_⟩
    have hsum : ∀ a : Fin m → Ω, (∑ q, a q • (Pi.basisFun Ω (Fin m)) q) = a := by
      intro a
      simpa using (Pi.basisFun Ω (Fin m)).sum_repr a
    constructor
    · rintro ⟨_, hn⟩
      simp only [one_pow, one_smul] at hn
      exact ⟨e, fun q => ⟨0, by simpa using (mem_stdLat R).1 hn q⟩, (hsum e).symm⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨0, ?_⟩
      rw [hsum, pow_zero, one_smul, mem_stdLat]
      intro q
      obtain ⟨n, hn⟩ := ha q
      simpa using hn

theorem locFree_divLat (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] {c : Ω}
    (hc : c ≠ 0) {r : ℕ} {L : AddSubgroup E} (h : LocFree R r L) : LocFree R r (divLat c L) := by
  have := locFree_map_equiv R (LinearEquiv.smulOfNeZero Ω E c⁻¹ (inv_ne_zero hc)) h
  convert this using 1
  ext v
  constructor
  · intro hv
    exact ⟨c • v, hv, by simp [smul_smul, hc]⟩
  · rintro ⟨x, hx, rfl⟩
    show c • (c⁻¹ • x) ∈ L
    simpa [smul_smul, hc] using hx

theorem locFree_map_mkQ_iff (R : Subalgebra o Ω) {E E₂ : Type} [AddCommGroup E] [Module Ω E]
    [AddCommGroup E₂] [Module Ω E₂] (q : E →ₗ[Ω] E₂) (hq : Function.Surjective q) {r : ℕ}
    (L : AddSubgroup E) :
    LocFree R r (L.map (LinearMap.ker q).mkQ.toAddMonoidHom) ↔ LocFree R r (L.map q.toAddMonoidHom) := by
  let e := q.quotKerEquivOfSurjective hq
  have h1 : (L.map (LinearMap.ker q).mkQ.toAddMonoidHom).map e.toLinearMap.toAddMonoidHom =
      L.map q.toAddMonoidHom := by
    rw [AddSubgroup.map_map]
    congr 1
  constructor
  · intro h
    rw [← h1]
    exact locFree_map_equiv R e h
  · intro h
    have h2 : (L.map q.toAddMonoidHom).map e.symm.toLinearMap.toAddMonoidHom =
        L.map (LinearMap.ker q).mkQ.toAddMonoidHom := by
      rw [← h1, AddSubgroup.map_map]
      ext v
      simp
    rw [← h2]
    exact locFree_map_equiv R e.symm h

theorem isBaseChange_bcMap (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (ι : Type) [Finite ι] :
    IsBaseChange C (bcMap Ω C ι) := by
  have := Fintype.ofFinite ι
  have h := IsBaseChange.pi (S := C) (fun _ : ι => Algebra.linearMap Ω C)
    (fun _ => IsBaseChange.linearMap Ω C)
  exact h

theorem span_bcMap_annSub (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (n i : ℕ) :
    Submodule.span C (bcMap Ω C (Fin n) '' (annSub Ω n i : Set (Fin n → Ω))) = annSub C n i := by
  classical
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv ⊢
    intro j hj
    simp [bcMap, hv j hj]
  · intro v hv
    simp only [annSub, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot] at hv
    have : v = ∑ j, v j • bcMap Ω C (Fin n) (if (j : ℕ) < i then 0 else Pi.single j 1) := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · by_cases hk : (k : ℕ) < i
        · simp [hk, hv k hk, bcMap]
        · simp [hk, bcMap]
      · intro j _ hjk
        by_cases hj : (j : ℕ) < i
        · simp [hj, bcMap]
        · simp [hj, bcMap, Pi.single_apply, hjk.symm]
      · simp
    rw [this]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    simp only [annSub, SetLike.mem_coe, Submodule.mem_pi, Set.mem_setOf_eq, Submodule.mem_bot]
    intro k hk
    by_cases hj : (j : ℕ) < i
    · simp [hj]
    · have : k ≠ j := by rintro rfl; exact hj hk
      simp [hj, Pi.single_apply, this]

theorem spanOver_swap {C V Z Vc Zc : Type} [Field C] [Algebra o C] (RC : Subalgebra o C)
    [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (Γ : AddSubgroup (Z × V)) :
    spanOver RC (Prod.map b b' '' (Γ.map (AddEquiv.prodComm (M := Z) (N := V)).toAddMonoidHom : AddSubgroup (V × Z))) =
      (spanOver RC (Prod.map b' b '' Γ)).map (AddEquiv.prodComm (M := Zc) (N := Vc)).toAddMonoidHom := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, _, ⟨_, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a • (b' z, b v), ⟨a, ha, _, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨a, ha, _, ⟨⟨z, v⟩, hzv, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, _, ⟨_, ⟨(z, v), hzv, rfl⟩, rfl⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChangeStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_finite_projective_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), LocFree R r L.toAddSubgroup → Module.Finite R L ∧ Module.Projective R L ∧ Module.finrank Ω E = r ∧ IsBaseChange Ω L.subtype := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjectiveStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_of_finite_projective : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), Module.Finite R L → Module.Projective R L → Module.finrank Ω E = r → IsBaseChange Ω L.subtype → LocFree R r L.toAddSubgroup := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.locFree_of_projective <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingsConjugateOfUnitsStatement
section
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_embeddings_conjugate_of_units : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes) (κ κ' : K →+* ℂ_[p]), (∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) → ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | exact GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.Conj.exists_isometry_conj_of_unit_ball <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicIsometryEquivariance
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem proIsoAt_of_padic_isometry : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (L L' : Type) [AddCommGroup L] [Module O L] [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') [Module.Projective O L] [Module.Finite ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L'] [Module.Free ℤ L'] (φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L')), (∀ (a : O) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul O L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) → (∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v) → Nonempty (ProIsoAt p O B B') :=
  @PositivityTheory.UnitarySelfGeneration.tw_lift

end GlobalTheory.CompanionTheory.Ar
end

