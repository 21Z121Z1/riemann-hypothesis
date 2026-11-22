import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0153
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfSymmetricTensorZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicative
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.PlogMul

open Polynomial

variable {B : Type} [CommRing B]

noncomputable def logPoly (c : ℕ → B) (s : ℕ) : B[X] :=
  ∑ k ∈ Finset.range s, C ((-1) ^ k * c k) * X ^ (k + 1)

theorem derivative_logPoly (c : ℕ → B) (hc : ∀ k : ℕ, c k * ((k : B) + 1) = 1) (s : ℕ) :
    derivative (logPoly c s) = ∑ k ∈ Finset.range s, (-X) ^ k := by
  unfold logPoly
  rw [derivative_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (C (c k) : B[X]) * ((k : B[X]) + 1) = 1 := by
    have := congrArg (C : B →+* B[X]) (hc k)
    simpa using this
  rw [derivative_C_mul, derivative_X_pow, neg_pow (X : B[X]) k]
  simp only [Nat.add_sub_cancel, map_mul, map_pow, map_neg, map_one, Nat.cast_add, Nat.cast_one]
  calc _ = (-1) ^ k * (C (c k) * ((k : B[X]) + 1)) * X ^ k := by
        simp only [map_add, map_natCast, map_one]; ring
    _ = _ := by rw [h1, mul_one]

theorem one_add_mul_geom {R : Type} [CommRing R] (u : R) (s : ℕ) :
    (1 + u) * ∑ k ∈ Finset.range s, (-u) ^ k = 1 - (-u) ^ s := by
  have := mul_neg_geom_sum (-u) s
  simpa using this

theorem geom_comp (s : ℕ) (u : B[X]) :
    (∑ k ∈ Finset.range s, (-X : B[X]) ^ k).comp u = ∑ k ∈ Finset.range s, (-u) ^ k := by
  induction s with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, ih]

theorem eval_logPoly_zero (c : ℕ → B) (s : ℕ) : (logPoly c s).eval 0 = 0 := by
  simp [logPoly, eval_finset_sum]

theorem eval_logPoly_mul (c : ℕ → B) (hc : ∀ k : ℕ, c k * ((k : B) + 1) = 1)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) (s : ℕ) {x y : B}
    (hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0) :
    (logPoly c s).eval ((1 + x) * (1 + y) - 1) = (logPoly c s).eval x + (logPoly c s).eval y := by
  set a : B[X] := C x * X with ha
  set Z : B[X] := (1 + a) * (1 + C y) - 1 with hZ
  set G : B[X] := (logPoly c s).comp Z - (logPoly c s).comp a - C ((logPoly c s).eval y) with hG
  have has : a ^ s = 0 := by
    have h := hxy s 0 (by simp)
    have h' : x ^ s = 0 := by simpa using h
    rw [ha, mul_pow, ← C_pow, h']
    simp
  have hZs : Z ^ s = 0 := by
    have hZ' : Z = a * (1 + C y) + C y := by rw [hZ]; ring
    rw [hZ', add_pow]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i ≤ s := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h0 := hxy i (s - i) (by omega)
    have : (a * (1 + C y)) ^ i * (C y) ^ (s - i) = C (x ^ i * y ^ (s - i)) * (X ^ i * (1 + C y) ^ i) := by
      rw [ha, C_mul, C_pow, C_pow, mul_pow, mul_pow]; ring
    rw [this, h0]
    simp
  have hderiv : derivative G = 0 := by
    have hda : derivative a = C x := by rw [ha]; simp
    have hdZ : derivative Z = C x * (1 + C y) := by
      rw [hZ]; simp [hda]
    have hD : derivative G = C x * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k)
        - C x * (∑ k ∈ Finset.range s, (-a) ^ k) := by
      rw [hG, derivative_sub, derivative_sub, derivative_C, sub_zero, derivative_comp, derivative_comp,
        derivative_logPoly c hc, hdZ, hda]
      rw [geom_comp, geom_comp]
    have h1 : (1 + a) * (∑ k ∈ Finset.range s, (-a) ^ k) = 1 := by
      rw [one_add_mul_geom, neg_pow, has]; simp
    have h2 : (1 + a) * (1 + C y) * (∑ k ∈ Finset.range s, (-Z) ^ k) = 1 := by
      have := one_add_mul_geom Z s
      rw [neg_pow, hZs] at this
      have e : 1 + Z = (1 + a) * (1 + C y) := by rw [hZ]; ring
      rw [← e, this]; simp
    have h3 : (1 + a) * derivative G = 0 := by
      rw [hD]
      linear_combination (C x) * h2 - (C x) * h1
    have h4 : derivative G = (∑ k ∈ Finset.range s, (-a) ^ k) * ((1 + a) * derivative G) := by
      linear_combination (- derivative G) * h1
    rw [h4, h3, mul_zero]
  have hG0 : G.eval 0 = 0 := by
    simp [hG, hZ, ha, eval_comp, eval_logPoly_zero]
  have hGC : G = C (G.eval 0) := by
    ext n
    cases n with
    | zero => simp [coeff_zero_eq_eval_zero]
    | succ n =>
      have h := congrArg (fun p => coeff p n) hderiv
      simp only [coeff_derivative, coeff_zero] at h
      have hn : IsUnit ((n : B) + 1) := by
        have := hu (n + 1) (by omega)
        simpa using this
      have : G.coeff (n + 1) = 0 := hn.mul_left_eq_zero.1 h
      simp [this, coeff_C]
  have hG1 : G.eval 1 = 0 := by
    rw [hGC, hG0]; simp
  have : (logPoly c s).eval ((1 + x) * (1 + y) - 1) - (logPoly c s).eval x - (logPoly c s).eval y = 0 := by
    simpa [hG, hZ, ha, eval_comp] using hG1
  linear_combination this

theorem plogK_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ)
    (hs : pdP δ s = ⊥) (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {x y : B} (hx : x ∈ J) (hy : y ∈ J) :
    plogK δ s ((1 + x) * (1 + y) - 1) = plogK δ s x + plogK δ s y := by
  have hunit : ∀ k : ℕ, IsUnit ((k : B) + 1) := fun k => by
    have := hu (k + 1) (by omega)
    simpa using this
  choose c hc using fun k : ℕ => (hunit k).exists_left_inv
  have hlog : ∀ {z : B}, z ∈ J → plogK δ s z = (logPoly c s).eval z := by
    intro z hz
    simp only [plogK, logPoly, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := δ.factorial_mul_dpow_eq_pow (n := k + 1) hz
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    rw [← h]
    linear_combination (-(-1 : B) ^ k * (k.factorial : B) * δ.dpow (k + 1) z) * hc k
  have hxy : ∀ a b : ℕ, s ≤ a + b → x ^ a * y ^ b = 0 := by
    intro a b hab
    have hmem : δ.dpow a x * δ.dpow b y ∈ pdP δ s := by
      refine Ideal.subset_span ⟨[(a, x), (b, y)], ?_, ?_, ?_⟩
      · intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact hx
        · exact hy
      · simpa using hab
      · simp
    rw [hs, Ideal.mem_bot] at hmem
    rw [← δ.factorial_mul_dpow_eq_pow hx, ← δ.factorial_mul_dpow_eq_pow hy]
    linear_combination ((a.factorial : B) * (b.factorial : B)) * hmem
  have hz : (1 + x) * (1 + y) - 1 ∈ J := by
    have e : (1 + x) * (1 + y) - 1 = x + y + x * y := by ring
    rw [e]
    exact J.add_mem (J.add_mem hx hy) (J.mul_mem_right y hx)
  rw [hlog hz, hlog hx, hlog hy]
  exact eval_logPoly_mul c hc hu s hxy

end GlobalTheory.CompanionTheory.PlogMul
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedPolyLatticeHyp
section
set_option autoImplicit false

noncomputable section

open DividedPowers CrystallineSemistableComparison.Pb Polynomial

namespace GlobalTheory.CompanionTheory.LatPolyB

variable (l : ℕ) [Fact l.Prime]

theorem dvd_pow_of_ne_zero {x : ℤ_[l]} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (l : ℤ_[l]) ^ n := by
  have h := PadicInt.unitCoeff_spec hx
  refine ⟨x.valuation, ((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ), ?_⟩
  calc (l : ℤ_[l]) ^ x.valuation
      = (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) *
          (((PadicInt.unitCoeff hx : ℤ_[l]ˣ) : ℤ_[l]) * (l : ℤ_[l]) ^ x.valuation) :=
        (Units.inv_mul_cancel_left _ _).symm
    _ = (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * x := congrArg _ h.symm
    _ = x * (((PadicInt.unitCoeff hx)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) := mul_comm _ _

def quotX : (ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])}) ≃+* ℤ_[l] :=
  (Ideal.quotEquivOfEq (by simp)).trans (Polynomial.quotientSpanXSubCAlgEquiv (0 : ℤ_[l])).toRingEquiv

theorem quotX_natCast (n : ℕ) : quotX l (n : ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])}) = n := map_natCast _ n

theorem cpl : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])})})
    (ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])}) := by
  have h : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  have e : (Ideal.span {(l : ℤ_[l])}).map ((quotX l).symm : ℤ_[l] →+* _) =
      Ideal.span {((l : ℕ) : ℤ_[l][X] ⧸ Ideal.span {(X : ℤ_[l][X])})} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  rw [← e]
  exact (IsAdicComplete.congr_ringEquiv _ (quotX l).symm).2 h

theorem padic_poly_graded_smul_pow (m i : ℕ) (hi : i < m) (a : ℤ_[l][X])
    (b : ℚ_[l][X] ⧸ Ideal.span {(X : ℚ_[l][X]) ^ m})
    (h : ((Ideal.Quotient.mk (Ideal.span {(X : ℚ_[l][X]) ^ m})).comp (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := l)))) a *
      ((Ideal.Quotient.mk (Ideal.span {(X : ℚ_[l][X]) ^ m})).comp (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := l)))) X ^ i =
      ((Ideal.Quotient.mk (Ideal.span {(X : ℚ_[l][X]) ^ m})).comp (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := l)))) X ^ (i + 1) * b) :
    X ∣ a := by
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X] at h
  rw [← map_pow, ← map_mul, ← map_pow, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  have h1 : (X : ℚ_[l][X]) ^ (i + 1) ∣ a.map (PadicInt.Coe.ringHom (p := l)) * X ^ i := by
    have h2 : (X : ℚ_[l][X]) ^ (i + 1) ∣ a.map (PadicInt.Coe.ringHom (p := l)) * X ^ i - X ^ (i + 1) * b' :=
      (pow_dvd_pow _ hi).trans h
    exact (dvd_sub_left (Dvd.intro _ rfl)).1 h2
  rw [pow_succ', mul_comm] at h1
  have h3 : (X : ℚ_[l][X]) ∣ a.map (PadicInt.Coe.ringHom (p := l)) :=
    (mul_dvd_mul_iff_left (pow_ne_zero i Polynomial.X_ne_zero)).1 (by simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h1)
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_map] at h3
  rw [Polynomial.X_dvd_iff]
  exact PadicInt.coe_eq_zero.1 h3

theorem hyp : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ), 1 ≤ m → Lat.Hyp ((Ideal.Quotient.mk (Ideal.span {(Polynomial.X : Polynomial ℚ_[l]) ^ m})).comp (Polynomial.mapRingHom (PadicInt.Coe.ringHom (p := l)))) Polynomial.X l m := by
  intro l _ m hm
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine
    { one_le := hm
      nil := ?_
      gr := fun i hi a b h => padic_poly_graded_smul_pow l m i hi a b h
      dom := (quotX l).toMulEquiv.isDomain _
      val := fun x y => ?_
      dv := fun x hx => ?_
      l0 := ?_
      cpl := cpl l
      unit := fun n hn => ?_ }
  · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  · rcases ValuationRing.dvd_total (quotX l x) (quotX l y) with h | h
    · exact Or.inl ((map_dvd_iff (quotX l)).1 h)
    · exact Or.inr ((map_dvd_iff (quotX l)).1 h)
  · obtain ⟨n, hn⟩ := dvd_pow_of_ne_zero l (x := quotX l x) (by simpa using hx)
    refine ⟨n, (map_dvd_iff (quotX l)).1 ?_⟩
    simpa [quotX_natCast] using hn
  · intro h
    apply hl0
    have := congrArg (quotX l) h
    simpa [quotX_natCast] using this
  · have hn0 : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn
    obtain ⟨k, u, hu⟩ := dvd_pow_of_ne_zero l hn0
    refine ⟨k, C u, ?_⟩
    have := congrArg (C : ℤ_[l] →+* ℤ_[l][X]) hu
    simpa using this.symm

end GlobalTheory.CompanionTheory.LatPolyB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonempty
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.ConeOne

variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def resI (x : X) : K →+* X.residueField x :=
  (Spec.preimage (X.fromSpecResidueField x ≫ q)).hom

theorem spec_resI (x : X) :
    Spec.map (CommRingCat.ofHom (resI q x)) = X.fromSpecResidueField x ≫ q := by
  have : CommRingCat.ofHom (resI q x) = Spec.preimage (X.fromSpecResidueField x ≫ q) := rfl
  rw [this, Spec.map_preimage]

def resPt (x : X) : PtOver X q (Ideal.Quotient.mk (⊥ : Ideal K))
    (X.residueField x ⧸ (⊥ : Ideal (X.residueField x))) :=
  ⟨(Ideal.quotientMap ⊥ (resI q x) bot_le,
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal (X.residueField x)))) ≫ X.fromSpecResidueField x), by
    rw [Category.assoc, ← spec_resI, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl⟩

def resT (x : X) : Thick (smFun X q) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (X.residueField x) (resI q x) ⊥
    (dividedPowersBot _)
    ⟨fun h => absurd rfl h, fun _ => ⟨1, by simp⟩⟩
    ⟨by simp, fun a ha => by
      classical
      have : a = 0 := ha
      subst this
      rw [map_zero, dividedPowersBot_dpow_eq, dividedPowersBot_dpow_eq]
      simp only [true_and]
      split_ifs <;> simp⟩
    (resPt q x) (fun _ => rfl)

end GlobalTheory.CompanionTheory.ConeOne

open GlobalTheory.CompanionTheory.ConeOne in
theorem GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  intro K _ X q ⟨x⟩ h
  have h1 := (Submodule.Quotient.mk_eq_zero _).1 h
  have h2 : (fun s : ComposableArrows (Thick (smFun X q)) 0 =>
      (1 : (thA (smFun X q)).obj (s.obj (Fin.last 0)))) = 0 := h1
  have h3 := congrFun h2 (ComposableArrows.mk₀ (resT q x))
  exact one_ne_zero (α := X.residueField x) h3
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitUniversalEqPullbackBoxEvaluationStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitUniversal_eq_pullback_box_evaluation : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) [Finite (Fin (0 + 1) ⥤ C)] (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) (n : ℕ) (w : Cn (box F) n), UU F (evF F T₀ ε) n w = pulln (boxE F T₀ ε) n w := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.UU_evF | exact GlobalTheory.CompanionTheory.HopfC.UU_evF | (intros; apply GlobalTheory.CompanionTheory.HopfC.UU_evF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorSpaceHasBasisOfDimensionStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_space_has_basis_of_dimension : ∀ {R : Type} [CommRing R] (_ : IsField R) {M : Type} [AddCommGroup M] [Module R M] (g : ℕ), VB R M g → Nonempty (Module.Basis (Fin g) R M) := by
  first | exact @GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField | exact GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField | (intros; apply GlobalTheory.CompanionTheory.HopfC.vb_basis_of_isField <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeOfSymmetricTensorZeroStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_of_symmetric_tensor_zero : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V] (t : V ⊗[R] V), t - TensorProduct.comm R V V t = 0 → wedgeT (R := R) V t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm | exact GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm <;> assumption)
end

