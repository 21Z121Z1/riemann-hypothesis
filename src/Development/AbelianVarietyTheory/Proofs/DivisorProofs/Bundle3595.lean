import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3583
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import ReciprocityTheory.ReductiveGroups.Lattices.LatUnrCharA
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3584
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3587
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsMemIntegralClosureGalois
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3588
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNatAbsEqMinpolyCoeffZeroPow
section
open CategoryTheory Polynomial NumberField IsDedekindDomain AlgebraicGeometry
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.HT
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_prime_cast_ne_zero_of_field (k : Type) [Field k] : ∃ l : ℕ, l.Prime ∧ (l : k) ≠ 0 := by
  obtain ⟨l, hl, hlp⟩ := Nat.exists_infinite_primes (ringChar k + 1)
  refine ⟨l, hlp, fun h => ?_⟩
  rw [CharP.cast_eq_zero_iff k (ringChar k)] at h
  rcases hlp.eq_one_or_self_of_dvd _ h with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

theorem minpoly_int_coeff_zero_ne_zero {F : Type} [Field F] [NumberField F] (x : 𝓞 F) (hx : x ≠ 0) :
    (minpoly ℤ x).coeff 0 ≠ 0 := by
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hxF : (x : F) ≠ 0 := by exact_mod_cast hx
  have h1 := minpoly.coeff_zero_ne_zero (A := ℚ) (IsIntegral.of_finite ℚ (x : F)) hxF
  have h2 : minpoly ℚ (x : F) = (minpoly ℤ x).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ F hi
  rw [h2, coeff_map] at h1
  intro h; exact h1 (by rw [h, map_zero])

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem norm_natAbs_eq_minpoly_coeff_zero_pow {F : Type} [Field F] [NumberField F] (x : 𝓞 F) :
    ∃ r : ℕ, r * (minpoly ℤ x).natDegree = Module.finrank ℚ F ∧
      (Algebra.norm ℤ x).natAbs = ((minpoly ℤ x).coeff 0).natAbs ^ r := by
  obtain ⟨r, -, hr⟩ := ReciprocityTheory.ChartRestriction.T1.lat_cp_eq_minpoly_pow x
  have hm : (minpoly ℤ x).Monic := minpoly.monic (RingOfIntegers.isIntegral x)
  refine ⟨r, ?_, ?_⟩
  · rw [← ReciprocityTheory.ChartRestriction.T1.lat_cp_natDegree x, hr, hm.natDegree_pow]
  · have e : Algebra.norm ℤ x = (-1) ^ Module.finrank ℤ (𝓞 F) * (ReciprocityTheory.ChartRestriction.T1.lat_cp x).coeff 0 := by
      rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff]; rfl
    rw [e, hr, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, Int.natAbs_mul, Int.natAbs_pow,
      Int.natAbs_pow]
    simp

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem deg_eq_coeff_zero_pow_of_aeval {k : Type} [Field k] (A : AbVar k) (f : End A) (m : ℤ[X]) (hm : m.Monic)
    (hp : Prime m) (hf : aeval f m = 0) :
    ∃ e : ℕ, e * m.natDegree = 2 * A.dim ∧ (deg (A := A) (B := A) f : ℤ) = m.coeff 0 ^ e := by
  obtain ⟨l, hl, hl0⟩ := exists_prime_cast_ne_zero_of_field k
  haveI := Fact.mk hl
  obtain ⟨-, -, -, hfin, hrank⟩ := GlobalTheory.AV.AbVar.tl_free_finrank k l hl0 A
  haveI := hfin
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.T.endCharpoly_tate_det_degree_trace k l hl0 A f
  have h1' := @h1 hfin
  have inj : Function.Injective (algebraMap ℤ ℚ_[l]) := RingHom.injective_int _
  let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
    (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp (tend l A)
  have hψ : ψ f = vmap l (A := A) (B := A) f := rfl
  have hT : aeval (vmap l (A := A) (B := A) f) m = 0 := by
    rw [← hψ]
    have := Polynomial.hom_eval₂ m (algebraMap ℤ (End A)) ψ f
    rw [← aeval_def, hf, map_zero, Subsingleton.elim (ψ.comp (algebraMap ℤ (End A))) (algebraMap ℤ _),
      ← aeval_def] at this
    exact this.symm
  have hdvd := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank (vmap l (A := A) (B := A) f) (m.map (algebraMap ℤ ℚ_[l]))
    (by rw [aeval_map_algebraMap]; exact hT)
  rw [← h1', ← Polynomial.map_pow] at hdvd
  have hQm : (charpoly f).Monic :=
    Polynomial.monic_of_injective inj (by rw [h1']; exact LinearMap.charpoly_monic _)
  rw [map_dvd_map _ inj hQm] at hdvd
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hp _).1 hdvd
  have hQ : charpoly f = m ^ i := eq_of_monic_of_associated hQm (hm.pow i) hi
  have hdeg : (charpoly f).natDegree = 2 * A.dim := by
    rw [← Polynomial.natDegree_map_eq_of_injective inj, h1', LinearMap.charpoly_natDegree, hrank]
  refine ⟨i, ?_, ?_⟩
  · rw [← hdeg, hQ, hm.natDegree_pow]
  · have e := LinearMap.det_eq_sign_charpoly_coeff (vmap l (A := A) (B := A) f)
    rw [h3, ← h1', coeff_map, hrank, pow_mul, neg_one_sq, one_pow, one_mul, hQ, coeff_zero_eq_eval_zero,
      eval_pow, ← coeff_zero_eq_eval_zero] at e
    apply Int.cast_injective (α := ℚ_[l])
    rw [Int.cast_natCast, e, eq_intCast, Int.cast_pow]

end GlobalTheory.AV.AbVar

namespace GlobalTheory.AV.AbVar

theorem isIsogeny_and_deg_eq_norm_pow : ∀ (k : Type) [Field k] (A : AbVar k) (F : Type) [Field F] [NumberField F]
    (ι : 𝓞 F →+* End A) (d : ℕ), 2 * A.dim = d * Module.finrank ℚ F → ∀ x : 𝓞 F, x ≠ 0 →
      IsIsogeny (A := A) (B := A) (ι x) ∧ deg (A := A) (B := A) (ι x) = (Algebra.norm ℤ x).natAbs ^ d := by
  intro k _ A F _ _ ι d hd x hx
  have hi : IsIntegral ℤ x := RingOfIntegers.isIntegral x
  have hm : (minpoly ℤ x).Monic := minpoly.monic hi
  have hp : Prime (minpoly ℤ x) := (minpoly.irreducible hi).prime
  have hf : aeval (ι x) (minpoly ℤ x) = 0 := by
    have := Polynomial.hom_eval₂ (minpoly ℤ x) (algebraMap ℤ (𝓞 F)) ι x
    rw [← aeval_def, minpoly.aeval, map_zero, Subsingleton.elim (ι.comp (algebraMap ℤ (𝓞 F))) (algebraMap ℤ _),
      ← aeval_def] at this
    exact this.symm
  obtain ⟨e, he, hdeg⟩ := deg_eq_coeff_zero_pow_of_aeval A (ι x) (minpoly ℤ x) hm hp hf
  obtain ⟨r, hr, hN⟩ := norm_natAbs_eq_minpoly_coeff_zero_pow x
  have hpos : 0 < (minpoly ℤ x).natDegree := minpoly.natDegree_pos hi
  have her : e = d * r := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [he, hd, ← hr, mul_assoc]
  have hdeg' : deg (A := A) (B := A) (ι x) = ((minpoly ℤ x).coeff 0).natAbs ^ e := by
    have := congrArg Int.natAbs hdeg
    rwa [Int.natAbs_natCast, Int.natAbs_pow] at this
  have hval : deg (A := A) (B := A) (ι x) = (Algebra.norm ℤ x).natAbs ^ d := by
    rw [hdeg', hN, ← pow_mul, her, mul_comm]
  refine ⟨?_, hval⟩
  by_contra h
  have h0 : deg (A := A) (B := A) (ι x) = 0 := by
    classical
    unfold deg
    rw [if_neg h]
  rw [hdeg'] at h0
  exact minpoly_int_coeff_zero_ne_zero x hx (Int.natAbs_eq_zero.1 (pow_eq_zero_iff'.1 h0).1)

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkPointGaloisFixedUpToEquivDividedData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DivGalFix

open GlobalTheory.TorusExt

attribute [local instance] GlobalTheory.TorusExt.gtGroup

theorem qkPt_rational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ q : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ q₀ : QkPt P.D.toPre (FractionRing R) l.M', QkExt (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) q₀ q := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD q
  have hB := P.D.tau_bimult
  have ha : (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))).comp
      (algebraMap (FractionRing R) (FractionRing R)) = algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, hy⟩ := GlobalTheory.T.exists_levelTorsionPoint_of_comesFromBase L R hR t P iw s ε e hε hs hD q.y
  set p₁ := qkExt hB (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ha p₀ with hp₁
  have h0 : l.M' • (q.g - p₁.g) = iota hB (AlgebraicClosure (FractionRing R)) 0 := by
    rw [smul_sub, qk_nsmul hB, qk_nsmul hB, map_zero]
    show iota hB _ q.y - iota hB _ p₀.y = 0
    rw [hy, sub_self]
  obtain ⟨r₀, hr⟩ := GlobalTheory.T.exists_qkPoint_extension_of_divided_data L R hR t P iw s ε e hε hs hD (qkMk hB 0 (q.g - p₁.g) h0) rfl
  rw [qkExt_iff hB _ ha] at hr
  refine ⟨qkAdd hB p₀ r₀, ?_⟩
  rw [qkExt_iff hB _ ha, qkExt_qkAdd, ← hr, ← hp₁]
  apply qk_ext
  · show q.y = p₀.y + 0
    rw [hy, add_zero]
  · show q.g = p₁.g + (q.g - p₁.g)
    abel

theorem qkExt_equiv_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p p' : QkPt P.D.toPre (AlgebraicClosure (FractionRing R)) l.M'), QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv P.D.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD σ p p' hpp'
  refine GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational R P.D l.M' (fun q => ?_) σ.toAlgHom p p' hpp'
  obtain ⟨q₀, hq⟩ := qkPt_rational L R hR t P iw s ε e hε hs hD q
  exact ⟨q₀, q, hq, qk_equiv_refl P.D.tau_bimult q⟩

end GlobalTheory.DivGalFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmTangentVectorsBasisDualLieStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_tangentVectors_basis_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E), IsBasis c.μ e → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  first | exact @GlobalTheory.LieBasisChange.lie_basis | exact GlobalTheory.LieBasisChange.lie_basis | (intros; apply GlobalTheory.LieBasisChange.lie_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsMemIntegralClosureGaloisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFourier_classSums_mem_integralClosure_galois : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 8 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 8 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod ℤ N (k y)) ∧ Φ.IsTerms W t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 8 → Φ.X y), ∀ S : Finset (Fin 8 → Φ.X y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.Poinc.ClassCore.classSums_integralClosure | exact GlobalTheory.Poinc.ClassCore.classSums_integralClosure | (intros; apply GlobalTheory.Poinc.ClassCore.classSums_integralClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberDividingLabelClassZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_dividing_label_class_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → 𝔪.YY a 0 := by
  first | exact @GlobalTheory.GSep.DivInt.label_zero_of_mem_supI | exact GlobalTheory.GSep.DivInt.label_zero_of_mem_supI | (intros; apply GlobalTheory.GSep.DivInt.label_zero_of_mem_supI <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTermsCoefficientsUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.GSep.TermsUniq

section Reformulated
variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V] [IsDomain V]
  [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {Y : Type} [AddCommGroup Y] {t : Y → V} {δ : I → Y → Y}

theorem hom_eq_of_comp (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {u v : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    (h : u.left ≫ 𝔪.φ = v.left ≫ 𝔪.φ) : u = v :=
  Over.OverMorphism.ext (𝔪.cart.1.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem frame_val_eq (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A}
    {a : X₁.S.Gam} (fr fr₂ : FrAt x)
    (h : ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl x.left z (J (x.left ≫ 𝔪.φ)) (J' x.left) * val fr (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J)
    (h₂ : ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl x.left z (J (x.left ≫ 𝔪.φ)) (J' x.left) * val fr₂ (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) :
    ∀ z J', Good 𝔪.A.L z J' → val fr₂ (𝟙 _) z J' = val fr (𝟙 _) z J' := by
  intro z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good' X₁.ρ.P.isLB z
  exact mul_left_cancel ((h₂ z J J' hJ hJ').trans (h z J J' hJ hJ').symm)
end Reformulated

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem valAt_congr {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {k : ℕ} {th : SecA A F k}
    {x : TFK (R := R) F ⟶ A.A} {e e' : FrAt x} {c : F} (h : ValAt th x e c)
    (he : ∀ z J, Good A.L z J → val e' (𝟙 _) z J = val e (𝟙 _) z J) : ValAt th x e' c := by
  intro z J hJ
  rw [h z J hJ]
  congr 2
  have := he z J hJ
  simp only [Geo.Tor.val, powFrame] at this ⊢
  exact (map_zpow _ _ _).trans ((congrArg (· ^ (k : ℤ)) this.symm).trans (map_zpow _ _ _).symm)

variable {D : DegPre R}

theorem coef_congr {k : ℕ} {g g₂ : GtPtF D F} {w : Frm D F k g.b} {w₂ : Frm D F k g₂.b} (hw : w.IsGen)
    (hb : g₂.b = g.b) (hs : ∀ χ z J, Good D.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J)
    (hv : ∀ z J, Good D.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g₂ w₂ χ = coef s g w χ := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e : lift (𝟙 (TF (R := R) F)) g₂.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hs χ z J hJ, hv z J hJ, e]
  exact a

theorem coef_smul {k : ℕ} {g : GtPtF D F} {w : Frm D F k g.b} (hw : w.IsGen) (u : F) (s : Fam D F k) (χ : D.X) :
    coef (u • s) g w χ = u * coef s g w χ := by
  have hlin := ((coef_basic R D F k g).2.2 w hw).2.1
  have e0 := hlin 0 0 1 χ
  simp only [_root_.one_smul, _root_.add_zero, _root_.one_mul] at e0
  have h0 : coef (0 : Fam D F k) g w χ = 0 := by linear_combination (-1 : F) * e0
  have e := hlin s 0 u χ
  rw [_root_.add_zero, h0, _root_.add_zero] at e
  exact e
end Gen

section Transport
variable {I : Type} {X₁ : GlobalTheory.GSep.GSet} {z₁ : X₁.M.Z} {act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} {V : Type} [CommRing V] [IsDomain V]
  [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V} {Y : Type} [AddCommGroup Y] {t : Y → V} {δ : I → Y → Y}

theorem over_transport (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) {w₀ w₀₂ : W0 𝔪.U.toUnifPre}
    {g : GtPtF 𝔪.D.toPre (FractionRing V)} {w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b}
    {x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A} {fr fr₂ : FrAt x} {u : FractionRing V}
    (hO : 𝔪.Over' w₀₂ g w x fr₂) (hw : w.IsGen)
    (hD : ∀ (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s : Fam 𝔪.D.toPre (FractionRing V) k),
      𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀₂ th (u ^ k • s))
    (hfr : ∀ z J, Good 𝔪.A.L z J → val fr₂ (𝟙 _) z J = val fr (𝟙 _) z J)
    (hv : ∀ z J, Good 𝔪.D.toPre.P.L z J →
      (val w' (𝟙 _) z J).val = cst (FractionRing V) z u * (val w (𝟙 _) z J).val) :
    𝔪.Over' w₀ g w' x fr := by
  intro k hk wk' hwk' hwk'g th s' v hexp hval
  obtain ⟨wk, hwkg, hwk⟩ := TorsionValue.exists_frm_pow w hw k
  have H := hO k hk wk hwk hwkg th (u ^ k • s') v (hD k th s' hexp) (valAt_congr hval fun z J hJ => hfr z J hJ)
  have hcv : ∀ z J, Good 𝔪.D.toPre.P.L z J →
      (val wk' (𝟙 _) z J).val = cst (FractionRing V) z (u ^ k) * (val wk (𝟙 _) z J).val := by
    intro z J hJ
    rw [hwk' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hv z J hJ, mul_pow, cst_eq, cst_eq,
      map_pow]
  have e : coef (u ^ k • s') g wk = coef s' g wk' := funext fun χ => by
    rw [coef_smul hwkg, TorsionValue.coef_scale hwkg hcv s' χ]
  rw [e] at H
  exact H
end Transport

theorem coef_eq : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (b : X₁.S.Gam)
  (x x₂ : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (fr₂ : ∀ a, FrAt (x₂ a))
  (th th₂ : SecA 𝔪.A (FractionRing V) 1) (w₀ w₀₂ : W0 𝔪.U.toUnifPre) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) 1)
  (g' g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g'.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀ th s →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g' o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g' w (x b) (fr b) →
  (∀ a, (x₂ a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) →
  (∀ a, (fr₂ a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      Geo.Tor.gw 𝔪.wl (x₂ a).left z (J ((x₂ a).left ≫ 𝔪.φ)) (J' (x₂ a).left) * val (fr₂ a) (𝟙 _) z J' =
        val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) →
  (∀ a, ValAt th₂ (x₂ a) (fr₂ a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → w₀₂.IsGen →
  𝔪.U.ExpandsF (FractionRing V) 1 w₀₂ th₂ s₂ →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀₂ g₂ w₂ (x₂ b) (fr₂ b) →
  ∀ χ, coef s g' w χ = coef s₂ g₂ w₂ χ := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 b x x₂ fr fr₂ th th₂ w₀ w₀₂ s s₂ g' g₂ w w₂ hx hfr hth hw₀ hs hg hw hO hx₂ hfr₂
    hth₂ hw₀₂ hs₂ hg₂ hw₂ hO₂ χ
  obtain rfl : x = x₂ := (funext fun a => hom_eq_of_comp 𝔪 ((hx₂ a).trans (hx a).symm)).symm
  have efr : ∀ a z J', Good 𝔪.A.L z J' → val (fr₂ a) (𝟙 _) z J' = val (fr a) (𝟙 _) z J' :=
    fun a => frame_val_eq 𝔪 (a := a) (fr a) (fr₂ a) (hfr a).2 (hfr₂ a).2
  have hth₂' : ∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩) :=
    fun a => valAt_congr (hth₂ a) fun z J hJ => (efr a z J hJ).symm
  obtain rfl : th = th₂ := Eq.symm <| GlobalTheory.T.section_eq_of_values_at_label_torsion I X₁ z₁ act V ev Y t δ 𝔪 x fr th th₂ (fun a => (hfr a).1) hth hth₂'
  obtain ⟨u, hu, hD⟩ := GlobalTheory.T.uniformisation_generic_frames_scale_by_constant I X₁ z₁ act V ev Y t δ 𝔪 w₀ w₀₂ hw₀ hw₀₂
  obtain ⟨w₂', hw₂'g, hv₂'⟩ := TorsionValue.exists_frm_scale w₂ hw₂ hu
  have hO₂' : 𝔪.Over' w₀ g₂ w₂' (x b) (fr b) := over_transport 𝔪 hO₂ hw₂ hD (efr b) hv₂'
  obtain ⟨hb, hsv⟩ := GlobalTheory.T.thetaMember_torsion_points_eq_same_values I X₁ z₁ act V ev Y t δ 𝔪 w₀ (x b) (fr b) g' g₂ w w₂' hw₀ (hfr b).1 hg hw hO hg₂ hw₂'g hO₂'
  have hwv := GlobalTheory.T.thetaMember_torsion_frame_unique I X₁ z₁ act V ev Y t δ 𝔪 w₀ (x b) (fr b) g' g₂ w w₂' hw₀ (hfr b).1 hg hw hO hg₂ hw₂'g hO₂' hb hsv
  have e1 : coef s g₂ w₂' χ = coef s g' w χ := coef_congr hw hb hsv hwv s χ
  have e2 : coef s₂ g₂ w₂ χ = coef (u ^ 1 • s) g₂ w₂ χ :=
    GlobalTheory.T.thetaMember_expansion_terms_eq I X₁ z₁ act V ev Y t δ 𝔪 w₀₂ 1 th (u ^ 1 • s) s₂ hw₀₂ le_rfl (hD 1 th s hs) hs₂ g₂ w₂ hw₂ χ
  rw [e2, pow_one, coef_smul hw₂, ← TorsionValue.coef_scale hw₂ hv₂' s χ, e1]

end GlobalTheory.GSep.TermsUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTranslationExponentsAffineStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_translation_exponents_affine : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩) := by
  first | exact @GlobalTheory.Poinc.Sep.trans_exp_affine | exact GlobalTheory.Poinc.Sep.trans_exp_affine | (intros; apply GlobalTheory.Poinc.Sep.trans_exp_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTermCoefficientSqEqMonomialSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.Coef

theorem ev_units_zpow {V K : Type} [CommRing V] [Field K] (f : V →+* K) (v : Vˣ) (n : ℤ) :
    f ((v ^ n : Vˣ) : V) = f v ^ n := by
  have h1 : f ((v ^ n : Vˣ) : V) = ((Units.map f.toMonoidHom (v ^ n) : Kˣ) : K) := rfl
  rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem coef_sq_mem_monomial : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁), D.PsiEven → D.TauBimult → ∀ (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (u : X → C → V₁) (mo : X → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → GlobalTheory.Poinc.Sep.IsThetaTerms D N₁ e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : GlobalTheory.UChart.Gens D) (m N : ℕ) (s : Fin m ⊕ Fin N → V₁) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ D.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.UChart.TauIn D τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, algebraMap V₁ (FractionRing V₁) (mo mu) ^ 2 = ∏ k, algebraMap V₁ (FractionRing V₁) (s (.inl k)) ^ ε (.inl k) (e mu) (e mu)) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁), GlobalTheory.UChart.FromBase D τ₀ ib → (∀ a, ev (ib a) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) ^ 2 = r * ∏ k, ev (s (.inr k)) ^ ε (.inr k) (e mu) (e mu) := by
  intro N₁ hN V₁ _ _ _ hV hunit D hpe htb X C _ e u mo hmo hT K _ _ ev k₀ hk₀ τ₀ m N s ε hs hτ hmo2 W₀ _ ib hB hib mu c
  obtain ⟨θ, b, t, χt, s₀, G, hθ, hb, ht, hχt, hs₀, hG, hGf⟩ :=
    GlobalTheory.T.integral_squaredThetaTerms_torusCoordinates N₁ hN V₁ hV hunit D hpe htb X C e u mo hmo hT τ₀ m N s ε hs hτ hmo2
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.integral_expression_values_at_descended_point N₁ hN V₁ hV hunit D X C e τ₀ θ hθ b hb t ht χt hχt G hGf K ev k₀ hk₀ W₀ ib hB hib
  obtain ⟨-, -, -, -, -, -, -, -, -, c₀, hc₀⟩ := hT
  have hc₀' : u 0 c₀ * mo 0 = 1 := hc₀
  have hm0 : mo 0 ^ 2 = 1 := by
    have h := hmo2 0
    simp only [map_zero, LinearMap.map_zero₂, zpow_zero, Finset.prod_const_one] at h
    exact IsFractionRing.injective V₁ (FractionRing V₁) (by simpa using h)
  have hu0 : u 0 c₀ ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hc₀'
    simpa only [mul_pow, hm0, _root_.mul_one, one_pow] using h
  have hP0 : ((∏ k, (hs k).unit ^ ε (.inr k) (e 0) (e 0) : V₁ˣ) : V₁) = 1 := by
    simp only [map_zero, LinearMap.map_zero₂, zpow_zero, Finset.prod_const_one, Units.val_one]
  have h0 : s₀ = G 0 c₀ := by
    have h := hG 0 c₀
    rw [hu0, _root_.one_mul, hP0, _root_.one_mul] at h
    exact h
  obtain ⟨r₀, hr₀, e₀⟩ := hΛ 0 c₀
  obtain ⟨r, hr, e₁⟩ := hΛ mu c
  have hev0 : ev s₀ ≠ 0 := (hs₀.map ev).ne_zero
  have hΛr₀ : Λ * r₀ ≠ 0 := by rw [← e₀, ← h0]; exact hev0
  have hr₀0 : r₀ ≠ 0 := right_ne_zero_of_mul hΛr₀
  have hΛ0 : Λ ≠ 0 := left_ne_zero_of_mul hΛr₀
  refine ⟨r / r₀, k₀.div_mem hr hr₀, ?_⟩
  have h := congrArg ev (hG mu c)
  rw [map_mul, map_mul, map_pow, e₁, h0, e₀, Units.coe_prod, map_prod] at h
  simp only [ev_units_zpow, IsUnit.unit_spec] at h
  field_simp
  apply mul_left_cancel₀ hΛ0
  linear_combination h

end GlobalTheory.USep.Coef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPartPsiTauTangentVectorVariationStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitPart_psi_tau_tangent_vector_variation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ lam : ℕ → P.D.toPre.X → k, ∀ (mu α : P.D.toPre.X) (n : Fin m → ℕ) (ψ₀ : LB.Gen (LB.LinComb P.D.toPre.P.L (K := PUnit) (fun _ => (P.D.toPre.c mu).left) fun _ => -1)) τ₀, GlobalTheory.LogKSChart.IsUnitPart P.D.toPre (bdParam k m d) gam mu n ψ₀ → IsUnitTau P.D.toPre (bdParam k m d) gam mu α τ₀ → ∃ e₀ : ℕ, ∀ e : ℕ, e₀ ≤ e → ∀ ee : (DualNumber k)ˣ, (ee : DualNumber k) = 1 + TrivSqZeroExt.inr (lam e mu - ∑ i, ((e : k) * (n i : k) + (gam i mu α : k)) * MvPowerSeries.constantCoeff (q i)) → ∀ zz J, Good P.D.toPre.P.L zz J → (val ψ₀ (spMap ρ) zz J) ^ e * val τ₀ (spMap ρ) zz J * (val P.D.toPre.rig (spMap ρ) zz J) ^ e = gm (c' (mu)) zz _ (w.s (fun _ => J (c' (mu) ≫ π₂), fun _ => J (c' (mu) ≫ π₁))) ^ ((e : ℤ) - 1) * gm (c' (mu + α)) zz _ (w.s (fun _ => J (c' (mu + α) ≫ π₂), fun _ => J (c' (mu + α) ≫ π₁))) * (gm (c' (α)) zz _ (w.s (fun _ => J (c' (α) ≫ π₂), fun _ => J (c' (α) ≫ π₁))))⁻¹ * gm (c' (0)) zz _ (w.s (fun _ => J (c' (0) ≫ π₂), fun _ => J (c' (0) ≫ π₁))) ^ (1 - (e : ℤ)) * gm (𝟙 (Sp (DualNumber k))) zz ⊤ (unitOn ee) * (val ψ₀ (spMap (constHom ρ)) zz J) ^ e * val τ₀ (spMap (constHom ρ)) zz J * (val P.D.toPre.rig (spMap (constHom ρ)) zz J) ^ e := by
  first | exact @GlobalTheory.UnitsEval.units_eval | exact GlobalTheory.UnitsEval.units_eval | (intros; apply GlobalTheory.UnitsEval.units_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitPeriodsBoundedBelowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classical_trait_periods_bounded_below : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X' : USetup C) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (z' : X'.M.Z), IsClosed ({z'} : Set X'.M.Z) → ∀ t : UCTrait X' p z', X'.S.R ≤ X'.M.O ((gPt p ≫ t.y) (IsLocalRing.closedPoint (PadicAlgCl p))) → ∀ x : t.T.P.D.toPre.X, x ≠ 0 → ∃ h ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  first | exact @GlobalTheory.UPoinc.ShortBound.main | exact GlobalTheory.UPoinc.ShortBound.main | (intros; apply GlobalTheory.UPoinc.ShortBound.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryComparisonLatticePeriodsAtPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryComparison_lattice_periods_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∃ (m₁ m₂ : ℕ), 1 ≤ m₁ ∧ 1 ≤ m₂ ∧ ∀ (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X) (_ : Module.Projective (𝓞 E) X) (n : ℕ) (eb : X ≃ₗ[ℤ] (Fin n → ℤ)) (b₀ : LinearMap.BilinForm ℤ X) (μ : (Fin n → ZMod X₁.S.N) → X) (e : (Fin n → ZMod X₁.S.N) → X₁.Ω₁), Module.finrank (𝓞 E) X ≤ min Dw.p Dw.q ∧ b₀ ∈ balForms H.bar X ∧ (∀ y, y ≠ 0 → 0 < b₀ y y) ∧ (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod X₁.S.N) = cl i) ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) ∧ (∀ cl, e cl ≠ 0 ∧ ∃ (T₀ : AddSubgroup X₁.S.Gam) (c' : T₀ →+ ZMod X₁.S.N) (κ : X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) (x₀ : X₁.S.Gam), X₁.S.IsoFree T₀ ∧ e cl = X₁.S.FF T₀ c' κ / X₁.S.th x₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : X →ₗ[𝓞 E] T.P.D.toPre.X, Function.Surjective π ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → T.be (π (μ cl)) (π (μ cl)) ≤ T.be (π α) (π α)) ∧ ∀ cl, UOrdEq M T ξ (e cl ^ m₁) ((m₂ : ℤ) * T.be (π (μ cl)) (π (μ cl))).toNat := by
  first | exact @GlobalTheory.unitaryStepA_at_point | exact GlobalTheory.unitaryStepA_at_point | (intros; apply GlobalTheory.unitaryStepA_at_point <;> assumption)
end

