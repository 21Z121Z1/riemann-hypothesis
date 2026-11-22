import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2260
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingDualNumber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLatticeLAdicReduction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMPowerIsogeny

theorem exists_mem_condQ {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣) {l : ℕ} (hl : l.Prime)
    (Q : Finset (HeightOneSpectrum (OF E))) (hQ : ∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) :
    condQ 𝔣 Q ≠ ⊥ ∧ ∃ m : ℕ, ¬ l ∣ m ∧ ((l ^ a0 𝔣 l * m : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  have hc : condQ 𝔣 Q ≠ ⊥ := mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  refine ⟨hc, ?_⟩
  have hN : Ideal.absNorm (condQ 𝔣 Q) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  obtain ⟨k, m, hlm, hkm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN l hl.one_lt.ne'
  refine ⟨m, hlm, ?_⟩
  set x : OF E := ((l ^ a0 𝔣 l * m : ℕ) : OF E) with hx
  let J : Ideal (OF E) := Submodule.comap (LinearMap.mulRight (OF E) x) (condQ 𝔣 Q)
  have hJ : ∀ r, r ∈ J ↔ r * x ∈ condQ 𝔣 Q := fun r => Iff.rfl
  by_contra hne
  have hJt : J ≠ ⊤ := fun h => hne (by simpa using (hJ 1).1 (h ▸ Submodule.mem_top))
  obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJt
  have hlk : ((l : OF E)) ^ k ∈ J := by
    rw [hJ, hx]
    have h1 := Ideal.absNorm_mem (condQ 𝔣 Q)
    rw [hkm] at h1
    have h2 := Ideal.mul_mem_left _ ((l : OF E) ^ a0 𝔣 l) h1
    convert h2 using 1
    push_cast; ring
  have hlP : (l : OF E) ∈ P := hP.isPrime.mem_of_pow_mem k (hJP hlk)
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hlP))
  let v : HeightOneSpectrum (OF E) := ⟨P, hP.isPrime, hP0⟩
  obtain ⟨J', hJ', hnd⟩ := (FiniteMultiplicity.of_prime_left v.prime h𝔣.1).exists_eq_pow_mul_and_not_dvd
  have hle : expIn 𝔣 v ≤ a0 𝔣 l := by
    refine le_csSup ⟨2, ?_⟩ ⟨v, hlP, rfl⟩
    rintro _ ⟨w, -, rfl⟩
    by_cases hw : w.asIdeal ∣ 𝔣
    · exact (h𝔣.2.2 w hw).2.1
    · rw [expIn, multiplicity_eq_zero.2 hw]; omega
  have hnd' : ¬ (J' * ∏ q ∈ Q, q.asIdeal) ≤ P := by
    intro h
    rcases hP.isPrime.mul_le.1 h with h | h
    · exact hnd (Ideal.dvd_iff_le.2 h)
    · obtain ⟨q, hq, hqP⟩ := (Ideal.IsPrime.prod_le hP.isPrime).1 h
      exact hQ q hq (by rw [q.isMaximal.eq_of_le hP.ne_top hqP]; exact hlP)
  refine hnd' fun r hr => hJP ?_
  rw [hJ, hx, condQ]
  have h1 : (l : OF E) ^ a0 𝔣 l ∈ v.asIdeal ^ multiplicity v.asIdeal 𝔣 :=
    Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hlP _)
  have h2 := Ideal.mul_mem_right (m : OF E) _ (Ideal.mul_mem_mul h1 hr)
  rw [← _root_.mul_assoc, ← hJ'] at h2
  convert h2 using 1
  push_cast; ring

theorem sz_inv_pow_mul (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (a m : ℕ) (hm : ¬ l ∣ m) :
    Sz l lam a (((l ^ a * m : ℕ) : ℂ)⁻¹) := by
  refine ⟨inv_mem (natCast_mem _ _), ?_⟩
  have e : (⟨((l ^ a * m : ℕ) : ℂ)⁻¹, inv_mem (natCast_mem _ _)⟩ : algebraicClosure ℚ ℂ) =
      ((l ^ a * m : ℕ) : algebraicClosure ℚ ℂ)⁻¹ := Subtype.ext (by simp)
  have hn : ∀ n : ℕ, ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := fun n => by
    rw [← norm_algebraMap' ℂ_[l] (n : ℚ_[l]), map_natCast]
  have h1 : ‖(m : ℚ_[l])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm)
  rw [e, map_inv₀, map_natCast, norm_inv, hn, Nat.cast_mul, norm_mul, h1, Nat.cast_pow, norm_pow, Padic.norm_p]
  simp

theorem exists_separating (E : Type) [Field E] [NumberField E] :
    ∃ θ : 𝓞 E, ∀ σ τ : E →+* ℂ, σ θ = τ θ → σ = τ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨m, hm, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic α)).exists_integral_multiple
  refine ⟨⟨m • α, hint⟩, fun σ τ h => ?_⟩
  have h1 : σ α = τ α := by
    have h2 : σ (m • α) = τ (m • α) := h
    rw [map_zsmul, map_zsmul] at h2
    exact smul_right_injective ℂ hm h2
  have h3 : σ.toRatAlgHom = τ.toRatAlgHom := by
    have := (Field.primitive_element_iff_algHom_eq_of_eval' ℚ ℂ (fun x => IsAlgClosed.splits _) α).1 hα
    exact this h1
  exact RingHom.ext fun x => DFunLike.congr_fun h3 x

theorem exists_kill (A B : CategoryTheory.Over (Sp ℂ)) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (ψ : A ⟶ B) [IsMonHom ψ] [IsFinite ψ.left] :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ (T : CategoryTheory.Over (Sp ℂ)) (x : T ⟶ A), x ≫ ψ = 1 → x ^ n = 1 := by
  have := hB.proper
  have := hA.proper
  have := hA.comm
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := GlobalTheory.IsogenyModel.exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main ℂ Z hZ inferInstance
  refine ⟨N, hN, fun T x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem exists_isogeny : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ))
    (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (A' : Over (Sp ℂ)) [GrpObj A'] (L' : LB A'.left)
    (u : HolUnif A' L' (Module.finrank ℚ (FR E))), IsAbelianScheme A' →
    SmoothOfRelativeDimension (Module.finrank ℚ (FR E)) A'.hom → (∀ w, w ∈ u.Λ ↔ ∀ j, w j ∈ Λ.lattice) →
    ∀ j₀ : Fin (Module.finrank ℚ (FR E)),
    ∃ (α : A' ⟶ X.A) (M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ)) (n N : ℕ),
      IsMonHom α ∧ IsFinite α.left ∧ Flat α.left ∧ Surjective α.left ∧ 1 ≤ N ∧
      (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) ∧ (∀ w, U.u.ex (M w) = u.ex w ≫ α) ∧
      M (Pi.single j₀ 1) = (fun _ ↦ (n : ℂ)) ∧ 0 < n ∧ Sz l lam (a0 𝔣 l) ((n : ℂ)⁻¹) := by
  intro E _ _ _ _ I _ d φ hφ 𝔣 Λ h𝔣 hΛ l _ Q _ hQ y hy lam 𝔠 X U A' _ L' u hA' hg hu j₀
  classical
  have hl : l.Prime := Fact.out
  obtain ⟨-, -, -, -, -, -, hCM, ω, -, hω⟩ := hφ
  obtain ⟨hc, m, hm, hmc⟩ := exists_mem_condQ h𝔣 hl Q hQ
  obtain ⟨m', hm', -, hm'L⟩ := GlobalTheory.CMVal.LatLoc.lattice_near_orderC E _ hc l hl y hy
  have hmm : ¬ l ∣ m * m' := fun h =>
    (hl.dvd_mul.1 h).elim hm ((Nat.Prime.coprime_iff_not_dvd hl).1 hm'.symm)
  set n : ℕ := l ^ a0 𝔣 l * (m * m') with hn
  have hn0 : 0 < n := Nat.mul_pos (pow_pos hl.pos _) (Nat.pos_of_ne_zero fun h => hmm (h ▸ dvd_zero l))
  have hnL : ∀ b : 𝓞 E, (n : E) * (b : E) ∈ lattice (condQ 𝔣 Q) y := fun b => by
    have h1 := hm'L (((l ^ a0 𝔣 l * m : ℕ) : E) * (b : E)) (mem_orderC.2 ⟨0, _, Ideal.mul_mem_right b _
      (Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) hmc), by rw [map_zero, zero_add, map_mul, map_natCast, map_natCast]⟩)
    convert h1 using 1
    rw [hn]; push_cast; ring
  obtain ⟨θ, hθ⟩ := exists_separating E
  have hinj : Function.Injective fun k => φ (U.e k) (θ : E) := fun k k' h => by
    have h1 := hθ _ _ h
    exact U.e.injective ((hCM (φ (U.e k))).unique (Or.inl rfl) (Or.inl h1))
  let z : Fin (Module.finrank ℚ (FR E)) := ⟨0, j₀.pos⟩
  let s := Equiv.swap j₀ z
  let V : Matrix (Fin (Module.finrank ℚ (FR E))) (Fin (Module.finrank ℚ (FR E))) ℂ :=
    (n : ℂ) • (Matrix.vandermonde fun k => φ (U.e k) (θ : E)).submatrix id s
  have hV : V.det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_permute']
    refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn0.ne')) (mul_ne_zero ?_ ?_)
    · exact_mod_cast Units.ne_zero _
    · exact Matrix.det_vandermonde_ne_zero_iff.2 hinj
  have hVe : ∀ x k, Matrix.toLin' V x k = ∑ j, (n : ℂ) * φ (U.e k) (θ : E) ^ (s j : ℕ) * x j := fun x k => rfl
  have hsurj : Function.Surjective (Matrix.toLin' V) := fun w =>
    ⟨V⁻¹.mulVec w, by rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hV),
      Matrix.one_mulVec]⟩
  have hlift : ∀ x ∈ Λ.lattice, ∃ b : 𝓞 E, ∀ i, φ i (b : E) = x := fun x hx => by
    obtain ⟨hint, a, b, hab⟩ := (hΛ x).1 hx
    have h1 : ∀ i, φ i ((a : E) + (b : E) * ω) = x := fun i => by
      rw [map_add, map_mul, map_ratCast, map_ratCast, hω, hab]
    refine ⟨⟨(a : E) + (b : E) * ω, ?_⟩, h1⟩
    rw [← h1 (U.e j₀)] at hint
    exact (isIntegral_algHom_iff (φ (U.e j₀)).toIntAlgHom (φ (U.e j₀)).injective).1 hint
  have hM : ∀ x ∈ u.Λ, Matrix.toLin' V x ∈ U.u.Λ := fun x hx => by
    choose b hb using fun j => hlift (x j) ((hu x).1 hx j)
    refine (U.lat _).2 ⟨_, hnL (∑ j, θ ^ (s j : ℕ) * b j), funext fun k => ?_⟩
    have e : ((∑ j, θ ^ (s j : ℕ) * b j : 𝓞 E) : E) = ∑ j, (θ : E) ^ (s j : ℕ) * (b j : E) := by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, map_pow]
    rw [hVe, e, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, Pi.zero_apply, zero_mul, add_zero, map_mul, map_natCast, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hb, _root_.mul_assoc]
  obtain ⟨α, hα, hαe⟩ := GlobalTheory.HolUnifHom.exists_isMonHom_of_map_lattice A' X.A _ hA' X.ab hg X.dim L' _ u U.u
    (Matrix.toLin' V) hM
  haveI : Surjective α.left := GlobalTheory.ComplexAbVarSurj.surjective_of_surjective_points A' X.A α hA' X.ab fun p => by
    obtain ⟨w, rfl⟩ := U.u.ex_onto p
    obtain ⟨w', rfl⟩ := hsurj w
    exact ⟨u.ex w', (hαe w').symm⟩
  obtain ⟨hfin, hflat⟩ := GlobalTheory.SurjHomFlat.finite_flat A' X.A _ hA' X.ab hg X.dim α
  obtain ⟨N, hN, hkill⟩ := exists_kill A' X.A hA' X.ab α
  refine ⟨α, Matrix.toLin' V, n, N, hα, hfin, hflat, inferInstance, hN, hkill, hαe, funext fun k => ?_, hn0,
    sz_inv_pow_mul l lam _ _ hmm⟩
  rw [hVe, Finset.sum_eq_single j₀ (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero]) (by simp), Pi.single_eq_same,
    show s j₀ = z from Equiv.swap_apply_left _ _]
  simp [z]

end GlobalTheory.CMPowerIsogeny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelLocallyNoetherian
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.ModelNoeth

theorem isLocallyNoetherian_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ),
    p.Prime → (p : ℂ) ∈ W.nonunits → IsLocallyNoetherian Y.X := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ _
  obtain ⟨⟨_, hD⟩, -, -⟩ :=
    (GlobalTheory.CoeffValuation.isDedFrac_and_isOpenImmersion E H l' c' (c'.V W)).1
  haveI : IsNoetherianRing (c'.V W) := hD.toIsNoetherian
  obtain ⟨N, i, hi, hcomp⟩ := Y.proj
  haveI := hi
  haveI := isProper_str (c'.V W) N
  haveI : LocallyOfFiniteType (i ≫ PSpace.str (c'.V W) N) := inferInstance
  haveI : LocallyOfFiniteType Y.s := hcomp ▸ this
  exact LocallyOfFiniteType.isLocallyNoetherian Y.s

end GlobalTheory.ModelNoeth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicOverInclusionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_p_adic_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] [Algebra c.F ℂ_[p]] (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c')
      (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (y : FrPt Xo c ℂ_[p]),
      HTAt Y r ν yb yy P π ψ y →
    ∀ (z : FrPt Xo c ℂ_[p]) (gm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ_[p]) (am : ℂ_[p])
      (x : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → LieG P.Gt), GlobalTheory.Frames.FrChg gm am z y →
      (∀ τ j, LieTie P (ψ ≫ ν.φ) (x τ j) (z.u τ j)) →
    ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)), IsTanBasis Y.t yb e →
    ∀ (xb : Fin g → LieG P.Gt), (∀ b, ITie P π (xb b) (e b)) →
    ∀ (σ : E →+* ℂ) (U : Fin g → 𝓞_ℂ_[p]), (∀ u, IsCombAtG Y.t yb e U u → IsEigG Y.t (β.comp (embV c' W σ)) u) →
    ∃ (w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left) (cf : Fin (Dw.mult σ) → ℂ_[p]),
      IsCombAtG Y.t (yy ≫ Y.j) (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun b => (U b : ℂ_[p])) (w ≫ Y.m.φ) ∧
      IsCombAt y.x (y.u σ) cf (w ≫ ν.φ) ∧
      ∑ b, (U b : ℂ_[p]) • P.bLie (xb b) = ∑ j, cf j • ∑ l, gm σ j l • P.bLie (x σ l) := by
  first | exact @GlobalTheory.FlatModel.htComb_lift | exact GlobalTheory.FlatModel.htComb_lift | (intros; apply GlobalTheory.FlatModel.htComb_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelTangentOverInclusionStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_model_tangent_over_inclusion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F), OverIncl r hle →
    ∀ (τ : Psi H) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A), ξ ≫ Y.s = spMap β →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
    ∀ (L : Type) [CommRing L] [IsLocalRing L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∃ (_ : Algebra c.F L) (z : FrPt Xo c L) (w₁ : Fin (Dw.mult τ.1) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left))
      (w₂ : Fin (Dw.mult (conjEmb τ.1)) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left)),
      ptF z = yL ≫ r ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₁ i b)) (w₁ i ≫ Y.m.φ)) ∧
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U₂ i b)) (w₂ i ≫ Y.m.φ)) ∧
      (∀ i, z.u τ.1 i = w₁ i ≫ ν.φ) ∧ ∀ i, z.u (conjEmb τ.1) i = w₂ i ≫ ν.φ := by
  first | exact @GlobalTheory.FlatModel.FrameLoc.exists_frPt_of_chart | exact GlobalTheory.FlatModel.FrameLoc.exists_frPt_of_chart | (intros; apply GlobalTheory.FlatModel.FrameLoc.exists_frPt_of_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointClosureExtension
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.IntPt

theorem top_le_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (t : Sp R ⟶ X) {W : X.Opens}
    (h : t (IsLocalRing.closedPoint R) ∈ W) : ⊤ ≤ t ⁻¹ᵁ W := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map t.continuous).mem_open W.isOpen h

theorem w_eq_one_iff {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (c : e.O) :
    e.w c = 1 ↔ IsUnit c :=
  ⟨fun h => RegCrit.isUnit_of_one_le e c h.ge, fun h => OfModel.w_unit e h⟩

open GlobalTheory.TrueGeo.HorizPt in

theorem exists_intPt : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (W : V.X.Opens) (x : V.X), x ∈ W → (l : 𝓞 F) ∈ (V.p x).asIdeal → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal ∧ z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ x ⤳ yt (IsLocalRing.closedPoint e.O) ∧ ∀ g : V.X.functionField, RegAt (yt (IsLocalRing.closedPoint e.O)) g → (e.w (TrueGeo.valAt (z ≫ V.j) g) = 1 ↔ UnitAt (yt (IsLocalRing.closedPoint e.O)) g) := by
  intro F _ _ Y V l W x hx hl
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨x, hxU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, -⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 1 one_ne_zero
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  have hc : yt (IsLocalRing.closedPoint e.O) = hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩ := by
    change hU.fromSpec (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O)) = _
    congr 1
    exact PrimeSpectrum.ext h₂
  have hsp : x ⤳ yt (IsLocalRing.closedPoint e.O) := by
    have h0 : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) ⤳ hU.fromSpec ⟨𝔪, h𝔪.isPrime⟩ :=
      ((PrimeSpectrum.le_iff_specializes _ ⟨𝔪, h𝔪.isPrime⟩).1 hle').map hU.fromSpec.continuous
    rw [hU.fromSpec_primeIdealOf] at h0
    rw [hc]
    exact h0
  have hl' : algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F) ∈ 𝔪 := by
    apply hle'
    have e1 : V.p x = (Spec.map (HorizPt.strHom V.p U)) (hU.primeIdealOf ⟨x, hxU⟩) := by
      rw [← fromSpec_str V.p hU]
      change V.p x = V.p (hU.fromSpec _)
      rw [hU.fromSpec_primeIdealOf]
    rw [e1] at hl
    exact hl
  have hv : (l : 𝓞 F) ∈ v.asIdeal := by
    have hm : φ (algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F)) ∈ IsLocalRing.maximalIdeal e.O := by
      rw [← Ideal.mem_comap, h₂]
      exact hl'
    have hlt : e.w ((φ (algebraMap (𝓞 F) Γ(V.X, U) (l : 𝓞 F)) : e.O) : AlgebraicClosure F) < 1 := by
      refine lt_of_le_of_ne ((e.mem_O _).1 (φ _).2) fun h => ?_
      exact (IsLocalRing.mem_maximalIdeal _).1 hm (RegCrit.isUnit_of_one_le e _ h.ge)
    rw [h₁, e.w_alg] at hlt
    exact (v.adicAbv_coe_lt_one_iff _ _).1 hlt
  refine ⟨v, e, V.pb.lift _ _ hw, yt, hv, V.pb.lift_snd _ _ hw, hy.symm, ?_, hsp, ?_⟩
  · intro p _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro g hg
    obtain ⟨W₀, hW₀, s, hs⟩ := hg.exists_fnOf
    have ht : ⊤ ≤ yt ⁻¹ᵁ W₀ := top_le_of_closedPoint yt hW₀
    have hb : below (V.pb.lift _ _ hw ≫ V.j) ∈ W₀ := by
      change (V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ W₀
      rw [hy]
      exact ht trivial
    have ht' : ⊤ ≤ (V.pb.lift _ _ hw ≫ V.j) ⁻¹ᵁ W₀ := fun p _ => by
      change (V.pb.lift _ _ hw ≫ V.j) p ∈ W₀
      rw [hy]
      exact ht (x := spMap e.O.subtype p) trivial
    have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (V.pb.lift _ _ hw ≫ V.j) yt
      (hy.symm.trans (Category.comp_id _).symm) (U := W₀) (W := W₀) le_rfl ht' ht s
    have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE W₀ W₀ le_rfl).hom s = s := by
      have : (𝟙 V.X : V.X ⟶ V.X).appLE W₀ W₀ le_rfl = 𝟙 _ :=
        (Category.id_comp _).trans (V.X.presheaf.map_id _)
      rw [this]
      rfl
    rw [hid] at hev
    rw [← hs, OfModel.valAt_fnOf _ hb ht', hev, unitAt_fnOf_iff hW₀, ← RegCrit.isUnit_eval_iff yt ht s]
    exact w_eq_one_iff e _

end GlobalTheory.HtGen.IntPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjectiveStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantOneForms_abelianScheme_finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  first | exact @GlobalTheory.InvFormProj.finite_projective | exact GlobalTheory.InvFormProj.finite_projective | (intros; apply GlobalTheory.InvFormProj.finite_projective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantVectorFieldEvalOriginEqTangentDerivativStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CoordsOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantVectorField_eval_origin_eq_tangentDerivative : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G) (dd : Fld G.left), IsInv G v dd → ∀ (O : G.left.Opens) (hO : origin G ∈ O) (f : Γ(G.left, O)), evO G ((G.left.presheaf.germ O (origin G) hO).hom (dd O f)) = tanDer G v ((G.left.presheaf.germ O (origin G) hO).hom f) := by
  first | exact @GlobalTheory.CoordsOrigin.evO_germ_of_isInv | exact GlobalTheory.CoordsOrigin.evO_germ_of_isInv | (intros; apply GlobalTheory.CoordsOrigin.evO_germ_of_isInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceFibreSemiAbelianFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SemiAbFibre

theorem irreducibleSpace_fibre : ∀ (T : Scheme.{0}) (G : Over T) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ T), IrreducibleSpace (pullback G.hom x : Scheme.{0}) := by
  intro T G _ hG Ω _ x
  have := hG.smooth
  have := hG.geomConnected
  have h : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral (pullback G.hom x : Scheme.{0}) :=
    h.geometrically_isIntegral _ _ _ (IsPullback.of_hasPullback G.hom x)
  infer_instance

end GlobalTheory.SemiAbFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_inf_of_separated_over_affineOpen : ∀ {X Z : Scheme.{0}} (h : Z ⟶ X) [IsSeparated h] (U : X.affineOpens) (Ω₁ Ω₂ : Z.affineOpens), Ω₁.1 ≤ h ⁻¹ᵁ U.1 → Ω₂.1 ≤ h ⁻¹ᵁ U.1 → IsAffineOpen (Ω₁.1 ⊓ Ω₂.1) := by
  first | exact @GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage | exact GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage | (intros; apply GlobalTheory.SepAffInf.isAffineOpen_inf_of_le_preimage <;> assumption)
end

