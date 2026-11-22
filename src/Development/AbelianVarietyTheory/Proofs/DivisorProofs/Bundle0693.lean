import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0137
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalities
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulProdChoose

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTorsionSubgroupUniversal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_torsion_subgroup_universal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r r' : ℕ), r ≤ r' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Etale H.hom → (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → ∃ (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom ∧ Etale K.hom ∧ (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le) | (exact GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_rep_pow_of_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvResCounitCompat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.EvRes

theorem comp_eval_eq {σ O A A' : Type} [Fintype σ] [CommRing O] [CommRing A] [CommRing A']
    [Algebra O A] [Algebra O A'] (p : ℕ) [IsHausdorff (Ideal.span {(p : A')}) A']
    (g : A →ₐ[O] A') (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A) (hE : IsEval p x E)
    (ψ : MvPowerSeries σ O →+* A') (hC : ∀ c, ψ (C c) = algebraMap O A' c)
    (hX : ∀ i, ψ (X i) = g (x i))
    (hψ : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A') ^ m ∣ ψ f)
    (f : MvPowerSeries σ O) : g (E f) = ψ f :=
  CEval.ext_of_cont p ((g : A →+* A').comp (E : MvPowerSeries σ O →+* A)) ψ
    (fun c => by
      show g (E (C c)) = ψ (C c)
      rw [hC, c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes])
    (fun i => by
      show g (E (X i)) = ψ (X i)
      rw [hX, hE.1])
    (fun m => by
      obtain ⟨N, hN⟩ := hE.2 m
      exact ⟨N, fun f hf => by
        show (p : A') ^ m ∣ g (E f)
        have := map_dvd g (hN f hf)
        rwa [map_pow, map_natCast] at this⟩)
    hψ f

theorem constantCoeff_cont {σ O : Type} [CommRing O] (p : ℕ) :
    ∀ m : ℕ, ∃ N : ℕ, ∀ f : MvPowerSeries σ O, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : O) ^ m ∣ constantCoeff f := fun _ =>
  ⟨1, fun f hf => by
    rw [← coeff_zero_eq_constantCoeff_apply, hf 0 (by simp)]
    exact dvd_zero _⟩

end GlobalTheory.EvRes

open GlobalTheory.EvRes in

theorem GlobalTheory.QLog.Chart.ev_res_counit : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n, (∀ f, G.res n (c.ev (n + 1) f) = c.ev n f ∧ Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O (G.A n)) (Bialgebra.counitAlgHom O (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  intro p O _ _ G d c n
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) :=
    FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n)
  refine ⟨fun f => ⟨?_, ?_⟩, fun s => ?_⟩
  · exact comp_eval_eq p (G.res n : G.A (n + 1) →ₐ[O] G.A n) (c.x (n + 1)) (c.ev (n + 1))
      (c.isEval (n + 1)) (c.ev n : MvPowerSeries (Fin d) O →+* G.A n)
      (fun a => by rw [c_eq_algebraMap]; exact (c.ev n).commutes a)
      (fun i => by
        show c.ev n (X i) = G.res n (c.x (n + 1) i)
        rw [(c.isEval n).1, c.res])
      (c.isEval n).2 f
  · exact comp_eval_eq p (Bialgebra.counitAlgHom O (G.A n)) (c.x n) (c.ev n) (c.isEval n)
      constantCoeff (fun a => by rw [constantCoeff_C]; rfl)
      (fun i => by
        rw [constantCoeff_X]
        exact (c.aug n i).symm)
      (constantCoeff_cont p) f
  · exact comp_eval_eq p _ _ (c.ev₂ n) (c.isEval₂ n) constantCoeff
      (fun a => by rw [constantCoeff_C]; rfl)
      (fun i => by
        rw [constantCoeff_X]
        rcases i with i | i <;> simp [Bialgebra.counitAlgHom_apply, c.aug n i])
      (constantCoeff_cont p) s
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineMapNeTopStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_map_maximal_proper : ∀ (R' : Type) [CommRing R'] (X X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), Surjective s' → ∀ m : Ideal R', m.IsMaximal → ∃ U : X.affineOpens, Ideal.map (algebraMap R' (Sec s' (φ ⁻¹ᵁ U.1))) m ≠ ⊤ := by
  first | exact @GlobalTheory.PointSec.exists_affine_map_ne_top | exact GlobalTheory.PointSec.exists_affine_map_ne_top | (intros; apply GlobalTheory.PointSec.exists_affine_map_ne_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfFrameLiftTwistedFrobeniusStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ainf_frame_lift_twisted_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ u : F.B, F.τ ∣ u - 1 → ∃ l : F.B, F.τ ∣ l - 1 ∧ F.σ l = u * l := by
  first | exact @GlobalTheory.FLam.exists_lam | exact GlobalTheory.FLam.exists_lam | (intros; apply GlobalTheory.FLam.exists_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomAlgebraicClosureApplyEqPow
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_algHom_algebraicClosure_apply_eq_pow :
    ∀ (Ω : Type) [Field Ω] (K0 : Subfield Ω) (x : Ω), Transcendental K0 x → ∀ m : ℕ, 0 < m →
      ∃ τ : Ω →ₐ[K0] AlgebraicClosure Ω, τ x = algebraMap Ω (AlgebraicClosure Ω) x ^ m := by
  intro Ω _ K0 x hx m hm
  classical
  have h1 : AlgebraicIndepOn K0 id ({x} : Set Ω) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let i₀ : s := ⟨x, hxs rfl⟩
  have h2 := (algebraicIndependent_update_pow hs.1 i₀ hm).map'
    (f := IsScalarTower.toAlgHom K0 Ω (AlgebraicClosure Ω))
    (algebraMap Ω (AlgebraicClosure Ω)).injective
  obtain ⟨j, hj⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hs h2
  exact ⟨j, by simpa [i₀] using hj i₀⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAutCentre
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.ThmAMove

section Val

variable {K : Type} [Field K] (A : ValuationSubring K)

theorem exists_ext {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) [IsAlgClosed K] (jk : FractionRing R →+* K) :
    ∃ je : FractionRing S →+* K, ∀ x, je (IsFractionRing.map (j := algebraMap R S) hinj x) = jk x := by
  let k : FractionRing R →+* FractionRing S := IsFractionRing.map (j := algebraMap R S) hinj
  letI : Algebra (FractionRing R) (FractionRing S) := k.toAlgebra
  letI : Algebra (FractionRing R) K := jk.toAlgebra
  have hi : ∀ a : S, IsIntegral (FractionRing R) (algebraMap S (FractionRing S) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap R (FractionRing R)) (algebraMap S (FractionRing S))
      (RingHom.ext fun r => by
        show k (algebraMap R _ r) = _
        simp [k, IsFractionRing.map]) (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    rw [div_eq_mul_inv]
    exact ((hi a).mul (hi b).inv).isAlgebraic⟩
  let j : FractionRing S →ₐ[FractionRing R] K := IsAlgClosed.lift
  exact ⟨j.toRingHom, fun x => j.commutes x⟩

theorem exists_unit {S : Type} [CommRing S] [IsDomain S] [ValuationRing S] (je : FractionRing S →+* K)
    (hA : ∀ a : S, je (algebraMap S _ a) ∈ A) (hu : ∀ a : S, A.valuation (je (algebraMap S _ a)) = 1 → IsUnit a)
    {x y : FractionRing S} (h : A.valuation (je x) = A.valuation (je y)) : ∃ u : Sˣ, x = algebraMap S _ (u : S) * y := by
  by_cases hy : y = 0
  · subst hy
    refine ⟨1, ?_⟩
    simpa using h
  have hy' : A.valuation (je y) ≠ 0 := by simpa using hy
  have h1 : A.valuation (je (x / y)) = 1 := by rw [map_div₀, map_div₀, h, div_self hy']
  rcases ValuationRing.isInteger_or_isInteger S (x / y) with ⟨a, ha⟩ | ⟨a, ha⟩
  · obtain ⟨u, rfl⟩ := hu a (by rw [ha, h1])
    exact ⟨u, by rw [ha, div_mul_cancel₀ _ hy]⟩
  · obtain ⟨u, rfl⟩ := hu a (by rw [ha, map_inv₀, map_inv₀, h1, inv_one])
    refine ⟨u⁻¹, ?_⟩
    rw [map_units_inv, ha, inv_inv, div_mul_cancel₀ _ hy]

theorem mem_max_iff {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (f : R →+* K) (hf : ∀ r, f r ∈ A) {l : ℕ}
    (hl0 : (l : K) ≠ 0) (hl : A.valuation (l : K) < 1) (a : R) :
    a ∈ IsLocalRing.maximalIdeal R ↔ A.valuation (f a) < 1 := by
  have hle : ∀ r, A.valuation (f r) ≤ 1 := fun r => (A.valuation_le_one_iff _).2 (hf r)
  constructor
  · intro ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have h0 : (l : R) ≠ 0 := fun h => hl0 (by rw [← map_natCast f, h, map_zero])
    obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
    have hd : (l : R) ∣ a ^ n := by
      rw [hn, Units.mul_left_dvd]
      exact pow_dvd_pow_of_dvd ha n
    obtain ⟨c, hc⟩ := hd
    refine lt_of_le_of_ne (hle a) fun h1 => ?_
    have h2 := congrArg (fun r => A.valuation (f r)) hc
    simp only [map_pow, map_mul, map_natCast, h1, one_pow] at h2
    exact absurd h2 (mul_lt_one_of_lt_of_le hl (hle c)).ne'
  · intro h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, rfl⟩
    have h2 : A.valuation (f u) * A.valuation (f (u⁻¹ : Rˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    exact absurd h2 (mul_lt_one_of_lt_of_le h (hle _)).ne

variable {L : Type} [Field L] [NumberField L]

theorem int_le_one (β : L →+* K) (x : 𝓞 L) : A.valuation (β x) ≤ 1 := by
  rw [A.valuation_le_one_iff]
  have h : IsIntegral A (β x) := IsIntegral.map_of_comp_eq (Int.castRingHom A) β (RingHom.ext_int _ _) x.isIntegral_coe
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact hy ▸ y.2

theorem unit_of_centre (β : L →+* K) (P : HeightOneSpectrum (𝓞 L)) (h : ∀ x : 𝓞 L, A.valuation (β x) < 1 ↔ x ∈ P.asIdeal)
    (y : L) (hy : P.valuation L y = 1) : A.valuation (β y) = 1 := by
  obtain ⟨n, d, e⟩ := P.exists_primeCompl_mul_eq_of_integer y hy.le
  have h1 : ∀ x : 𝓞 L, x ∉ P.asIdeal → A.valuation (β x) = 1 := fun x hx =>
    le_antisymm (int_le_one A β x) (not_lt.1 fun h' => hx ((h x).1 h'))
  have hd : P.valuation L (algebraMap (𝓞 L) L d) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 d.2
  have hn : n ∉ P.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := L)]
    show P.valuation L (algebraMap (𝓞 L) L n) = 1
    rw [← e, map_mul, hy, hd, one_mul]
  have h2 := congrArg (fun r => A.valuation (β r)) e
  simp only [map_mul] at h2
  rw [show A.valuation (β (algebraMap (𝓞 L) L d)) = 1 from h1 _ d.2, show A.valuation (β (algebraMap (𝓞 L) L n)) = 1 from h1 _ hn,
    mul_one] at h2
  exact h2

theorem val_eq_of_unit (α β : L →+* K) (P : HeightOneSpectrum (𝓞 L)) {l : ℕ} (hl0 : l ≠ 0) (hl : P.valuation L (l : L) ≠ 1)
    (hα : ∀ y, P.valuation L y = 1 → A.valuation (α y) = 1) (hβ : ∀ y, P.valuation L y = 1 → A.valuation (β y) = 1) (x : L) :
    A.valuation (α x) = A.valuation (β x) := by
  by_cases hx : x = 0
  · simp [hx]
  have hl1 : (l : L) ≠ 0 := Nat.cast_ne_zero.2 hl0
  have e1 : P.valuation L x = WithZero.exp (WithZero.log (P.valuation L x)) := (WithZero.exp_log (by simpa using hx)).symm
  have e2 : P.valuation L (l : L) = WithZero.exp (WithZero.log (P.valuation L (l : L))) :=
    (WithZero.exp_log (by simpa using hl1)).symm
  generalize WithZero.log (P.valuation L x) = n at e1
  generalize WithZero.log (P.valuation L (l : L)) = e at e2
  have he : e ≠ 0 := by
    rintro rfl
    exact hl e2
  have hy : P.valuation L (x ^ e * (l : L) ^ (-n)) = 1 := by
    rw [map_mul, map_zpow₀, map_zpow₀, e1, e2, ← WithZero.exp_zsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [mul_comm]
  have h1 := (hα _ hy).trans (hβ _ hy).symm
  simp only [map_mul, map_zpow₀, map_natCast] at h1
  have h0 : A.valuation (l : K) ^ (-n) ≠ 0 := zpow_ne_zero _ (by
    rw [← map_natCast α, map_ne_zero, map_ne_zero]; exact hl1)
  exact (zpow_left_inj₀ zero_le' zero_le' he).1 (mul_right_cancel₀ h0 h1)

theorem exists_aut_centre [IsGalois ℚ L] (L0 : IntermediateField ℚ L) (β : L →+* K) (P : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L0, A.valuation (β ((x : L0) : L)) < 1 ↔ algebraMap (𝓞 L0) (𝓞 L) x ∈ P.asIdeal) :
    ∃ σ : L ≃ₐ[L0] L, ∀ x : 𝓞 L, A.valuation (β (σ x)) < 1 ↔ x ∈ P.asIdeal := by
  let f : 𝓞 L →+* A := (β.comp (algebraMap (𝓞 L) L)).codRestrict A fun x => (A.valuation_le_one_iff _).1 (int_le_one A β x)
  let P' : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP' : ∀ x : 𝓞 L, x ∈ P' ↔ A.valuation (β x) < 1 := fun x => A.valuation_lt_one_iff (f x)
  haveI : P'.IsPrime := Ideal.comap_isPrime _ _
  haveI := P.isPrime
  haveI : P'.LiesOver (P.asIdeal.under (𝓞 L0)) := ⟨Ideal.ext fun x => ((hP' (algebraMap (𝓞 L0) (𝓞 L) x)).trans (h x)).symm⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (P.asIdeal.under (𝓞 L0)) P.asIdeal P' (L ≃ₐ[L0] L)
  refine ⟨σ, fun x => ?_⟩
  rw [← Ideal.smul_mem_pointwise_smul_iff (a := σ), hσ, hP']
  rfl

end Val

theorem exists_symbol {K Ω : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field Ω] [Algebra K Ω]
    {art : Ideles K →* Gab K Ω} (ha : IsGlobalArtin art) (σ : Formalism.ConjugateSelfDual.G K Ω) :
    ∃ t, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol art t σ := by
  obtain ⟨x, hx⟩ := ha.quot.surjective (toAb K Ω σ)⁻¹
  let t : (Af K)ˣ := Units.map (MonoidHom.snd (InfiniteAdeleRing K) (Af K)) x
  let y : (InfiniteAdeleRing K)ˣ := Units.map (MonoidHom.fst (InfiniteAdeleRing K) (Af K)) x
  have hy : y ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing K)ˣ := by
    let T : Set (InfiniteAdeleRing K) := Set.univ.pi fun w => {0}ᶜ
    have hS : ∀ w : InfinitePlace K, IsPreconnected ({0}ᶜ : Set w.Completion) := fun w => by
      have hw := IsTotallyComplex.isComplex w
      have := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isPreconnected_preimage.2
        (isConnected_compl_singleton_of_one_lt_rank (E := ℂ) (by simp) 0).isPreconnected
      convert this using 1
      ext z
      exact (map_ne_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw)).symm
    have hp : IsPreconnected ((Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T) := by
      rw [← (isOpenEmbedding_val_inf K).isInducing.isPreconnected_image, Set.image_preimage_eq_of_subset]
      · exact isPreconnected_univ_pi hS
      · intro y hy
        have : IsUnit y := Pi.isUnit_iff.2 fun w => IsUnit.mk0 _ (hy w trivial)
        exact this
    have hm : ∀ u : (InfiniteAdeleRing K)ˣ, u ∈ (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) ⁻¹' T :=
      fun u w _ => (Pi.isUnit_iff.1 u.isUnit w).ne_zero
    exact hp.subset_connectedComponent (hm 1) (hm y)
  let y' : Ideles K := Units.map (MonoidHom.inl (InfiniteAdeleRing K) (Af K)) y
  have h1 : art y' = 1 := by
    rw [← MonoidHom.mem_ker, ha.ker]
    exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right ⟨y, hy, rfl⟩)
  have e : x = y' * finIdele K t := by
    ext : 1
    apply Prod.ext
    · show _ = _ * 1
      rw [mul_one]; rfl
    · show _ = 1 * _
      rw [one_mul]; rfl
  refine ⟨t, ?_⟩
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.IsSymbol, inv_eq_iff_eq_inv, ← hx]
  conv_rhs => rw [e, map_mul, h1, one_mul]

theorem exists_exponent {G : Type} [CommGroup G] (ψ : G →* ℂˣ) {l n : ℕ} (hl : l.Prime) (h : ∀ q, ψ q ^ l ^ n = 1) (g : ℂ ≃+* ℂ)
    {c : ℤ} (hc : IsCoprime c (l : ℤ)) :
    ∃ a : ℤ, IsCoprime a (l : ℤ) ∧ (Units.map g.toRingHom.toMonoidHom).comp ψ = ψ ^ (c * a) := by
  have hN : l ^ (n + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ (n + 1)) := ⟨hN⟩
  have hζ := Complex.isPrimitiveRoot_exp _ hN
  generalize Complex.exp _ = ζ at hζ
  have hg : IsPrimitiveRoot (g ζ) (l ^ (n + 1)) := hζ.map_of_injective g.injective
  obtain ⟨e, -, he⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hec : e.Coprime (l ^ (n + 1)) := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero hN) e).1 (he ▸ hg)
  have hel : IsCoprime (e : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_pow_right_iff n.succ_pos _ _).1 hec)
  obtain ⟨u, v, huv⟩ : IsCoprime c ((l : ℤ) ^ (n + 1)) := hc.pow_right
  have hu : IsCoprime u (l : ℤ) := ⟨c, v * l ^ n, by rw [← huv]; ring⟩
  refine ⟨u * e, hu.mul_left hel, MonoidHom.ext fun q => ?_⟩
  have h1 : ψ q ^ l ^ (n + 1) = 1 := by rw [pow_succ, pow_mul, h, one_pow]
  have h2 : ψ q ^ (c * (u * e)) = ψ q ^ e := by
    rw [show c * (u * e) = e + ((l ^ (n + 1) : ℕ) : ℤ) * (-(v * e)) by push_cast; linear_combination (e : ℤ) * huv, zpow_add,
      zpow_mul, zpow_natCast, zpow_natCast, h1, one_zpow, mul_one]
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (ψ q : ℂ)) (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
  refine Eq.trans (Units.ext ?_) h2.symm
  show g (ψ q : ℂ) = _
  rw [Units.val_pow_eq_pow_val, ← hk, map_pow, ← he, ← pow_mul, ← pow_mul, mul_comm]

open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols in

theorem ratio_conj (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : ToricRatioConjugates)
    (E : Type) [Field E] [NumberField E] [IsCMField E]
    (K : Type) [Field K] [NumberField K] [Algebra K E] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (I : Type) [Fintype I] [Nonempty I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E)
    (h1 : UnramFin E) (h2 : Module.finrank ℚ K = 2) (h3 : 0 < d) (h4 : δ ^ 2 = -(d : K))
    (h5 : IsCMType φ) (h6 : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (h7 : 1 ≤ s) (h8 : ∀ i, 1 ≤ κ i) (h9 : IsBaseCond 𝔣) (h10 : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (h11 : IsValChar φ s κ 𝔣 ∅ χ)
    {T₀ : ℂ} {T : (PicO (condQ 𝔣 Q) →* ℂˣ) → ℂ} (hT₀ : IsToricSum φ s κ 𝔣 χ T₀)
    (hT : ∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ (T ψ)) (g : ℂ ≃+* ℂ)
    (hφ : ∀ i x, g (φ i x) = φ i x) (hχ : ∀ y, g (lamF χ s y) = lamF χ s y) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) :
    ∃ ζ : ℂˣ, IsOfFinOrder ζ ∧ g (T ψ / T₀) = (ζ : ℂ)⁻¹ * (T (conjChar g ψ) / T₀) := by
  obtain ⟨T₀', T', a1, -, a2, -, a3⟩ := hG E K d δ ι I φ s κ 𝔣 Q χ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain rfl : T₀' = T₀ := a1.unique hT₀
  obtain rfl : T' = T := funext fun ψ => (a2 ψ).unique (hT ψ)
  haveI : IsTotallyComplex K := ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.1 fun hw => by
    have h := congrArg (InfinitePlace.embedding_of_isReal hw) h4
    rw [map_pow, map_neg, map_natCast] at h
    have : (0 : ℝ) < d := by exact_mod_cast h3
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hw δ)]⟩
  let Ω := AlgebraicClosure K
  letI : Algebra K ℂ := ι.toAlgebra
  let j : Ω →ₐ[K] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower K Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have hg : ∀ x : K, g (algebraMap K ℂ x) = algebraMap K ℂ x := fun x => by
    change g (ι x) = ι x
    rw [← h6 (Classical.arbitrary I)]
    exact hφ _ _
  let gK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := g) hg
  obtain ⟨art, ha⟩ := hA K Ω
  obtain ⟨t, ht⟩ := exists_symbol ha (gK.restrictNormal Ω)
  obtain ⟨b1, b2⟩ := a3 Ω j.toRingHom art (RingHom.ext j.commutes) ha g _ t hφ hχ (gK.restrictNormal_commutes Ω) ht ψ
  exact ⟨_, b2, b1⟩

end GlobalTheory.ThmAMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualLiftLinearCoefficientsModStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  first | exact @GlobalTheory.QLog.Chart.exists_dual_lift_lin | exact GlobalTheory.QLog.Chart.exists_dual_lift_lin | (intros; apply GlobalTheory.QLog.Chart.exists_dual_lift_lin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualTangentOfCoboundaryOneEqSmulStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartierDual_tangent_of_coboundaryOne_eq_smul : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A] [Coalgebra.IsCocomm O A] (a : O) (b : A) (z : A ⊗[O] A), cobOne O A b = a • z → ∃ u : Cot O (CartierDual O A) →ₗ[O] O ⧸ Ideal.span {a}, ∀ φ : CartierDual O A, u (dUnit O φ) = Ideal.Quotient.mk _ (φ b) := by
  first | exact @GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul | exact GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul | (intros; apply GlobalTheory.PDiv.exists_tangent_of_cobOne_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePDivGroupLevelCoordinatesStatement
section
open GlobalTheory GlobalTheory.PDivGroup
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n), (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n, Submodule.span O (Set.range fun i => PDiv.dUnit O (x n i)) = ⊤) ∧ ∀ n, ∃ l : Fin d → (PDiv.Cot O (G.A n) →ₗ[O] O ⧸ Ideal.span {(p : O) ^ n}), ∀ i j, l i (PDiv.dUnit O (x n j)) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.PDiv.exists_compatible_coordinates | exact GlobalTheory.PDiv.exists_compatible_coordinates | (intros; apply GlobalTheory.PDiv.exists_compatible_coordinates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConcaveTwistEtaInequalitiesStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_concaveTwist_eta_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ η η1 η2 : ℝ → ℝ, ContDiffOn ℝ ∞ η (Set.Ioi (-1/4)) ∧ (∀ y, -1/4 < y → 0 < η y ∧ HasDerivAt η (η1 y) y ∧ HasDerivAt η1 (η2 y) y) ∧ (∀ y, 0 ≤ y → 0 ≤ η1 y ∧ η1 y ≤ 2 ∧ 2 ≤ η y ∧ η2 y < 0 ∧ η y ≤ 2 + 2 * min y (T + 1) ∧ η y + η1 y ^ 2 / (-η2 y) ≤ 8 * (1 + (min y (T + 1)) ^ 2)) ∧ (∀ y, T - 1 ≤ y → y ≤ T + 1 → 3 / 16 ≤ -η2 y ∧ T ≤ η y) := by
  first | exact @GlobalTheory.concave_twist_exists | exact GlobalTheory.concave_twist_exists | (intros; apply GlobalTheory.concave_twist_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectionOfCohomologyDerivativeRelationStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connection_of_cohomologyDerivativeRelation : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F), DRel F x y w → (∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = 0) → ∃ (m : ℕ) (u v : Fin m → Glob1 F), ObRel F x u v := by
  first | exact @GlobalTheory.AbCoh.exists_obRel_of_dRel | exact GlobalTheory.AbCoh.exists_obRel_of_dRel | (intros; apply GlobalTheory.AbCoh.exists_obRel_of_dRel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulProdChooseStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_prod_choose_smul_of_choose_relation : ∀ (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M], (∀ m : M, ∃ m', p • m' = m) → (∀ n : ℕ, Nat.Coprime n p → Function.Bijective fun m : M => n • m) → ∀ (d : ℕ) (n : Fin d →₀ ℕ) (c : (Fin d →₀ ℕ) → M), (∀ a, a ≤ n → c a = c (n - a)) → (∀ a b, a ≠ 0 → b ≠ 0 → a + b ≤ n → a + b ≠ n → (∏ i, Nat.choose ((a + b : Fin d →₀ ℕ) i) (a i)) • c (a + b) = (∏ i, Nat.choose ((n - a : Fin d →₀ ℕ) i) (b i)) • c a) → ∃ g : M, ∀ a, a ≤ n → a ≠ 0 → a ≠ n → c a = (∏ i, Nat.choose (n i) (a i)) • g := by
  first | exact @GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose | exact GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose | (intros; apply GlobalTheory.SymCocycleMV.exists_eq_smul_prod_choose <;> assumption)
end

