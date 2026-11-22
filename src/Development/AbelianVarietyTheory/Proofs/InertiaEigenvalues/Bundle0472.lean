import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfLinearIndependentDdRE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0195
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0445
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.LetterDim

theorem card_le_of_idem {R : Type} [CommRing R] {e : R} (he : e * e = e) (he0 : e ≠ 0)
    {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → κ → R)
    (h : ∀ r : ι → R, (∀ j, ∑ i, r i * a i j = 0) → ∀ i, e * r i = 0) :
    Fintype.card ι ≤ Fintype.card κ := by
  let I : Ideal R := Ideal.span {1 - e}
  have hI : ∀ x, x ∈ I ↔ e * x = 0 := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      linear_combination (-c) * he
    · intro hx
      exact ⟨x, by linear_combination -hx⟩
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 (by
    intro hT
    have : (1 : R) ∈ I := by rw [hT]; trivial
    rw [hI, mul_one] at this
    exact he0 this)
  have hli : LinearIndependent (R ⧸ I) (fun i j => Ideal.Quotient.mk I (a i j)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    choose r hr using fun i => Ideal.Quotient.mk_surjective (g i)
    rw [← hr, Ideal.Quotient.eq_zero_iff_mem, hI, ← he, mul_assoc]
    refine h (fun i => e * r i) (fun j => ?_) i
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, ← hr, ← map_mul,
      ← map_sum] at this
    rw [Ideal.Quotient.eq_zero_iff_mem, hI, Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  simpa using hli.fintype_card_le_finrank

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V]

open GlobalTheory.DRFil in

theorem component_le [FiniteDimensional Qp K] [CharZero Qp] (hF : IsField F) (ρ : Representation LL G V)
    (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    finrank LL ↥(DdRE PD ρ τ) ≤ finrank LL V := by
  haveI := nontrivial_dR PD
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  let v := Module.finBasis LL V
  have hli : LinearIndependent LL (fun i => (b i : V ⊗[Qp] F)) :=
    b.linearIndependent.map' (DdRE PD ρ τ).subtype (Submodule.ker_subtype _)
  have h := indep_of_linearIndependent_DdRE PD ρ τ _ hF (fun i => (b i).2) hli
  have := card_le_of_idem (idem_mul_idem (F := F) τ) (idem_ne_zero (F := F) τ)
    (fun i j => ext Qp F (v.coord j) (b i : V ⊗[Qp] F)) (fun r hr => h r (by
      rw [eq_sum_basis v (∑ i, sm Qp F LL V (r i) (b i : V ⊗[Qp] F))]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_sum]
      simp only [ext_sm, sm_self]
      rw [hr j, map_zero, LinearMap.zero_apply]))
  simpa using this

theorem component_eq [CharZero Qp] (hF : IsField F) (ρ : Representation LL G V)
    (hc : Nat.card (K →ₐ[Qp] LL) = finrank Qp K) (h : IsDR PD ρ) (τ : K →ₐ[Qp] LL) :
    finrank LL ↥(DdRE PD ρ τ) = finrank LL V := by
  haveI := PD.finK
  haveI := (GlobalTheory.Per.FontaineBound.ddR_finite_le PD hF ρ).1
  haveI : ∀ τ, FiniteDimensional LL ↥(DdRE PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  rw [Nat.card_eq_fintype_card] at hc
  have hs := (GlobalTheory.DeRhamSplit.finrank_DdR PD ρ hc 0).1
  unfold IsDR at h
  refine (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (g := fun _ => finrank LL V)
    fun τ _ => component_le PD hF ρ τ).1 ?_ τ (Finset.mem_univ τ)
  rw [← hs, h, Finset.sum_const, Finset.card_univ, hc, smul_eq_mul]

omit [FiniteDimensional Qp LL] in

theorem finite_Dcris (ρ : Representation LL G V) (h : IsCrys PD ρ) : Module.Finite LL ↥(Dcris PD ρ) := by
  haveI := PD.finK₀
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · haveI : Subsingleton V := finrank_zero_iff.1 h0
    infer_instance
  · exact FiniteDimensional.of_finrank_pos (by
      unfold IsCrys at h
      rw [h]
      exact Nat.mul_pos finrank_pos h0)

omit [FiniteDimensional Qp LL] in
open GlobalTheory.RegularRing in

theorem letter_eq [IsDomain B] (ρ : Representation LL G V)
    (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (h : IsCrys PD ρ) (τ : K₀ →ₐ[Qp] LL) :
    finrank LL ↥(DcrisL PD ρ τ) = finrank LL V := by
  haveI := PD.finK₀
  haveI := finite_Dcris PD ρ h
  have hle : ∀ (n : ℕ) (τ τ' : K₀ →ₐ[Qp] LL), (∀ c, τ' c = τ (PD.σ^[n] c)) →
      finrank LL ↥(DcrisL PD ρ τ') ≤ finrank LL ↥(DcrisL PD ρ τ) := by
    intro n
    induction n with
    | zero =>
      intro τ τ' h
      rw [show τ' = τ from AlgHom.ext h]
    | succ n ih =>
      intro τ τ' h
      exact (ih (τ.comp PD.σ) τ' fun c => by rw [h, Function.iterate_succ_apply']; rfl).trans
        (letter_le PD ρ τ _ fun _ => rfl)
  have heq : ∀ τ', finrank LL ↥(DcrisL PD ρ τ') = finrank LL ↥(DcrisL PD ρ τ) := fun τ' => by
    obtain ⟨n, hn⟩ := exists_pow_sigma PD LL hc τ τ'
    obtain ⟨n', hn'⟩ := exists_pow_sigma PD LL hc τ' τ
    exact le_antisymm (hle n _ _ hn) (hle n' _ _ hn')
  rw [Nat.card_eq_fintype_card] at hc
  have hs : finrank LL ↥(Dcris PD ρ) = ∑ τ', finrank LL ↥(DcrisL PD ρ τ') :=
    GlobalTheory.DeRhamSplit.finrank_eq_sum hc (GlobalTheory.DeRhamSplit.mulHom Qp K₀ B LL V) (Dcris PD ρ)
      fun a x hx => (GlobalTheory.FontCmp.mK PD ρ a ⟨x, hx⟩).2
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, hc] at hs
  unfold IsCrys at h
  exact Nat.eq_of_mul_eq_mul_left finrank_pos (hs.symm.trans h)

end General

theorem tied_letter_component_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) → IsCrys (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DcrisL (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) ∧ (Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 → IsDR (P.PD K) ρ → ∀ τ, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = Module.finrank ↥LL.1 V) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  exact ⟨letter_eq (P.PD K) ρ, component_eq (P.PD K) (GlobalTheory.RegularRing.isField_of_tied T) ρ⟩

end GlobalTheory.Per.LetterDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobDualOfAttached
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleFrobDual

theorem charpoly_smul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (h : M * N = 1) (m : Multiset ℂ) (c : ℂ)
    (hM : M.charpoly = (m.map fun β => X - C β).prod) :
    (c • M).charpoly = (m.map fun β => X - C (c * β)).prod := by
  have h1 := GlobalTheory.ConjPoly.charpoly_smul_inv M N h m 1 hM
  have h2 := GlobalTheory.ConjPoly.charpoly_smul_inv N M (mul_eq_one_comm.1 h) (m.map (·⁻¹)) c
    (by rw [one_smul] at h1; rw [h1, Multiset.map_map]; simp)
  rw [h2, Multiset.map_map]
  simp

theorem cyclotomicChar_frobenius_eq_normPlace {D : D7} (i : D.ntw.Tw) {v : HeightOneSpectrum (𝓞 D.host.E)}
    (hv : v ∉ placesOver D.host.E (D.ntw.l i)) {A : ValuationSubring D.nd.Om} (hA : IsPlaceOver (F := D.host.E) A v)
    {σ : Gen.GE D.nd} (hσ : IsFrob (F := D.host.E) A (normV v) σ) :
    ((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = (normV v : ℕ) := by
  have h := cycZ_of_isFrob hv hA hσ
  change algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) ((cycZ D.host.E D.nd.Om (D.ntw.l i) σ : ℤ_[D.ntw.l i]ˣ) : _) = _
  rw [h, map_natCast]

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective _ _)

theorem frobDual_of_tripleAtt : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i),
    TripleAtt D.naut bkP i s → FrobDual i s := by
  rintro D bkP i s ⟨ι, π₁, π, -, hT, hR, -⟩ P hP - - A hA g g' hg hg'
  obtain rfl : g' = GlobalTheory.TwistDet.cConj D.ntw g := AlgEquiv.ext fun x => by rw [hg', GlobalTheory.TwistDet.cConj_apply]
  obtain ⟨bar, -, hbar⟩ := GlobalTheory.ConjPoly.exists_conj D
  obtain ⟨hcj, hn, -⟩ := hbar P
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)
  have hl' : bar P ∉ placesOver D.host.E (D.ntw.l i) := fun h =>
    hl (GlobalTheory.TwistDet.mem_placesOver_conj (GlobalTheory.TwistDet.isConjPl_symm hcj) h)
  have hu := hR.unr P (fun k h => hP (D.ntw.placesOver_subset_exceptional i k h)) fun h => hP (D.ntw.primes_subset_exceptional i h)
  obtain ⟨hu', he⟩ := D.naut.csd_unr π P (bar P) hR.csd hcj hu
  have hA' := GlobalTheory.TwistDet.isPlaceOver_moveVal_cc D.ntw hcj hA
  have hg2 := GlobalTheory.TwistDet.isFrob_cConj D.ntw hg
  rw [← hn] at hg2
  have e1 := hT.frob P hl hu A g hA hg
  have e2 := hT.frob _ hl' hu' _ _ hA' hg2
  rw [D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map, Tgl_coe] at e1
  rw [D.naut.frobEig_tw _ _ hu', he, hn, ← Matrix.charpoly_map, Tgl_coe] at e2
  have hinv : ∀ x, (Tmat i s x).map (rd i ι) * ((Tmat i s x)⁻¹).map (rd i ι) = 1 := fun x => by
    rw [← Matrix.map_mul, ← Tgl_coe, Matrix.mul_nonsing_inv _ (Matrix.isUnit_iff_isUnit_det _ |>.1 (Units.isUnit _)),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hq : ((normV P : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.ConjPoly.normV_ne_zero P)
  have e3 := charpoly_smul _ _ (hinv _) _ (((normV P : ℕ) : ℂ) ^ D.R.t) e1
  have e4 := GlobalTheory.ConjPoly.charpoly_smul_inv _ _ (hinv _) _ ((normV P : ℕ) : ℂ) e2
  apply Polynomial.map_injective _ (rd_injective i ι)
  rw [Tdual, ← Matrix.transpose_smul, Matrix.charpoly_transpose, ← Matrix.charpoly_map, ← Matrix.charpoly_map,
    cyclotomicChar_frobenius_eq_normPlace i hl hA hg, cyclotomicChar_frobenius_eq_normPlace i hl' hA' hg2, hn]
  refine Eq.trans ?_ (e4.trans (Eq.trans ?_ (e3.symm.trans ?_)))
  · congr 1
    ext a b
    simp
  · rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    have h2 := GlobalTheory.ConjPoly.cpow_sq hq ((1 - (D.R.t : ℝ)) / 2) (1 - D.R.t) (by push_cast; ring)
    have h3 : ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.t : ℝ)) / 2 : ℝ) : ℂ) ≠ 0 := by simp [hq]
    rw [zpow_sub₀ hq, zpow_one, zpow_natCast, div_eq_iff (pow_ne_zero _ hq)] at h2
    congr 2
    rw [mul_inv, inv_inv]
    field_simp
    linear_combination a * h2
  · congr 1
    ext a b
    simp

end GlobalTheory.TripleFrobDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityCoeffTensorAinfVector
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

namespace GlobalTheory.FrobIntO

theorem frobenius_integrality_vec_O : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : Type) [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι (OA l O)) (w : ι → OA l O) (z : ι → OW l O), (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) → ∀ i, z i ∈ (inclO l O).range := by
  intro l _ O _ _ _ _ ι _ _ Y w z h i
  classical
  have key := GlobalTheory.FrobIntegralCoeff.integrality_baseChange (R := ℤ_[l]) (O := O) (inclWA l) (frobW l)
    (fun p q _ _ Z S S' Y h => GlobalTheory.FrobInt.frobenius_integrality l p q Z S S' Y h) ι Unit
    (Matrix.of fun j (_ : Unit) => z j) Y 1 (Matrix.of fun j (_ : Unit) => w j) (by
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
      refine Matrix.ext fun j u => ?_
      have := congrFun h j
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Fintype.sum_unique, Pi.add_apply] at this ⊢
      exact this) i ()
  exact key

end GlobalTheory.FrobIntO
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusStratificationCoeffEqConnectionPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TaylorStrat

def idl (K : Type) [Field K] : Ideal K⟦X⟧⟦X⟧ := Ideal.span {C (X : K⟦X⟧), X}

theorem idl_ne_top (K : Type) [Field K] : idl K ≠ ⊤ := by
  intro h
  have hle : idl K ≤ RingHom.ker ((constantCoeff : K⟦X⟧ →+* K).comp (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧)) := by
    rw [idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp
  have h1 := hle (h ▸ Submodule.mem_top : (1 : K⟦X⟧⟦X⟧) ∈ idl K)
  simp at h1

theorem eq_zero_of_forall_mem {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : ∀ m, g ∈ idl K ^ m) : g = 0 := by
  have := Ideal.iInf_pow_eq_bot_of_isDomain (idl K) (idl_ne_top K)
  rw [← Ideal.mem_bot, ← this, Ideal.mem_iInf]
  exact h

theorem mem_idl_of_constantCoeff {K : Type} [Field K] {g : K⟦X⟧⟦X⟧} (h : constantCoeff g = 0) :
    g ∈ idl K := by
  obtain ⟨c, rfl⟩ := X_dvd_iff.2 h
  exact Ideal.mul_mem_right c _ (Ideal.subset_span (by simp))

theorem taylor_eq_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (f : K⟦X⟧) (hf : PowerSeries.derivative K f = 0) : sh f = C f := by
  ext1 i
  rcases i with _ | i
  · simpa using hsh f 0
  · have h := hsh f (i + 1)
    rw [Function.iterate_succ_apply, hf, Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 1).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [coeff_C, if_neg (by omega)]
    exact (mul_eq_zero.1 h).resolve_left hne

theorem taylor_X {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) :
    sh X = C X + X := by
  ext1 i
  rcases i with _ | _ | i
  · simpa using hsh X 0
  · simpa using hsh X 1
  · have h := hsh X (i + 2)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X, Derivation.map_one_eq_zero,
      Function.iterate_fixed (map_zero _)] at h
    have hne : ((i + 2).factorial : K⟦X⟧) ≠ 0 := by
      intro h0
      have := congrArg (constantCoeff : K⟦X⟧ →+* K) h0
      simp [Nat.factorial_ne_zero] at this
    rw [map_add, coeff_C, coeff_X, if_neg (by omega), if_neg (by omega), add_zero]
    exact (mul_eq_zero.1 h).resolve_left hne

end GlobalTheory.TaylorStrat

namespace GlobalTheory.TaylorStrat

theorem map_idl_pow_le {K : Type} [Field K] (l : ℕ) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hshX : sh X = C X + X) (hC : φ₂ (C X) = C X ^ l) (hsh : φ₂ (sh X) = sh X ^ l)
    (m : ℕ) {g : K⟦X⟧⟦X⟧} (hg : g ∈ idl K ^ m) : φ₂ g ∈ idl K ^ (l * m) := by
  have hCm : (C (X : K⟦X⟧) : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have hXm : (X : K⟦X⟧⟦X⟧) ∈ idl K := Ideal.subset_span (by simp)
  have h1 : (idl K).map φ₂ ≤ idl K ^ l := by
    rw [Ideal.map_le_iff_le_comap, idl, Ideal.span_le]
    rintro x (rfl | rfl) <;> simp only [SetLike.mem_coe, Ideal.mem_comap]
    · rw [hC]
      exact Ideal.pow_mem_pow hCm l
    · have hφX : φ₂ (X : K⟦X⟧⟦X⟧) = (C X + X) ^ l - C X ^ l :=
        (congrArg φ₂ (by rw [hshX]; ring : (X : K⟦X⟧⟦X⟧) = sh X - C X)).trans
          (by rw [map_sub, hsh, hC, hshX])
      rw [hφX]
      exact sub_mem (Ideal.pow_mem_pow (add_mem hCm hXm) l) (Ideal.pow_mem_pow hCm l)
  have h2 := Ideal.mem_map_of_mem φ₂ hg
  rw [Ideal.map_pow] at h2
  rw [pow_mul]
  exact Ideal.pow_right_mono h1 m h2

theorem mul_mul_mem {R : Type} [CommRing R] {ι : Type} [Fintype ι] (J : Ideal R) (A N B : Matrix ι ι R)
    (hN : ∀ i j, N i j ∈ J) (i j : ι) : (A * N * B) i j ∈ J := by
  rw [Matrix.mul_apply]
  refine J.sum_mem fun k _ => J.mul_mem_right _ ?_
  rw [Matrix.mul_apply]
  exact J.sum_mem fun p _ => J.mul_mem_left _ (hN p k)

end GlobalTheory.TaylorStrat

open GlobalTheory.TaylorStrat in

theorem GlobalTheory.TaylorStrat.stratification_coeff_eq_nabla_pow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) → (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) → ∀ (τ : ZMod a) (n : ℕ) (i j : ι), (n.factorial : K⟦X⟧) * coeff n (ε τ i j) = (P.mxInv τ *ᵥ (P.nabla ^ n) (P.phi (bas j)) τ) i := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P sh φ₂ hsh hφC hφsh ε hε0 hε τ n i j
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hshX := taylor_X sh hsh
  have hshC : ∀ c : K, sh (C c) = C (C c) := fun c => taylor_eq_C sh hsh _ (by simp)
  have hcc : ∀ f, constantCoeff (sh f) = f := fun f => by simpa using hsh f 0
  have hCX : φ₂ (C X) = C X ^ l := by rw [hφC, frob_X, map_pow]
  have hshl : φ₂ (sh X) = sh X ^ l := by rw [hφsh, frob_X, map_pow]
  have hXi : ∀ τ, P.xiMat τ * (P.xiMat τ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)
  let W : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => (P.xiMat τ)⁻¹ * P.mx τ
  let Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ
  let ε₀ : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => (Y τ).map C * (W τ).map sh
  have hYW : ∀ τ, Y τ * W τ = 1 := by
    intro τ
    simp only [Y, W]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.xiMat τ), hXi, Matrix.one_mul, P.mxInv_mul_mx]
  have h00 : ∀ τ, (ε₀ τ).map constantCoeff = 1 := by
    intro τ
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun (hYW τ) i) j
    simpa [ε₀, Matrix.mul_apply, hcc] using this
  have hrel : ∀ τ, ε₀ τ * ((P.mx (τ - 1)).map (frob K l)).map sh =
      ((P.mx (τ - 1)).map (frob K l)).map C * (ε₀ (τ - 1)).map φ₂ := by
    intro τ
    have F1 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (C.mapMatrix M) = C.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφC]
    have F2 : ∀ M : Matrix ι ι K⟦X⟧, φ₂.mapMatrix (sh.mapMatrix M) = sh.mapMatrix ((frob K l).mapMatrix M) := by
      intro M; ext1 p q; simp [hφsh]
    have F3 : ∀ M : Matrix ι ι K, sh.mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) =
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix M) := by
      intro M; ext1 p q; simp [hshC]
    have hM := P.mx_mul_xiMat τ
    rw [← AlgHom.mapMatrix_apply, ← RingHom.mapMatrix_apply] at hM
    have hFXi : (frob K l).mapMatrix (P.xiMat (τ - 1)) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ = 1 := by
      rw [← map_mul, hXi, map_one]
    have hW : W τ = (C : K →+* K⟦X⟧).mapMatrix (P.mx0 τ) * (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
      calc W τ = (P.xiMat τ)⁻¹ * (P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1))) *
            (frob K l).mapMatrix (P.xiMat (τ - 1))⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hFXi, Matrix.mul_one]
        _ = _ := by
          rw [hM, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ), Matrix.one_mul]
    have hY : Y τ = (frob K l).mapMatrix (P.xiMat (τ - 1)) *
        (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
      have h1 : P.xiMat τ = P.mx τ * (frob K l).mapMatrix (P.xiMat (τ - 1)) *
          (C : K →+* K⟦X⟧).mapMatrix ((P.mxInv τ).map constantCoeff) := by
        rw [hM, Matrix.mul_assoc, ← map_mul, P.matrix_mul_inv_const_eq_one, map_one, Matrix.mul_one]
      show P.mxInv τ * P.xiMat τ = _
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, P.mxInv_mul_mx, Matrix.one_mul]
    simp only [ε₀, ← RingHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply]
    rw [hW, hY]
    simp only [Y, W, map_mul, F1, F2, Matrix.mul_assoc]
    rw [F3, ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((C : K →+* K⟦X⟧).mapMatrix _)), ← map_mul,
      ← map_mul, P.inv_const_mul_matrix_eq_one, map_one, map_one, Matrix.one_mul,
      ← Matrix.mul_assoc ((C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx _)))]
    have hc : (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mx (τ - 1))) *
        (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).mapMatrix ((frob K l).mapMatrix (P.mxInv (τ - 1))) = 1 := by
      rw [← map_mul, ← map_mul, P.mx_mul_mxInv, map_one, map_one]
    rw [hc, Matrix.one_mul]
  have hinv : ∀ τ, ((P.mx (τ - 1)).map (frob K l)).map sh * ((P.mxInv (τ - 1)).map (frob K l)).map sh = 1 := by
    intro τ
    rw [← Matrix.map_mul, ← AlgHom.mapMatrix_apply, ← AlgHom.mapMatrix_apply, ← map_mul, P.mx_mul_mxInv, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hδ : ∀ τ, ε τ - ε₀ τ = ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ *
      ((P.mxInv (τ - 1)).map (frob K l)).map sh := by
    intro τ
    have h1 : (ε τ - ε₀ τ) * ((P.mx (τ - 1)).map (frob K l)).map sh =
        ((P.mx (τ - 1)).map (frob K l)).map C * (ε (τ - 1) - ε₀ (τ - 1)).map φ₂ := by
      rw [Matrix.sub_mul, hε, hrel, ← Matrix.mul_sub, Matrix.map_sub _ (map_sub φ₂)]
    calc ε τ - ε₀ τ = (ε τ - ε₀ τ) * (((P.mx (τ - 1)).map (frob K l)).map sh *
          ((P.mxInv (τ - 1)).map (frob K l)).map sh) := by rw [hinv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1]
  have hmem : ∀ m τ i j, (ε τ - ε₀ τ) i j ∈ idl K ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      intro τ i j
      rw [zero_add, pow_one]
      apply mem_idl_of_constantCoeff
      have h1 := congrFun (congrFun (hε0 τ) i) j
      have h2 := congrFun (congrFun (h00 τ) i) j
      simp only [Matrix.map_apply] at h1 h2
      rw [Matrix.sub_apply, map_sub, h1, h2, sub_self]
    | succ m ih =>
      intro τ i j
      rw [hδ τ]
      apply mul_mul_mem
      intro p q
      rw [Matrix.map_apply]
      exact Ideal.pow_le_pow_right (by nlinarith) (map_idl_pow_le l sh φ₂ hshX hCX hshl (m + 1) (ih (τ - 1) p q))
  have key : ε τ = ε₀ τ := by
    refine Matrix.ext fun i j => ?_
    exact sub_eq_zero.1 (eq_zero_of_forall_mem fun m => Ideal.pow_le_pow_right (Nat.le_succ m) (hmem m τ i j))
  have hphi : P.phi (bas j) = P.xiExt (fun τ => W τ *ᵥ Pi.single j 1) := by
    ext1 τ
    rw [P.phi_apply, P.xiExt_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hXi, Matrix.one_mul]
    congr 1
    ext1 k
    simp [bas, Pi.single_apply]
  have hnab : ∀ (n : ℕ) (w : Vec K a ι), (P.nabla ^ n) (P.xiExt w) =
      P.xiExt (fun τ i => (PowerSeries.derivative K)^[n] (w τ i)) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, P.nabla_xiExt, ih]
      rfl
  rw [hphi, hnab, P.xiExt_apply, Matrix.mulVec_mulVec, key]
  show (n.factorial : K⟦X⟧) * coeff n (((Y τ).map C * (W τ).map sh) i j) =
    (Y τ *ᵥ fun k => (PowerSeries.derivative K)^[n] ((W τ *ᵥ Pi.single j 1) k)) i
  rw [Matrix.mul_apply, map_sum, Finset.mul_sum, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.map_apply, Matrix.map_apply, coeff_C_mul, mul_left_comm, hsh, Matrix.mulVec_single_one]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevCharacterGLnNormAndReciprocityStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandGraevCharacterGLn_norm_and_reciprocity : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n → wh ψ (gg ψ n) = (g : ℂ) ^ n - (g : ℂ) ^ (n - 1) ∧ ∀ χ : Gn g n → ℂ, IsClass χ → ip χ (gg ψ n) = wh ψ χ := by
  first | exact @GlobalTheory.GLq.GGNorm.gg_norm | exact GlobalTheory.GLq.GGNorm.gg_norm | (intros; apply GlobalTheory.GLq.GGNorm.gg_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFiniteStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEigenvalueSystemSet_finite : HeckeStdPlain → ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (X : MtReal D μ j) (l : ℕ) (Q : Finset (PlE D.host)) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))), NG.HypOutside X.J X.χ B → (∀ v k (s : SplitPlace D.host.E), GenAt D l Q v k → IsConjPl D.host v s.w → s.v ∉ B) → (EigSet X l Q).Finite := by
  first | exact @GlobalTheory.EigFinite.eigSet_finite | exact GlobalTheory.EigFinite.eigSet_finite | (intros; apply GlobalTheory.EigFinite.eigSet_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegralStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStableLocalLattice_of_integral : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  first | exact @GlobalTheory.LatStab.latStable_of_latInt | exact GlobalTheory.LatStab.latStable_of_latInt | (intros; apply GlobalTheory.LatStab.latStable_of_latInt <;> assumption)
end

