import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0283
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTateStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate : ∀ (l : ℕ) [Fact l.Prime] (y : ℂ_[l]), y ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) → ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  first | exact @GlobalTheory.Per.exists_unit_character_of_stable_line | exact GlobalTheory.Per.exists_unit_character_of_stable_line | (intros; apply GlobalTheory.Per.exists_unit_character_of_stable_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLatticeCocyclesModUniformizerPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_latticeCocycles_mod_uniformizer_pow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)), (quotientCocycles LA _ hI : Set (↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))).Finite := by
  first | exact @GlobalTheory.CocycleModPow.finite_Z1Q | exact GlobalTheory.CocycleModPow.finite_Z1Q | (intros; apply GlobalTheory.CocycleModPow.finite_Z1Q <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpansLeContinuousCocyclesStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  first | exact @GlobalTheory.Cut.CocN.main | exact GlobalTheory.Cut.CocN.main | (intros; apply GlobalTheory.Cut.CocN.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeAndInvariantsGen
section
noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.DelParam

theorem algHom_eq_subst {O : Type} [CommRing O] (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (hj : (X : O⟦X⟧) ∣ j X)
    (a : O⟦X⟧) : j a = a.subst (j X) := by
  have hs : HasSubst (j X) := HasSubst.of_constantCoeff_zero' (X_dvd_iff.1 hj)
  have := algHom_ext_X j (substAlgHom hs) hj (by rw [coe_substAlgHom, subst_X hs])
  rw [← coe_substAlgHom hs, ← this]

theorem dvd_coeff_of_aeval {O : Type} [CommRing O] (a : O) (ξ w : O⟦X⟧) (s e : ℕ) (hs : 0 < s)
    (hw : IsUnit w) (hξ : ξ = w * X ^ s) (E : Polynomial O) (b c : O⟦X⟧)
    (h : Polynomial.aeval ξ E = X ^ (e * s) * b + C a * c) : ∀ k < e, a ∣ E.coeff k := by
  induction e generalizing E b c with
  | zero => intro k hk; omega
  | succ e ih =>
    have hE := Polynomial.X_mul_divX_add E
    have h0 : a ∣ E.coeff 0 := by
      have h1 := congrArg constantCoeff h
      rw [← hE] at h1
      simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hξ, map_pow,
        constantCoeff_X, zero_pow hs.ne', zero_pow (Nat.mul_pos e.succ_pos hs).ne', mul_zero,
        zero_mul, zero_add, constantCoeff_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply] at h1
      exact ⟨_, h1⟩
    obtain ⟨d, hd⟩ := h0
    obtain ⟨w', hw'⟩ := hw.exists_right_inv
    have h2 : X ^ s * (w * Polynomial.aeval ξ E.divX - X ^ (e * s) * b) = C a * (c - C d) := by
      rw [← hE, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hd] at h
      have hC : algebraMap O O⟦X⟧ (a * d) = C a * C d := by rw [← map_mul]; rfl
      rw [hC] at h
      nth_rewrite 1 [hξ] at h
      linear_combination h
    have h3 : ∃ c', w * Polynomial.aeval ξ E.divX - X ^ (e * s) * b = C a * c' := by
      refine ⟨PowerSeries.mk fun k => coeff (k + s) (c - C d), ?_⟩
      ext k
      rw [coeff_C_mul, coeff_mk, ← coeff_C_mul, ← h2, coeff_X_pow_mul]
    obtain ⟨c', hc'⟩ := h3
    have h4 := ih E.divX (w' * b) (w' * c') (by
      linear_combination w' * hc' - Polynomial.aeval ξ E.divX * hw')
    intro k hk
    cases k with
    | zero => exact ⟨d, hd⟩
    | succ k => rw [← Polynomial.coeff_divX]; exact h4 k (by omega)

theorem prod_one_root {O : Type} [CommRing O] (ϖ : Fin 1 → O) (a : O) (E : Polynomial O)
    (hE : E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ))) (h : ϖ 0 = -a) :
    E = Polynomial.X + Polynomial.C a := by
  rw [hE, Fin.prod_univ_one, h, map_neg, sub_neg_eq_add]

theorem lvl_zero_mod {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] :
    ∃ r : O⟦X⟧, lvl l O 0 = X ^ (l - 1) + C (l : O) * r := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : l.Prime) (1 : O⟦X⟧) X
  have h1 := mul_lvl (l := l) (O := O) 0
  simp only [pow_zero, pow_one, zero_add, add_sub_cancel_left] at h1
  refine ⟨r, mul_left_cancel₀ (X_ne_zero (R := O)) ?_⟩
  have h2 : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : l.Prime).one_le]
  rw [h1, hr, map_natCast, h2]; ring

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O]
    (hp : PD.p = l)

def EisAt (l e : ℕ) (ξ : O⟦X⟧) (E : Polynomial O) : Prop :=
  E.Monic ∧ E.natDegree = e ∧ (∀ k < e, (l : O) ∣ E.coeff k) ∧
    Associated (E.coeff 0) (l : O) ∧ Associated (Polynomial.aeval ξ E) W.q₀ ∧
    (∃ c : O⟦X⟧, IsUnit c ∧ W.φ₀ ξ = c.subst ξ * ξ * Polynomial.aeval ξ E ^ W.DelF.card) ∧
    ∃ c : O⟦X⟧, IsUnit c ∧ W.γ₀ W.gam ξ - ξ = c.subst ξ * ξ * Polynomial.aeval ξ E

def HasEis (l e : ℕ) (ξ : O⟦X⟧) : Prop :=
  ∃ (E : Polynomial O) (ϖ : Fin e → O), E = ∏ τ, (Polynomial.X - Polynomial.C (ϖ τ)) ∧
    (∀ τ, Associated (ϖ τ ^ e) (l : O)) ∧
    (∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ ξ - C (ϖ τ)) ∧
    Function.Injective ϖ ∧ EisAt W l e ξ E

include hp

theorem free_and_invariants_gen [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hu : ¬ IsUnit (l : O))
    (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O)) (ξ : O⟦X⟧)
    (hξ : Associated ξ (X ^ W.DelF.card)) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    (∀ b : O⟦X⟧, ∃! G : Fin W.DelF.card → O⟦X⟧,
      b = ∑ k : Fin W.DelF.card, X ^ (k : ℕ) * (G k).subst ξ) ∧
    ∀ b : O⟦X⟧, (∀ δ ∈ W.DelF, W.γ₀ δ b = b) ↔ ∃ g : O⟦X⟧, b = g.subst ξ := by
  classical
  have hγ : ∀ g, W.γ₀ g = GlobalTheory.Cyc.act l O (χ g : ℤ_[l]) := fun g => by
    rw [γ₀_eq W hp χ hχ g]
    refine algHom_ext_X _ _ (X_dvd_act_X _) ?_
    rw [act_X, GlobalTheory.Cyc.Series.act_X, GlobalTheory.Cyc.Series.cyc_eq]
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  have : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  let _ : Fintype Δ := Fintype.ofFinite _
  have hcard : Fintype.card Δ = W.DelF.card := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  obtain ⟨w, hw⟩ := hξ.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.Cyc.invariants_param l O
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hu Δ ξ w w.isUnit
    (by rw [hcard, ← hw, mul_comm])
    (fun d => (hfa fun d => GlobalTheory.Cyc.act l O (d : ℤ_[l]) ξ = ξ).2 (fun δ hδ => by
      rw [← hγ]; exact hinv δ hδ) d d.2)
  refine ⟨hcard ▸ h1, fun b => ?_⟩
  rw [← h2, Subtype.forall, hfa fun d => GlobalTheory.Cyc.act l O (d : ℤ_[l]) b = b]
  simp only [hγ]

theorem eisenstein_gen (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (ht : FrTie W R j)
    (E : Polynomial O) (hEd : E = ∏ τ, (Polynomial.X - Polynomial.C (R.ϖ τ))) :
    Function.Injective R.ϖ ∧ EisAt W l R.e (j X) E := by
  subst hEd
  obtain ⟨-, -, hφ, hγ, -, hs, hX, hE⟩ := ht
  have hes := R.es
  have h2l := (Fact.out : l.Prime).two_le
  have hs0 : 0 < R.s := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hes; omega
  have he0 : R.e ≠ 0 := fun h0 => by rw [h0] at hes; omega
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hj : (X : O⟦X⟧) ∣ j X := (dvd_pow_self X hs0.ne').trans hX.symm.dvd
  have hq := (φ₀_eq W hp).2
  rw [EisAt, ← hs]
  have hjE : Polynomial.aeval (j X) (∏ τ, (Polynomial.X - Polynomial.C (R.ϖ τ))) = j R.E := by
    rw [R.E_def, map_prod, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_sub, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, algHom_C]
  refine ⟨fun τ τ' hτ => ?_,
    Polynomial.monic_prod_of_monic _ _ fun τ _ => Polynomial.monic_X_sub_C _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hne
    have h1 := R.ϖ_sub τ τ' hne
    rw [hτ, sub_self, ← hτ] at h1
    have h2 := R.ϖ_val τ
    rw [(associated_zero_iff_eq_zero _).1 h1.symm, zero_pow he0] at h2
    exact hl0 ((associated_zero_iff_eq_zero _).1 h2.symm)
  · rw [Polynomial.natDegree_prod_of_monic _ _ fun τ _ => Polynomial.monic_X_sub_C _]
    simp
  · obtain ⟨w, hw⟩ := hX.symm
    obtain ⟨u, hu⟩ := hE.symm
    obtain ⟨r, hr⟩ := lvl_zero_mod (l := l) O
    refine dvd_coeff_of_aeval _ (j X) w R.s R.e hs0 w.isUnit (by rw [← hw, mul_comm]) _ u (r * u) ?_
    rw [hjE, ← hu, hq, hr, hes]; ring
  · obtain ⟨u, hu⟩ := hE.symm
    have h1 := congrArg constantCoeff hu
    rw [map_mul, hq, constantCoeff_lvl, constantCoeff_algHom j hj, R.E_def, map_prod] at h1
    rw [Polynomial.coeff_zero_prod]
    simp only [map_sub, constantCoeff_X, constantCoeff_C] at h1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero]
    rw [← h1]
    exact associated_mul_unit_left _ _ (u.isUnit.map _)
  · rw [hjE]; exact hE
  · refine ⟨R.u, R.u.isUnit, ?_⟩
    rw [← hφ, R.φ_X, map_mul, map_mul, map_pow, hjE, algHom_eq_subst j hj R.u]
  · refine ⟨R.κ, R.κ.isUnit, ?_⟩
    rw [← hγ, R.γ_X, map_mul, map_add, map_one, map_mul, hjE, algHom_eq_subst j hj R.κ]
    ring

omit hp [CharZero O] [Algebra ℤ_[l] O] in

theorem eisAt_one [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hu : ¬ IsUnit (l : O)) (ξ : O⟦X⟧) (hq : lvl l O 0 ∣ ξ + (l : O⟦X⟧)) (e₀ : ℕ) (he₀ : e₀ = 1)
    (hA : HasEis W l e₀ ξ) : EisAt W l 1 ξ (Polynomial.X + Polynomial.C (l : O)) := by
  obtain ⟨E, ϖ, hE, -, hr, -, hA⟩ := hA
  subst he₀
  obtain ⟨ζ, hζ, hd⟩ := hr 0
  rwa [prod_one_root ϖ _ E hE (eq_neg_of_root hu _ _ ζ hζ hd hq)] at hA

end Generic

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
  (h : Good K 1 LL) (hl : l ≠ 2)
include hl

theorem card_eq : (H.W K 1 LL h).DelF.card = (l - 1) / Module.finrank ↥(K0 K) ↥K.1 := by
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
  have h2l := (Fact.out : l.Prime).two_le
  have h0 : 0 < Module.finrank ↥(K0 K) ↥K.1 := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hc; omega
  rw [← hc, Nat.mul_div_cancel _ h0]

omit hl in

theorem free_and_invariants (ξ : (↥(OL LL))⟦X⟧)
    (hξ : Associated ξ (X ^ (H.W K 1 LL h).DelF.card))
    (hinv : ∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ ξ = ξ) :
    (∀ b : (↥(OL LL))⟦X⟧, ∃! G : Fin (H.W K 1 LL h).DelF.card → (↥(OL LL))⟦X⟧,
      b = ∑ k : Fin (H.W K 1 LL h).DelF.card, X ^ (k : ℕ) * (G k).subst ξ) ∧
    ∀ b : (↥(OL LL))⟦X⟧, (∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ b = b) ↔
      ∃ g : (↥(OL LL))⟦X⟧, b = g.subst ξ := by
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL (H.W K 1 LL h)
  exact free_and_invariants_gen (H.W K 1 LL h) (P.PD_p K) hu χ hχ ξ hξ hinv

theorem exists_eisenstein (ξ : (↥(OL LL))⟦X⟧)
    (hξ : Associated ξ (X ^ (H.W K 1 LL h).DelF.card))
    (hinv : ∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ ξ = ξ) :
    HasEis (H.W K 1 LL h) l (Module.finrank ↥(K0 K) ↥K.1) ξ := by
  obtain ⟨R, j, jE, hj, he, ht, -, hr, -⟩ := exists_attached H h hl ξ hξ hinv
  have h1 : HasEis (H.W K 1 LL h) l R.e (j X) :=
    ⟨_, R.ϖ, rfl, R.ϖ_val, hr, eisenstein_gen (H.W K 1 LL h) (P.PD_p K) R j ht _ rfl⟩
  rwa [hj, he] at h1

set_option maxHeartbeats 800000 in

theorem trace_param (h1 : Module.finrank ↥(K0 K) ↥K.1 = 1) :
    (H.W K 1 LL h).DelF.card = l - 1 ∧
    Associated (H.W K 1 LL h).π₀₁ (X ^ (H.W K 1 LL h).DelF.card) ∧
    (∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ (H.W K 1 LL h).π₀₁ = (H.W K 1 LL h).π₀₁) ∧
    EisAt (H.W K 1 LL h) l 1 (H.W K 1 LL h).π₀₁
      (Polynomial.X + Polynomial.C ((l : ℕ) : ↥(OL LL))) := by
  have hc := card_eq H h hl
  rw [h1, Nat.div_one] at hc
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL (H.W K 1 LL h)
  obtain ⟨p2, p3, p4⟩ := π₀₁_spec (H.W K 1 LL h) (P.PD_p K) χ hχ hl hc
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  exact ⟨hc, p2, p3, eisAt_one (H.W K 1 LL h) hu _ p4 _ h1 (exists_eisenstein H h hl _ p2 p3)⟩

end GlobalTheory.DelParam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjectiveStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_map_surjective : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.FundOnto := by
  first | exact @GlobalTheory.MemLoc.FundOnto.fundOnto | exact GlobalTheory.MemLoc.FundOnto.fundOnto | (intros; apply GlobalTheory.MemLoc.FundOnto.fundOnto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalTwoCocycleMultipleNotCoboundaryStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalTwoCocycle_multiple_not_coboundary : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] {G : Type} [Group G] [TopologicalSpace G] (χ : G →* ℤ_[p]ˣ) (c : G × G → ℤ_[p]), (∀ r, GlobalTheory.TateTop.Gen χ r c) → ∀ (φ : ℤ_[p] →+* O) (ε : G →* Oˣ), (∀ g, ((ε g : Oˣ) : O) = φ (χ g : ℤ_[p])) → ∀ (ϖ : O), Irreducible ϖ → (p : O) ∈ IsLocalRing.maximalIdeal O → (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → ∀ (a : O) (f : G → O), Continuous f → (∀ g h : G, d1 (twist ε O) f (g, h) = a * φ (c (g, h))) → a = 0 := by
  first | exact @GlobalTheory.TateNat.free_inj | exact GlobalTheory.TateNat.free_inj | (intros; apply GlobalTheory.TateNat.free_inj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReduction
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.RedAct

theorem ringHom_padicInt_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k)
    (z : ℤ_[l]) : f z = ((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) z := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.zmodRepr : ℤ_[l]) + l * c := by rw [← hc]; ring
  rw [hz]
  simp only [map_add, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem map_act {l : ℕ} [Fact l.Prime] {O k : Type} [CommRing O] [Algebra ℤ_[l] O] [Field k] [CharP k l]
    (f : O →+* k) (c : ℤ_[l]) (a : O⟦X⟧) :
    PowerSeries.map f (GlobalTheory.CycFr.act O c a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l c (PowerSeries.map f a) := by
  have hb : PowerSeries.map f (GlobalTheory.CycFr.bin O c) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l c := by
    ext n
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.binomialSeries_coeff, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
      ← Algebra.algebraMap_eq_smul_one]
    exact ringHom_padicInt_eq (f.comp (algebraMap ℤ_[l] O)) _
  rw [GlobalTheory.CycFr.act_apply, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, ← hb]
  have h := PowerSeries.map_subst (GlobalTheory.CycFr.hasSubst_bin O c) (h := f) a
  have h2 : PowerSeries.map f (GlobalTheory.CycFr.bin O c - 1) = PowerSeries.map f (GlobalTheory.CycFr.bin O c) - 1 := by
    rw [map_sub, map_one]
  rw [← h2]
  exact h

theorem deltaPi_one_add {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (b : k⟦X⟧) :
    GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (1 + l) b = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l b := by
  have h := PowerSeries.binomialSeries_nat (R := ℤ_[l]) (A := ℤ_[l]) (1 + l)
  rw [Nat.cast_add, Nat.cast_one] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, h]
  simp

theorem chi_surjective {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) :
    Function.Surjective χ := by
  intro u
  obtain ⟨χ', h1, -, h3⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨g, hg, hgu⟩ := h3 K 0 (le_trans (le_inf le_rfl hK) le_sup_left) u (by simp)
  refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (GlobalTheory.algebraMap_padicInt_OL_injective LL ?_)⟩
  rw [hχ]
  apply Subtype.ext
  have h := W.χΓ_res ⟨g, hg⟩
  rw [P.PD_χ, ← h1] at h
  refine h.trans ?_
  change algebraMap ℚ_[l] ↥LL.1 ((χ' g : ℤ_[l]) : ℚ_[l]) = _
  rw [hgu]
  rfl

theorem card_torsion {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) (h : K.1 ≤ Ks K 1) :
    W.DelF.card = l - 1 := by
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h
  rw [p1, mul_one] at hc
  exact hc

theorem gamma_eq_act {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) (g : W.Gam) :
    W.γ₀ g = GlobalTheory.CycFr.act ↥(OL LL) (χ g : ℤ_[l]) :=
  GlobalTheory.WachTie.γ₀_eq W (P.PD_p K) χ hχ g

theorem action_of_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O)) (hs : Function.Surjective χ)
    (hγ : ∀ g, W.γ₀ g = GlobalTheory.CycFr.act O (χ g : ℤ_[l])) (hc : W.DelF.card = l - 1)
    {k : Type} [Field k] [CharP k l] (r : O →+* k) :
    (∃ γ : W.Gam, (W.χΓ γ : O) = 1 + (l : O) ∧
      ∀ a, PowerSeries.map r (W.γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map r a)) ∧
    ∃ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a,
      PowerSeries.map r (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map r a) := by
  have h2l := (Fact.out : l.Prime).two_le
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  have hcard : Nat.card (CommGroup.torsion W.Gam) = l - 1 := by
    rw [← hc, ← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [CommGroup.mem_torsion, Finset.mem_coe, GlobalTheory.WachTie.mem_DelF_iff]
  have hpow : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := fun δ hδ => by
    have h1 : (⟨δ, (GlobalTheory.WachTie.mem_DelF_iff W δ).1 hδ⟩ : CommGroup.torsion W.Gam) ^ (l - 1) = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    exact congrArg Subtype.val h1
  constructor
  · have hu : IsUnit (1 + (l : ℤ_[l])) := by
      have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
      rw [sub_neg_eq_add, IsUnit.neg_iff] at h1
      exact h1.resolve_left PadicInt.p_nonunit
    obtain ⟨g, hg⟩ := hs hu.unit
    have hg' : (χ g : ℤ_[l]) = 1 + l := by rw [hg, hu.unit_spec]
    refine ⟨g, by rw [← hχ, hg', map_add, map_one, map_natCast], fun a => ?_⟩
    rw [hγ, map_act, hg', deltaPi_one_add]
  · let f : {δ // δ ∈ W.DelF} → {z : ℤ_[l] // z ^ (l - 1) = 1} := fun δ =>
      ⟨χ δ.1, by rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow δ.1 δ.2, map_one, Units.val_one]⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => Subtype.ext (hχi (Units.ext (congrArg Subtype.val hab))), fun z => ?_⟩
      have hu : IsUnit z.1 := IsUnit.of_pow_eq_one z.2 (by omega)
      obtain ⟨g, hg⟩ := hs hu.unit
      have hg' : (χ g : ℤ_[l]) = z.1 := by rw [hg, hu.unit_spec]
      refine ⟨⟨g, (W.DelF_def g).2 ⟨l - 1, by omega, hχi (Units.ext ?_)⟩⟩, Subtype.ext hg'⟩
      rw [map_pow, Units.val_pow_eq_pow_val, hg', z.2, map_one, Units.val_one]
    refine ⟨Equiv.ofBijective f hf, fun δ a => ?_⟩
    rw [hγ, map_act]
    rfl

theorem gamma_action_reduction : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  intro l _ P H S k _ _ _
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P S.K S.LL (S.W H)
  exact action_of_surjective (S.W H) χ hχ (chi_surjective P S.K S.LL _ S.hyp.1.2.1.1 χ hχ)
    (gamma_eq_act P S.K S.LL _ χ hχ)
    (card_torsion P S.K S.LL _ S.hyp.1.2.1.1 S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1) (algebraMap S.O k)

end GlobalTheory.RedAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalEulerChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.EulerScalars

noncomputable def subquotEquiv {R R' X : Type*} [CommRing R] [CommRing R'] [AddCommGroup X]
    [Module R X] [Module R' X] (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    (Z ⧸ B.comap Z.subtype) ≃ (Z' ⧸ B'.comap Z'.subtype) :=
  Quotient.congr (Equiv.subtypeEquivRight hZ) fun a b => by
    rw [Submodule.quotientRel_def, Submodule.quotientRel_def]
    exact hB _

theorem global_euler_char : GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (Λ M : Type) [CommRing Λ] [AddCommGroup M] [Module Λ M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation Λ (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), (∀ m : M, l • m = 0) → ContainsAbove S l → ContAction ρ → Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H2 ρ) * Nat.card M ^ InfinitePlace.nrComplexPlaces F := by
  intro hF hE F Ω _ _ _ _ _ _ l _ Λ M _ _ _ _ _ _ S ρ hl hS hc

  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ 1)) M) :=
    ⟨AddCommGroup.zmodModule (n := l ^ 1) (by simpa using hl)⟩
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M,
      ∀ g m, ρ' g m = ρ g m := ⟨zmodRep (l ^ 1) ρ, fun _ _ => rfl⟩

  have hc' : ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction at hc ⊢
    simpa only [hρ'] using hc
  have hd : ∀ c : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M,
      ReciprocityTheory.Gal.d1 ρ c = ReciprocityTheory.Gal.d1 ρ' c := by
    intro c
    funext p
    rcases p with ⟨g, h⟩
    simp only [ReciprocityTheory.Gal.d1_apply, hρ']
  have e0 : {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ} ≃ {m : M // m ∈ ReciprocityTheory.Gal.H0 ρ'} := by
    refine Equiv.subtypeEquivRight fun m => ?_
    rw [ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere]
    simp only [hρ']
  have c0 : Nat.card (ReciprocityTheory.Gal.H0 ρ) = Nat.card (ReciprocityTheory.Gal.H0 ρ') := Nat.card_congr e0
  have e1 : ReciprocityTheory.Gal.H1 ρ ≃ ReciprocityTheory.Gal.H1 ρ' :=
    subquotEquiv _ _ _ _
      (fun f => by rw [ReciprocityTheory.Gal.mem_Z1_iff_cocycle, ReciprocityTheory.Gal.mem_Z1_iff_cocycle]; simp only [hρ'])
      (fun f => by rw [ReciprocityTheory.Gal.mem_coboundaries1, ReciprocityTheory.Gal.mem_coboundaries1]; simp only [hρ'])
  have e2 : ReciprocityTheory.Gal.H2 ρ ≃ ReciprocityTheory.Gal.H2 ρ' :=
    subquotEquiv _ _ _ _
      (fun f => by rw [ReciprocityTheory.Gal.mem_cocycles2, ReciprocityTheory.Gal.mem_cocycles2]; simp only [hρ'])
      (fun f => by rw [ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]; simp only [hd])

  obtain ⟨-, f1, f2, -⟩ := hF F Ω l 1 M S ρ' one_pos hS hc'
  have hreal : ∀ w : InfinitePlace F, ¬ w.IsReal := fun w =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
  have heq := hE F Ω l 1 M S ρ' one_pos hS hc' (fun _ => 1) (fun w hw => absurd hw (hreal w))

  have harch : archH0Card S ρ' (fun _ => 1) = Nat.card M ^ InfinitePlace.nrComplexPlaces F := by
    classical
    unfold archH0Card
    rw [Finset.prod_eq_one, one_mul]
    intro w hw
    exact absurd (Finset.mem_filter.mp hw).2 (hreal w)
  rw [harch, IsTotallyComplex.finrank] at heq
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e1, c0, Nat.card_congr e2]
  have hpos : 0 < Nat.card M ^ InfinitePlace.nrComplexPlaces F := pow_pos Nat.card_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← heq, two_mul, pow_add]
  ring

end GlobalTheory.EulerScalars
end

