import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0626
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0645
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0596
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstLiftXPowFrob
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' k'' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]
  [Field k''] [CharP k'' p]

theorem wittMap_injective (σ : k →+* k') :
    Function.Injective ((algebraMap (WittVector p k') (Fr p k')).comp (WittVector.map σ)) :=
  (IsFractionRing.injective (WittVector p k') (Fr p k')).comp (WittVector.map_injective σ σ.injective)

def frMap (σ : k →+* k') : Fr p k →+* Fr p k' := IsFractionRing.lift (wittMap_injective p σ)

theorem frMap_algebraMap (σ : k →+* k') (w : WittVector p k) :
    frMap p σ (algebraMap _ _ w) = algebraMap _ _ (WittVector.map σ w) :=
  IsFractionRing.lift_algebraMap _ _

theorem frMap_id : frMap p (RingHom.id k) = RingHom.id (Fr p k) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp [frMap_algebraMap, WittVector.map_id]

theorem frMap_comp (σ : k →+* k') (τ : k' →+* k'') :
    frMap p (τ.comp σ) = (frMap p τ).comp (frMap p σ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap]
  congr 1

theorem map_lift {ι : Type} (σ : k →+* k') (f : MvPowerSeries ι k) :
    MvPowerSeries.map (frMap p σ) (lift p f) = lift p (MvPowerSeries.map σ f) := by
  ext α
  rw [coeff_map, coeff_lift, coeff_lift, frMap_algebraMap, WittVector.map_teichmuller, coeff_map]

theorem map_subst_lift {d e : ℕ} (τ : k' →+* k'') (ψ : Fin d → MvPowerSeries (Fin e) k')
    (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : MvPowerSeries (Fin d) (Fr p k')) :
    MvPowerSeries.map (frMap p τ) (subst (fun j => lift p (ψ j)) g) =
      subst (fun j => lift p (MvPowerSeries.map τ (ψ j))) (MvPowerSeries.map (frMap p τ) g) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero fun j => constantCoeff_lift p (hψ j))]
  simp only [map_lift]

theorem lift_X_pow {ι : Type} (i : ι) (n : ℕ) :
    lift p ((X i : MvPowerSeries ι k) ^ n) = X i ^ n := by
  classical
  ext α
  rw [coeff_lift, coeff_X_pow, coeff_X_pow]
  split_ifs <;> simp

theorem frobRing_eq (h : (p : k) = 0) : frobRing h = frobenius k p :=
  RingHom.ext fun r => by rw [frobRing_apply, frobenius_def]

theorem frMap_frobenius [PerfectRing k p] : frMap p (frobenius k p) = KatzF.sig p k := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap, KatzF.sig, WittVector.FractionRing.frobenius]
  rw [RingEquiv.coe_toRingHom, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  rw [← WittVector.frobenius_eq_map_frobenius]
  rfl

theorem subst_lift_X_pow_frob [PerfectRing k p] (h : (p : k) = 0) {d : ℕ}
    (f : MvPowerSeries (Fin d) (Fr p k)) :
    subst (fun j => lift p ((X j : MvPowerSeries (Fin d) k) ^ p)) (MvPowerSeries.map (frMap p (frobRing h)) f) =
      KatzF.frobS p f := by
  simp only [lift_X_pow, frobRing_eq p h, frMap_frobenius, KatzF.frobS]
  rfl

theorem ringHom_eq_of_app {q : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
    {σ : O →+* O'} {τ : O' →+* O''} {υ : O →+* O''} {G : PDivGroup q O} {G' : PDivGroup q O'}
    {G'' : PDivGroup q O''} (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (h : ∀ n a, u.app n a = t.app n (s.app n a)) : υ = τ.comp σ := by
  ext r
  have e := h 0 (r • 1)
  rw [(u.app 0).smul_map, (s.app 0).smul_map, (t.app 0).smul_map, map_one, map_one, map_one] at e
  have := congrArg (Coalgebra.counit (R := O'')) e
  simpa [Algebra.smul_def] using this

end GlobalTheory.Katz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePullHO2OfPullHO1
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pullHO2_surjective_of_wedge : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0})
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ),
    Function.Surjective (pullHO1 h) → WedgeO (OAff s') → Function.Surjective (pullHO2 h) := by
  first
  | exact @_root_.GlobalTheory.PullbackCupProduct.main
  | exact _root_.GlobalTheory.PullbackCupProduct.main
  | (apply _root_.GlobalTheory.PullbackCupProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PullbackCupProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PullbackCupProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PullbackCupProduct.main ..)

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapVariableGroupsFormalGroupLawCoboundaryOneCom
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.CobSwap

theorem hasSubst_swapVars {R : Type} [CommRing R] {d : ℕ} :
    HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (fun i => X (Sum.inl i))) :=
  hasSubst_of_constantCoeff_zero fun j => by cases j <;> simp

theorem swap_map {B Q : Type} [CommRing B] [CommRing Q] (h : B →+* Q) {d : ℕ}
    (c : MvPowerSeries (Fin d ⊕ Fin d) B) : swap (map h c) = map h (swap c) := by
  unfold swap at2
  rw [map_subst hasSubst_swapVars]
  congr 1
  funext j
  cases j <;> simp

theorem swap_subst {R : Type} [CommRing R] {d : ℕ} (ν : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (hν : ∀ i, constantCoeff (ν i) = 0) (f : MvPowerSeries (Fin d) R) :
    swap (subst ν f) = subst (fun i => swap (ν i)) f := by
  unfold swap at2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hν) hasSubst_swapVars]

theorem swap_inL {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inL f) = inR f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_inR {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) :
    swap (inR f) = inL f := by
  unfold swap at2 inL inR
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    hasSubst_swapVars]
  congr 1
  funext i
  rw [subst_X hasSubst_swapVars]
  rfl

theorem swap_sub {R : Type} [CommRing R] {d : ℕ} (a b : MvPowerSeries (Fin d ⊕ Fin d) R) :
    swap (a - b) = swap a - swap b := by
  unfold swap at2
  exact subst_sub hasSubst_swapVars a b

theorem swap_cob1_eq_of_swap_eq : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) →
    (∀ i, swap (μ i) = μ i) → ∀ g : MvPowerSeries (Fin d) Q,
    swap (cob1 (up Q μ) g) = cob1 (up Q μ) g := by
  intro B Q _ _ _ d μ h0 hs g
  have h0' : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, h0 i]
  have hs' : ∀ i, swap (up Q μ i) = up Q μ i := fun i => by
    simp only [up]; rw [swap_map, hs i]
  unfold cob1
  rw [swap_sub, swap_sub, swap_subst _ h0', swap_inL, swap_inR]
  simp only [hs']
  abel

end GlobalTheory.CobSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzValueOfFamily
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_value_of_family (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (r : ℝ) (τ₀ : ℍ) (Ω : ℂ)
    (hN : 0 < N) (hact : ActBij act) (hf : IsFam act w f) (hq : ∀ i, QAll (Sz l lam r) N (f i))
    (hj : Sz l lam 0 (jT τ₀)) (hΩ : Ω ^ 12 = DD τ₀) (i : ι) :
    Sz l lam r (f i τ₀ / Ω ^ w) := by
  refine GlobalTheory.T.algebraicValuationAtLeast_of_forall_rat_gt l lam r _ fun q hrq => ?_
  obtain ⟨c, hc0, hc, hc'⟩ := GlobalTheory.T.exists_algebraic_of_rational_valuation l lam q
  obtain ⟨R, hR, hcl⟩ := GlobalTheory.T.exists_integrallyClosed_padicIntegralSubring l lam
  obtain ⟨hconst, hmono, -, hmul, -⟩ := GlobalTheory.T.qExpansionValuationBound_ring_closure l lam N hN
  have hfam : IsFam act w fun i τ => c * f i τ := (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.1 w c f hf
  have hq' : ∀ i, QAll (· ∈ R) N fun τ => c * f i τ := fun i => by
    obtain ⟨a, ha, ha'⟩ := hmono _ 0 _ (by linarith) (hmul _ _ _ _ (hconst _ c hc) (hq i))
    exact ⟨a, ha, fun n => (hR _).2 (ha' n)⟩
  have hjR : IsIntegral R (jT τ₀) :=
    isIntegral_algebraMap (R := R) (A := ℂ) (x := ⟨jT τ₀, (hR _).2 hj⟩)
  have h0 : Sz l lam 0 (c * f i τ₀ / Ω ^ w) :=
    (hR _).1 (hcl _ (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N _ R τ₀ Ω hN hact hfam hq' hjR hΩ i))
  have h1 := (GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam).2.2.1 _ _ _ _ hc' h0
  have e : c⁻¹ * (c * f i τ₀ / Ω ^ w) = f i τ₀ / Ω ^ w := by
    rw [mul_div_assoc, inv_mul_cancel_left₀ hc0]
  rwa [add_zero, e] at h1

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentEqZeroOfFormalGroupLawCoboundaryOneEqZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.LieAdd

variable {R : Type} [CommRing R] {d : ℕ}

theorem subst_zero_of_constantCoeff {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    subst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) f = 0 := by
  have ha : HasSubst (fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun a => ?_
  by_cases h : a = 0
  · subst h
    rw [coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h
    have : (a.prod fun _ k => (0 : MvPowerSeries (Fin d) R) ^ k) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 (by simpa using hs))
        (zero_pow (by simpa using hs))
    rw [this, map_zero, smul_zero]

theorem constantCoeff_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [ih]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

theorem subst_nmul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) {f : MvPowerSeries (Fin d) R} (hf0 : constantCoeff f = 0)
    (hf : cob1 μ f = 0) (n : ℕ) : subst (nmul μ n) f = (n : R) • f := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul]
    exact subst_zero_of_constantCoeff hf0
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    have hb := hasSubst_of_constantCoeff_zero hs
    have hm : nmul μ (n + 1) = fun i => subst (Sum.elim (nmul μ n) fun i => X i) (μ i) := by
      rw [nmul, Function.iterate_succ_apply', ← nmul]; rfl
    have hc : subst μ f = inL f + inR f := by
      rw [cob1, sub_sub, sub_eq_zero] at hf; exact hf
    have hl0 : ∀ i, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    have hr0 : ∀ i, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
      fun _ => constantCoeff_X _
    rw [hm, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hμ) hb, hc,
      subst_add hb, inL, inR,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hl0) hb,
      subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hr0) hb]
    simp only [subst_X hb, Sum.elim_inl, Sum.elim_inr]
    rw [ih, subst_self, id, Nat.cast_succ, add_smul, one_smul]

theorem nmul_succ {S : Type} [CommRing S] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  rw [nmul, Function.iterate_succ_apply', ← nmul]

theorem up_nmul {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B} (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ n) = nmul (up Q μ) n := by
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j) <;> simp [constantCoeff_nmul hμ]
    funext i
    rw [nmul_succ, nmul_succ, ← ih]
    simp only [up, op, at2]
    rw [map_subst (hasSubst_of_constantCoeff_zero hs)]
    congr 1
    funext j
    rcases j with j | j <;> simp [map_X, up]

end GlobalTheory.QLog.LieAdd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem Chart.isLie_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (f : MvPowerSeries (Fin d) C),
    constantCoeff f = 0 → cob1 (up C c.μ) f = 0 → c.IsLie f 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c f hf0 hf
  have hμ := c.isLaw.const
  have hμC : ∀ i, constantCoeff (up C c.μ i) = 0 := fun i => by
    rw [up, constantCoeff_map, hμ, map_zero]
  refine (c.isLie_iff hv.hom_inj f 0).2 fun n => ⟨0, ?_, fun w φ _ => by simp⟩
  rw [map_zero, defect, LieAdd.up_nmul hμ, LieAdd.subst_nmul hμC hf0 hf, sub_self]

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTSummand

variable {R' : Type} [CommRing R'] {I : Ideal R'} {S : Scheme.{0}}

def crysAct (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) : O →+* Module.End R' (Crys κ t A) :=
  RingHom.mk'
    { toFun x := haveI := a.hom x; push κ t (a.act x)
      map_one' := haveI := a.hom 1; (push_congr κ t a.one).trans (push_id κ t)
      map_mul' x y := by
        haveI := a.hom
        exact (push_congr κ t (a.mul x y)).trans (push_comp κ t _ _) }
    fun x y ↦ by
      haveI := a.hom
      haveI : IsMonHom (a.act x * a.act y) := a.add x y ▸ a.hom _
      exact (push_congr κ t (a.add x y)).trans (push_mul κ t _ _)

theorem crysAct_apply (κ : DividedPowers I) (t : S ⟶ Sp R') {A : Over S} [GrpObj A] {O : Type} [Ring O]
    (a : GlobalTheory.UPel.HT.OActN O A) (x : O) (h : Crys κ t A) :
    crysAct κ t a x h = (haveI := a.hom x; push κ t (a.act x) h) := rfl

@[reducible] def tensorModOf {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) : Module (C ⊗[ℤ] B) H :=
  Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId C (Module.End C H)) ρ.toIntAlgHom
    fun r _ ↦ Algebra.commutes r _).toRingHom

theorem tensorModOf_tmul {C H B : Type*} [CommRing C] [AddCommGroup H] [Module C H] [CommRing B]
    (ρ : B →+* Module.End C H) (r : C) (x : B) (h : H) :
    (letI := tensorModOf ρ; (r ⊗ₜ[ℤ] x : C ⊗[ℤ] B) • h) = r • ρ x h := rfl

end GlobalTheory.HTSummand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProjectiveDvdOfCoordDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensor_projective_dvd_of_coord_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  intro O M _ _ _ N _ _ _ _ a z h
  obtain ⟨s, hs⟩ := (Module.Projective.out : ∃ s : M →ₗ[O] M →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  obtain ⟨s', hs'⟩ := (Module.Projective.out : ∃ s : N →ₗ[O] N →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  have hf : ∀ (w : M ⊗[O] N) (p : M × N), finsuppTensorFinsupp' O M N (TensorProduct.map s s' w) p =
      TensorProduct.dualDistrib O M N ((Finsupp.lapply p.1 ∘ₗ s) ⊗ₜ (Finsupp.lapply p.2 ∘ₗ s')) w := by
    intro w ⟨i, j⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply, dualDistrib_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  set f := finsuppTensorFinsupp' O M N (TensorProduct.map s s' z) with hfdef
  have hdiv : ∀ p, a ∣ f p := fun p => by rw [hfdef, hf]; exact h _ _
  choose c hc using hdiv
  let g : M × N →₀ O := ∑ p ∈ f.support, Finsupp.single p (c p)
  have hg : f = a • g := by
    simp only [g, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← hc]
    exact (Finsupp.sum_single f).symm
  have hid : (Finsupp.linearCombination O id : (M →₀ O) →ₗ[O] M) ∘ₗ s = LinearMap.id :=
    LinearMap.ext hs
  have hid' : (Finsupp.linearCombination O id : (N →₀ O) →ₗ[O] N) ∘ₗ s' = LinearMap.id :=
    LinearMap.ext hs'
  refine ⟨TensorProduct.map (Finsupp.linearCombination O id) (Finsupp.linearCombination O id)
    ((finsuppTensorFinsupp' O M N).symm g), ?_⟩
  rw [← map_smul, ← map_smul, ← hg, hfdef, LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, hid, hid', TensorProduct.map_id, LinearMap.id_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorSquarePerfectProjectionStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_map_nilpotent_sub_and_pow_of_projection : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A : Type) [CommRing A] [Algebra k A] (π : A →ₐ[k] A), ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : A ⊗[k] A, IsNilpotent (a - Algebra.TensorProduct.map π π a)) ∧ ∀ a : A ⊗[k] A, ∃ b : A ⊗[k] A, Algebra.TensorProduct.map π π a = Algebra.TensorProduct.map π π b ^ p) := by
  first | exact @GlobalTheory.tensorSquare_perfectProjection | exact GlobalTheory.tensorSquare_perfectProjection | (intros; apply GlobalTheory.tensorSquare_perfectProjection <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedVirtualCharacterNormOneSupport
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem kills_const_mul {G : Type} [Group G] [Finite G] (c : ℂ) (f Y : G → ℂ) (h : Kills f Y) :
    Kills (fun g => c * f g) Y := by
  intro V _ _ _ ρ hY
  have hk := h V ρ hY
  have : Fintype G := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype] at hk ⊢
  have e : (fun g => star (c * f g) • ρ g) = fun g => star c • (star (f g) • ρ g) := by
    funext g; rw [star_mul', mul_smul]
  simp only []
  rw [e, ← Finset.smul_sum, hk, smul_zero]

theorem kills_of_norm_one_of_pairing_prime :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime →
      s ≠ 1 → ∀ X ∈ Virt ℂ ℂ (G ⋊[φ] Γ), ∑ᶠ g, X (inl g * inr s) * star (X (inl g * inr s)) = (Nat.card G : ℂ) →
      ∀ Y : G → ℂ, IsChar ℂ ℂ Y → (∀ g, Y (φ s g) = Y g) → ∀ z : ℤ,
      ∑ᶠ g, X (inl g) * star (Y g) = z * (Nat.card G : ℂ) → ¬ ((Nat.card Γ : ℤ) ∣ z) →
      Kills (fun δ => X (inl δ * inr s)) Y := by
  intro G Γ _ _ _ _ φ s hp hs X hX hn Y hY hYs z hz hl
  obtain ⟨χ, e, hχ, hχG, hXe⟩ := GlobalTheory.T.virtualCharacter_coset_normOne_single G Γ φ s hp hs X hX hn
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
    intro t
    rw [zpowers_eq_top_of_prime_card rfl hs]
    exact Subgroup.mem_top t
  obtain ⟨Z, hZ, hZY⟩ := GlobalTheory.T.exists_semidirect_character_ext_of_stable G Γ φ s hgen Y hY hYs
  have hZv : Z ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := AddSubgroup.subset_closure hZ
  have hXZ : ∑ᶠ g, X (inl g) * star (Z (inl g)) = z * (Nat.card G : ℂ) := by
    simp only [hZY]; exact hz
  have hc := GlobalTheory.T.finsum_semidirect_coset_pairing_ne_zero G Γ φ s hp hs X hX Z hZv z hXZ hl
  have hχc : ∑ᶠ g, χ (inl g * inr s) * star (Z (inl g * inr s)) ≠ 0 := by
    intro h0
    apply hc
    have : (fun g => X (inl g * inr s) * star (Z (inl g * inr s)))
        = fun g => e * (χ (inl g * inr s) * star (Z (inl g * inr s))) := by
      funext g; rw [hXe, mul_assoc]
    rw [this, ← mul_finsum, h0, mul_zero]
  have hχchar : IsChar ℂ ℂ χ := by
    obtain ⟨n, ρ, -, h⟩ := hχ; exact ⟨n, ρ, h⟩
  have hχY : ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 := by
    intro h0
    apply hχc
    apply GlobalTheory.T.finsum_semidirect_coset_character_orth_zero G Γ φ s hp hs χ Z hχchar hZ
    simp only [hZY]; exact h0
  have hK := GlobalTheory.T.twisted_restricted_character_in_isotypic_part G Γ φ s χ Y hχchar hχG hY hχY
  have := kills_const_mul e _ Y hK
  simpa only [hXe] using this

end GlobalTheory.Shin
end

