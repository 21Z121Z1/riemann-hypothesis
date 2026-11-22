import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StrictlyHenselianIsColimit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLe
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TailSubstPAdicallySmallOfIntegralDifferential
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem GlobalTheory.tail_subst_small : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → ∀ m : ℕ, ∃ M0 : ℕ, ∀ M ≥ M0, ∀ n : σ →₀ ℕ, ∃ b : B, MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) (f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q)))) = algebraMap B Q (p ^ m * b) := by
  intro p hp B O Q _ _ _ _ θ hF σ _ _ z hz τ _ _ u f hu hD m
  have hpr : p.Prime := hp.out
  obtain ⟨L, hL⟩ := GlobalTheory.T.pow_dvd_eval_trunc_of_high_order p B σ z hz
  obtain ⟨M0, hM0⟩ := GlobalTheory.T.add_mul_le_of_pow_le_of_large p L m hpr.two_le
  refine ⟨M0, fun M hM n => ?_⟩
  set g : MvPowerSeries τ Q := f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q) with hg
  have hfin := Finsupp.finite_of_degree_le (σ := τ) n.degree
  rw [GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum B Q σ τ z u hu g n hfin.toFinset (fun α hα => by simpa using hα)]

  have key : ∀ α : τ →₀ ℕ, ∃ b : B, coeff α g * algebraMap B Q (MvPolynomial.eval z
      (trunc' B n (α.prod fun j e => u j ^ e))) = algebraMap B Q (p ^ m * b) := by
    intro α
    by_cases hα : α ≤ Finsupp.equivFunOnFinite.symm fun _ => M
    · refine ⟨0, ?_⟩
      have : coeff α g = 0 := by
        simp [hg, coeff_trunc', hα]
      simp [this]
    · have hcg : coeff α g = coeff α f := by
        simp [hg, coeff_trunc', hα]
      rw [hcg]
      obtain ⟨i, hi⟩ : ∃ i, M < α i := by
        by_contra h
        push_neg at h
        exact hα (fun i => by simpa using h i)
      obtain ⟨b, -, hb⟩ := hD α i
      obtain ⟨v, n', hn', hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := α i) (by omega) p hpr.one_lt.ne'
      have hcop : Nat.Coprime n' p := ((Nat.Prime.coprime_iff_not_dvd hpr).2 hn').symm
      obtain ⟨w, hw⟩ := (hF.unit_coprime n' hcop).exists_right_inv
      have hn'pos : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hdec; omega)
      have hpv : p ^ v ≤ α.degree := by
        have : p ^ v ≤ α i := by rw [hdec]; exact Nat.le_mul_of_pos_right _ hn'pos
        exact this.trans (Finsupp.le_degree i α)
      have hdeg : (v + m) * L ≤ α.degree :=
        hM0 α.degree v (by have := Finsupp.le_degree i α; omega) hpv
      obtain ⟨c, hc⟩ := hL (v + m) (α.prod fun j e => u j ^ e) (fun β hβ =>
        GlobalTheory.T.coeff_finsuppProd_constFree_eq_zero_of_degree_lt B σ τ u hu α β (by rw [mul_comm] at hβ; omega)) n
      refine ⟨b * w * c, ?_⟩
      rw [hc]
      rw [hdec] at hb
      have hw' := congrArg (algebraMap B Q) hw
      simp only [map_mul, map_pow, map_natCast, map_one, Nat.cast_mul, Nat.cast_pow] at hb hw' ⊢
      linear_combination ((p : Q) ^ m * algebraMap B Q w * algebraMap B Q c) * hb
        - (coeff α f * (p : Q) ^ (v + m) * algebraMap B Q c) * hw'
  choose bb hbb using key
  refine ⟨∑ α ∈ hfin.toFinset, bb α, ?_⟩
  rw [Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun α _ => hbb α
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCompChain
section
set_option autoImplicit false

open Filter Topology

namespace GlobalTheory.PeriodFamily

section
variable {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)

theorem taylor_finset_sum_chain {ι : Type} (S : Finset ι) (f : ι → (I → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    taylor N t (fun z ↦ ∑ i ∈ S, f i z) = ∑ i ∈ S, taylor N t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.2.1 0
  | insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    rw [(GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).1 (f i) (fun z ↦ ∑ i ∈ S, f i z) (hf i)
      (Finset.analyticAt_fun_sum S fun j _ ↦ hf j), ih]

theorem taylor_finset_prod_chain (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {ι : Type} (S : Finset ι)
    (f : ι → (I → ℂ) → ℂ) (hf : ∀ i, AnalyticAt ℂ (f i) 0) :
    taylor N t (fun z ↦ ∏ i ∈ S, f i z) = ∏ i ∈ S, taylor N t (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.2.1 1
  | insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    rw [GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht (f i) (fun z ↦ ∏ i ∈ S, f i z) (hf i)
      (Finset.analyticAt_fun_prod S fun j _ ↦ hf j), ih]

end

theorem taylor_comp_chain : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {K : Type} [Fintype K] [DecidableEq K] (Φ : (I → ℂ) → K → ℂ) (h : (K → ℂ) → ℂ), AnalyticAt ℂ Φ 0 → Φ 0 = 0 → AnalyticAt ℂ h 0 → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (Φ z)) = GlobalTheory.PeriodFamily.taylor N (fun k ↦ GlobalTheory.PeriodFamily.taylor N t fun z ↦ Φ z k) h := by
  intro I _ _ D _ _ N t ht K _ _ Φ h hΦ h0 hh
  have hk : ∀ k, AnalyticAt ℂ (fun z ↦ Φ z k) 0 := fun k ↦ analyticAt_pi_iff.1 hΦ k
  have hhΦ : AnalyticAt ℂ (fun z ↦ h (Φ z)) 0 := AnalyticAt.comp (g := h) (f := Φ) (by rw [h0]; exact hh) hΦ
  have hprod : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ ∏ a, Φ z (s a)) 0 := fun k s ↦
    Finset.analyticAt_fun_prod _ fun a _ ↦ hk (s a)
  set c : (k : ℕ) → (Fin k → K) → ℂ := fun k s ↦
    (k.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ k h 0 fun a ↦ Pi.single (s a) 1 with hc
  have hP : (fun z ↦ taylor N (Φ z) h) =
      fun z ↦ ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a) := by
    funext z
    simp only [taylor, smul_eq_mul, hc]
  have hterm : ∀ (k : ℕ) (s : Fin k → K), AnalyticAt ℂ (fun z ↦ c k s * ∏ a, Φ z (s a)) 0 := fun k s ↦
    analyticAt_const.mul (hprod k s)
  have hin : ∀ k : ℕ, AnalyticAt ℂ (fun z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) 0 := fun k ↦
    Finset.analyticAt_fun_sum _ fun s _ ↦ hterm k s
  have hPa : AnalyticAt ℂ (fun z ↦ taylor N (Φ z) h) 0 := by
    rw [hP]
    exact Finset.analyticAt_fun_sum _ fun k _ ↦ hin k
  have hra : AnalyticAt ℂ (fun z ↦ h (Φ z) - taylor N (Φ z) h) 0 := hhΦ.sub hPa
  have htend : Tendsto Φ (𝓝 0) (𝓝 0) := by
    have := hΦ.continuousAt.tendsto
    rwa [h0] at this
  have hO : Φ =O[𝓝 0] fun z : I → ℂ ↦ z := by
    have := hΦ.differentiableAt.isBigO_sub
    simpa [h0] using this
  have hr : (fun z ↦ h (Φ z) - taylor N (Φ z) h) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1) :=
    ((GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat N h hh).1.comp_tendsto htend).trans (hO.norm_norm.pow (N + 1))
  have hz : taylor N t (fun z ↦ h (Φ z) - taylor N (Φ z) h) = 0 := (GlobalTheory.T.taylorRemainder_isBigO_and_taylor_flat N _ hra).2 hr t
  have hsplit : (fun z ↦ h (Φ z)) = fun z ↦ (h (Φ z) - taylor N (Φ z) h) + taylor N (Φ z) h := by
    funext z; ring
  rw [hsplit, (GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).1 _ _ hra hPa, hz, zero_add, hP,
    taylor_finset_sum_chain N t _ (fun k z ↦ ∑ s : Fin k → K, c k s * ∏ a, Φ z (s a)) hin]
  conv_rhs => rw [taylor]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [taylor_finset_sum_chain N t _ (fun s z ↦ c k s * ∏ a, Φ z (s a)) (hterm k)]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [(GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t).2.1 _ _ (hprod k s),
    taylor_finset_prod_chain N t ht _ (fun a z ↦ Φ z (s a)) fun a ↦ hk (s a)]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCoordAndEval
section
open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_coord_of_nilpotent {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D) (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (i : I) :
    taylor N t (fun z ↦ z i) = t i := by
  have hd : (fun y : I → ℂ ↦ fderiv ℂ (fun z : I → ℂ ↦ z i) y) =
      fun _ ↦ ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i := by
    funext y
    exact (hasFDerivAt_apply i y).fderiv
  have h2 : ∀ (k : ℕ) (v : Fin (k + 1 + 1) → I → ℂ),
      iteratedFDeriv ℂ (k + 1 + 1) (fun z : I → ℂ ↦ z i) 0 v = 0 := by
    intro k v
    rw [iteratedFDeriv_succ_apply_right, hd, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
    simp
  have h1 : ∀ v : Fin 1 → I → ℂ, iteratedFDeriv ℂ 1 (fun z : I → ℂ ↦ z i) 0 v = v 0 i := by
    intro v
    rw [iteratedFDeriv_one_apply, congrFun hd 0]
    simp
  unfold taylor
  cases N with
  | zero =>
    have := ht fun _ ↦ i
    simp at this
    simp [this]
  | succ N =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [h2, mul_zero, zero_smul, Finset.sum_const_zero, zero_add, h1]
    rw [Finset.sum_eq_single (fun _ ↦ i)]
    · simp
    · intro s _ hs
      have : s 0 ≠ i := fun h ↦ hs (funext fun a ↦ by rw [Fin.fin_one_eq_zero a, h])
      simp [Pi.single_eq_of_ne' this]
    · simp

theorem taylor_coord_and_eval : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → (∀ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ z i) = t i) ∧ ∀ P : MvPolynomial I ℂ, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ MvPolynomial.eval z P) = MvPolynomial.aeval t P := by
  intro I _ _ D _ _ N t ht
  refine ⟨taylor_coord_of_nilpotent N t ht, fun P ↦ ?_⟩
  obtain ⟨hadd, -, hconst, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hc : ∀ i, AnalyticAt ℂ (fun z : I → ℂ ↦ z i) 0 := fun i ↦
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ↦ ℂ) i).analyticAt 0
  have han : ∀ Q : MvPolynomial I ℂ, AnalyticAt ℂ (fun z : I → ℂ ↦ MvPolynomial.eval z Q) 0 := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add p q hp hq => simpa using hp.fun_add hq
    | mul_X p i hp => simpa using hp.fun_mul (hc i)
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hconst a
  | add p q hp hq =>
    simp only [map_add]
    rw [hadd _ _ (han p) (han q), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X, MvPolynomial.aeval_X]
    rw [GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht _ _ (han p) (hc i), hp, taylor_coord_of_nilpotent N t ht]

end GlobalTheory.PeriodFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCountCompactFinite
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.GmPhiNoeth

theorem coeff_laurentMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem laurentMap_id (R : Type) [CommRing R] : laurentMap (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun p => AddMonoidAlgebra.ext (Finsupp.ext fun n => by rw [coeff_laurentMap]; rfl)

def laurentFunctor : CommRingCat.{0} ⥤ CommRingCat.{0} where
  obj R := CommRingCat.of (LaurentPolynomial R)
  map f := CommRingCat.ofHom (laurentMap f.hom)
  map_id R := by
    change CommRingCat.ofHom (laurentMap (RingHom.id R)) = _
    rw [laurentMap_id]; rfl
  map_comp f g := by
    change CommRingCat.ofHom (laurentMap (g.hom.comp f.hom)) = _
    rw [GmPhiNat.laurentMap_comp]; rfl

def isColimit_laurent {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
    (hc : IsColimit c) : IsColimit (laurentFunctor.mapCocone c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have hc' : IsColimit ((forget CommRingCat.{0}).mapCocone c) := isColimitOfPreserves _ hc

  have hsurj : ∀ a : c.pt, ∃ j, ∃ b : D.obj j, (c.ι.app j).hom b = a := fun a =>
    Types.jointly_surjective_of_isColimit hc' a

  have hker : ∀ j (b : D.obj j), (c.ι.app j).hom b = 0 → ∃ k, ∃ f : j ⟶ k, (D.map f).hom b = 0 := by
    intro j b hb
    have h := (Types.FilteredColimit.isColimit_eq_iff' hc' b 0).1 (by
      change (c.ι.app j).hom b = (c.ι.app j).hom 0
      rw [hb, map_zero])
    obtain ⟨k, f, hf⟩ := h
    refine ⟨k, f, ?_⟩
    change (D.map f).hom b = (D.map f).hom 0 at hf
    rw [hf, map_zero]
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : LaurentPolynomial (D.obj j)),
      laurentMap (c.ι.app k).hom (laurentMap (D.map f).hom y) = laurentMap (c.ι.app j).hom y := by
    intro j k f y
    rw [← RingHom.comp_apply, ← GmPhiNat.laurentMap_comp, ← CommRingCat.hom_comp, c.w f]
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (laurentFunctor.mapCocone c)) ?_ ?_)
  · intro (x : LaurentPolynomial c.pt)
    suffices h : ∃ j, ∃ y : LaurentPolynomial (D.obj j), laurentMap (c.ι.app j).hom y = x by
      obtain ⟨j, y, hy⟩ := h
      exact ⟨j, y, hy.symm⟩
    induction x using LaurentPolynomial.induction_on' with
    | add p p' hp hp' =>
      obtain ⟨j, y, rfl⟩ := hp
      obtain ⟨j', y', rfl⟩ := hp'
      refine ⟨IsFiltered.max j j', laurentMap (D.map (IsFiltered.leftToMax j j')).hom y +
        laurentMap (D.map (IsFiltered.rightToMax j j')).hom y', ?_⟩
      rw [map_add, hw, hw]
    | C_mul_T n a =>
      obtain ⟨j, b, rfl⟩ := hsurj a
      refine ⟨j, LaurentPolynomial.C b * LaurentPolynomial.T n, ?_⟩
      rw [map_mul, GmPhiNat.laurentMap_T, ← RingHom.comp_apply, GmPhiNat.laurentMap_C, RingHom.comp_apply]
  · intro i j (xi : LaurentPolynomial (D.obj i)) (xj : LaurentPolynomial (D.obj j)) h
    change laurentMap (c.ι.app i).hom xi = laurentMap (c.ι.app j).hom xj at h
    let m := IsFiltered.max i j
    let fi := IsFiltered.leftToMax i j
    let fj := IsFiltered.rightToMax i j
    let z : LaurentPolynomial (D.obj m) := laurentMap (D.map fi).hom xi - laurentMap (D.map fj).hom xj
    have hz : laurentMap (c.ι.app m).hom z = 0 := by
      simp only [z, map_sub, hw, h, sub_self]

    have hfin : ∀ s : Finset ℤ, ∃ k, ∃ h : m ⟶ k, ∀ n ∈ s, (D.map h).hom (z.coeff n) = 0 := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => exact ⟨m, 𝟙 m, fun n hn => absurd hn (Finset.notMem_empty n)⟩
      | insert n s _ ih =>
        obtain ⟨k₁, h₁, hk₁⟩ := ih
        have hn : (c.ι.app m).hom (z.coeff n) = 0 := by
          rw [← coeff_laurentMap, hz]; rfl
        obtain ⟨k₂, h₂, hk₂⟩ := hker m _ hn
        obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span h₁ h₂
        refine ⟨k, h₁ ≫ g₁, fun n' hn' => ?_⟩
        rcases Finset.mem_insert.1 hn' with rfl | hn'
        · rw [hg, D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₂, map_zero]
        · rw [D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₁ n' hn', map_zero]
    obtain ⟨k, hmk, hk⟩ := hfin z.coeff.support
    have hz0 : laurentMap (D.map hmk).hom z = 0 := by
      refine AddMonoidAlgebra.ext (Finsupp.ext fun n => ?_)
      rw [coeff_laurentMap]
      by_cases hn : n ∈ z.coeff.support
      · exact hk n hn
      · rw [Finsupp.notMem_support_iff.1 hn, map_zero]; rfl
    refine ⟨k, fi ≫ hmk, fj ≫ hmk, ?_⟩
    change laurentMap (D.map (fi ≫ hmk)).hom xi = laurentMap (D.map (fj ≫ hmk)).hom xj
    rw [D.map_comp, D.map_comp, CommRingCat.hom_comp, CommRingCat.hom_comp, GmPhiNat.laurentMap_comp,
      GmPhiNat.laurentMap_comp, RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub]
    exact hz0

end GlobalTheory.EtC.GmPhiNoeth

open GlobalTheory.EtC.GmPhiNoeth in

theorem GlobalTheory.EtC.gmPhi_surjective_of_noetherian : ∀ (q : ℕ) [NeZero q],
    (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
      Function.Surjective (gmPhi q A i)) →
    ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  intro q _ hN A _ hSH hq i x
  obtain ⟨hH, hsep⟩ := hSH
  obtain ⟨J, _, _, D, ι, hc, hl, hst, hqj, -, -⟩ :=
    GlobalTheory.SHColim.strictlyHenselian_isColimit q A ⟨hH, hsep⟩ hq
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ laurentFunctor) _ (isColimit_laurent hc) 1 i).1 x hqL
  obtain ⟨B, _, _, s, hs⟩ := hst j
  haveI := hl j
  haveI : IsNoetherianRing (D.obj j) := GlobalTheory.StalkNoeth.isNoetherianRing_of_isStalk B (D.obj j) s hs
  obtain ⟨b, hb⟩ := hN (D.obj j) hs.1 (hqj j) i y
  have hn := gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (A := D.obj j) (B := A) (ι.app j).hom (hqj j) i b
  rw [hb] at hn
  exact ⟨_, hn.symm.trans hy⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryChartSectionFrameEntriesHasStrictFDerivAtStatement
section
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.SUVol GlobalTheory.RiemConst GlobalTheory.SUChartSection
open scoped ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryChartSectionFrameEntries_hasStrictFDerivAt : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {x : Frame X.Ψ r}, IsOrth X x → HasStrictFDerivAt (yF X) (dY X) 0 := by
  first | exact @GlobalTheory.SUChartSection.yF_hasStrictFDerivAt | exact GlobalTheory.SUChartSection.yF_hasStrictFDerivAt | (intros; apply GlobalTheory.SUChartSection.yF_hasStrictFDerivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesOnEtaleNeighbourhood
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vanishes_on_etale_neighbourhood : ∀ (q : ℕ) (B O : Type) [CommRing B] [CommRing O] [Algebra B O], IsUnit (q : B) → IndEt B O → ∀ (n i : ℤ) (y : Ht q (sp B) n i), pull _ (spMap (algebraMap B O)) _ _ y = 0 → ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (_ : D →ₐ[B] O), pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  first | (exact @GlobalTheory.EtC.exists_etale_kill_of_indEt) | (exact GlobalTheory.EtC.exists_etale_kill_of_indEt) | (intros; apply GlobalTheory.EtC.exists_etale_kill_of_indEt  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedIdempotent_localShare_bad_tuples_le : ∀ (D : D7) (ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ), (∀ k, ψ₀ k ≠ 1) → admLq D → TieAdmG D → 100 ≤ D.R.r → (∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k) → ∀ (k : Fin 2) (S : Finset (Tup D k)), (∀ t ∈ S, ¬ goodAt D k t) → locShare D (fun k _ => eUk D k (ψ₀ k)) k S ≤ 3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) * Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) * (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) + (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ))) := by
  first | exact @GlobalTheory.PropWU.propW_eUk | exact GlobalTheory.PropWU.propW_eUk | (intros; apply GlobalTheory.PropWU.propW_eUk <;> assumption)
end

